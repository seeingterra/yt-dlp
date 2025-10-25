#!/usr/bin/env python3
"""
Web-based channel monitor for yt-dlp.

This provides a simple web GUI to add/remove channels, view status, logs and trigger
monitoring/downloads. It uses Flask and a background thread to run yt-dlp for each
configured channel. Designed to be lightweight and easy to run from the source tree.

Run (example):
  pip install -r devscripts/requirements-web.txt
  python devscripts/web_monitor.py --channels channels.txt --output-dir downloads --interval 1800

Open http://localhost:8080/ in your browser.
"""
from __future__ import annotations

import argparse
import json
import logging
import shlex
import subprocess
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional

import re
from urllib.parse import urlsplit, unquote

import requests
from flask import Flask, jsonify, redirect, render_template, request, url_for, send_file
import shutil
import os

# Try to load .env if python-dotenv is available; falling back to environment variables.
try:
    from dotenv import load_dotenv
    # load .env from repository root (same dir as this file's parent parent) then cwd
    repo_root = Path(__file__).parent.parent
    load_dotenv(repo_root / '.env')
    load_dotenv()
except Exception:
    # python-dotenv not installed; rely on existing environment variables
    pass


LOG = logging.getLogger("web_monitor")


def get_platform(url: str) -> str:
    """Heuristic platform name from a channel URL (used to create per-platform folders)."""
    try:
        host = urlsplit(url).netloc.lower()
    except Exception:
        host = (url or '').lower()
    if 'odysee.com' in host or 'lbry' in host:
        return 'odysee'
    if 'rumble.com' in host:
        return 'rumble'
    # fallback: simplified host name
    name = re.sub(r'[^a-z0-9]+', '_', host)
    return name or 'other'


def parse_args():
    p = argparse.ArgumentParser(description="Run web GUI monitor for yt-dlp")
    p.add_argument("--channels", "-c", required=True, help="Channels file (one URL per line)")
    p.add_argument("--interval", "-i", type=int, default=3600, help="Polling interval in seconds")
    p.add_argument("--output-dir", "-o", default=".", help="Download output directory")
    p.add_argument("--archive-dir", default=".archives", help="Directory to store download archives")
    p.add_argument("--host", default="127.0.0.1", help="Host to bind the web server")
    p.add_argument("--port", type=int, default=8080, help="Port for the web server")
    p.add_argument("--python", default=None, help="Python executable to run yt-dlp (default: current env)" )
    p.add_argument("--yt-args", default="-f best", help="Extra default yt-dlp args to use for downloads")
    p.add_argument("--concurrency", type=int, default=1, help="Max concurrent downloads (default 1)")
    p.add_argument("--auth-user", default=None, help="Username for basic auth (optional)")
    p.add_argument("--auth-pass", default=None, help="Password for basic auth (optional)")
    p.add_argument("--webhook", default=None, help="Optional webhook URL to POST notifications when new items are downloaded")
    return p.parse_args()


def read_channels_file(path: Path) -> List[str]:
    if not path.exists():
        return []
    lines = []
    for ln in path.read_text(encoding="utf-8").splitlines():
        ln = ln.strip()
        if not ln or ln.startswith("#"):
            continue
        lines.append(ln)
    return lines


def write_channels_file(path: Path, channels: List[str]):
    path.write_text("\n".join(channels) + ("\n" if channels else ""), encoding="utf-8")


def safe_name(url: str) -> str:
    """Create a filesystem-safe short name for a channel URL.

    Rules:
    - Keep netloc + path (drop query/fragment)
    - Decode percent-encodings
    - Replace any run of characters that are not alphanumeric, dot, dash or underscore with a single underscore
    - Trim leading/trailing underscores and collapse multiple underscores
    - Limit length to a sensible value
    This handles Odysee channel URLs like /@NAME:d and URLs with query parts like ?view=content.
    """
    try:
        u = urlsplit(url)
        path = (u.netloc or '') + (u.path or '')
        s = unquote(path)
    except Exception:
        s = url

    # strip leading slashes
    s = s.lstrip('/')
    # Replace anything not allowed by Windows filenames with underscore (allow A-Z a-z 0-9 . _ -)
    s = re.sub(r'[^A-Za-z0-9._-]+', '_', s)
    # collapse multiple underscores
    s = re.sub(r'_+', '_', s)
    # trim underscores
    s = s.strip('_')
    if not s:
        s = 'channel'
    return s[:200]


class ChannelState:
    def __init__(self, url: str, archive_dir: Path, base_out_dir: Path):
        self.url = url
        self.archive_file = archive_dir / (safe_name(url) + ".archive")
        self.log_file = archive_dir / (safe_name(url) + ".log")
        self.platform = get_platform(url)
        # per-platform folder, then channel-safe name
        self.out_dir = base_out_dir / self.platform / safe_name(url)
        self.lock = threading.Lock()
        self.is_running = False
        self.last_run: Optional[float] = None
        self.last_status: Optional[str] = None
        self.total_downloads: int = 0
        # optional metadata populated by _fetch_channel_metadata
        self.thumbnail: Optional[str] = None
        self.display_name: Optional[str] = None
        # total number of videos in the channel (if known)
        self.total_videos: Optional[int] = None
        # track currently active download items -> map name -> progress dict
        self.active_items: Dict[str, Dict[str, Optional[str]]] = {}
        self.completed_items: List[str] = []
        # process handle for the currently running yt-dlp (if any)
        self.proc: Optional[subprocess.Popen] = None
        # pause/resume controls
        self.paused: bool = False
        self.pause_requested_items: set = set()

    def load_total_downloads(self):
        if self.archive_file.exists():
            try:
                self.total_downloads = sum(1 for _ in self.archive_file.read_text(encoding="utf-8").splitlines() if _.strip())
            except Exception:
                self.total_downloads = 0
        else:
            self.total_downloads = 0


class Monitor(threading.Thread):
    def __init__(self, channels_file: Path, archive_dir: Path, out_dir: Path, interval: int, python_exec: Optional[str], yt_args: str, concurrency: int = 1, webhook: Optional[str] = None):
        super().__init__(daemon=True)
        self.channels_file = channels_file
        self.archive_dir = archive_dir
        self.out_dir = out_dir
        self.interval = interval
        self.python_exec = python_exec
        self.yt_args = yt_args
        self.concurrency = max(1, int(concurrency))
        self.webhook = webhook
        # enabled controls whether the monitor will start downloads automatically
        # default: False -> require user to "Start Sync" from the UI
        self.enabled: bool = False
        self.states: Dict[str, ChannelState] = {}
        self._stop = threading.Event()
        self._reload = threading.Event()
        # semaphores per platform so rumble and odysee can run concurrently even if concurrency==1
        self.platform_semaphores: Dict[str, threading.Semaphore] = {}

        archive_dir.mkdir(parents=True, exist_ok=True)
        out_dir.mkdir(parents=True, exist_ok=True)

    def _fetch_channel_metadata(self, state: ChannelState):
        """Fetch simple channel metadata (thumbnail/title) using yt-dlp --dump-single-json and store in state."""
        try:
            cmd = []
            if self.python_exec:
                cmd = [self.python_exec, '-m', 'yt_dlp', '--dump-single-json', state.url]
            else:
                cmd = ['python', '-m', 'yt_dlp', '--dump-single-json', state.url]
            proc = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, timeout=30)
            if proc.returncode == 0 and proc.stdout:
                try:
                    data = json.loads(proc.stdout)
                    thumb = data.get('thumbnail')
                    title = data.get('title')
                    # try to discover total entries / playlist size
                    total = None
                    # several extractor keys may contain counts
                    for k in ('n_entries', 'playlist_count', 'count', 'entries_count', 'total_videos'):
                        v = data.get(k)
                        if isinstance(v, int) and v >= 0:
                            total = v
                            break
                    # fallback: entries list length
                    if total is None and isinstance(data.get('entries'), list):
                        try:
                            total = len(data.get('entries'))
                        except Exception:
                            total = None
                    with state.lock:
                        state.thumbnail = thumb
                        state.display_name = title
                        state.total_videos = total
                except Exception:
                    LOG.exception('Failed to parse channel metadata for %s', state.url)
        except Exception:
            LOG.exception('Failed to fetch channel metadata for %s', state.url)

    def _write_metadata_txt_for_file(self, state: ChannelState, dest_name: str):
        """Given the Destination filename (full path), find the .info.json produced by yt-dlp and write a .txt with selected metadata.
        dest_name is the full path string as printed by yt-dlp Destination. It may be absolute or relative; normalize.
        """
        try:
            # Normalize to Path
            p = Path(dest_name)
            if not p.is_absolute():
                # assume it's relative to out_dir
                p = state.out_dir / dest_name
            # info json path is video + .info.json
            info_json = Path(str(p) + '.info.json')
            txt_path = Path(str(p).rsplit('.', 1)[0] + '.txt')
            if info_json.exists():
                try:
                    info = json.loads(info_json.read_text(encoding='utf-8', errors='ignore'))
                except Exception:
                    LOG.exception('Failed to read info json for %s', info_json)
                    return
                # Compose text: title, uploader, upload_date (YYYYMMDD -> ISO), webpage_url, description
                lines = []
                lines.append(f"title: {info.get('title','')}")
                lines.append(f"uploader: {info.get('uploader','')}")
                upload_date = info.get('upload_date')
                if upload_date and len(upload_date) == 8:
                    lines.append(f"upload_date: {upload_date[:4]}-{upload_date[4:6]}-{upload_date[6:8]}")
                else:
                    lines.append(f"upload_date: {upload_date or ''}")
                lines.append(f"webpage_url: {info.get('webpage_url','')}")
                lines.append('')
                lines.append('description:')
                desc = info.get('description') or ''
                # Ensure consistent newlines
                desc = desc.replace('\r\n', '\n').replace('\r', '\n')
                lines.append(desc)
                try:
                    txt_path.parent.mkdir(parents=True, exist_ok=True)
                    txt_path.write_text('\n'.join(lines), encoding='utf-8')
                except Exception:
                    LOG.exception('Failed to write metadata txt for %s', txt_path)

                # try to download the thumbnail for this video (if present in info json)
                try:
                    self._download_thumbnail_for_file(state, p)
                except Exception:
                    LOG.exception('Failed to download thumbnail for %s', p)
        except Exception:
            LOG.exception('Error creating metadata txt for %s', dest_name)

    def run(self):
        LOG.info("Monitor thread started")
        while not self._stop.is_set():
            try:
                self.sync_channels()
                # Use ThreadPoolExecutor to run up to `concurrency` downloads concurrently.
                # Only submit channels that are not already running and not paused and only when enabled.
                to_run = []
                if self.enabled:
                    to_run = [st for st in list(self.states.values()) if not st.is_running and not st.paused]
                if to_run:
                    with ThreadPoolExecutor(max_workers=self.concurrency) as exc:
                        futures = {exc.submit(self.run_for_channel, st): st for st in to_run}
                        for fut in as_completed(futures):
                            try:
                                fut.result()
                            except Exception:
                                LOG.exception("Task raised")
                # Wait interval or until reload
                self._reload.wait(timeout=self.interval)
                self._reload.clear()
            except Exception:
                LOG.exception("Error in monitor loop")

    def stop(self):
        self._stop.set()
        self._reload.set()

    def _download_thumbnail_for_file(self, state: ChannelState, p: Path):
        """Given the Path to a downloaded video file, look for its .info.json and download the thumbnail URL if present.
        Save thumbnail next to the video with suffix '.thumbnail.<ext>' (e.g. video.thumbnail.jpg).
        """
        try:
            info_json = Path(str(p) + '.info.json')
            if not info_json.exists():
                return
            try:
                info = json.loads(info_json.read_text(encoding='utf-8', errors='ignore'))
            except Exception:
                return
            thumb = info.get('thumbnail')
            if not thumb:
                return
            # choose extension from URL path or Content-Type
            ext = None
            try:
                up = urlsplit(thumb)
                path = up.path or ''
                import os
                _, e = os.path.splitext(path)
                if e and len(e) <= 5:
                    ext = e
            except Exception:
                ext = None
            # fallback to HEAD request to get content-type
            if not ext:
                try:
                    r = requests.head(thumb, allow_redirects=True, timeout=10)
                    ctype = r.headers.get('Content-Type', '')
                    if 'jpeg' in ctype or 'jpg' in ctype:
                        ext = '.jpg'
                    elif 'png' in ctype:
                        ext = '.png'
                    elif 'webp' in ctype:
                        ext = '.webp'
                except Exception:
                    ext = None
            if not ext:
                ext = '.jpg'
            thumb_path = p.with_suffix('.thumbnail' + ext)
            # stream download and save
            try:
                r = requests.get(thumb, stream=True, timeout=20)
                if r.status_code == 200:
                    thumb_path.parent.mkdir(parents=True, exist_ok=True)
                    with thumb_path.open('wb') as fh:
                        for chunk in r.iter_content(8192):
                            if chunk:
                                fh.write(chunk)
            except Exception:
                LOG.exception('Failed to fetch thumbnail %s', thumb)
        except Exception:
            LOG.exception('Error in _download_thumbnail_for_file for %s', p)

    def reload(self):
        self._reload.set()

    def set_output_dir(self, new_out: Path):
        try:
            new_out.mkdir(parents=True, exist_ok=True)
            self.out_dir = new_out
            # update each state's out_dir
            for st in self.states.values():
                st.out_dir = self.out_dir / st.platform / safe_name(st.url)
                try:
                    st.out_dir.mkdir(parents=True, exist_ok=True)
                except Exception:
                    LOG.exception('Failed to create out_dir for %s', st.url)
            return True
        except Exception:
            LOG.exception('Failed to set output dir %s', new_out)
            return False

    def sync_channels(self):
        urls = read_channels_file(self.channels_file)
        # Add new
        for u in urls:
            if u not in self.states:
                st = ChannelState(u, self.archive_dir, self.out_dir)
                st.load_total_downloads()
                self.states[u] = st
                # fetch channel metadata (thumbnail, title) in background
                try:
                    threading.Thread(target=self._fetch_channel_metadata, args=(st,), daemon=True).start()
                except Exception:
                    LOG.exception('Failed to start metadata fetch thread for %s', u)
        # Remove missing
        for u in list(self.states.keys()):
            if u not in urls:
                del self.states[u]

    def run_for_channel(self, state: ChannelState):
        # Acquire per-platform semaphore so different platforms can run concurrently
        sem = self.platform_semaphores.setdefault(state.platform, threading.Semaphore(self.concurrency))
        acquired = False
        try:
            sem.acquire()
            acquired = True
            with state.lock:
                state.is_running = True
                state.last_run = time.time()
                state.last_status = None
            LOG.info("Running yt-dlp for %s (platform=%s) -> out: %s", state.url, state.platform, state.out_dir)

            # Normalize some common channel URL patterns to forms supported by extractors.
            effective_url = state.url
            try:
                us = urlsplit(state.url)
                host = (us.netloc or '').lower()
                path = (us.path or '').lstrip('/')
                if 'rumble.com' in host and path and not any(path.startswith(p) for p in ('c/', 'user/', 'v', 'videos', 'embed')):
                    slug = path.split('/')[0]
                    alt = f'https://rumble.com/c/{slug}'
                    LOG.info('Normalizing rumble channel url %s -> %s', state.url, alt)
                    effective_url = alt
            except Exception:
                effective_url = state.url

            # count previous downloads to detect new ones
            prev_count = 0
            if state.archive_file.exists():
                try:
                    prev_count = sum(1 for _ in state.archive_file.read_text(encoding="utf-8").splitlines() if _.strip())
                except Exception:
                    prev_count = 0

            cmd = []
            if self.python_exec:
                cmd = [self.python_exec, "-m", "yt_dlp", effective_url]
            else:
                cmd = ["python", "-m", "yt_dlp", effective_url]
            cmd += ["-P", str(state.out_dir), "--download-archive", str(state.archive_file), "--newline", "--write-info-json", "--write-description"]
            if self.yt_args:
                cmd += shlex.split(self.yt_args)

            # Run subprocess and capture output to log, parse progress
            try:
                rc = -1
                with state.log_file.open("a", encoding="utf-8") as lf:
                    lf.write(f"\n===== Run at {datetime.utcnow().isoformat()} UTC =====\n")
                    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
                    state.proc = proc
                    assert proc.stdout is not None
                    # regexes for destination and progress
                    dest_re = re.compile(r'Destination:\s*(.+)$')
                    percent_re = re.compile(r'\[download\].*?(?P<percent>\d{1,3}(?:\.\d+)?)%.*?at\s+(?P<speed>\S+/?s)?\s+ETA\s+(?P<eta>\S+)', re.IGNORECASE)
                    current_name: Optional[str] = None
                    # ensure output directory exists
                    try:
                        state.out_dir.mkdir(parents=True, exist_ok=True)
                    except Exception:
                        LOG.exception('Failed to create out_dir %s', state.out_dir)

                    for line in proc.stdout:
                        lf.write(line)
                        # check destination line
                        m = dest_re.search(line)
                        if m:
                            name = m.group(1).strip()
                            current_name = name
                            with state.lock:
                                if name not in state.active_items and name not in state.completed_items:
                                    state.active_items[name] = {"percent": "0%", "speed": None, "eta": None}
                        # parse progress lines
                        pm = percent_re.search(line)
                        if pm and current_name:
                            pct = pm.group('percent') + '%'
                            speed = pm.group('speed')
                            eta = pm.group('eta')
                            with state.lock:
                                if current_name in state.active_items:
                                    state.active_items[current_name]["percent"] = pct
                                    state.active_items[current_name]["speed"] = speed
                                    state.active_items[current_name]["eta"] = eta
                            # if percent indicates completion, move to completed
                            try:
                                if float(pm.group('percent')) >= 99.9:
                                    with state.lock:
                                        if current_name in state.active_items:
                                            state.completed_items.append(current_name)
                                            del state.active_items[current_name]
                                            # attempt to create a metadata .txt for this completed file
                                            try:
                                                self._write_metadata_txt_for_file(state, current_name)
                                            except Exception:
                                                LOG.exception('Failed to write metadata txt for %s', current_name)
                            except Exception:
                                pass
                        # honor pause requests: if current file requested to pause, terminate process
                        with state.lock:
                            if current_name and (current_name in state.pause_requested_items or state.paused):
                                lf.write(f"User requested pause/stop for {current_name} or channel paused\n")
                                try:
                                    proc.terminate()
                                except Exception:
                                    LOG.exception('Failed to terminate process')
                                # if we asked to pause this specific item, remove the request so it doesn't persist
                                try:
                                    state.pause_requested_items.discard(current_name)
                                except Exception:
                                    pass
                                break
                    rc = proc.wait()
                    lf.write(f"yt-dlp exit code: {rc}\n")
                    try:
                        lf.write(f"Process ended rc={rc} reload={self._reload.is_set()} stop={self._stop.is_set()} at {datetime.utcnow().isoformat()} UTC\n")
                    except Exception:
                        pass
                    # clear proc handle
                    state.proc = None
                    # ensure active items consistent
                    with state.lock:
                        # remove any active items that were completed earlier
                        # leave partially downloaded items in archive (yt-dlp will resume)
                        pass
            except Exception:
                LOG.exception('Error while running subprocess for %s', state.url)

            state.load_total_downloads()
            new_count = max(0, state.total_downloads - prev_count)
            with state.lock:
                state.last_status = "success" if rc == 0 else f"failed({rc})"
            # If failed with Unsupported URL, try some common fallbacks for platforms
            if rc != 0:
                try:
                    log_text = state.log_file.read_text(encoding='utf-8', errors='ignore')
                except Exception:
                    log_text = ''
                if 'Unsupported URL' in log_text:
                    # Odysee: try adding ?view=content
                    if 'odysee.com' in state.url and '?view=' not in state.url:
                        alt = state.url + ('' if state.url.endswith('?') else '') + '?view=content'
                        LOG.info('Retrying with odysee videos view: %s', alt)
                        try:
                            retry_cmd = cmd[:-1] + [alt] if cmd else [alt]
                            # run retry similarly but append to log
                            with state.log_file.open('a', encoding='utf-8') as lf:
                                lf.write(f"\n===== Retry with videos view at {datetime.utcnow().isoformat()} UTC =====\n")
                                proc = subprocess.Popen(retry_cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
                                assert proc.stdout is not None
                                for line in proc.stdout:
                                    lf.write(line)
                                rc2 = proc.wait()
                                lf.write(f"yt-dlp retry exit code: {rc2}\n")
                            state.load_total_downloads()
                            new_count = max(0, state.total_downloads - prev_count)
                            with state.lock:
                                state.last_status = 'success' if rc2 == 0 else f'failed_retry({rc2})'
                            rc = rc2
                        except Exception:
                            LOG.exception('Retry failed')
                    # Rumble: try appending /videos or try /c/<name>
                    if rc != 0 and 'rumble.com' in state.url:
                        base_name = state.url.rstrip('/').split('/')[-1]
                        attempts = [state.url.rstrip('/') + '/videos', f'https://rumble.com/c/{base_name}']
                        for alt in attempts:
                            LOG.info('Retrying rumble variant: %s', alt)
                            try:
                                retry_cmd = cmd[:-1] + [alt] if cmd else [alt]
                                with state.log_file.open('a', encoding='utf-8') as lf:
                                    lf.write(f"\n===== Retry rumble variant {alt} at {datetime.utcnow().isoformat()} UTC =====\n")
                                    proc = subprocess.Popen(retry_cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
                                    assert proc.stdout is not None
                                    for line in proc.stdout:
                                        lf.write(line)
                                    rc2 = proc.wait()
                                    lf.write(f"yt-dlp retry exit code: {rc2}\n")
                                state.load_total_downloads()
                                new_count = max(0, state.total_downloads - prev_count)
                                with state.lock:
                                    state.last_status = 'success' if rc2 == 0 else f'failed_retry({rc2})'
                                rc = rc2
                                if rc == 0:
                                    break
                            except Exception:
                                LOG.exception('Rumble retry failed for %s', alt)
            # send webhook if configured and new downloads occurred
            if self.webhook and new_count > 0:
                try:
                    payload = {"channel": state.url, "new_downloads": new_count, "timestamp": datetime.utcnow().isoformat()}
                    requests.post(self.webhook, json=payload, timeout=10)
                except Exception:
                    LOG.exception("Failed to post webhook for %s", state.url)
        except Exception as e:
            LOG.exception("Error running yt-dlp for %s", state.url)
            with state.lock:
                state.last_status = f"error: {e}"
        finally:
            # release platform semaphore if acquired
            try:
                if acquired:
                    sem.release()
            except Exception:
                LOG.exception('Failed to release semaphore for platform %s', state.platform)
            with state.lock:
                state.is_running = False


app = Flask(__name__, template_folder=str(Path(__file__).parent / "templates"))
monitor: Optional[Monitor] = None
_AUTH_USER: Optional[str] = None
_AUTH_PASS: Optional[str] = None


def check_auth():
    """Return True if no auth configured or if request has valid basic auth."""
    if not _AUTH_USER:
        return True
    auth = request.authorization
    if not auth:
        return False
    return auth.username == _AUTH_USER and auth.password == _AUTH_PASS


def require_auth(func):
    def wrapper(*args, **kwargs):
        if not check_auth():
            return ("Authentication required", 401, {"WWW-Authenticate": "Basic realm=\"yt-dlp-monitor\""})
        return func(*args, **kwargs)
    wrapper.__name__ = getattr(func, '__name__', 'wrapped')
    return wrapper


@app.route("/")
@require_auth
def index():
    if monitor is None:
        return "Monitor not started", 500
    # server-side render page; client will fetch dynamic status via API
    return render_template("index.html")


@app.route("/api/status", methods=["GET"])
@require_auth
def api_status():
    if monitor is None:
        return jsonify({"error": "monitor not started"}), 500
    data = []
    for url, state in monitor.states.items():
        with state.lock:
            # convert active_items dict -> list of objects for the UI
            active = []
            for name, info in state.active_items.items():
                active.append({"name": name, "percent": info.get("percent"), "speed": info.get("speed"), "eta": info.get("eta")})
            data.append({
                "url": url,
                "platform": state.platform,
                "thumbnail": getattr(state, 'thumbnail', None),
                "display_name": getattr(state, 'display_name', None),
                    "total_videos": getattr(state, 'total_videos', None),
                "is_running": state.is_running,
                "paused": state.paused,
                "last_run": datetime.fromtimestamp(state.last_run).isoformat() if state.last_run else None,
                "last_status": state.last_status,
                "total_downloads": state.total_downloads,
                "active_items": active,
                "recently_completed": list(state.completed_items[-10:]),
                "out_dir": str(state.out_dir),
            })
    return jsonify(data)



@app.route("/api/channel/pause", methods=["POST"])
@require_auth
def api_channel_pause():
    if monitor is None:
        return jsonify({"error": "monitor not started"}), 500
    data = request.get_json(force=True)
    url = data.get('url')
    if not url:
        return jsonify({"error": "missing url"}), 400
    state = monitor.states.get(url)
    if not state:
        return jsonify({"error": "unknown channel"}), 404
    with state.lock:
        state.paused = True
        # try to terminate running process if any
        try:
            if state.proc and state.proc.poll() is None:
                # Log to the channel log that we are terminating due to user pause
                try:
                    with state.log_file.open('a', encoding='utf-8') as lf:
                        lf.write(f"User requested channel pause at {datetime.utcnow().isoformat()} UTC - terminating yt-dlp process\n")
                except Exception:
                    LOG.exception('Failed to write pause message to log for %s', state.url)
                state.proc.terminate()
                state.last_status = 'paused'
        except Exception:
            LOG.exception('Failed to terminate process for pause')
    # do not force a monitor reload here; the monitor loop will pick up the paused state
    return jsonify({"ok": True})


@app.route("/api/channel/start", methods=["POST"])
@require_auth
def api_channel_start():
    if monitor is None:
        return jsonify({"error": "monitor not started"}), 500
    data = request.get_json(force=True)
    url = data.get('url')
    if not url:
        return jsonify({"error": "missing url"}), 400
    state = monitor.states.get(url)
    if not state:
        return jsonify({"error": "unknown channel"}), 404
    with state.lock:
        state.paused = False
        state.pause_requested_items.clear()
        already_running = state.is_running
    # If the channel is not currently running, start it immediately in background
    if not already_running:
        try:
            t = threading.Thread(target=monitor.run_for_channel, args=(state,), daemon=True)
            t.start()
        except Exception:
            LOG.exception('Failed to start channel thread for %s', state.url)
    else:
        # ensure monitor wakes up to pick up state changes
        monitor.reload()
    return jsonify({"ok": True})


@app.route("/api/channel/stop", methods=["POST"])
@require_auth
def api_channel_stop():
    if monitor is None:
        return jsonify({"error": "monitor not started"}), 500
    data = request.get_json(force=True)
    url = data.get('url')
    if not url:
        return jsonify({"error": "missing url"}), 400
    state = monitor.states.get(url)
    if not state:
        return jsonify({"error": "unknown channel"}), 404
    with state.lock:
        state.paused = True
        try:
            if state.proc and state.proc.poll() is None:
                try:
                    with state.log_file.open('a', encoding='utf-8') as lf:
                        lf.write(f"User requested channel stop at {datetime.utcnow().isoformat()} UTC - terminating yt-dlp process\n")
                except Exception:
                    LOG.exception('Failed to write stop message to log for %s', state.url)
                try:
                    state.proc.terminate()
                except Exception:
                    LOG.exception('Failed to terminate process for %s', state.url)
                state.last_status = 'stopped_by_user'
        except Exception:
            LOG.exception('Failed to stop process for %s', state.url)
    monitor.reload()
    return jsonify({"ok": True})


@app.route("/api/channel/reset", methods=["POST"])
@require_auth
def api_channel_reset():
    """Reset a channel's archive/logs/state. If clear_out is True, delete the out_dir contents as well.
    This helps recover after manually deleting files in the output folder during testing.
    """
    if monitor is None:
        return jsonify({"error": "monitor not started"}), 500
    data = request.get_json(force=True)
    url = data.get('url')
    clear_out = bool(data.get('clear_out'))
    clear_log = bool(data.get('clear_log', True))
    clear_archive = bool(data.get('clear_archive', True))
    if not url:
        return jsonify({"error": "missing url"}), 400
    state = monitor.states.get(url)
    if not state:
        return jsonify({"error": "unknown channel"}), 404
    # stop running process first
    try:
        with state.lock:
            if state.proc and state.proc.poll() is None:
                try:
                    with state.log_file.open('a', encoding='utf-8') as lf:
                        lf.write(f"User requested reset at {datetime.utcnow().isoformat()} UTC - terminating yt-dlp process\n")
                except Exception:
                    LOG.exception('Failed to write reset message to log for %s', state.url)
                try:
                    state.proc.terminate()
                except Exception:
                    LOG.exception('Failed to terminate process for reset %s', state.url)
                # give the process a moment to exit
        time.sleep(0.2)
    except Exception:
        LOG.exception('Error while attempting to terminate process for reset %s', url)

    # clear archive file
    try:
        if clear_archive and state.archive_file.exists():
            try:
                state.archive_file.unlink()
            except Exception:
                # fallback: truncate
                try:
                    with state.archive_file.open('w', encoding='utf-8') as af:
                        af.write('')
                except Exception:
                    LOG.exception('Failed to clear archive file for %s', url)
    except Exception:
        LOG.exception('Error clearing archive for %s', url)

    # clear log file
    try:
        if clear_log and state.log_file.exists():
            try:
                with state.log_file.open('w', encoding='utf-8') as lf:
                    lf.write(f"=== Reset log at {datetime.utcnow().isoformat()} UTC ===\n")
            except Exception:
                LOG.exception('Failed to clear log for %s', url)
    except Exception:
        LOG.exception('Error clearing log for %s', url)

    # optionally remove out_dir contents
    try:
        if clear_out and state.out_dir.exists():
            try:
                # remove entire channel folder and recreate
                shutil.rmtree(state.out_dir)
                state.out_dir.mkdir(parents=True, exist_ok=True)
            except Exception:
                LOG.exception('Failed to clear out_dir for %s', url)
    except Exception:
        LOG.exception('Error clearing out_dir for %s', url)

    # reset in-memory state
    try:
        with state.lock:
            state.active_items.clear()
            state.completed_items.clear()
            state.pause_requested_items.clear()
            state.paused = False
            state.load_total_downloads()
            state.last_status = None
    except Exception:
        LOG.exception('Failed to reset in-memory state for %s', url)

    monitor.reload()
    return jsonify({"ok": True})


@app.route("/api/channel/resume", methods=["POST"])
@require_auth
def api_channel_resume():
    if monitor is None:
        return jsonify({"error": "monitor not started"}), 500
    data = request.get_json(force=True)
    url = data.get('url')
    if not url:
        return jsonify({"error": "missing url"}), 400
    state = monitor.states.get(url)
    if not state:
        return jsonify({"error": "unknown channel"}), 404
    with state.lock:
        state.paused = False
        state.pause_requested_items.clear()
    # do not force a monitor reload here; clearing paused will let the monitor resume naturally
    return jsonify({"ok": True})


@app.route("/api/download/pause", methods=["POST"])
@require_auth
def api_download_pause():
    if monitor is None:
        return jsonify({"error": "monitor not started"}), 500
    data = request.get_json(force=True)
    url = data.get('channel')
    name = data.get('name')
    if not url or not name:
        return jsonify({"error": "missing channel or name"}), 400
    state = monitor.states.get(url)
    if not state:
        return jsonify({"error": "unknown channel"}), 404
    with state.lock:
        state.pause_requested_items.add(name)
        try:
            if state.proc and state.proc.poll() is None:
                # Log to the channel log that we are terminating due to user-requested item pause
                try:
                    with state.log_file.open('a', encoding='utf-8') as lf:
                        lf.write(f"User requested download pause for {name} at {datetime.utcnow().isoformat()} UTC - terminating yt-dlp process\n")
                except Exception:
                    LOG.exception('Failed to write download-pause message to log for %s', state.url)
                state.proc.terminate()
                state.last_status = 'paused'
        except Exception:
            LOG.exception('Failed to terminate process for download pause')
    # do not force a monitor reload here; the monitor will pick up the paused item
    return jsonify({"ok": True})


@app.route("/api/log", methods=["GET"])
@require_auth
def api_log():
    if monitor is None:
        return jsonify({"error": "monitor not started"}), 500
    url = request.args.get("channel")
    if not url:
        return jsonify({"error": "missing channel parameter"}), 400
    state = monitor.states.get(url)
    if not state:
        return jsonify({"error": "unknown channel"}), 404
    lines = tail_lines(state.log_file, 200)
    return jsonify({"lines": lines})


def tail_lines(path: Path, n: int) -> List[str]:
    if not path.exists():
        return []
    try:
        lines = path.read_text(encoding="utf-8", errors="ignore").splitlines()
        return lines[-n:]
    except Exception:
        return ["<failed to read log>"]


@app.route("/api/channels", methods=["GET", "POST", "DELETE"])
@require_auth
def api_channels():
    if monitor is None:
        return jsonify({"error": "monitor not started"}), 500
    if request.method == "GET":
        return jsonify(list(monitor.states.keys()))
    data = request.get_json(force=True)
    if request.method == "POST":
        url = data.get("url")
        if not url:
            return jsonify({"error": "missing url"}), 400
        channels = read_channels_file(monitor.channels_file)
        if url in channels:
            return jsonify({"ok": True, "msg": "already present"})
        channels.append(url)
        write_channels_file(monitor.channels_file, channels)
        monitor.reload()
        return jsonify({"ok": True})
    if request.method == "DELETE":
        url = data.get("url")
        if not url:
            return jsonify({"error": "missing url"}), 400
        channels = read_channels_file(monitor.channels_file)
        if url not in channels:
            return jsonify({"ok": True, "msg": "not present"})
        channels = [c for c in channels if c != url]
        write_channels_file(monitor.channels_file, channels)
        monitor.reload()
        return jsonify({"ok": True})


@app.route("/api/sync/start", methods=["POST"])
@require_auth
def api_sync_start():
    if monitor is None:
        return jsonify({"error": "monitor not started"}), 500
    monitor.enabled = True
    monitor.reload()
    return jsonify({"ok": True})


@app.route("/api/sync/stop", methods=["POST"])
@require_auth
def api_sync_stop():
    if monitor is None:
        return jsonify({"error": "monitor not started"}), 500
    # disable new runs
    monitor.enabled = False
    # terminate currently running yt-dlp processes
    for st in monitor.states.values():
        try:
            with st.lock:
                if st.proc and st.proc.poll() is None:
                    try:
                        with st.log_file.open('a', encoding='utf-8') as lf:
                            lf.write(f"User requested global stop at {datetime.utcnow().isoformat()} UTC - terminating yt-dlp process\n")
                    except Exception:
                        LOG.exception('Failed to write stop message to log for %s', st.url)
                    try:
                        st.proc.terminate()
                    except Exception:
                        LOG.exception('Failed to terminate process for %s', st.url)
                    st.last_status = 'stopped_by_user'
        except Exception:
            LOG.exception('Error stopping process for %s', st.url)
    monitor.reload()
    return jsonify({"ok": True})


@app.route("/api/config", methods=["POST"])
@require_auth
def api_config():
    if monitor is None:
        return jsonify({"error": "monitor not started"}), 500
    data = request.get_json(force=True)
    out = data.get('output_dir')
    if not out:
        return jsonify({"error": "missing output_dir"}), 400
    new_out = Path(out).expanduser().resolve()
    ok = monitor.set_output_dir(new_out)
    if not ok:
        return jsonify({"ok": False, "msg": "failed to set output dir"}), 500
    monitor.reload()
    return jsonify({"ok": True, "out_dir": str(new_out)})


@app.route("/api/config", methods=["GET"])
@require_auth
def api_config_get():
    if monitor is None:
        return jsonify({"error": "monitor not started"}), 500
    try:
        return jsonify({"ok": True, "out_dir": str(monitor.out_dir), "enabled": bool(monitor.enabled)})
    except Exception:
        return jsonify({"ok": False}), 500


@app.route("/api/check-path", methods=["POST"])
@require_auth
def api_check_path():
    data = request.get_json(force=True)
    path = data.get('path')
    if not path:
        return jsonify({"error": "missing path"}), 400
    p = Path(path).expanduser().resolve()
    try:
        p.mkdir(parents=True, exist_ok=True)
    except Exception as e:
        return jsonify({"ok": False, "writable": False, "msg": f"Cannot create path: {e}"}), 200
    # try write a small temp file
    try:
        tf = p / ('.yt-dlp-perm-check')
        with tf.open('w', encoding='utf-8') as f:
            f.write('ok')
        tf.unlink()
        return jsonify({"ok": True, "writable": True, "msg": "Path is writable"})
    except Exception as e:
        return jsonify({"ok": False, "writable": False, "msg": f"Write failed: {e}"})


@app.route("/api/files", methods=["GET"])
@require_auth
def api_files():
    if monitor is None:
        return jsonify({"error": "monitor not started"}), 500
    q = request.args.get('q', '').strip().lower()
    limit = int(request.args.get('limit', '200'))
    base = monitor.out_dir
    results = []
    try:
        # walk the tree
        for p in base.rglob('*'):
            if p.is_file():
                rel = str(p.relative_to(base))
                name = p.name.lower()
                match = True
                if q:
                    tokens = [t for t in q.split() if t]
                    # require all tokens to be present in name (simple forgiving search)
                    match = all(tok in name for tok in tokens)
                if match:
                    stat = p.stat()
                    results.append({"path": str(p), "relpath": rel, "size": stat.st_size, "mtime": stat.st_mtime})
                    if len(results) >= limit:
                        break
        return jsonify({"ok": True, "count": len(results), "files": results})
    except Exception:
        LOG.exception('Failed to enumerate files under %s', base)
        return jsonify({"ok": False, "msg": "enumeration failed"}), 500


@app.route("/api/reload", methods=["POST"])
@require_auth
def api_reload():
    if monitor is None:
        return jsonify({"error": "monitor not started"}), 500
    monitor.reload()
    return jsonify({"ok": True})


@app.route('/download')
@require_auth
def download_file():
    """Serve a file from the monitor output directory as an attachment (triggers browser Save As).
    Query param: relpath (path relative to monitor.out_dir)
    """
    if monitor is None:
        return "Monitor not started", 500
    rel = request.args.get('relpath')
    if not rel:
        return "Missing relpath", 400
    try:
        base = monitor.out_dir
        p = (base / Path(rel)).resolve()
        # ensure p is under base
        if not str(p).startswith(str(base.resolve())):
            return "Invalid path", 400
        if not p.exists() or not p.is_file():
            return "Not found", 404
        return send_file(str(p), as_attachment=True)
    except Exception:
        LOG.exception('Failed to send file %s', rel)
        return "Server error", 500


def run_app(args):
    global monitor
    global _AUTH_USER, _AUTH_PASS
    # Determine auth credentials using this precedence (highest -> lowest):
    # 1. CLI args (--auth-user / --auth-pass)
    # 2. Environment variables YTDLP_MONITOR_USER / YTDLP_MONITOR_PASS (.env can set these)
    # 3. No auth (None)
    _AUTH_USER = args.auth_user or os.environ.get('YTDLP_MONITOR_USER')
    _AUTH_PASS = args.auth_pass or os.environ.get('YTDLP_MONITOR_PASS')
    channels_file = Path(args.channels).expanduser().resolve()
    archive_dir = Path(args.archive_dir).expanduser().resolve()
    out_dir = Path(args.output_dir).expanduser().resolve()
    monitor = Monitor(channels_file, archive_dir, out_dir, args.interval, args.python, args.yt_args, concurrency=args.concurrency, webhook=args.webhook)
    monitor.start()
    try:
        app.run(host=args.host, port=args.port, debug=False)
    finally:
        monitor.stop()


def main():
    args = parse_args()
    logging.basicConfig(level=logging.INFO, format="[%(asctime)s] %(levelname)s: %(message)s")
    run_app(args)


if __name__ == "__main__":
    main()
