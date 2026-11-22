#!/usr/bin/env python3
"""
Telegram Media Saver - FAST edition
===================================
The same window, checkboxes and folder sorting as telegram_media_saver.py, but the actual
downloading is done by tdl (https://github.com/iyear/tdl), which splits every file across several
connections, can use Telegram's official "takeout" export mode, and resumes after interruptions.

Needs:   Python 3.9+ (no extra packages)   +   tdl installed (tdl.exe)
Run:     py telegram_media_saver_fast.py          (Linux: python3 telegram_media_saver_fast.py)

How it works for each chat:
  1. tdl lists your chats                        (tdl chat ls)
  2. tdl writes a list of every media message     (tdl chat export --raw)  -> <chat>/.tms/export.json
  3. this app sorts that list into Photos / Videos / Voice messages / Video messages /
     Stickers / GIFs / Files, using Telegram's own labels, and writes one list per type
  4. tdl downloads each list into its own folder  (tdl dl -f <type>.json -d <chat>/<Type>)
     with --skip-same --continue, so re-running never downloads a file twice.

Built for big jobs: finished files are never fetched twice, the live list shows every file (green =
done, orange = Telegram making us wait, red = failed and retried on the next Start), the PC is kept
awake, disk space is checked first, and a summary at the end lists anything that didn't download.

Limitations (because tdl decides what it can download):
  * Pictures/videos inside link previews are NOT downloaded (tdl skips link previews).
  * Telegram doesn't label GIFs in tdl's export directly; they are recognised as mp4 files that
    carry the "animated" marker. Very rarely a normal video with stickers drawn on it can be
    counted as a GIF.
"""
from __future__ import annotations

import collections
import colorsys
import copy
import json
import math
import os
import queue
import random
import re
import shutil
import subprocess
import sys
import threading
import time
import traceback
from pathlib import Path

import tkinter as tk
from tkinter import filedialog, messagebox, ttk

IS_WINDOWS = os.name == "nt"
APP_DIR = (Path(os.environ.get("APPDATA", "")) if IS_WINDOWS and os.environ.get("APPDATA")
           else Path.home() / ".config") / "TelegramMediaSaver"
SETTINGS_FILE = APP_DIR / "fast_settings.json"

CATEGORIES = [
    ("photos", "Photos"),
    ("videos", "Videos"),
    ("voice", "Voice messages"),
    ("video_messages", "Video messages"),
    ("stickers", "Stickers"),
    ("gifs", "GIFs"),
    ("files", "Files"),
]
FOLDER_NAMES = dict(CATEGORIES)
ALL_KEYS = [k for k, _ in CATEGORIES]

PHOTO_EXT = {
    ".bmp", ".gif", ".jpeg", ".jpg", ".pcx", ".png", ".tga", ".tif", ".tiff", ".dng", ".cr2",
    ".webp", ".heic", ".heif", ".avif", ".jfif", ".ico", ".svg", ".psd",
    ".nef", ".arw", ".orf", ".rw2", ".raf", ".raw",
}
VIDEO_EXT = {
    ".mkv", ".mp4", ".mpeg", ".mpg", ".mov", ".ogm", ".ogv", ".swf", ".webm", ".wmv",
    ".mp3", ".ogg", ".wav", ".wma", ".opus", ".aup3",
    ".avi", ".flv", ".m4v", ".3gp", ".m2ts", ".mts", ".vob",
    ".m4a", ".flac", ".aac", ".aiff", ".amr", ".mka", ".oga",
}

DEFAULTS = {"tdl_path": "", "threads": 4, "limit": 2, "takeout": False, "engine": "tdl",
            "topic_include": "", "topic_exclude": "", "auto_speed": True,
            "theme": "qd_ion_cyan", "custom_themes": {}, "dock": None, "geometry": "", "graph": {}}
MAX_FILES_AT_ONCE = 12   # top of the "Files at the same time" box
CONSOLE_SNAPSHOT = APP_DIR / f"console_{os.getpid()}.json"
CONSOLE_MIRROR_SCRIPT = APP_DIR / "console_mirror.py"
CHATS_CACHE_FILE = APP_DIR / "chats_cache.json"
QUEUE_FILE = APP_DIR / "queue.json"          # the download queue survives closing the app
SAVE_FORMAT = "TelegramMediaSaver.save"      # marker inside progress save files (*.tmsave.json)
SAVE_EXT = ".tmsave.json"
ENGINE_FILE = Path(__file__).resolve().with_name("tg_engine.py")  # the Built-in engine sits next to this app


def python_exe() -> str:
    """The console Python (python.exe, not pythonw.exe) to run the Built-in engine with."""
    exe = Path(sys.executable)
    if exe.name.lower() == "pythonw.exe" and exe.with_name("python.exe").exists():
        return str(exe.with_name("python.exe"))
    return str(exe)


def as_cmd(tool) -> list[str]:
    """tdl is one program; the Built-in engine is [python, tg_engine.py]. Both are accepted."""
    return list(tool) if isinstance(tool, (list, tuple)) else [tool]


# --------------------------------------------------------------------------- #
#  Small helpers
# --------------------------------------------------------------------------- #
_BAD_CHARS = re.compile(r'[<>:"/\\|?*\x00-\x1f%!^&]')  # also drops characters that upset .cmd files
_RESERVED = {"CON", "PRN", "AUX", "NUL", *(f"COM{i}" for i in range(1, 10)), *(f"LPT{i}" for i in range(1, 10))}


def safe_name(text: str, limit: int = 60) -> str:
    s = _BAD_CHARS.sub("_", text or "").strip(" .")
    s = s[:limit].rstrip(" .")
    if not s:
        return "unnamed"
    if s.upper() in _RESERVED:
        s = "_" + s
    return s


def load_settings() -> dict:
    s = dict(DEFAULTS)
    try:
        s.update(json.loads(SETTINGS_FILE.read_text(encoding="utf-8")))
    except (OSError, ValueError):
        pass
    return s


def save_settings(s: dict) -> None:
    try:
        APP_DIR.mkdir(parents=True, exist_ok=True)
        tmp = SETTINGS_FILE.with_suffix(".tmp")
        tmp.write_text(json.dumps(s, indent=2), encoding="utf-8")
        os.replace(tmp, SETTINGS_FILE)
    except OSError:
        pass


def find_tdl(saved: str = "") -> str | None:
    candidates = [saved, shutil.which("tdl") or ""]
    if IS_WINDOWS:
        drive = os.environ.get("SystemDrive", "C:")
        candidates += [rf"{drive}\tdl\tdl.exe", str(Path.home() / "scoop" / "shims" / "tdl.exe")]
    else:
        candidates += [str(Path.home() / ".local/bin/tdl"), "/usr/local/bin/tdl", "/usr/bin/tdl"]
    for c in candidates:
        if c and Path(c).is_file():
            return str(Path(c))
    return None


def now_iso() -> str:
    return time.strftime("%Y-%m-%d %H:%M:%S")


# --------------------------------------------------------------------------- #
#  Technical log: every detail the app can record, in
#     <this app's folder>/tms logs/<YYYY-MM-DD>/<YYYY-MM-DD_HH-MM-SS when the app started>.log
# --------------------------------------------------------------------------- #
class TechLog:
    def __init__(self):
        self.lock = threading.Lock()
        self.path: Path | None = None
        self.f = None
        self.started = time.localtime()

    def open(self) -> Path | None:
        if self.f is not None:
            return self.path
        day = time.strftime("%Y-%m-%d", self.started)
        name = time.strftime("%Y-%m-%d_%H-%M-%S", self.started) + ".log"
        bases = []
        try:
            bases.append(Path(__file__).resolve().parent / "tms logs")
        except OSError:
            pass
        bases.append(APP_DIR / "tms logs")  # fallback if the app's own folder can't be written to
        for base in bases:
            try:
                d = base / day
                d.mkdir(parents=True, exist_ok=True)
                p = d / name
                self.f = open(p, "a", encoding="utf-8", buffering=1)  # line-buffered: every line hits the disk
                self.path = p
                return p
            except OSError:
                continue
        return None

    def write(self, cat: str, msg) -> None:
        if self.f is None:
            return
        t = time.time()
        stamp = time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(t)) + f".{int(t % 1 * 1000):03d}"
        lines = str(msg).replace("\r", "").split("\n")
        out = (f"{stamp} [{cat:<9}] [{threading.current_thread().name}] {lines[0]}\n"
               + "".join(f"{'':>26}{ln}\n" for ln in lines[1:]))
        with self.lock:
            try:
                self.f.write(out)
            except (OSError, ValueError):
                pass

    def close(self) -> None:
        with self.lock:
            try:
                if self.f:
                    self.f.close()
            except OSError:
                pass
            self.f = None


TLOG = TechLog()


def tlog(cat: str, msg) -> None:
    TLOG.write(cat, msg)


# --------------------------------------------------------------------------- #
#  Reading tdl's export (streamed, so huge chats don't eat all your RAM)
# --------------------------------------------------------------------------- #
def iter_export(path: Path, chunk_size: int = 1 << 20):
    """
    tdl writes:  {"id": <chat id>, "messages": [ {...}, {...}, ... ]}
    Yields ("id", chat_id) once, then ("msg", dict) for every message, reading the file in chunks.
    """
    dec = json.JSONDecoder()
    with open(path, "r", encoding="utf-8") as f:
        buf = ""
        pos = 0
        eof = False

        def need(n: int = 1) -> bool:
            nonlocal buf, pos, eof
            while len(buf) - pos < n and not eof:
                more = f.read(chunk_size)
                if not more:
                    eof = True
                    break
                buf = buf[pos:] + more
                pos = 0
            return len(buf) - pos >= n

        def skip_ws_and(chars: str = "") -> str:
            nonlocal pos
            while need():
                ch = buf[pos]
                if ch.isspace() or ch in chars:
                    pos += 1
                    continue
                return ch
            return ""

        # header: everything before the "messages" array (small)
        while need():
            idx = buf.find('"messages"', pos)
            if idx != -1:
                head = buf[pos:idx]
                m = re.search(r'"id"\s*:\s*(-?\d+)', head)
                if m:
                    yield ("id", int(m.group(1)))
                pos = idx + len('"messages"')
                break
            if eof:
                return
            # keep reading until "messages" appears
            if not need(len(buf) - pos + 1):
                return
        if skip_ws_and(":") != "[":
            return
        pos += 1

        while True:
            ch = skip_ws_and(",")
            if ch in ("]", ""):
                return
            while True:
                try:
                    obj, end = dec.raw_decode(buf, pos)
                    break
                except json.JSONDecodeError:
                    if eof:
                        raise
                    before = len(buf) - pos
                    need(before + chunk_size)  # object spans the chunk edge: read more and retry
                    if len(buf) - pos == before and eof:
                        raise
            pos = end
            if isinstance(obj, dict):
                yield ("msg", obj)


# --------------------------------------------------------------------------- #
#  Sorting messages into categories (from tdl's --raw MTProto data)
# --------------------------------------------------------------------------- #
def classify_raw(raw) -> list[str]:
    """
    `raw` is Telegram's message object as tdl exports it (Go field names, no type tags).
    Returns the categories this message's media belongs to, primary first; [] = no media.
    """
    if not isinstance(raw, dict):
        return []
    media = raw.get("Media")
    for _ in range(3):  # paid media wraps the real media one level down
        if isinstance(media, dict) and isinstance(media.get("ExtendedMedia"), dict):
            media = media["ExtendedMedia"].get("Media")
        else:
            break
    if not isinstance(media, dict):
        return []
    if "Photo" in media and "Document" not in media:
        return ["photos"]
    doc = media.get("Document")
    if not isinstance(doc, dict):
        return ["files"] if "Document" in media else []

    mime = str(doc.get("MimeType") or "").lower()
    attrs = [a for a in (doc.get("Attributes") or []) if isinstance(a, dict)]
    name = ""
    sticker = animated = has_video = has_audio = False
    voice = bool(media.get("Voice"))
    round_video = bool(media.get("Round"))
    for a in attrs:
        if "FileName" in a:
            name = str(a.get("FileName") or "")
        elif "Stickerset" in a:                      # sticker or custom emoji
            sticker = True
        elif "RoundMessage" in a:                    # video attribute
            has_video = True
            round_video = round_video or bool(a.get("RoundMessage"))
        elif "Waveform" in a or "Performer" in a:    # audio attribute
            has_audio = True
            voice = voice or bool(a.get("Voice"))
        elif a == {}:                                # "animated" marker has no fields
            animated = True
    ext = os.path.splitext(name)[1].lower()

    if sticker or mime == "application/x-tgsticker":
        return ["stickers"]
    if round_video:
        return ["video_messages"]
    if voice:
        return ["voice"]
    if animated and (mime.startswith("video/") or mime == "image/gif"):
        return ["gifs"]
    if mime == "image/gif" or ext == ".gif":
        return ["photos", "gifs"]
    if mime.startswith("image/") or ext in PHOTO_EXT:
        return ["photos"]
    if has_video or has_audio or mime.startswith(("video/", "audio/")) or ext in VIDEO_EXT:
        return ["videos"]
    return ["files"]


def media_size(raw) -> int:
    """Expected download size in bytes from tdl's raw data (0 = unknown). Used for the % column."""
    try:
        media = raw.get("Media")
        if isinstance(media, dict) and isinstance(media.get("ExtendedMedia"), dict):
            media = media["ExtendedMedia"].get("Media")
        if not isinstance(media, dict):
            return 0
        doc = media.get("Document")
        if isinstance(doc, dict):
            return int(doc.get("Size") or 0)
        photo = media.get("Photo")
        if isinstance(photo, dict):  # tdl downloads the biggest size
            best = 0
            for s in photo.get("Sizes") or []:
                if isinstance(s, dict):
                    best = max([best, int(s.get("Size") or 0)] + [int(x) for x in (s.get("Sizes") or []) if isinstance(x, int)])
            return best
    except (TypeError, ValueError, AttributeError):
        pass
    return 0


def media_doc_id(raw) -> int:
    """Telegram's unique 64-bit Document.ID or Photo.ID from raw MTProto message data (0 if unavailable)."""
    try:
        media = raw.get("Media") if isinstance(raw, dict) else None
        for _ in range(3):
            if isinstance(media, dict) and isinstance(media.get("ExtendedMedia"), dict):
                media = media["ExtendedMedia"].get("Media")
            else:
                break
        if not isinstance(media, dict):
            return 0
        doc = media.get("Document")
        if isinstance(doc, dict) and doc.get("ID"):
            return int(doc["ID"])
        photo = media.get("Photo")
        if isinstance(photo, dict) and photo.get("ID"):
            return int(photo["ID"])
    except (TypeError, ValueError, AttributeError):
        pass
    return 0


def wanted(cats: list[str], selected: set[str]):
    for c in cats:
        if c in selected:
            return c
    return None


GENERAL_TOPIC = 1


def topic_of(raw) -> int:
    """
    Forum groups: which topic a message is in. Telegram marks topic messages with a reply header that
    has ForumTopic=true; the topic id is ReplyToTopID (a reply inside the topic) or ReplyToMsgID (a
    normal post in the topic). Everything else is in "General" (id 1).
    """
    rt = raw.get("ReplyTo") if isinstance(raw, dict) else None
    if isinstance(rt, dict) and rt.get("ForumTopic"):
        tid = rt.get("ReplyToTopID") or rt.get("ReplyToMsgID")
        if isinstance(tid, int) and tid > 0:
            return tid
    return GENERAL_TOPIC


def build_lists(export_path: Path, selected: set[str]):
    """Returns (chat_id, {category: [entries]}, counts_of_all_media_by_primary_category, sizes).
    Each entry also carries its forum topic id under "topic" (1 = General / not a forum)."""
    chat_id = None
    lists: dict[str, list] = {k: [] for k in ALL_KEYS}
    counts: dict[str, int] = {k: 0 for k in ALL_KEYS}
    sizes: dict[int, int] = {}
    for kind, val in iter_export(export_path):
        if kind == "id":
            chat_id = val
            continue
        msg = val
        if msg.get("type") != "message" or not isinstance(msg.get("id"), int):
            continue
        raw = msg.get("raw")
        cats = classify_raw(raw)
        if not cats:
            continue
        counts[cats[0]] += 1
        cat = wanted(cats, selected)
        if cat is None:
            continue
        lists[cat].append({"id": msg["id"], "type": "message", "file": msg.get("file") or "media",
                           "topic": topic_of(raw), "doc_id": media_doc_id(raw)})
        sizes[msg["id"]] = media_size(raw)
    if chat_id is None:
        raise ValueError("The export file has no chat id - it may be incomplete. Run it again.")
    return chat_id, lists, counts, sizes


# --------------------------------------------------------------------------- #
#  Media index: the result of reading a chat ONCE (id, file name, type, topic, size per media message).
#  It is what progress save files store, so a saved chat never has to be re-read.
# --------------------------------------------------------------------------- #
def read_media_index(export_path: Path) -> tuple[int, list[dict]]:
    chat_id = None
    media: list[dict] = []
    for kind, val in iter_export(export_path):
        if kind == "id":
            chat_id = val
            continue
        msg = val
        if msg.get("type") != "message" or not isinstance(msg.get("id"), int):
            continue
        raw = msg.get("raw")
        cats = classify_raw(raw)
        if not cats:
            continue
        did = media_doc_id(raw)
        item = {"id": msg["id"], "file": msg.get("file") or "media", "cats": cats,
                "topic": topic_of(raw), "size": media_size(raw)}
        if did:
            item["doc_id"] = did
        media.append(item)
    if chat_id is None:
        raise ValueError("The export file has no chat id - it may be incomplete. Run it again.")
    return chat_id, media


def lists_from_media(media: list[dict], selected: set[str]):
    """Same output as build_lists, but from a media index (fresh, or from a save file)."""
    lists: dict[str, list] = {k: [] for k in ALL_KEYS}
    counts: dict[str, int] = {k: 0 for k in ALL_KEYS}
    sizes: dict[int, int] = {}
    for m in media:
        cats = [c for c in (m.get("cats") or []) if c in counts]
        if not cats:
            continue
        counts[cats[0]] += 1
        cat = wanted(cats, selected)
        if cat is None:
            continue
        mid = int(m["id"])
        lists[cat].append({"id": mid, "type": "message", "file": m.get("file") or "media",
                           "topic": int(m.get("topic") or GENERAL_TOPIC),
                           "doc_id": int(m.get("doc_id") or 0)})
        sizes[mid] = int(m.get("size") or 0)
    return lists, counts, sizes


STATUS_HELP = {
    "done": "downloaded",
    "failed": "Telegram refused it, it was deleted, or it errored - retried on the next Start",
    "downloading": "was being downloaded when this was saved (starts over next time)",
    "pending": "not downloaded yet",
    "not_selected": "a media type that wasn't ticked for this job",
    "filtered": "in a forum topic left out by the Include / Exclude topic filter",
}


class JobState:
    """
    Everything one download job has read and done. Autosaved every few seconds to
    <chat folder>/.tms/progress_autosave.tmsave.json, and written wherever you like by Save / the
    pause & stop prompt. 'Load save' reads the same file back, so the chat never has to be re-read.
    """
    AUTOSAVE_EVERY = 10.0

    def __init__(self, chat: dict, base_dir: Path, selected: set[str], topic_inc: str, topic_exc: str,
                 engine: str = "", ref_dir: str | Path | None = None):
        self.lock = threading.RLock()
        self.chat = {k: chat.get(k) for k in ("id", "type", "visible_name", "username", "topics") if k in chat}
        self.base_dir = str(base_dir)
        self.ref_dir = str(ref_dir or "").strip()
        self.selected = sorted(selected)
        self.topic_inc, self.topic_exc, self.engine = topic_inc, topic_exc, engine
        self.chat_id: int | None = None
        self.media: dict[int, dict] = {}
        self.status: dict[int, str] = {}
        self.errors: dict[int, str] = {}
        self.updated: dict[int, str] = {}
        self.history: list[list[str]] = []
        self.created = now_iso()
        self.result = ""
        self.source = ""          # "fresh read", "re-used export", "save file ..."
        self.dirty = False
        self.autosave_path: Path | None = None
        self._last_auto = 0.0

    def set_media(self, chat_id: int, media: list[dict]) -> None:
        with self.lock:
            self.chat_id = int(chat_id)
            self.media = {int(m["id"]): {k: m.get(k) for k in ("file", "cats", "topic", "size")} for m in media}
            for m in media:
                st = m.get("status") or "pending"
                self.status[int(m["id"])] = "pending" if st == "downloading" else st
                if m.get("error"):
                    self.errors[int(m["id"])] = str(m["error"])
            self.dirty = True

    def mark(self, mid, status: str, err: str = "") -> bool:
        if mid is None:
            return False
        with self.lock:
            mid = int(mid)
            if self.status.get(mid) == status and not err:
                return False
            self.status[mid] = status
            if err:
                self.errors[mid] = err
            elif status == "done":
                self.errors.pop(mid, None)
            self.updated[mid] = now_iso()
            self.dirty = True
            return True

    def event(self, text: str) -> None:
        with self.lock:
            self.history.append([now_iso(), text])
            del self.history[:-500]
            self.dirty = True
        tlog("job", text)

    def counts(self) -> dict[str, int]:
        with self.lock:
            return dict(collections.Counter(self.status.get(mid, "pending") for mid in self.media))

    def to_dict(self) -> dict:
        with self.lock:
            media = []
            for mid in sorted(self.media):
                m = self.media[mid]
                e = {"id": mid, "status": self.status.get(mid, "pending"), "file": m.get("file"),
                     "cats": m.get("cats"), "topic": m.get("topic"), "size": m.get("size")}
                if mid in self.errors:
                    e["error"] = self.errors[mid]
                if mid in self.updated:
                    e["updated"] = self.updated[mid]
                media.append(e)
            return {"format": SAVE_FORMAT, "version": 1, "saved_at": now_iso(), "created": self.created,
                    "chat": self.chat, "chat_id": self.chat_id, "save_folder": self.base_dir,
                    "reference_folder": self.ref_dir,
                    "selected_types": self.selected, "topic_include": self.topic_inc,
                    "topic_exclude": self.topic_exc, "engine": self.engine, "source": self.source,
                    "result": self.result, "summary": self.counts(), "status_meaning": STATUS_HELP,
                    "history": list(self.history), "media_count": len(media), "media": media}

    def save(self, path) -> Path:
        path = Path(path)
        write_save_file(path, self.to_dict())
        tlog("save", f"Progress saved to {path}  summary={self.counts()}")
        return path

    def autosave(self, force: bool = False) -> None:
        if not self.autosave_path or not self.media:
            return
        now = time.monotonic()
        if not force and (not self.dirty or now - self._last_auto < self.AUTOSAVE_EVERY):
            return
        self._last_auto = now
        self.dirty = False
        try:
            write_save_file(self.autosave_path, self.to_dict())
        except OSError as e:
            tlog("save", f"autosave failed: {e}")


def write_save_file(path: Path, data: dict) -> None:
    """Readable JSON: settings at the top, then one line per media message."""
    head = {k: v for k, v in data.items() if k != "media"}
    text = json.dumps(head, ensure_ascii=False, indent=1)
    text = text[:text.rfind("}")].rstrip() + ',\n "media": [\n'
    text += ",\n".join("  " + json.dumps(m, ensure_ascii=False) for m in data.get("media") or [])
    text += "\n ]\n}\n"
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(path.name + ".tmp")
    tmp.write_text(text, encoding="utf-8")
    os.replace(tmp, path)


def read_save_file(path) -> dict:
    raw = Path(path).read_text(encoding="utf-8")
    try:
        data = json.loads(raw)
    except ValueError:
        # If the user hand-edited save_folder / reference_folder with single Windows backslashes (e.g. "A:\G DL"),
        # escape single backslashes inside those path fields automatically.
        fixed = re.sub(
            r'("(?:save_folder|reference_folder)"\s*:\s*")([^"\r\n]*)(")',
            lambda m: m.group(1) + re.sub(r'\\(?![\\"/])', r'\\\\', m.group(2)) + m.group(3),
            raw,
        )
        data = json.loads(fixed)
    if not isinstance(data, dict) or data.get("format") != SAVE_FORMAT or not isinstance(data.get("media"), list):
        raise ValueError("That isn't a Telegram Media Saver save file.")
    if not data.get("chat_id") or not isinstance(data.get("chat"), dict):
        raise ValueError("The save file doesn't say which chat it belongs to.")
    data["_path"] = str(path)
    return data


def write_list(path: Path, chat_id: int, entries: list) -> None:
    """Same shape tdl itself writes, so `tdl dl -f` accepts it."""
    # only the fields tdl reads, in a stable order -> stable tdl resume fingerprint
    entries = [{"id": e["id"], "type": "message", "file": e.get("file") or "media"}
               for e in sorted(entries, key=lambda e: e["id"])]
    tmp = path.with_suffix(".tmp")
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump({"id": chat_id, "messages": entries}, f)
        f.flush()
        os.fsync(f.fileno())
    os.replace(tmp, path)


# --------------------------------------------------------------------------- #
#  Running tdl
# --------------------------------------------------------------------------- #
def cmd_quote(arg: str) -> str:
    """Quote one argument for a .cmd file (inside quotes only % still needs escaping)."""
    return '"' + str(arg).replace('"', "").replace("%", "%%") + '"'


if IS_WINDOWS:
    import ctypes
    from ctypes import wintypes

    class _PROCESSENTRY32W(ctypes.Structure):
        _fields_ = [("dwSize", wintypes.DWORD), ("cntUsage", wintypes.DWORD),
                    ("th32ProcessID", wintypes.DWORD), ("th32DefaultHeapID", ctypes.c_size_t),
                    ("th32ModuleID", wintypes.DWORD), ("cntThreads", wintypes.DWORD),
                    ("th32ParentProcessID", wintypes.DWORD), ("pcPriClassBase", ctypes.c_long),
                    ("dwFlags", wintypes.DWORD), ("szExeFile", ctypes.c_wchar * 260)]

    _k32 = ctypes.WinDLL("kernel32", use_last_error=True)
    _ntdll = ctypes.WinDLL("ntdll")
    _k32.CreateToolhelp32Snapshot.restype = wintypes.HANDLE
    _k32.CreateToolhelp32Snapshot.argtypes = [wintypes.DWORD, wintypes.DWORD]
    _k32.Process32FirstW.argtypes = [wintypes.HANDLE, ctypes.POINTER(_PROCESSENTRY32W)]
    _k32.Process32NextW.argtypes = [wintypes.HANDLE, ctypes.POINTER(_PROCESSENTRY32W)]
    _k32.OpenProcess.restype = wintypes.HANDLE
    _k32.OpenProcess.argtypes = [wintypes.DWORD, wintypes.BOOL, wintypes.DWORD]
    _k32.CloseHandle.argtypes = [wintypes.HANDLE]
    _ntdll.NtSuspendProcess.argtypes = [wintypes.HANDLE]
    _ntdll.NtResumeProcess.argtypes = [wintypes.HANDLE]

    def _win_descendants(root_pid: int, exe_name: str) -> list[int]:
        """PIDs of every process under root_pid whose program is exe_name (e.g. tdl.exe)."""
        snap = _k32.CreateToolhelp32Snapshot(0x2, 0)  # TH32CS_SNAPPROCESS
        if not snap or snap == wintypes.HANDLE(-1).value:
            return []
        procs = []
        try:
            e = _PROCESSENTRY32W()
            e.dwSize = ctypes.sizeof(e)
            ok = _k32.Process32FirstW(snap, ctypes.byref(e))
            while ok:
                procs.append((e.th32ProcessID, e.th32ParentProcessID, e.szExeFile.lower()))
                ok = _k32.Process32NextW(snap, ctypes.byref(e))
        finally:
            _k32.CloseHandle(snap)
        found, frontier = [], {root_pid}
        while frontier:
            kids = [(p, n) for p, pp, n in procs if pp in frontier and p not in frontier]
            frontier = {p for p, _ in kids}
            found += [p for p, n in kids if n == exe_name.lower()]
            if len(found) > 50:
                break
        return found

    def _win_suspend(pid: int, suspend: bool) -> bool:
        h = _k32.OpenProcess(0x0800, False, pid)  # PROCESS_SUSPEND_RESUME
        if not h:
            return False
        try:
            fn = _ntdll.NtSuspendProcess if suspend else _ntdll.NtResumeProcess
            return fn(h) == 0
        finally:
            _k32.CloseHandle(h)


_CONSOLE_MIRROR_CODE = r'''#!/usr/bin/env python3
"""Runs a command inside the current Windows console and mirrors the live screen buffer (text + colours) to JSON."""
import ctypes
from ctypes import wintypes
import json
import os
import subprocess
import sys
import time
from pathlib import Path


class _COORD(ctypes.Structure):
    _fields_ = [("X", ctypes.c_short), ("Y", ctypes.c_short)]


class _SMALL_RECT(ctypes.Structure):
    _fields_ = [("Left", ctypes.c_short), ("Top", ctypes.c_short),
                ("Right", ctypes.c_short), ("Bottom", ctypes.c_short)]


class _CSBI(ctypes.Structure):
    _fields_ = [("dwSize", _COORD), ("dwCursorPosition", _COORD),
                ("wAttributes", wintypes.WORD), ("srWindow", _SMALL_RECT),
                ("dwMaximumWindowSize", _COORD)]


class _CU(ctypes.Union):
    _fields_ = [("UnicodeChar", wintypes.WCHAR), ("AsciiChar", ctypes.c_char)]


class _CI(ctypes.Structure):
    _fields_ = [("Char", _CU), ("Attributes", wintypes.WORD)]


def main() -> int:
    if len(sys.argv) < 3:
        return 1
    out_path = Path(sys.argv[1])
    title = sys.argv[2]
    cmd = sys.argv[3:]
    k32 = ctypes.WinDLL("kernel32", use_last_error=True)
    h = k32.CreateFileW("CONOUT$", 0xC0000000, 3, None, 3, 0, None)
    if not h or h == wintypes.HANDLE(-1).value:
        h = k32.CreateFileW("CONOUT$", 0x80000000, 3, None, 3, 0, None)
    try:
        mode = wintypes.DWORD()
        if k32.GetConsoleMode(h, ctypes.byref(mode)):
            k32.SetConsoleMode(h, mode.value | 0x0004)  # ENABLE_VIRTUAL_TERMINAL_PROCESSING
        csbi = _CSBI()
        if k32.GetConsoleScreenBufferInfo(h, ctypes.byref(csbi)):
            if csbi.dwSize.X < 130:
                k32.SetConsoleScreenBufferSize(h, _COORD(130, max(csbi.dwSize.Y, 600)))
    except Exception:
        pass

    done_hist = []
    done_seen = set()

    def snap():
        if not h or h == wintypes.HANDLE(-1).value:
            return
        csbi = _CSBI()
        if not k32.GetConsoleScreenBufferInfo(h, ctypes.byref(csbi)):
            return
        w = int(csbi.dwSize.X)
        bot = max(int(csbi.dwCursorPosition.Y), int(csbi.srWindow.Bottom))
        bot = min(bot, int(csbi.dwSize.Y) - 1)
        if w <= 0 or bot < 0:
            return
        top = max(0, bot - 260)
        rows_out = []
        chunk = 40
        for r0 in range(top, bot + 1, chunk):
            r1 = min(bot, r0 + chunk - 1)
            h_rows = r1 - r0 + 1
            buf = (_CI * (w * h_rows))()
            rect = _SMALL_RECT(0, r0, w - 1, r1)
            if not k32.ReadConsoleOutputW(h, buf, _COORD(w, h_rows), _COORD(0, 0), ctypes.byref(rect)):
                continue
            for ry in range(h_rows):
                base = ry * w
                # find last non-space character on this line
                end_x = w
                while end_x > 0:
                    ch = buf[base + end_x - 1].Char.UnicodeChar
                    if ch and ch not in (" ", "\x00"):
                        break
                    end_x -= 1
                if end_x == 0:
                    rows_out.append([])
                    continue
                spans = []
                cur_col = buf[base].Attributes & 0x0F
                cur_chars = []
                for x in range(end_x):
                    cell = buf[base + x]
                    ch = cell.Char.UnicodeChar
                    if not ch or ch == "\x00":
                        ch = " "
                    col = cell.Attributes & 0x0F
                    if col != cur_col and cur_chars:
                        spans.append(["".join(cur_chars), int(cur_col)])
                        cur_chars = [ch]
                        cur_col = col
                    else:
                        cur_chars.append(ch)
                if cur_chars:
                    spans.append(["".join(cur_chars), int(cur_col)])
                rows_out.append(spans)
                plain = "".join(s[0] for s in spans).strip()
                if "done! [" in plain and plain not in done_seen:
                    done_seen.add(plain)
                    done_hist.append((plain, spans))
                    if len(done_hist) > 500:
                        old_p, _ = done_hist.pop(0)
                        done_seen.discard(old_p)

        # drop trailing blank lines
        while rows_out and not rows_out[-1]:
            rows_out.pop()
        # if the console viewport scrolled older "done!" lines off the top, keep them visible at the top
        visible_plains = {"".join(s[0] for s in row).strip() for row in rows_out if row}
        scrolled_off = [sp for pl, sp in done_hist if pl not in visible_plains]
        final_rows = scrolled_off + rows_out
        if len(final_rows) > 400:
            final_rows = final_rows[-400:]
        try:
            tmp = out_path.with_suffix(".tmp")
            tmp.write_text(json.dumps({"title": title, "lines": final_rows}, ensure_ascii=False), encoding="utf-8")
            os.replace(tmp, out_path)
        except OSError:
            pass

    proc = subprocess.Popen(cmd)
    try:
        while proc.poll() is None:
            snap()
            time.sleep(0.15)
        snap()
        return proc.returncode
    except KeyboardInterrupt:
        proc.terminate()
        return 1


if __name__ == "__main__":
    sys.exit(main())
'''



class Runner:
    """Runs tdl. Visible steps get their own console window on Windows so you see tdl's progress."""

    def __init__(self, tdl_path: str = ""):
        self.proc: subprocess.Popen | None = None
        self.stopped = False
        self.paused = False
        self.exe_name = Path(tdl_path).name if tdl_path else "tdl.exe"
        self.lock = threading.Lock()
        # live speed / topic-filter change: the download step reads these each time it (re)launches tdl
        self.speed: tuple[int, int] | None = None   # (connections per file, files at once)
        self.cur_speed: tuple[int, int] = (4, 2)
        self.auto_speed: bool = True
        self.topic_filter: tuple[str, str] | None = None  # (include_spec, exclude_spec)
        self.restart_requested = False
        self.downloading = False                    # True while the download step's tdl is running

    def apply_speed(self, threads: int, limit: int,
                    topic_inc: str | None = None, topic_exc: str | None = None,
                    auto_speed: bool | None = None) -> bool:
        """
        New speed / topic-filter settings while running. tdl can't change them on the fly, so if it's
        downloading right now it's closed and started again straight away with the new settings - no
        rescan, and finished files are kept. Returns True if tdl is being restarted, False if the new
        settings will simply be used when the download step starts.
        """
        with self.lock:
            self.speed = (threads, limit)
            if auto_speed is not None:
                self.auto_speed = auto_speed
            if topic_inc is not None or topic_exc is not None:
                self.topic_filter = (topic_inc or "", topic_exc or "")
            tlog("speed", f"apply_speed threads={threads} limit={limit} auto={self.auto_speed} "
                          f"topic_filter={self.topic_filter} downloading={self.downloading}")
            if not self.downloading or self.stopped:
                return False
            self.restart_requested = True
            p = self.proc
        self._kill(p)
        return True

    def take_restart(self) -> bool:
        with self.lock:
            r, self.restart_requested = self.restart_requested, False
            return r and not self.stopped

    def _tdl_pids(self) -> list[int]:
        p = self.proc
        if p is None or p.poll() is not None:
            return []
        if IS_WINDOWS:
            return _win_descendants(p.pid, self.exe_name)
        return [p.pid]  # on Linux/macOS we start tdl directly

    def pause(self) -> bool:
        """Freeze tdl where it is (files stay half-written; nothing is lost). True if it worked."""
        with self.lock:
            pids = self._tdl_pids()
            done = False
            for pid in pids:
                try:
                    if IS_WINDOWS:
                        done = _win_suspend(pid, True) or done
                    else:
                        import signal
                        os.kill(pid, signal.SIGSTOP)
                        done = True
                except OSError:
                    pass
            if done:
                self.paused = True
            tlog("run", f"pause: pids={pids} ok={done}")
            return done

    def resume(self) -> None:
        tlog("run", "resume")
        with self.lock:
            for pid in self._tdl_pids():
                try:
                    if IS_WINDOWS:
                        _win_suspend(pid, False)
                    else:
                        import signal
                        os.kill(pid, signal.SIGCONT)
                except OSError:
                    pass
            self.paused = False

    def capture(self, args: list[str], timeout: int = 600) -> tuple[int, str]:
        kw = {"creationflags": subprocess.CREATE_NO_WINDOW} if IS_WINDOWS else {}
        env = dict(os.environ, PYTHONIOENCODING="utf-8", PYTHONUTF8="1")  # Built-in engine: names with emoji
        t0 = time.monotonic()
        tlog("run", f"capture (timeout {timeout}s): {subprocess.list2cmdline([str(a) for a in args])}")
        try:
            p = subprocess.run(args, stdin=subprocess.DEVNULL, capture_output=True, text=True,
                               encoding="utf-8", errors="replace", timeout=timeout, env=env, **kw)
        except subprocess.TimeoutExpired:
            tlog("run", f"capture TIMED OUT after {time.monotonic() - t0:.1f}s")
            raise
        tlog("run", f"capture exit={p.returncode} after {time.monotonic() - t0:.1f}s, "
                    f"stdout {len(p.stdout or ''):,} chars, stderr {len(p.stderr or ''):,} chars")
        if p.stderr:
            tlog("run", "stderr:\n" + p.stderr[-3000:])
        return p.returncode, (p.stdout or "") + (p.stderr or "")

    def visible(self, title: str, args: list[str]) -> int:
        if self.stopped:
            return -1
        t0 = time.monotonic()
        tlog("run", f"window '{title}': {subprocess.list2cmdline([str(a) for a in args])}")
        if IS_WINDOWS:
            APP_DIR.mkdir(parents=True, exist_ok=True)
            try:
                CONSOLE_MIRROR_SCRIPT.write_text(_CONSOLE_MIRROR_CODE, encoding="utf-8")
            except OSError:
                pass
            bat = APP_DIR / f"run_{os.getpid()}.cmd"
            safe_t = safe_name(title, 80)
            mirror_cmd = " ".join(
                cmd_quote(a) for a in [python_exe(), str(CONSOLE_MIRROR_SCRIPT), str(CONSOLE_SNAPSHOT), safe_t, *args]
            )
            lines = [
                "@echo off",
                "chcp 65001 >nul",
                "set PYTHONIOENCODING=utf-8",
                f"title {safe_t}",
                mirror_cmd,
                "if errorlevel 1 (",
                "  echo.",
                "  echo ===== tdl stopped with an error. Read the message above. =====",
                "  echo Press any key to close this window.",
                "  pause >nul",
                "  exit /b 1",
                ")",
                "exit /b 0",
            ]
            bat.write_text("\r\n".join(lines) + "\r\n", encoding="utf-8")
            self.proc = subprocess.Popen(["cmd", "/c", str(bat)], creationflags=subprocess.CREATE_NEW_CONSOLE)
        else:
            print(f"\n=== {title} ===\n$ " + " ".join(args), flush=True)
            self.proc = subprocess.Popen(args)
        code = self.proc.wait()
        with self.lock:
            self.proc = None
            self.paused = False
        tlog("run", f"window '{title}' closed: exit={code} after {time.monotonic() - t0:.1f}s"
                    + ("  (stopped by you)" if self.stopped else ""))
        return -1 if self.stopped else code

    def stop(self) -> None:
        tlog("run", "stop requested")
        self.stopped = True
        self._kill(self.proc)

    def _kill(self, p) -> None:
        if p is None or p.poll() is not None:
            return
        try:
            if IS_WINDOWS:
                subprocess.run(["taskkill", "/T", "/F", "/PID", str(p.pid)], capture_output=True,
                               creationflags=subprocess.CREATE_NO_WINDOW)
            else:
                p.terminate()
                if self.paused:  # a frozen process only acts on the stop signal once it's unfrozen
                    import signal
                    os.kill(p.pid, signal.SIGCONT)
        except OSError:
            pass


def parse_chat_list(text: str) -> list[dict]:
    """`tdl chat ls -o json` prints a JSON array; tolerate warnings / colour codes around it."""
    clean = re.sub(r"\x1b\[[0-9;?]*[A-Za-z]", "", text)  # strip terminal colour codes (they contain '[')
    dec = json.JSONDecoder()
    for m in re.finditer(r"\[", clean):
        try:
            data, _ = dec.raw_decode(clean, m.start())
        except json.JSONDecodeError:
            continue
        if isinstance(data, list) and (not data or isinstance(data[0], dict)):
            return [d for d in data if isinstance(d, dict) and "id" in d]
    raise ValueError(clean.strip()[-600:] or "tdl printed nothing")


def looks_logged_out(text: str) -> bool:
    t = text.lower()
    return any(s in t for s in ("not authorized", "auth_key_unregistered", "login first",
                                "unauthorized", "session_revoked", "please login"))


# --------------------------------------------------------------------------- #
#  Filename & duplicate detection (supports both new <chat_id>_<msg_id>_<name>
#  and older <YYYY-MM-DD>_<HH-MM-SS>_... formats)
# --------------------------------------------------------------------------- #
_CHAT_MID_RE = re.compile(r"^-?\d+_(\d+)_(.+)$")
_DATE_MID_RE = re.compile(r"^\d{4}-\d{2}-\d{2}[_ -]\d{2}[-:]\d{2}[-:]\d{2}_(\d+)_(.+)$")
_OLD_DATE_RE = re.compile(r"^\d{4}-\d{2}-\d{2}[_ -]\d{2}[-:]\d{2}[-:]\d{2}_(.+)$")
_DUP_COPY_RE = re.compile(r"\s+\(\d+\)(\.[^.]+)$")
_TG_DOCID_RE = re.compile(r"(?<!\d)(\d{15,20})(?!\d)")
_BAD_FS_RE = re.compile(r'[<>:"/\\|?*\x00-\x1f]')


def _norm_media_tail(name: str, strip_copy: bool = True) -> str:
    """Normalizes a media filename for comparison across old and new TMSF versions."""
    s = _BAD_FS_RE.sub("_", name or "").strip(" .").lower()
    if strip_copy:
        s = _DUP_COPY_RE.sub(r"\1", s)
    return s[:150]


def _extract_doc_ids(text: str) -> list[int]:
    """Extracts 15-20 digit Telegram document/photo IDs embedded in a filename."""
    return [int(x) for x in _TG_DOCID_RE.findall(text or "")]


def _strip_known_prefix(fname: str) -> tuple[int | None, str, bool]:
    """
    Returns (msg_id_or_None, tail_filename, is_old_date_format) for a filename on disk.
    Recognizes:
      - <chat_id>_<msg_id>_<tail>
      - <YYYY-MM-DD>_<HH-MM-SS>_<msg_id>_<tail>
      - <YYYY-MM-DD>_<HH-MM-SS>_<tail>
    """
    m = _CHAT_MID_RE.match(fname)
    if m:
        return int(m.group(1)), m.group(2), False
    m = _DATE_MID_RE.match(fname)
    if m:
        return int(m.group(1)), m.group(2), True
    m = _OLD_DATE_RE.match(fname)
    if m:
        return None, m.group(1), True
    return None, fname, False


def _same_file_bytes(p1: Path, p2: Path, sz: int) -> bool:
    """Fast byte-level identity check (first 64 KB, middle 64 KB, last 64 KB) for two files of equal size."""
    if sz <= 0:
        return False
    chunk = 65536
    try:
        with open(p1, "rb") as f1, open(p2, "rb") as f2:
            if sz <= chunk * 2:
                return f1.read() == f2.read()
            if f1.read(chunk) != f2.read(chunk):
                return False
            mid_off = sz // 2
            f1.seek(mid_off)
            f2.seek(mid_off)
            if f1.read(chunk) != f2.read(chunk):
                return False
            f1.seek(max(0, sz - chunk))
            f2.seek(max(0, sz - chunk))
            return f1.read(chunk) == f2.read(chunk)
    except OSError:
        return False


def resolve_ref_dirs(ref_spec: str | Path | None, chat: dict | None = None) -> list[Path]:
    """
    Turns a reference folder path (or ';'-separated list of paths) into concrete directories on disk.
    If a path contains `<chat_name>` inside it (e.g. you pointed at `D:\\Telegram Downloads`), resolves to
    `D:\\Telegram Downloads\\<chat_name>`; otherwise uses the path itself so you can point directly at any folder.
    """
    if not ref_spec:
        return []
    cname = ""
    if chat:
        cname = safe_name(chat.get("visible_name") or chat.get("username") or str(chat.get("id") or "chat"))
    out: list[Path] = []
    seen: set[str] = set()
    for part in str(ref_spec).split(";"):
        raw = part.strip()
        if not raw:
            continue
        p = Path(raw)
        if not p.exists():
            continue
        target = (p / cname) if (cname and (p / cname).is_dir()) else p
        key = os.path.normcase(os.path.abspath(str(target)))
        if key not in seen:
            seen.add(key)
            out.append(target)
    return out


def find_duplicate_files(
    root_dir: Path, prefer_new: bool = True, ref_spec: str | Path | None = None, chat: dict | None = None
) -> list[tuple[Path, Path, int]]:
    """
    Scans `root_dir` (skipping .tms) and finds duplicate files where the same media was downloaded
    more than once (e.g. once by an older version as YYYY-MM-DD_HH-MM-SS_... and once as <chat_id>_<msg_id>_...,
    with a ' (2)' suffix, or already present in `ref_spec`). Every pair is verified to have the exact same
    byte size and identical content.
    Returns [(keep_path, remove_path, size_in_bytes), ...].
    """
    dups: list[tuple[Path, Path, int]] = []
    if not root_dir.exists():
        return dups

    # Optional: index files in the reference folder(s) by size so any copy in `root_dir` that already
    # exists in the reference folder can also be flagged as a duplicate (keeping the reference copy).
    ref_by_size: dict[int, list[Path]] = {}
    root_norm = os.path.normcase(os.path.abspath(str(root_dir)))
    for rdir in resolve_ref_dirs(ref_spec, chat):
        if os.path.normcase(os.path.abspath(str(rdir))) == root_norm:
            continue
        rstack = [rdir]
        while rstack:
            rcur = rstack.pop()
            try:
                with os.scandir(rcur) as it:
                    for e in it:
                        try:
                            if e.is_dir(follow_symlinks=False):
                                if e.name != ".tms":
                                    rstack.append(Path(e.path))
                            elif e.is_file(follow_symlinks=False) and not e.name.endswith(".tmp"):
                                rsz = e.stat().st_size
                                if rsz > 0:
                                    ref_by_size.setdefault(rsz, []).append(Path(e.path))
                        except OSError:
                            continue
            except OSError:
                continue

    def _names_match(p1: Path, p2: Path) -> bool:
        mid1, tail1, old1 = _strip_known_prefix(p1.name)
        mid2, tail2, old2 = _strip_known_prefix(p2.name)
        nt1 = _norm_media_tail(tail1, strip_copy=True)
        nt2 = _norm_media_tail(tail2, strip_copy=True)
        nt1_full = _norm_media_tail(f"{mid1}_{tail1}" if mid1 is not None else tail1, strip_copy=True)
        nt2_full = _norm_media_tail(f"{mid2}_{tail2}" if mid2 is not None else tail2, strip_copy=True)
        dids1 = set(_extract_doc_ids(p1.name))
        dids2 = set(_extract_doc_ids(p2.name))
        return (
            (mid1 is not None and mid1 == mid2)
            or (nt1 and (nt1 == nt2 or nt1 == nt2_full or nt1_full == nt2 or nt1_full == nt2_full))
            or bool(dids1 and (dids1 & dids2))
            or (old1 != old2)
        )

    stack = [root_dir]
    while stack:
        cur = stack.pop()
        by_size: dict[int, list[Path]] = {}
        try:
            with os.scandir(cur) as it:
                for e in it:
                    try:
                        if e.is_dir(follow_symlinks=False):
                            if e.name != ".tms":
                                stack.append(Path(e.path))
                        elif e.is_file(follow_symlinks=False) and not e.name.endswith(".tmp"):
                            sz = e.stat().st_size
                            if sz > 0:
                                by_size.setdefault(sz, []).append(Path(e.path))
                    except OSError:
                        continue
        except OSError:
            continue

        for sz, paths in by_size.items():
            # 1. Check against reference folder first (always keep the reference folder's file)
            remaining_paths: list[Path] = []
            ref_cands = ref_by_size.get(sz) or []
            for p_cand in paths:
                matched_ref = None
                for p_ref in ref_cands:
                    if os.path.normcase(os.path.abspath(str(p_ref))) == os.path.normcase(os.path.abspath(str(p_cand))):
                        continue
                    if _names_match(p_ref, p_cand) and _same_file_bytes(p_ref, p_cand, sz):
                        matched_ref = p_ref
                        break
                if matched_ref is not None:
                    dups.append((matched_ref, p_cand, sz))
                else:
                    remaining_paths.append(p_cand)

            if len(remaining_paths) < 2:
                continue

            # 2. Check within the same folder
            def _rank(p: Path):
                mid, _tail, is_old = _strip_known_prefix(p.name)
                has_copy = bool(_DUP_COPY_RE.search(p.name))
                is_new_fmt = (mid is not None and not is_old)
                want_fmt = is_new_fmt if prefer_new else is_old
                return (0 if want_fmt else 1, 1 if has_copy else 0, p.name.lower())

            ordered = sorted(remaining_paths, key=_rank)
            removed_idx: set[int] = set()
            for i, p_keep in enumerate(ordered):
                if i in removed_idx:
                    continue
                for j in range(i + 1, len(ordered)):
                    if j in removed_idx:
                        continue
                    p_cand = ordered[j]
                    if _names_match(p_keep, p_cand) and _same_file_bytes(p_keep, p_cand, sz):
                        dups.append((p_keep, p_cand, sz))
                        removed_idx.add(j)
    return dups


# --------------------------------------------------------------------------- #
#  The download job (runs on a background thread)
# --------------------------------------------------------------------------- #
def finished_ids(folder: Path, chat_id: int, any_chat: bool = False,
                 entries: list[dict] | None = None, sizes: dict[int, int] | None = None,
                 recursive: bool = False) -> set[int]:
    """
    Message IDs that already have a finished file in `folder` (or anywhere under `folder` when `recursive=True`).
    Recognizes both new filenames (<chat_id>_<msg_id>_<name>) and files downloaded by older versions
    of TMSF (<YYYY-MM-DD>_<HH-MM-SS>_<msg_id>_<name> or <YYYY-MM-DD>_<HH-MM-SS>_<name_or_doc_id>).
    """
    done: set[int] = set()
    if not folder.exists():
        return done
    prefixes = (f"{chat_id}_", f"-100{chat_id}_", f"-{chat_id}_")
    disk_tails: dict[str, set[int]] = {}      # normalized_tail -> {file_sizes_on_disk}
    disk_doc_ids: dict[int, set[int]] = {}    # 15-20 digit Telegram doc/photo ID -> {file_sizes_on_disk}
    date_size_ext: set[tuple[int, str]] = set()
    cand_date_mids: dict[int, set[int]] = {}  # candidate msg_id from YYYY-MM-DD_HH-MM-SS_<mid>_... -> {sizes}

    stack = [folder]
    while stack:
        cur_dir = stack.pop()
        try:
            with os.scandir(cur_dir) as it:
                for e in it:
                    n = e.name
                    if recursive and e.is_dir(follow_symlinks=False):
                        if n != ".tms":
                            stack.append(Path(e.path))
                        continue
                    if n.endswith(".tmp"):
                        continue
                    try:
                        if not e.is_file(follow_symlinks=False):
                            continue
                        sz = e.stat().st_size
                    except OSError:
                        continue
                    if sz <= 0:
                        continue

                    # 1. New format: <chat_id>_<msg_id>_<name>
                    if any_chat:
                        m = _TDL_NAME.match(n)
                        if m:
                            done.add(int(m.group(1)))
                    elif n.startswith(prefixes):
                        m = _CHAT_MID_RE.match(n)
                        if m:
                            done.add(int(m.group(1)))
                            for t in (_norm_media_tail(m.group(2), True), _norm_media_tail(m.group(2), False)):
                                if t:
                                    disk_tails.setdefault(t, set()).add(sz)

                    # 2. Old format: <YYYY-MM-DD>_<HH-MM-SS>_<msg_id>_<name> or <YYYY-MM-DD>_<HH-MM-SS>_<name>
                    dm = _DATE_MID_RE.match(n)
                    if dm:
                        cmid = int(dm.group(1))
                        cand_date_mids.setdefault(cmid, set()).add(sz)
                        if entries is None:
                            done.add(cmid)
                        for t in (_norm_media_tail(dm.group(2), True), _norm_media_tail(dm.group(2), False)):
                            if t:
                                disk_tails.setdefault(t, set()).add(sz)

                    om = _OLD_DATE_RE.match(n)
                    if om:
                        raw_tail = om.group(1)
                        for t in (_norm_media_tail(raw_tail, True), _norm_media_tail(raw_tail, False)):
                            if t:
                                disk_tails.setdefault(t, set()).add(sz)
                        ext = os.path.splitext(n)[1].lower()
                        if ext:
                            date_size_ext.add((sz, ext))
                    else:
                        # Also index plain filenames in the folder
                        for t in (_norm_media_tail(n, True), _norm_media_tail(n, False)):
                            if t:
                                disk_tails.setdefault(t, set()).add(sz)

                    # 3. Any 15-20 digit Telegram document/photo IDs in the filename
                    for did in _extract_doc_ids(n):
                        disk_doc_ids.setdefault(did, set()).add(sz)
        except OSError:
            pass

    if entries:
        for ent in entries:
            mid = int(ent["id"])
            if mid in done:
                continue
            exp_sz = int((sizes or {}).get(mid, ent.get("size", 0)) or 0)

            def _size_ok(found_sizes: set[int]) -> bool:
                if not found_sizes:
                    return False
                if exp_sz <= 0:
                    return True
                return exp_sz in found_sizes or any(abs(s - exp_sz) <= 1024 for s in found_sizes)

            # A. Old date-prefixed file with <msg_id>_
            if mid in cand_date_mids and _size_ok(cand_date_mids[mid]):
                done.add(mid)
                continue

            # B. Match by 15-20 digit Telegram Document.ID / Photo.ID
            did = int(ent.get("doc_id") or 0)
            if did and did in disk_doc_ids and _size_ok(disk_doc_ids[did]):
                done.add(mid)
                continue
            fname = str(ent.get("file") or "")
            matched_did = False
            for f_did in _extract_doc_ids(fname):
                if f_did in disk_doc_ids and _size_ok(disk_doc_ids[f_did]):
                    done.add(mid)
                    matched_did = True
                    break
            if matched_did:
                continue

            # C. Match by normalized filename tail (after stripping prefix and optional ' (2)')
            nt = _norm_media_tail(fname, True)
            nt_with_mid = _norm_media_tail(f"{mid}_{fname}", True)
            if nt and nt not in ("media", "file", "video", "photo"):
                if (nt in disk_tails and _size_ok(disk_tails[nt])) or (
                    nt_with_mid in disk_tails and _size_ok(disk_tails[nt_with_mid])
                ):
                    done.add(mid)
                    continue

            # D. Match old date-prefixed file by exact byte size (>= 32 KB) + file extension
            if exp_sz >= 32768:
                ext = os.path.splitext(fname)[1].lower()
                if ext and (exp_sz, ext) in date_size_ext:
                    done.add(mid)
                    continue

    return done


def reference_finished_ids(
    ref_spec: str | Path | None, chat: dict, chat_id: int,
    entries: list[dict] | None = None, sizes: dict[int, int] | None = None
) -> set[int]:
    """
    Returns all message IDs that already exist anywhere inside the reference folder(s) `ref_spec`,
    allowing a conversation to be split across multiple drives without downloading duplicates.
    """
    done: set[int] = set()
    for rdir in resolve_ref_dirs(ref_spec, chat):
        done |= finished_ids(rdir, chat_id, entries=entries, sizes=sizes, recursive=True)
    return done


def topic_folders(work: Path, topics: list[dict], used_ids) -> dict[int, str]:
    """
    Folder name for every forum topic: its title (made safe for Windows). Remembered in
    .tms/topics.json so a topic keeps its folder even if it's renamed later. Two topics with the same
    title get " (2)", " (3)" ... ; a topic that no longer exists becomes "Topic <id>".
    """
    path = work / "topics.json"
    try:
        saved = {int(k): v for k, v in json.loads(path.read_text(encoding="utf-8")).items()}
    except (OSError, ValueError, AttributeError):
        saved = {}
    titles = {int(t["id"]): str(t.get("title") or "") for t in topics if isinstance(t, dict) and "id" in t}
    titles.setdefault(GENERAL_TOPIC, "General")
    taken = {v.lower() for v in saved.values()}
    out = dict(saved)
    for tid in sorted(set(titles) | set(used_ids)):
        if tid in out:
            continue
        base = safe_name(titles.get(tid) or f"Topic {tid}", 80)
        name, n = base, 2
        while name.lower() in taken or name.lower() == ".tms":
            name, n = f"{base} ({n})", n + 1
        out[tid] = name
        taken.add(name.lower())
    if out != saved:
        try:
            atomic = path.with_suffix(".tmp")
            atomic.write_text(json.dumps({str(k): v for k, v in out.items()}, ensure_ascii=False, indent=1),
                              encoding="utf-8")
            os.replace(atomic, path)
        except OSError:
            pass
    return out


# --------------------------------------------------------------------------- #
#  Forum topic Include / Exclude filter
#    Tokens joined by + :
#      "text"  literal text (case-insensitive)
#      *       any 1 word/number/symbol token (no spaces)
#      **      1 or more tokens
#      num     numbers only (1 token of digits)
#      word    letters only (1 token of letters, no digits)
#    Multiple rules can be separated by ; or ,
# --------------------------------------------------------------------------- #
def _split_outside_quotes(text: str, seps: str) -> list[str]:
    out, buf, quote = [], [], None
    for ch in text:
        if quote:
            buf.append(ch)
            if ch == quote:
                quote = None
        elif ch in ('"', "'"):
            quote = ch
            buf.append(ch)
        elif ch in seps:
            out.append("".join(buf))
            buf = []
        else:
            buf.append(ch)
    out.append("".join(buf))
    return out


def _tokenize_rule(rule: str) -> list[tuple[str, str]]:
    """Breaks one rule (e.g. '"house " + num' or '"house " + * + *') into (kind, value) tokens."""
    s = rule.strip()
    if len(s) >= 2 and s[0] == s[-1] and s[0] in ("'", '"') and ('"' in s[1:-1] or "'" in s[1:-1] or "+" in s[1:-1]):
        # e.g. user pasted '"house " + *' with outer single quotes around the whole expression
        if s[0] == "'" and '"' in s[1:-1]:
            s = s[1:-1].strip()
    tokens: list[tuple[str, str]] = []
    for piece in _split_outside_quotes(s, "+"):
        p = piece.strip()
        if not p:
            continue
        i, n = 0, len(p)
        while i < n:
            while i < n and p[i].isspace():
                i += 1
            if i >= n:
                break
            if p[i] in ('"', "'"):
                q = p[i]
                j = i + 1
                while j < n and p[j] != q:
                    j += 1
                lit = p[i + 1:j].strip()
                if lit:
                    tokens.append(("lit", lit))
                i = j + 1
            else:
                j = i
                while j < n and not p[j].isspace() and p[j] not in ('"', "'"):
                    j += 1
                w = p[i:j]
                wl = w.lower()
                if w == "**":
                    tokens.append(("many", ""))
                elif w == "*":
                    tokens.append(("star", ""))
                elif wl in ("num", "number", "numbers"):
                    tokens.append(("num", ""))
                elif wl in ("word", "words"):
                    tokens.append(("word", ""))
                else:
                    tokens.append(("lit", w))
                i = j
    return tokens


def compile_topic_rule(rule: str) -> re.Pattern | None:
    tokens = _tokenize_rule(rule)
    if not tokens:
        return None
    parts = []
    for kind, val in tokens:
        if kind == "lit":
            parts.append(r"\s+".join(re.escape(w) for w in val.split()))
        elif kind == "star":
            parts.append(r"\S+")
        elif kind == "many":
            parts.append(r"\S+(?:\s+\S+)*")
        elif kind == "num":
            parts.append(r"\d+")
        elif kind == "word":
            parts.append(r"[^\W\d_]+")
    return re.compile(r"^\s*" + r"\s+".join(parts) + r"\s*$", re.IGNORECASE)


def parse_topic_rules(spec: str) -> list[re.Pattern]:
    if not spec or not spec.strip():
        return []
    rules = []
    for raw in _split_outside_quotes(spec, ";,\n"):
        pat = compile_topic_rule(raw)
        if pat is not None:
            rules.append(pat)
    return rules


def topic_matches(title: str, inc_rules: list[re.Pattern], exc_rules: list[re.Pattern]) -> bool:
    t = (title or "").strip()
    if inc_rules and not any(r.match(t) for r in inc_rules):
        return False
    if exc_rules and any(r.match(t) for r in exc_rules):
        return False
    return True


# --------------------------------------------------------------------------- #
#  Auto-tuning connections per file (-t) and files at once (-l) by file size
# --------------------------------------------------------------------------- #
_MB = 1024 * 1024


def auto_speed_for_sizes(file_sizes: list[int]) -> tuple[int, int, str]:
    """
    Returns (connections_per_file, files_at_once, description) tuned to the given file sizes:
      * Small  (< 25 MB):     3 connections x 12 files  (fast turnover on small clips/photos)
      * Medium (25-100 MB):   4 connections x 10 files  (balanced 40 streams)
      * Large  (100-350 MB):  6 connections x 8 files   (48 streams; extra connections for 100 MB+ files)
      * Huge   (350 MB+):     8 connections x 6 files   (or up to 12 connections when <= 4 huge files left)
    """
    if not file_sizes:
        return 4, 8, "default"
    n = len(file_sizes)
    huge = sum(1 for sz in file_sizes if sz >= 350 * _MB)
    large = sum(1 for sz in file_sizes if sz >= 100 * _MB)
    med = sum(1 for sz in file_sizes if sz >= 25 * _MB)
    avg = sum(file_sizes) / n
    if huge >= max(1, n // 2) or avg >= 350 * _MB:
        if n <= 4:
            return 12, max(1, n), "Huge files (350 MB+, final few)"
        return 8, 6, "Huge files (350 MB+)"
    if large >= max(1, n // 2) or avg >= 100 * _MB:
        if n <= 5:
            return 8, max(1, n), "Large files (100-350 MB, final few)"
        return 6, 8, "Large files (100-350 MB)"
    if med >= max(1, n // 2) or avg >= 25 * _MB:
        if n <= 4:
            return 6, max(1, n), "Medium files (25-100 MB, final few)"
        return 4, 10, "Medium files (25-100 MB)"
    return 3, min(12, max(1, n)), "Small files (< 25 MB)"


def split_into_size_tiers(entries: list[dict], sizes: dict[int, int]) -> list[tuple[str, list[dict]]]:
    """
    Groups remaining entries into size tiers so tdl runs each tier with the ideal (connections, files)
    from start to finish - without ever having to interrupt a half-downloaded 500 MB file.
    """
    small, medium, large, huge = [], [], [], []
    for e in entries:
        sz = sizes.get(e["id"], 0)
        if sz >= 350 * _MB:
            huge.append(e)
        elif sz >= 100 * _MB:
            large.append(e)
        elif sz >= 25 * _MB:
            medium.append(e)
        else:
            small.append(e)
    tiers = []
    if small:
        tiers.append(("Small files (< 25 MB)", small))
    if medium:
        tiers.append(("Medium files (25-100 MB)", medium))
    if large:
        tiers.append(("Large files (100-350 MB)", large))
    if huge:
        tiers.append(("Huge files (350 MB+)", huge))
    return tiers




MOVE_MIN_AGE = 2.0  # seconds a finished file must sit untouched before it's moved (tdl sets its date right after renaming)


def move_finished(incoming: Path, dest_for: dict[int, Path], seen: dict[str, float] | None = None,
                  now: float | None = None) -> list[tuple[str, int]]:
    """
    Forum downloads land in a staging folder first; this moves each finished file into its topic's
    folder. With `seen`, a file is only moved once it has been sitting there for MOVE_MIN_AGE seconds
    (tdl is done with it). Without `seen` (tdl has exited) everything is moved at once.
    Returns [(file name, message id)] that were moved.
    """
    moved = []
    now = time.monotonic() if now is None else now
    try:
        entries = list(os.scandir(incoming))
    except OSError:
        return moved
    for e in entries:
        n = e.name
        if n.endswith(".tmp"):
            continue
        m = _TDL_NAME.match(n)
        mid = int(m.group(1)) if m else None
        dest = dest_for.get(mid) if mid is not None else None
        if dest is None:
            continue
        if seen is not None:
            first = seen.setdefault(n, now)
            if now - first < MOVE_MIN_AGE:
                continue
        try:
            Path(dest).mkdir(parents=True, exist_ok=True)
            target = Path(dest) / n
            if target.exists() and target.stat().st_size == e.stat().st_size:
                os.remove(e.path)  # already there (e.g. moved by the other mover a moment ago)
            else:
                os.replace(e.path, target)
            moved.append((n, mid))
            if seen is not None:
                seen.pop(n, None)
        except FileNotFoundError:
            pass  # the other mover got it first
        except OSError:
            pass  # locked for a moment (antivirus/indexer) - try again next time
    return moved


def run_job(runner: Runner, tdl: str, chat: dict, base_dir: Path, selected: set[str],
            threads: int, limit: int, takeout: bool, reuse_export: bool, ui, ask=None,
            topic_include: str = "", topic_exclude: str = "",
            state: JobState | None = None, preloaded: dict | None = None,
            ref_dir: str | Path | None = None) -> str:
    """
    Whole job for one chat. `ui(kind, ...)` sends updates to the window; `ask(text) -> bool` asks a
    yes/no question. Returns "done", "incomplete:<n>", "nothing", "stopped", "no_space",
    "export_failed" or "dl_failed:<type>".
    `state` records everything read and every file's outcome (autosaved); `preloaded` is a loaded save
    file - its message list is used instead of reading the chat again. `ref_dir` is an optional reference
    folder (e.g. on another drive) whose already-downloaded files are skipped so a conversation can be
    split across multiple drives without duplicates.
    """
    name = chat.get("visible_name") or chat.get("username") or str(chat["id"])
    chat_dir = base_dir / safe_name(name)
    work = chat_dir / ".tms"
    work.mkdir(parents=True, exist_ok=True)
    export = work / "export.json"
    target = chat.get("username") or str(chat["id"])
    who = "Built-in engine" if str(as_cmd(tdl)[-1]).endswith("tg_engine.py") else "tdl"
    # --ntp pool.ntp.org prevents tdl from hanging on "bad message id: created too far in past" if PC clock drifts
    common = ["--reconnect-timeout", "0"] + (["--ntp", "pool.ntp.org"] if who == "tdl" else [])
    state = state or JobState(chat, base_dir, selected, topic_include, topic_exclude, who, ref_dir=ref_dir)
    state.autosave_path = work / f"progress_autosave{SAVE_EXT}"
    ref_dirs = resolve_ref_dirs(ref_dir, chat)
    tlog("job", f"run_job chat={name!r} id={chat.get('id')} dir={chat_dir} ref={ref_dirs} types={sorted(selected)} "
                f"threads={threads} limit={limit} takeout={takeout} reuse={reuse_export} engine={who} "
                f"include={topic_include!r} exclude={topic_exclude!r} preloaded={bool(preloaded)}")

    # If splitting across drives and the new drive doesn't have topics.json or export.json yet,
    # copy topics.json (for identical topic folder names) and optionally reuse export.json from the reference folder.
    for rdir in ref_dirs:
        ref_topics = rdir / ".tms" / "topics.json"
        if not (work / "topics.json").exists() and ref_topics.is_file():
            try:
                shutil.copy2(ref_topics, work / "topics.json")
            except OSError:
                pass
        if reuse_export and not export.exists():
            ref_exp = rdir / ".tms" / "export.json"
            if ref_exp.is_file():
                try:
                    shutil.copy2(ref_exp, export)
                    ui("log", f"Copied the message list from reference folder ({rdir}) so it doesn't need to rescan.")
                except OSError:
                    pass

    if who == "tdl" and IS_WINDOWS:
        try:
            subprocess.run(["taskkill", "/F", "/IM", runner.exe_name],
                           stdin=subprocess.DEVNULL, capture_output=True,
                           creationflags=subprocess.CREATE_NO_WINDOW)
        except OSError:
            pass

    # 1. list every media message (or take it from a save file / last time's export)
    trusted_done: set[int] = set()
    if preloaded and preloaded.get("media"):
        chat_id, media = int(preloaded["chat_id"]), list(preloaded["media"])
        state.source = f"save file {preloaded.get('_path', '')}"
        ui("log_ok", f"Using the save file's message list ({len(media):,} media messages) - no rescan.")
        saved_fld = os.path.normcase(os.path.abspath(str(preloaded.get("save_folder") or "")))
        valid_flds = {os.path.normcase(os.path.abspath(str(base_dir)))}
        for rdir in ref_dirs:
            valid_flds.add(os.path.normcase(os.path.abspath(str(rdir))))
            valid_flds.add(os.path.normcase(os.path.abspath(str(rdir.parent))))
        if saved_fld in valid_flds:
            trusted_done = {int(m["id"]) for m in media if m.get("status") == "done"}
            if trusted_done:
                ui("log", f"The save file lists {len(trusted_done):,} file(s) as already downloaded - they're skipped.")
    else:
        if reuse_export and export.exists():
            ui("log", "Re-using the message list from last time (no rescan).")
            state.source = "re-used last export"
        else:
            ui("status", f"Step 1 of 2: {who} is listing the chat's media messages (progress in its window) ...")
            tmp = work / "export.partial.json"
            code = runner.visible(f"{who} - listing {name}",
                                  as_cmd(tdl) + ["chat", "export", "-c", target, "--raw", "-o", str(tmp)] + common)
            if code != 0 and not runner.stopped and who == "tdl" and ENGINE_FILE.exists():
                ui("log_warn", "tdl couldn't list the chat - using the Built-in Python engine to list messages instead ...")
                code = runner.visible(f"Built-in engine - listing {name}",
                                      [python_exe(), str(ENGINE_FILE), "chat", "export", "-c", target,
                                       "--raw", "-o", str(tmp)] + common)
            if code != 0:
                return "stopped" if runner.stopped else "export_failed"
            os.replace(tmp, export)
            state.source = "fresh read"
        ui("status", "Reading the message list ...")
        chat_id, media = read_media_index(export)
    state.set_media(chat_id, media)
    tlog("read", f"{len(media):,} media messages in chat {chat_id} ({state.source}):")
    for m in media:
        tlog("read", f"msg={m['id']} cats={','.join(m.get('cats') or [])} topic={m.get('topic')} "
                     f"size={m.get('size')} status={m.get('status', 'pending')} file={m.get('file')}")
    state.event(f"Message list ready: {len(media):,} media messages ({state.source})")
    state.autosave(force=True)

    # 2. sort it
    ui("status", "Sorting messages into categories ...")
    lists, counts, sizes = lists_from_media(media, selected)
    ui("log", "Media in this chat: " + ", ".join(f"{FOLDER_NAMES[k]} {counts[k]:,}" for k in ALL_KEYS))
    picked = {e["id"] for k in ALL_KEYS for e in lists[k]}
    for m in media:
        if int(m["id"]) not in picked and state.status.get(int(m["id"])) != "done":
            state.mark(m["id"], "not_selected")
    todo = [(k, lists[k]) for k in ALL_KEYS if lists[k]]
    if not todo:
        ui("log_warn", "Nothing in this chat matches the ticked types.")
        return "nothing"

    # 3. work out what's left. tdl re-checks EVERY message with Telegram (one request each, silently)
    #    before skipping files you already have, which looks like a hang after a restart - so finished
    #    files are left out of tdl's list. tdl only gives a file its final name (no ".tmp") once it's
    #    complete, so a final-named file means it's done.
    topics = [t for t in (chat.get("topics") or []) if isinstance(t, dict)]
    all_tids = {e["topic"] for _, es in todo for e in es}
    forum = bool(topics) or any(tid != GENERAL_TOPIC for tid in all_tids)
    tnames: dict[int, str] = {}
    raw_titles: dict[int, str] = {}
    if forum:
        tnames = topic_folders(work, topics, all_tids)
        raw_titles = {int(t["id"]): str(t.get("title") or "") for t in topics if "id" in t}
        raw_titles.setdefault(GENERAL_TOPIC, "General")
        if runner.topic_filter is not None:
            topic_include, topic_exclude = runner.topic_filter

        def allowed_topic_ids(inc_spec: str, exc_spec: str) -> set[int]:
            inc_r, exc_r = parse_topic_rules(inc_spec), parse_topic_rules(exc_spec)
            if not inc_r and not exc_r:
                return set(tnames) | all_tids
            kept = set()
            for tid in set(tnames) | all_tids:
                t1 = raw_titles.get(tid) or tnames.get(tid, f"Topic {tid}")
                t2 = tnames.get(tid, t1)
                if topic_matches(t1, inc_r, exc_r) or (t2 != t1 and topic_matches(t2, inc_r, exc_r)):
                    kept.add(tid)
            return kept

        if topic_include.strip() or topic_exclude.strip():
            allowed = allowed_topic_ids(topic_include, topic_exclude)
            kept_used = sorted(all_tids & allowed, key=lambda t: (raw_titles.get(t) or tnames.get(t, "")).lower())
            skip_used = sorted(all_tids - allowed, key=lambda t: (raw_titles.get(t) or tnames.get(t, "")).lower())
            kept_ex = ", ".join((raw_titles.get(t) or tnames.get(t, "")) for t in kept_used[:4])
            skip_ex = ", ".join((raw_titles.get(t) or tnames.get(t, "")) for t in skip_used[:4])
            ui("log", f"Topic filter: keeping {len(kept_used):,} of {len(all_tids):,} topic(s) with media"
                      + (f" (e.g. {kept_ex})" if kept_ex else "")
                      + (f"  |  skipping {len(skip_used):,} (e.g. {skip_ex})" if skip_ex else "") + ".")
            todo = [(k, [e for e in es if e["topic"] in allowed]) for k, es in todo]
            todo = [(k, es) for k, es in todo if es]
            for k in ALL_KEYS:
                for e in lists[k]:
                    if e["topic"] not in allowed and state.status.get(e["id"]) != "done":
                        state.mark(e["id"], "filtered")
            if not todo:
                ui("log_warn", "Nothing left to download: no forum topics with media matched your Include/Exclude filter.")
                return "nothing"
        used = {e["topic"] for _, es in todo for e in es}
        ui("log", f"Forum group: {len(used):,} topic(s) have matching media - each gets its own folder "
                  f"(<chat>/<topic name>/<type>).")

    # Pre-scan reference folder(s) (e.g. on another drive) once for all matching media entries
    ref_done: set[int] = set()
    if ref_dirs:
        all_todo_entries = [e for _, es in todo for e in es]
        ref_done = reference_finished_ids(ref_dir, chat, chat_id, entries=all_todo_entries, sizes=sizes)
        ref_label = ", ".join(str(p) for p in ref_dirs)
        if ref_done:
            ui("log_ok", f"Reference folder ({ref_label}): {len(ref_done):,} file(s) already present there - they will be skipped.")
        else:
            ui("log", f"Reference folder ({ref_label}): checked (no matching files from this selection found there).")

    def dest_of(key: str, e: dict) -> Path:
        if forum:
            return chat_dir / tnames[e["topic"]] / FOLDER_NAMES[key]
        return chat_dir / FOLDER_NAMES[key]

    def done_ids(key: str, entries: list) -> set[int]:
        entry_ids = {e["id"] for e in entries}
        done = set(ref_done & entry_ids)
        by_folder: dict[Path, list] = {}
        for e in entries:
            if e["id"] not in done:
                by_folder.setdefault(dest_of(key, e), []).append(e)
        for folder, f_entries in by_folder.items():
            done |= finished_ids(folder, chat_id, entries=f_entries, sizes=sizes)
        # Also check flat <chat_dir>/<Type> and <chat_dir> in case an older version saved files there
        remaining = [e for e in entries if e["id"] not in done]
        if remaining:
            for alt_folder in (chat_dir / FOLDER_NAMES[key], chat_dir):
                if alt_folder not in by_folder and alt_folder.is_dir():
                    done |= finished_ids(alt_folder, chat_id, entries=remaining, sizes=sizes)
        if trusted_done:  # listed as downloaded in the loaded save file (same save folder or reference folder)
            done |= trusted_done & entry_ids
        return done

    plan, left_bytes = [], 0
    for key, all_entries in todo:
        if forum:  # files left in the staging folder by a crash: put them where they belong first
            move_finished(work / "incoming" / key, {e["id"]: dest_of(key, e) for e in all_entries})
        done = done_ids(key, all_entries)
        entries = [e for e in all_entries if e["id"] not in done]
        for e in all_entries:
            state.mark(e["id"], "done" if e["id"] in done else "pending")
        if len(entries) < len(all_entries):
            ui("log", f"{FOLDER_NAMES[key]}: {len(all_entries) - len(entries):,} already downloaded - skipped.")
        left_bytes += sum(sizes.get(e["id"], 0) for e in entries)
        folder = (work / "incoming" / key) if forum else (chat_dir / FOLDER_NAMES[key])
        plan.append((key, all_entries, entries, folder, done))
    state.autosave(force=True)
    left_files = sum(len(p[2]) for p in plan)
    if left_files == 0:
        ui("log_ok", "Everything ticked is already downloaded.")
        return "done"
    ui("log", f"{left_files:,} files to download (about {fmt_size(left_bytes)}).")

    # 4. enough disk space?
    try:
        free = shutil.disk_usage(chat_dir).free
    except OSError:
        free = None
    if free is not None and left_bytes > free - 200 * 1024 * 1024:
        text = (f"This needs about {fmt_size(left_bytes)}, but the drive only has {fmt_size(free)} free.\n\n"
                "Start anyway? (It will stop when the drive is full - you can free space and press Start "
                "again to continue.)")
        ui("log_warn", f"Low disk space: need about {fmt_size(left_bytes)}, {fmt_size(free)} free.")
        if ask is None or not ask(text):
            return "no_space"

    # 5. download each type into its own folder
    steps = [p for p in plan if p[2]]
    step_bytes = [sum(sizes.get(e["id"], 0) for e in p[2]) for p in steps]
    for i, (key, all_entries, entries, folder, already) in enumerate(steps, 1):
        lst = work / f"{key}.json"
        write_list(lst, chat_id, entries)
        label = FOLDER_NAMES[key]
        # half-files from a stopped run: neither engine resumes them (they start that file over), but the
        # live view would count them as "downloading now" - so clear them out first
        stale = 0
        try:
            for e in os.scandir(folder):
                if e.name.endswith(".tmp") and _TDL_NAME.match(e.name[:-4]):
                    try:
                        os.remove(e.path)
                        stale += 1
                    except OSError:
                        pass
        except OSError:
            pass
        if stale:
            ui("log", f"{label}: removed {stale} half-downloaded file(s) left by an earlier stop (they restart).")
        ui("status", f"Step 2 of 2 - type {i} of {len(steps)}: downloading {label} ({len(entries):,} files)")
        ui("log", f"Downloading {len(entries):,} {label.lower()} -> {folder}")
        dest_for = {e["id"]: dest_of(key, e) for e in lists[key]} if forum else None
        ui("watch", folder, {e["id"]: sizes.get(e["id"], 0) for e in all_entries}, label, i, len(steps),
           {e["id"]: e["file"] for e in lists[key]},
           {"already": set(already) & {e["id"] for e in all_entries}, "dest_for": dest_for,
            "topic_of": {e["id"]: tnames[e["topic"]] for e in lists[key]} if forum else None,
            "later": sum(step_bytes[i:])})
        code = -1
        try:
            while True:
                if runner.auto_speed:
                    tiers = split_into_size_tiers(entries, sizes) or [("All", entries)]
                else:
                    tiers = [(None, entries)]
                restarted = False
                for tier_name, tier_entries in tiers:
                    if runner.auto_speed:
                        threads, limit, tier_desc = auto_speed_for_sizes(
                            [sizes.get(e["id"], 0) for e in tier_entries]
                        )
                        runner.cur_speed = (threads, limit)
                        ui("speed_ui", threads, limit)
                        ui("log_ok", f"Auto-speed [{tier_name or tier_desc}]: {threads} connections/file, "
                                     f"{limit} files at once ({len(tier_entries):,} {label.lower()} in this tier).")
                    else:
                        if runner.speed:
                            threads, limit = runner.speed
                        runner.cur_speed = (threads, limit)
                    write_list(lst, chat_id, tier_entries)
                    # --pool = how many connections tdl may open per Telegram server. Its default (8) silently caps
                    # "connections per file" x "files at once", so raising those did nothing past 8 before.
                    args = as_cmd(tdl) + ["dl", "-f", str(lst), "-d", str(folder), "--skip-same", "--continue",
                            "-t", str(threads), "-l", str(limit), "--pool", str(max(8, threads * limit))] + common
                    if takeout:
                        args.append("--takeout")
                    runner.downloading = True
                    try:
                        code = runner.visible(f"{who} - {label} - {name}", args)
                    finally:
                        runner.downloading = False
                    if forum:
                        move_finished(folder, dest_for)
                    if runner.take_restart():
                        restarted = True
                        break
                    if code != 0 or runner.stopped:
                        break
                if not restarted:
                    break
                # "Apply" (or auto-speed toggle) was pressed: start tdl again on what's left - no rescan.
                if forum and runner.topic_filter is not None:
                    inc_s, exc_s = runner.topic_filter
                    allowed_now = allowed_topic_ids(inc_s, exc_s)
                    all_entries = [e for e in lists[key] if e["topic"] in allowed_now]
                done_now = done_ids(key, all_entries)
                entries = [e for e in all_entries if e["id"] not in done_now]
                if not entries:
                    code = 0
                    break
                if not runner.auto_speed:
                    if runner.speed:
                        threads, limit = runner.speed
                    ui("log_ok", f"New settings applied: {threads} connection(s) per file, {limit} file(s) at once - "
                                 f"carrying on with the {len(entries):,} {label.lower()} left (no rescan).")
        finally:
            if forum:  # tdl has exited: move everything that finished into its topic folder
                move_finished(folder, dest_for)
            ui("unwatch", code == 0 and not runner.stopped)  # True = tdl went through the whole list
        if code != 0:
            return "stopped" if runner.stopped else f"dl_failed:{label}"

    # 6. check the result per type
    missing_total = 0
    for key, all_entries, _entries, _folder, _already in plan:
        done = done_ids(key, all_entries)
        missing = sum(1 for e in all_entries if e["id"] not in done)
        for e in all_entries:
            if e["id"] in done:
                state.mark(e["id"], "done")
            elif state.status.get(e["id"]) != "failed":
                state.mark(e["id"], "failed", "not in the folder after the download finished "
                                              "(Telegram refused it, it was deleted, or it errored)")
        state.autosave(force=True)
        if missing:
            missing_total += missing
            ui("log_err", f"{FOLDER_NAMES[key]}: {missing:,} of {len(all_entries):,} didn't download "
                          "(Telegram refused them or they were deleted). Press Start to retry just those.")
        else:
            ui("log_ok", f"{FOLDER_NAMES[key]}: all {len(all_entries):,} downloaded.")
    return "done" if missing_total == 0 else f"incomplete:{missing_total}"


# --------------------------------------------------------------------------- #
#  Live progress: watches tdl's ".tmp" files (tdl writes each file as NAME.tmp, renames when done,
#  and deletes the .tmp if that file failed)
# --------------------------------------------------------------------------- #
_TDL_NAME = re.compile(r"^(?:\d{4}-\d{2}-\d{2}[_ -]\d{2}[-:]\d{2}[-:]\d{2}|-?\d+)_(\d+)_(.*)$")
SPEED_WINDOW = 4.0   # seconds of history used for speeds (smooths out tdl writing parts out of order)
STALL_SECS = 20      # a file that hasn't grown for this long is shown orange ("waiting on Telegram")
MAX_ROWS = 3000      # rows kept in the file list; the oldest finished rows are dropped beyond this


def fmt_speed(bps: float) -> str:
    """MB/s when at least 1 MB/s, otherwise KB/s."""
    mb = 1024 * 1024
    if bps >= mb:
        return f"{bps / mb:.2f} MB/s"
    return f"{bps / 1024:.0f} KB/s"


def fmt_size(n: float) -> str:
    for unit in ("B", "KB", "MB", "GB"):
        if n < 1024 or unit == "GB":
            return f"{n:.0f} {unit}" if unit == "B" else f"{n:.1f} {unit}"
        n /= 1024
    return f"{n:.1f} GB"


ETA_SMOOTH = 20.0   # seconds; the ETA uses a smoothed speed so it doesn't jump around every second


def fmt_eta(seconds) -> str:
    if seconds is None or seconds != seconds or seconds < 0:
        return "-"
    s = int(seconds + 0.5)
    if s < 60:
        return f"{s}s"
    if s < 3600:
        return f"{s // 60}m {s % 60:02d}s"
    if s < 86400:
        return f"{s // 3600}h {s % 3600 // 60:02d}m"
    return f"{s // 86400}d {s % 86400 // 3600}h"


def _smooth(old, new: float, dt) -> float:
    if old is None or old <= 0 or dt is None:
        return new
    a = 1 - math.exp(-max(0.0, dt) / ETA_SMOOTH)
    return old + a * (new - old)


def _speed(hist) -> float:
    if not hist or len(hist) < 2:
        return 0.0
    (t0, b0), (t1, b1) = hist[0], hist[-1]
    return max(0.0, (b1 - b0) / (t1 - t0)) if t1 > t0 else 0.0


class Monitor:
    """
    Looks at the download folder every second and reports what changed:
      active   - tdl is writing NAME.tmp                          (normal colour)
      stalled  - NAME.tmp hasn't grown for STALL_SECS seconds       (orange: Telegram making us wait)
      paused   - you pressed Pause
      done     - NAME.tmp became NAME, or NAME appeared            (green)
      error    - NAME.tmp disappeared and NAME never appeared       (red: tdl gave up on that file)
    Note: tdl writes several pieces of a file at once, so a file's size on disk can briefly run a little
    ahead of what has really arrived. Speeds are averaged over a few seconds to smooth that out.
    """

    def __init__(self, folder: Path, sizes: dict[int, int], label: str, is_paused=lambda: False,
                 names: dict[int, str] | None = None, already=None, dest_for=None, topic_of=None,
                 later: int = 0):
        self.folder, self.sizes, self.label, self.is_paused = Path(folder), sizes, label, is_paused
        self.names = names or {}
        self.dest_for = dest_for          # forum: message id -> topic folder to move finished files to
        self.topic_of = topic_of or {}    # forum: message id -> topic folder name (shown in the list)
        self.move_seen: dict[str, float] = {}
        self.error_ids: set[int] = set()
        self.wanted = len(sizes)
        self.files: dict[str, dict] = {}
        self.vanished: dict[str, int] = {}   # key -> how many looks in a row it was missing
        self.total_hist: collections.deque = collections.deque()
        self.counted: dict[str, int] = {}    # bytes counted towards "downloaded this run", per file
        self.total_bytes = 0
        self.baseline: set[str] | None = None
        self.finished: set[int] = set(already or ())
        self.errors = 0
        self.last_tick: float | None = None
        self.later = later       # bytes still to come in the types after this one
        self.ema: float | None = None
        self.ema_t: float | None = None

    def _scan(self):
        tmps, finals = {}, {}
        try:
            with os.scandir(self.folder) as it:
                for e in it:
                    try:
                        if not e.is_file():
                            continue
                        if e.name.endswith(".tmp"):
                            # Files still being written: ask for the live size. On Windows the folder
                            # listing's size can lag far behind for a file another program has open
                            # (like Explorer showing a download stuck at the same size), which made
                            # the live view think nothing was moving.
                            size = os.stat(e.path).st_size
                        else:
                            size = e.stat().st_size
                    except OSError:
                        continue
                    (tmps if e.name.endswith(".tmp") else finals)[e.name] = size
        except OSError:
            pass
        return tmps, finals

    def _msg_id(self, final: str):
        m = _TDL_NAME.match(final)
        return int(m.group(1)) if m else None

    def _row(self, key: str, f: dict) -> dict:
        topic = self.topic_of.get(self._msg_id(key)) if self.topic_of else None
        return {"key": f"{self.folder}|{key}", "mid": self._msg_id(key), "name": f["name"],
                "type": f"{topic}  /  {self.label}" if topic else self.label, "status": f["status"],
                "done": f["done"], "total": f["total"], "speed": f.get("speed", 0.0),
                "eta": ((f["total"] - f["done"]) / f["ema"]) if f["status"] == "active" and f["total"]
                       and f.get("ema", 0) and f["ema"] > 1 else None}

    def _moved_ok(self, key: str) -> bool:
        mid = self._msg_id(key)
        dest = self.dest_for.get(mid) if mid is not None else None
        return bool(dest) and (Path(dest) / key).exists()

    def _count_bytes(self, key: str, size: int) -> None:
        prev = self.counted.get(key, 0)
        if size > prev:
            self.total_bytes += size - prev
            self.counted[key] = size

    def tick(self, now: float | None = None) -> dict:
        now = time.monotonic() if now is None else now
        tmps, finals = self._scan()
        paused = bool(self.is_paused())
        changed: list[dict] = []
        if self.baseline is None:  # files that were already there before this run
            self.baseline = set(finals)
            for fname in finals:
                mid = self._msg_id(fname)
                if mid in self.sizes:
                    self.finished.add(mid)

        # files being written right now
        for tname, size in tmps.items():
            key = tname[:-4]
            f = self.files.get(key)
            if f is None or f["status"] in ("done", "error"):  # new (or retried) file
                m = _TDL_NAME.match(key)
                f = self.files[key] = {"name": m.group(2) if m else key, "status": "active", "done": 0,
                                       "total": self.sizes.get(self._msg_id(key), 0),
                                       "hist": collections.deque(), "grew": now, "speed": 0.0}
                if self.last_tick is not None and key not in self.counted:
                    f["hist"].append((self.last_tick, 0))  # its bytes arrived after the last look
                if self.counted.get(key):  # tdl restarted this file from zero
                    self.counted[key] = 0
            self.vanished.pop(key, None)
            if size > f["done"]:
                f["grew"] = now
            f["done"] = size
            h = f["hist"]
            h.append((now, size))
            while len(h) > 2 and now - h[0][0] > SPEED_WINDOW:
                h.popleft()
            self._count_bytes(key, size)
            f["speed"] = _speed(h)
            if not paused:
                f["ema"] = _smooth(f.get("ema"), f["speed"], now - f["ema_t"] if f.get("ema_t") is not None else None)
            f["ema_t"] = now
            f["status"] = "paused" if paused else ("stalled" if now - f["grew"] >= STALL_SECS else "active")
            changed.append(self._row(key, f))

        # files whose .tmp went away: finished, or failed
        for key, f in list(self.files.items()):
            if f["status"] in ("done", "error") or key + ".tmp" in tmps:
                continue
            if key in finals or (self.dest_for and self._moved_ok(key)):
                f.update(status="done", done=finals.get(key, f["done"]), speed=0.0)
                # count the rest of the file now: it may have been renamed / moved away before the last
                # bytes were ever seen on disk, which made "downloaded" and the speed read too low
                self._count_bytes(key, max(finals.get(key, 0), f.get("total") or 0, f["done"]))
                mid = self._msg_id(key)
                if mid in self.sizes:
                    self.finished.add(mid)
                changed.append(self._row(key, f))
            else:
                # confirm on the next look too, so a rename caught half-way isn't called a failure
                self.vanished[key] = self.vanished.get(key, 0) + 1
                if self.vanished[key] >= 2:
                    del self.vanished[key]
                    f.update(status="error", speed=0.0)
                    self.errors += 1
                    if self._msg_id(key) is not None:
                        self.error_ids.add(self._msg_id(key))
                    changed.append(self._row(key, f))

        # finished files (incl. small ones that came and went between two looks)
        for fname, size in finals.items():
            if fname in self.baseline:
                continue
            mid = self._msg_id(fname)
            if mid in self.sizes:
                self.finished.add(mid)
            self._count_bytes(fname, size)
            if fname not in self.files:
                m = _TDL_NAME.match(fname)
                f = self.files[fname] = {"name": m.group(2) if m else fname, "status": "done", "done": size,
                                         "total": size, "hist": None, "grew": now, "speed": 0.0}
                changed.append(self._row(fname, f))

        if self.dest_for:  # forum: move finished files into their topic folders
            move_finished(self.folder, self.dest_for, self.move_seen, now)

        self.last_tick = now
        self.total_hist.append((now, self.total_bytes))
        while len(self.total_hist) > 2 and now - self.total_hist[0][0] > SPEED_WINDOW:
            self.total_hist.popleft()
        active = [self._row(k, f) for k, f in self.files.items() if f["status"] in ("active", "stalled", "paused")]
        speed = 0.0 if paused else _speed(self.total_hist)
        if not paused:
            self.ema = _smooth(self.ema, speed, now - self.ema_t if self.ema_t is not None else None)
        self.ema_t = now
        # bytes still to come in this type: everything not finished/failed, minus what's already half-downloaded
        partial = {}
        for k, f in self.files.items():
            if f["status"] in ("active", "stalled", "paused"):
                mid = self._msg_id(k)
                if mid is not None:
                    partial[mid] = f["done"]
        remaining = 0
        for mid, size in self.sizes.items():
            if mid not in self.finished and mid not in self.error_ids:
                remaining += max(0, size - partial.get(mid, 0))
        rate = self.ema or 0.0
        eta = remaining / rate if rate > 1 and remaining else (0.0 if not remaining else None)
        eta_all = (remaining + self.later) / rate if rate > 1 else (0.0 if not (remaining + self.later) else None)
        return {"label": self.label, "rows": changed, "active": active, "speed": speed,
                "finished": len(self.finished), "wanted": self.wanted, "downloaded": self.total_bytes,
                "errors": self.errors, "paused": paused, "remaining": remaining, "later": self.later,
                "eta": eta, "eta_all": eta_all}


def _missing_rows(m: "Monitor") -> list[dict]:
    """After tdl has gone through the whole list: every file that still isn't there failed (some fail
    too fast to ever be seen in the folder). Shown red with its original name."""
    rows = []
    if m.dest_for:  # files moved into their topic folder before the live view saw them: show them green
        found: dict[str, set[int]] = {}
        for mid, dest in m.dest_for.items():
            if mid in m.finished:
                continue
            d = str(dest)
            if d not in found:
                found[d] = finished_ids(Path(dest), 0, any_chat=True)
            if mid in found[d]:
                m.finished.add(mid)
                topic = m.topic_of.get(mid) if m.topic_of else None
                rows.append({"key": f"{m.folder}|moved:{mid}", "mid": mid, "name": m.names.get(mid) or f"message {mid}",
                             "type": f"{topic}  /  {m.label}" if topic else m.label, "status": "done",
                             "done": m.sizes.get(mid, 0), "total": m.sizes.get(mid, 0), "speed": 0.0})
    for mid in sorted(m.sizes):
        if mid in m.finished or mid in m.error_ids:
            continue
        m.error_ids.add(mid)
        m.errors += 1
        topic = m.topic_of.get(mid) if m.topic_of else None
        rows.append({"key": f"{m.folder}|missing:{mid}", "mid": mid, "name": m.names.get(mid) or f"message {mid}",
                     "type": f"{topic}  /  {m.label}" if topic else m.label,
                     "status": "error", "done": 0, "total": m.sizes.get(mid, 0), "speed": 0.0})
    return rows


class MonitorThread(threading.Thread):
    """Runs Monitor.tick() once a second off the window's thread (big folders take a moment to scan)."""

    def __init__(self, monitor: Monitor, out_q: queue.Queue, extra: dict, interval: float = 1.0):
        super().__init__(daemon=True)
        self.m, self.q, self.extra, self.interval = monitor, out_q, extra, interval
        self.stop_evt = threading.Event()
        self.mark_missing = False

    def run(self):
        while True:
            stopping = self.stop_evt.wait(self.interval)
            try:
                snap = self.m.tick()
            except Exception as e:  # noqa: BLE001  (the display must never break the download)
                snap = {"error": f"{type(e).__name__}: {e}"}
            if stopping and self.mark_missing and "rows" in snap:
                extra_rows = _missing_rows(self.m)
                snap["rows"] = snap["rows"] + extra_rows
                snap["errors"] = self.m.errors
            snap.update(self.extra, final=stopping)
            self.q.put(("live", snap))
            if stopping:
                return

    def stop(self, mark_missing: bool = False):
        self.mark_missing = mark_missing
        self.stop_evt.set()


def keep_awake(on: bool) -> None:
    """Stop Windows going to sleep while a download runs (the screen may still turn off)."""
    if not IS_WINDOWS:
        return
    try:
        flags = 0x80000000 | (0x00000001 if on else 0)  # ES_CONTINUOUS | ES_SYSTEM_REQUIRED
        ctypes.windll.kernel32.SetThreadExecutionState(flags)
    except Exception:  # noqa: BLE001
        pass


# --------------------------------------------------------------------------- #
#  Colours, themes and the little custom widgets the window is built from
# --------------------------------------------------------------------------- #
def _rgb(h: str) -> tuple[int, int, int]:
    h = h.lstrip("#")
    return int(h[0:2], 16), int(h[2:4], 16), int(h[4:6], 16)


def _hex(r: float, g: float, b: float) -> str:
    return "#%02x%02x%02x" % tuple(max(0, min(255, int(round(v)))) for v in (r, g, b))


def mix(a: str, b: str, t: float) -> str:
    """Blend colour a towards colour b (t = 0 -> a, t = 1 -> b)."""
    ra, ga, ba = _rgb(a)
    rb, gb, bb = _rgb(b)
    return _hex(ra + (rb - ra) * t, ga + (gb - ga) * t, ba + (bb - ba) * t)


def luma(h: str) -> float:
    r, g, b = _rgb(h)
    return (0.2126 * r + 0.7152 * g + 0.0722 * b) / 255.0


def is_hex(s) -> bool:
    return isinstance(s, str) and re.fullmatch(r"#[0-9a-fA-F]{6}", s) is not None


def hsv_hex(h: float, s: float, v: float) -> str:
    r, g, b = colorsys.hsv_to_rgb(h % 1.0, max(0.0, min(1.0, s)), max(0.0, min(1.0, v)))
    return _hex(r * 255, g * 255, b * 255)


def hex_hsv(hx: str) -> tuple[float, float, float]:
    r, g, b = _rgb(hx)
    return colorsys.rgb_to_hsv(r / 255, g / 255, b / 255)


def _quant(c: str, step: int = 12) -> str:
    r, g, b = _rgb(c)
    return _hex(round(r / step) * step, round(g / step) * step, round(b / step) * step)


# The eleven colours you pick in "Create your own"; everything else is worked out from them.
CORE_KEYS = [
    ("bg", "Window background"), ("panel", "Panels"), ("raised", "Buttons & fields"),
    ("line2", "Borders & dividers"), ("ink", "Main text"), ("muted", "Quiet text"),
    ("accent", "Accent colour"), ("ok", "Done / success"), ("warn", "Warning / waiting"),
    ("err", "Error / failed"), ("busy", "Downloading now"),
]
STATUS_DEFAULT = {"ok": "#4ade80", "warn": "#fb923c", "err": "#ff5d57", "busy": "#ffd60a"}


def finish_theme(c: dict, name: str | None = None) -> dict:
    """Fills in every colour the window needs from a (possibly partial) theme."""
    t = dict(c)
    if name:
        t["n"] = name
    t.setdefault("n", "Custom")
    bg = t["bg"]
    t.setdefault("panel2", mix(t["panel"], t["raised"], 0.5))
    t.setdefault("well", mix(bg, "#000000", 0.5))
    t.setdefault("line", mix(bg, t["line2"], 0.5))
    t.setdefault("glow", mix(bg, t["accent"], 0.18))
    t.setdefault("dim", mix(t["muted"], bg, 0.5))
    for k, v in STATUS_DEFAULT.items():
        t.setdefault(k, v)
    return t


def core_of(th: dict) -> dict:
    return {k: th[k] for k, _ in CORE_KEYS}


def _mk(name: str, bg: str, tint: str, accent: str, ink: str, s: float = 1.0, **over) -> dict:
    """Builds a whole theme from: background, a surface tint, one accent and the text colour."""
    def k(a):
        return mix(bg, tint, min(0.85, a * s))
    t = dict(n=name, bg=bg, panel=k(0.05), panel2=k(0.08), raised=k(0.13), well=mix(bg, "#000000", 0.6),
             line=k(0.14), line2=k(0.27), ink=ink, muted=mix(ink, bg, 0.38), dim=mix(ink, bg, 0.64),
             accent=accent, glow=mix(bg, accent, 0.17))
    t.update(over)
    return finish_theme(t)


# --- 17 classic dark colour schemes --------------------------------------------------------------
_CLASSIC = {
    "graphite": dict(n="Rack Graphite", bg="#0a0e13", glow="#132339", panel="#10161d", panel2="#141b24", raised="#19212d", well="#0b1016", line="#202a37", line2="#2c394a", ink="#e8eef5", muted="#95a3b5", dim="#66758b", accent="#f4ab3e"),
    "midnight": dict(n="Midnight Blue", bg="#070b16", glow="#10224a", panel="#0b1222", panel2="#0f172b", raised="#152038", well="#070c18", line="#1a2642", line2="#263559", ink="#e6edff", muted="#9aa9cc", dim="#62719a", accent="#5ea2ff"),
    "tokyo": dict(n="Tokyo Night", bg="#16161e", glow="#24283b", panel="#1a1b26", panel2="#1f2030", raised="#24283b", well="#13131a", line="#292e42", line2="#3b4261", ink="#c0caf5", muted="#a9b1d6", dim="#565f89", accent="#7aa2f7"),
    "nord": dict(n="Nord", bg="#1f232b", glow="#2b3a4f", panel="#242933", panel2="#2a303c", raised="#323946", well="#1c2028", line="#363d4a", line2="#434c5e", ink="#eceff4", muted="#aab4c5", dim="#7b8496", accent="#88c0d0"),
    "dracula": dict(n="Dracula", bg="#1e1f29", glow="#2f2a4a", panel="#242530", panel2="#282a36", raised="#313343", well="#1b1c25", line="#343746", line2="#44475a", ink="#f8f8f2", muted="#b7b9cc", dim="#7c7f99", accent="#bd93f9"),
    "catppuccin": dict(n="Catppuccin Mocha", bg="#11111b", glow="#1e1e2e", panel="#181825", panel2="#1e1e2e", raised="#252536", well="#0f0f17", line="#2a2a3c", line2="#45475a", ink="#cdd6f4", muted="#bac2de", dim="#6c7086", accent="#f5c2e7"),
    "onedark": dict(n="One Dark", bg="#1b1f27", glow="#2a3140", panel="#21252b", panel2="#282c34", raised="#2f343f", well="#191c22", line="#323842", line2="#3e4451", ink="#dcdfe4", muted="#abb2bf", dim="#6b7280", accent="#61afef"),
    "gruvbox": dict(n="Gruvbox", bg="#1d2021", glow="#32302f", panel="#242526", panel2="#282828", raised="#32302f", well="#1a1c1d", line="#3c3836", line2="#504945", ink="#ebdbb2", muted="#bdae93", dim="#7c6f64", accent="#fe8019"),
    "solarized": dict(n="Solarized Dark", bg="#00212b", glow="#063845", panel="#002833", panel2="#073642", raised="#0b404e", well="#001e27", line="#0e4552", line2="#1c5866", ink="#eee8d5", muted="#93a1a1", dim="#657b83", accent="#b58900"),
    "monokai": dict(n="Monokai", bg="#1e1f1c", glow="#2d2e27", panel="#232420", panel2="#272822", raised="#30312a", well="#1a1b18", line="#33342d", line2="#49483e", ink="#f8f8f2", muted="#cfcfc2", dim="#75715e", accent="#a6e22e"),
    "ocean": dict(n="Deep Ocean", bg="#07141a", glow="#0b2f3d", panel="#0a1b23", panel2="#0d212b", raised="#122b37", well="#06121a", line="#16323f", line2="#204556", ink="#e2f4f8", muted="#9cc3cc", dim="#5f8892", accent="#2dd4bf"),
    "forest": dict(n="Forest", bg="#0b120d", glow="#16301d", panel="#0f1811", panel2="#131e16", raised="#1a281d", well="#09100b", line="#1d2e21", line2="#2a4130", ink="#e6f2e8", muted="#a3c2a9", dim="#6b8a71", accent="#8bd450"),
    "crimson": dict(n="Crimson", bg="#120a0c", glow="#2a1016", panel="#170d10", panel2="#1c1014", raised="#26161b", well="#0f080a", line="#2f1b21", line2="#45262e", ink="#f5e6e9", muted="#c9a3ab", dim="#86636b", accent="#ff5d73"),
    "synthwave": dict(n="Synthwave", bg="#120b1f", glow="#2b1150", panel="#170e28", panel2="#1d1233", raised="#26183f", well="#0f0919", line="#2e1d4a", line2="#45306a", ink="#f6e9ff", muted="#c9b2e6", dim="#8a73a8", accent="#ff3fb4"),
    "matrix": dict(n="Terminal Green", bg="#030805", glow="#0b2414", panel="#06100a", panel2="#08150d", raised="#0c1f13", well="#020604", line="#123321", line2="#1b4a2f", ink="#c8f7d2", muted="#7fcf93", dim="#4a8a5c", accent="#39ff7a"),
    "amber": dict(n="Amber CRT", bg="#0d0904", glow="#2a1a06", panel="#130d06", panel2="#181008", raised="#22170b", well="#0a0703", line="#2e200e", line2="#46311a", ink="#ffe2b0", muted="#d6ab6a", dim="#8f6c3f", accent="#ffb000"),
    "slate": dict(n="Slate", bg="#0f1115", glow="#1d222b", panel="#14171c", panel2="#191d23", raised="#21262e", well="#0d0f13", line="#252a33", line2="#333a45", ink="#e5e7eb", muted="#9ca3af", dim="#6b7280", accent="#a3a3ff"),
    "oled": dict(n="OLED Black", bg="#000000", glow="#0a0a0a", panel="#050505", panel2="#0a0a0a", raised="#141414", well="#000000", line="#1c1c1c", line2="#2a2a2a", ink="#f2f2f2", muted="#a0a0a0", dim="#666666", accent="#f4ab3e"),
}

# --- baked-in QD-OLED themes: true black backgrounds so the pixels switch off, accents that glow ---
#      (id, name, background, surface tint, accent, text)
_QD = [
    ("qd_hyper_pink", "Hyper Pink", "#000000", "#ff2e93", "#ff2e93", "#ffe6f1"),
    ("qd_ion_cyan", "Ion Cyan", "#000000", "#00d9ff", "#00e5ff", "#e3fbff"),
    ("qd_acid_lime", "Acid Lime", "#000000", "#b4ff39", "#b4ff39", "#f3ffdc"),
    ("qd_blood_moon", "Blood Moon", "#000000", "#ff1f2d", "#ff2a36", "#ffe5e6"),
    ("qd_solar_flare", "Solar Flare", "#000000", "#ffe600", "#ffe600", "#fffce0"),
    ("qd_ultraviolet", "Ultraviolet", "#000000", "#8a3dff", "#a066ff", "#f1e9ff"),
    ("qd_cobalt_blaze", "Cobalt Blaze", "#000000", "#2f6bff", "#3d7bff", "#e6eeff"),
    ("qd_ember", "Ember", "#000000", "#ff6a00", "#ff7b1c", "#fff0e2"),
    ("qd_rose_gold", "Rose Gold", "#000000", "#e8a598", "#f3b9aa", "#fff0eb"),
    ("qd_gold_leaf", "Gold Leaf", "#000000", "#d4af37", "#e8bf45", "#fff7de"),
    ("qd_paper_ghost", "Paper Ghost", "#000000", "#ffffff", "#f2f2f2", "#f5f5f5"),
    ("qd_deep_space", "Deep Space", "#02020b", "#5b5bff", "#6e6eff", "#ececff"),
    ("qd_fuchsia_storm", "Fuchsia Storm", "#000000", "#d63aff", "#e257ff", "#fbe9ff"),
]

# --- the "Random Theme" pool: none of these are in the gallery, none repeat the ones above ---------
#      pastel / two-tone dark themes (tinted surfaces + a contrasting accent)
_POOL = [
    # pink, cyan, green, red, yellow on black
    ("Cotton Candy Void", "#070205", "#ff8ccb", "#ffb3dc", "#fff0f8", 1.0),
    ("Arctic Ice", "#00050a", "#5ad7ee", "#a5f3ff", "#effcff", 1.0),
    ("Jade Noir", "#010604", "#0f8f5a", "#1fcf86", "#e3fff1", 1.2),
    ("Ruby Rose", "#080105", "#e11d48", "#f43f5e", "#ffe9ee", 1.0),
    ("Butter Static", "#060600", "#fff08a", "#ffee8a", "#fffbe6", 1.0),
    # two-tone: tinted surfaces with a contrasting accent
    ("Teal & Tangerine", "#00080a", "#14808f", "#ff8a3d", "#e6fbff", 1.9),
    ("Plum & Mint", "#070009", "#7a2a8f", "#6ee7b7", "#f4eaff", 1.9),
    ("Navy & Gold", "#00020c", "#1d3b8f", "#f5c542", "#eaf0ff", 1.9),
    ("Wine & Cyan", "#080003", "#8f1d3f", "#22e4ff", "#ffe9ef", 1.9),
    ("Pine & Pink", "#000804", "#1d8f55", "#ff7ac6", "#e9fff2", 1.9),
    ("Violet & Lime", "#05000d", "#5a2dc9", "#c6ff3d", "#f0eaff", 1.9),
    ("Cocoa & Cream", "#080402", "#8a5a35", "#ffd9a8", "#fff4e6", 1.9),
    ("Slate & Coral", "#04060a", "#3d5a80", "#ff6b6b", "#eef3fa", 1.9),
    ("Obsidian & Peach", "#05030a", "#4b3a7a", "#ffb08a", "#f5f0ff", 1.9),
    ("Cobalt & Citron", "#00030f", "#1f4fd6", "#e6ff4d", "#eaf1ff", 1.9),
]

THEMES: dict[str, dict] = {}
THEME_GROUP: dict[str, str] = {}
for _k, _v in _CLASSIC.items():
    THEMES[_k] = finish_theme(_v)
    THEME_GROUP[_k] = "classic"
for _id, _n, _bg, _tint, _acc, _ink in _QD:
    THEMES[_id] = _mk(_n, _bg, _tint, _acc, _ink)
    THEME_GROUP[_id] = "qd"
RANDOM_POOL = [_mk(n, bg, tint, acc, ink, s) for n, bg, tint, acc, ink, s in _POOL]
DEFAULT_THEME = "qd_ion_cyan"


def pal_from_theme(t: dict) -> dict:
    acc = t["accent"]
    return dict(
        bg=t["bg"], panel=t["panel"], panel2=t["panel2"], field=t["raised"], well=t["well"], line=t["line"],
        border=t["line2"], hover=mix(t["raised"], acc, 0.22), fg=t["ink"], muted=t["muted"], dim=t["dim"],
        accent=acc, accent_hi=mix(acc, "#ffffff", 0.22), accent_lo=mix(acc, "#000000", 0.30),
        accent_ink="#0b0b0b" if luma(acc) > 0.5 else "#ffffff", sel=mix(t["panel"], acc, 0.38), glow=t["glow"],
        green=t["ok"], red=t["err"], orange=t["warn"], yellow=t["busy"], blue="#7aa7ff",
    )


PAL: dict = {}
PAL.update(pal_from_theme(THEMES[DEFAULT_THEME]))

# What each of the Windows console's 16 colours becomes in the live console view (follows the theme)
CONSOLE_KEY = {0: "dim", 1: "blue", 2: "green", 3: "accent_hi", 4: "red", 5: "accent", 6: "yellow", 7: "fg",
               8: "dim", 9: "blue", 10: "green", 11: "accent_hi", 12: "red", 13: "accent", 14: "yellow", 15: "fg"}

# ---- theme registry: tk widgets that don't follow ttk styles are re-coloured through these ---------
THEME_HOOKS: list = []
_THEMED: list = []
_THEMED_TAGS: list = []


def themed(w, **spec):
    """Colour a plain Tk widget from palette keys now, and again whenever the theme changes."""
    try:
        w.configure(**{o: PAL[k] for o, k in spec.items()})
    except tk.TclError:
        return w
    _THEMED.append((w, spec))
    return w


def themed_tag(w, tag: str, **spec):
    try:
        w.tag_configure(tag, **{o: PAL[k] for o, k in spec.items()})
    except tk.TclError:
        return
    _THEMED_TAGS.append((w, tag, spec))


def retheme_widgets():
    for item in list(_THEMED):
        w, spec = item
        try:
            w.configure(**{o: PAL[k] for o, k in spec.items()})
        except tk.TclError:
            try:
                _THEMED.remove(item)
            except ValueError:
                pass
    for item in list(_THEMED_TAGS):
        w, tag, spec = item
        try:
            w.tag_configure(tag, **{o: PAL[k] for o, k in spec.items()})
        except tk.TclError:
            try:
                _THEMED_TAGS.remove(item)
            except ValueError:
                pass


def run_theme_hooks():
    for h in list(THEME_HOOKS):
        try:
            h()
        except tk.TclError:
            try:
                THEME_HOOKS.remove(h)
            except ValueError:
                pass
        except Exception:  # noqa: BLE001
            pass


def apply_ttk_theme(root) -> None:
    P = PAL
    style = ttk.Style(root)
    try:
        style.theme_use("clam")  # the only built-in theme that lets every colour be changed
    except Exception:  # noqa: BLE001
        pass
    sc, fam, comp = ui_scale(), ui_family(), ui_compact()
    try:
        from tkinter import font as tkfont
        if IS_WINDOWS:
            for n in ("TkDefaultFont", "TkTextFont", "TkHeadingFont", "TkMenuFont"):
                tkfont.nametofont(n).configure(family=fam, size=max(7, round(10 * sc)))
    except Exception:  # noqa: BLE001
        pass

    def F(size=10, bold=False, family=None):
        if not IS_WINDOWS:
            return None
        if family in (None, "Segoe UI") or (family == "Segoe UI Semibold" and fam != "Segoe UI"):
            family = fam
        sz = max(6, round(size * sc))
        return (family, sz, "bold") if bold else (family, sz)
    try:
        root.configure(bg=P["bg"])
    except Exception:  # noqa: BLE001
        pass
    style.configure(".", background=P["panel"], foreground=P["fg"], fieldbackground=P["field"],
                    bordercolor=P["border"], darkcolor=P["panel"], lightcolor=P["panel"],
                    troughcolor=P["well"], focuscolor=P["accent"], selectbackground=P["sel"],
                    selectforeground=P["fg"], insertcolor=P["fg"], arrowcolor=P["fg"])
    style.map(".", foreground=[("disabled", P["dim"])])
    style.configure("TFrame", background=P["panel"])
    style.configure("Card.TFrame", background=P["panel2"])
    style.configure("TLabelframe", background=P["panel"], bordercolor=P["border"], relief="solid")
    style.configure("TLabelframe.Label", background=P["panel"], foreground=P["accent_hi"], font=F(10, True))
    style.configure("SectionHdr.TFrame", background=P["panel2"])
    style.configure("SectionTitle.TLabel", background=P["panel2"], foreground=P["accent_hi"], font=F(10, True))
    style.configure("Head.TLabel", background=P["panel"], foreground=P["accent_hi"], font=F(10, True))
    style.configure("Grip.TLabel", background=P["panel2"], foreground=P["dim"], font=F(12, True, "Segoe UI Symbol"))
    style.configure("Title.TLabel", background=P["bg"], foreground=P["fg"], font=F(18, True, "Segoe UI Semibold"))
    style.configure("TitleAccent.TLabel", background=P["bg"], foreground=P["accent"],
                    font=F(18, True, "Segoe UI Semibold"))
    style.configure("Sub.TLabel", background=P["bg"], foreground=P["dim"], font=F(9))
    style.configure("TLabel", background=P["panel"], foreground=P["fg"])
    style.configure("Muted.TLabel", background=P["panel"], foreground=P["muted"])
    style.configure("Speed.TLabel", background=P["panel"], foreground=P["accent_hi"], font=F(16, True))
    style.configure("Err.TLabel", background=P["panel"], foreground=P["red"])
    style.configure("Wait.TLabel", background=P["panel"], foreground=P["orange"], font=F(11, True))
    style.configure("Eta.TLabel", background=P["panel"], foreground=P["accent_hi"], font=F(11, True))
    style.configure("TButton", background=P["field"], foreground=P["fg"], bordercolor=P["border"],
                    lightcolor=P["field"], darkcolor=P["field"], padding=(8, 2) if comp else (12, 5), focusthickness=0)
    style.map("TButton", background=[("disabled", P["panel2"]), ("pressed", P["sel"]), ("active", P["hover"])],
              foreground=[("disabled", P["dim"])], bordercolor=[("active", P["accent"])])
    style.configure("Toggle.TButton", background=P["field"], foreground=P["muted"], bordercolor=P["border"],
                    lightcolor=P["field"], darkcolor=P["field"], padding=(6, 1) if comp else (8, 2), focusthickness=0,
                    font=F(9))
    style.map("Toggle.TButton", background=[("pressed", P["sel"]), ("active", P["hover"])],
              foreground=[("active", P["fg"])], bordercolor=[("active", P["accent"])])
    style.configure("Accent.TButton", background=P["accent"], foreground=P["accent_ink"], bordercolor=P["accent_lo"],
                    lightcolor=P["accent"], darkcolor=P["accent"], font=F(10, True))
    style.map("Accent.TButton", background=[("disabled", P["panel2"]), ("pressed", P["accent_lo"]),
                                            ("active", P["accent_hi"])],
              foreground=[("disabled", P["dim"])])
    style.configure("TMenubutton", background=P["field"], foreground=P["fg"], bordercolor=P["border"],
                    lightcolor=P["field"], darkcolor=P["field"], padding=(12, 5), arrowcolor=P["fg"])
    style.map("TMenubutton", background=[("active", P["hover"])], bordercolor=[("active", P["accent"])])
    for cls in ("TCheckbutton", "TRadiobutton"):
        style.configure(cls, background=P["panel"], foreground=P["fg"], indicatorbackground=P["field"],
                        indicatorforeground=P["accent_ink"], upperbordercolor=P["border"],
                        lowerbordercolor=P["border"])
        style.map(cls, background=[("active", P["panel"])],
                  indicatorbackground=[("disabled", P["panel2"]), ("selected", P["accent"]), ("active", P["hover"])],
                  foreground=[("disabled", P["dim"])])
    style.configure("TEntry", fieldbackground=P["field"], foreground=P["fg"], bordercolor=P["border"],
                    lightcolor=P["field"], darkcolor=P["field"], padding=3)
    style.map("TEntry", fieldbackground=[("readonly", P["field"])], foreground=[("readonly", P["fg"])],
              bordercolor=[("focus", P["accent"])])
    style.configure("TCombobox", fieldbackground=P["field"], background=P["field"], foreground=P["fg"],
                    arrowcolor=P["fg"], bordercolor=P["border"], lightcolor=P["field"], darkcolor=P["field"],
                    selectbackground=P["field"], selectforeground=P["fg"], padding=3)
    style.map("TCombobox", fieldbackground=[("readonly", P["field"])], foreground=[("readonly", P["fg"])],
              bordercolor=[("focus", P["accent"])])
    root.option_add("*TCombobox*Listbox.background", P["field"])
    root.option_add("*TCombobox*Listbox.foreground", P["fg"])
    root.option_add("*TCombobox*Listbox.selectBackground", P["sel"])
    root.option_add("*TCombobox*Listbox.selectForeground", P["fg"])
    style.configure("TSpinbox", fieldbackground=P["field"], foreground=P["fg"], background=P["field"],
                    arrowcolor=P["fg"], bordercolor=P["border"], lightcolor=P["field"], darkcolor=P["field"])
    style.configure("Treeview", background=P["well"], fieldbackground=P["well"], foreground=P["fg"],
                    bordercolor=P["border"], lightcolor=P["well"], darkcolor=P["well"],
                    rowheight=int(round((20 if comp else 24) * sc)))
    style.map("Treeview", background=[("selected", P["sel"])], foreground=[("selected", P["fg"])])
    style.configure("Treeview.Heading", background=P["panel2"], foreground=P["muted"], bordercolor=P["border"],
                    lightcolor=P["panel2"], darkcolor=P["panel2"], relief="flat", font=F(10, True))
    style.map("Treeview.Heading", background=[("active", P["hover"])], foreground=[("active", P["fg"])])
    style.configure("TNotebook", background=P["panel"], borderwidth=0, tabmargins=(0, 0, 0, 0))
    style.configure("TNotebook.Tab", background=P["panel2"], foreground=P["muted"], padding=(14, 7),
                    borderwidth=0, font=F(10, True))
    style.map("TNotebook.Tab", background=[("selected", P["field"]), ("active", P["hover"])],
              foreground=[("selected", P["accent_hi"]), ("active", P["fg"])])
    style.configure("TSeparator", background=P["border"])
    # Settings window
    style.configure("SetCard.TFrame", background=P["panel2"])
    style.configure("SetName.TLabel", background=P["panel2"], foreground=P["fg"], font=F(10, True))
    style.configure("SetDesc.TLabel", background=P["panel2"], foreground=P["dim"], font=F(9))
    style.configure("SetValue.TLabel", background=P["panel2"], foreground=P["accent_hi"], font=F(10, True, "Consolas"))
    style.configure("SetHead.TLabel", background=P["panel"], foreground=P["muted"], font=F(9, True))
    style.configure("SetNote.TLabel", background=P["panel"], foreground=P["dim"], font=F(9))
    style.configure("SetKicker.TLabel", background=P["panel"], foreground=P["accent"], font=F(9, True))
    style.configure("SetTitle.TLabel", background=P["panel"], foreground=P["fg"], font=F(18, True, "Segoe UI Semibold"))
    style.configure("Placeholder.TLabel", background=P["field"], foreground=P["dim"], font=F(10))
    for nm, on in (("Seg.TButton", False), ("SegOn.TButton", True), ("Tab.TButton", False), ("TabOn.TButton", True)):
        tab = nm.startswith("Tab")
        bg = (mix(P["field"], P["accent"], 0.22) if on else P["field"]) if not tab else \
            (mix(P["panel"], P["accent"], 0.14) if on else P["panel"])
        style.configure(nm, background=bg, foreground=P["accent_hi"] if on else P["muted"],
                        bordercolor=P["accent"] if on else (P["border"] if not tab else P["panel"]),
                        lightcolor=bg, darkcolor=bg, focusthickness=0, font=F(10, on and tab),
                        padding=((10, 4) if comp else (14, 6)) if tab else ((8, 2) if comp else (11, 4)))
        style.map(nm, background=[("pressed", P["sel"]), ("active", mix(bg, P["accent"], 0.14))],
                  foreground=[("active", P["accent_hi"] if on else P["fg"])],
                  bordercolor=[("active", P["accent"])])
    style.configure("Set.Horizontal.TScale", background=P["accent"], troughcolor=P["well"], bordercolor=P["border"],
                    lightcolor=P["accent_hi"], darkcolor=P["accent_lo"])
    style.map("Set.Horizontal.TScale", background=[("active", P["accent_hi"])])
    style.configure("Horizontal.TProgressbar", background=P["accent"], troughcolor=P["well"],
                    bordercolor=P["border"], lightcolor=P["accent"], darkcolor=P["accent"], thickness=10)
    root.option_add("*Menu.background", P["panel2"])
    root.option_add("*Menu.foreground", P["fg"])
    root.option_add("*Menu.activeBackground", P["accent"])
    root.option_add("*Menu.activeForeground", P["accent_ink"])


def dark_title_bar(root) -> None:
    """Windows 10/11: dark title bar, tinted (Windows 11) with the theme's colours; follows theme changes."""
    if not IS_WINDOWS:
        return

    def paint():
        root.winfo_exists()  # raises TclError once the window is gone -> the hook removes itself
        try:
            root.update_idletasks()
            hwnd = ctypes.windll.user32.GetParent(root.winfo_id())
            on = ctypes.c_int(1)
            for attr in (20, 19):  # DWMWA_USE_IMMERSIVE_DARK_MODE (newer, older builds)
                if ctypes.windll.dwmapi.DwmSetWindowAttribute(hwnd, attr, ctypes.byref(on), ctypes.sizeof(on)) == 0:
                    break
            for attr, col in ((35, PAL["bg"]), (34, PAL["border"]), (36, PAL["fg"])):  # caption, border, text
                r, g, b = _rgb(col)
                ref = ctypes.c_int(r | (g << 8) | (b << 16)) if UI.get("titlebar_tint", True) \
                    else ctypes.c_uint(0xFFFFFFFF)      # DWMWA_COLOR_DEFAULT
                ctypes.windll.dwmapi.DwmSetWindowAttribute(hwnd, attr, ctypes.byref(ref), ctypes.sizeof(ref))
        except Exception:  # noqa: BLE001
            pass
    paint()
    THEME_HOOKS.append(paint)


def dark_tk_widget(w, kind: str) -> None:
    """Classic Tk widgets (Listbox, Text) don't follow ttk styles; colour them from the theme."""
    themed(w, bg="well", fg="fg", highlightbackground="border", highlightcolor="accent",
           selectbackground="sel", selectforeground="fg")
    try:
        if kind == "text":
            w.configure(highlightthickness=1, relief="flat", borderwidth=0, padx=8, pady=6)
            themed(w, insertbackground="fg")
        else:
            w.configure(highlightthickness=1, relief="flat", borderwidth=0, activestyle="none")
    except tk.TclError:
        pass


def box(parent) -> tk.Frame:
    f = tk.Frame(parent, highlightthickness=1, bd=0)
    themed(f, bg="panel", highlightbackground="border")
    return f


def autowrap(lbl, pad: int = 16) -> None:
    """Wrap a label's text to the width of the box it sits in (so narrow panels never clip it)."""
    def fit(_e=None):
        try:
            w = lbl.master.winfo_width()
            if w > 60:
                lbl.configure(wraplength=max(120, w - pad))
        except tk.TclError:
            pass
    lbl.master.bind("<Configure>", fit, add="+")


def flow(frame, widgets, gap: int = 6) -> None:
    """Lay widgets out left-to-right and wrap onto new rows when the panel is narrow."""
    state = {"w": None}

    def lay(_e=None):
        try:
            W = frame.winfo_width()
        except tk.TclError:
            return
        if W < 60 or state["w"] == W:
            return
        state["w"] = W
        x = r = c = 0
        for w in widgets:
            w.grid_forget()
            need = w.winfo_reqwidth() + gap
            if c and x + need > W:
                r += 1
                x = c = 0
            w.grid(row=r, column=c, padx=(0, gap), pady=(0, gap), sticky="w")
            x += need
            c += 1
    frame.bind("<Configure>", lay, add="+")
    for i, w in enumerate(widgets):
        w.grid(row=0, column=i, padx=(0, gap), pady=(0, gap), sticky="w")


def heat3(t: float) -> str:
    """0 -> red, 0.5 -> yellow, 1 -> green (the colours of the progress bars)."""
    t = max(0.0, min(1.0, t))
    if t < 0.5:
        return mix(PAL["red"], PAL["yellow"], t * 2)
    return mix(PAL["yellow"], PAL["green"], (t - 0.5) * 2)


class NeonScrollbar(tk.Canvas):
    """
    A wide, always-visible scrollbar with a glowing thumb. You can drag the thumb, click anywhere in the
    track to jump straight there (great for thousands of rows), or use the mouse wheel over it.
    """
    MIN = 40

    ALL: list = []
    SIZES = {"slim": 0.62, "normal": 1.0, "wide": 1.4}

    @classmethod
    def resize_all(cls):
        f = cls.SIZES.get(UI.get("scrollbar"), 1.0)
        for sb in list(cls.ALL):
            try:
                sb.configure(**{"width" if sb.vert else "height": max(6, int(round(sb._base * f)))})
            except tk.TclError:
                cls.ALL.remove(sb)

    def __init__(self, master, orient="vertical", command=None, thickness=16, **kw):
        self.vert = str(orient).startswith("v")
        self._base = thickness
        kw.setdefault("highlightthickness", 0)
        kw.setdefault("bd", 0)
        kw["width" if self.vert else "height"] = max(6, int(round(thickness * self.SIZES.get(UI.get("scrollbar"), 1.0))))
        kw.setdefault("height" if self.vert else "width", 24)   # ask for no length: it stretches to fit
        NeonScrollbar.ALL.append(self)
        super().__init__(master, bg=PAL["well"], cursor="hand2", **kw)
        self.command = command
        self.lo, self.hi = 0.0, 1.0
        self._hover = False
        self._drag = False
        self._off = 0.0
        self._t0 = 0.0
        self._tl = 0.0
        self._pad = 3
        self.bind("<Configure>", lambda _e: self.redraw())
        self.bind("<ButtonPress-1>", self._press)
        self.bind("<B1-Motion>", self._motion)
        self.bind("<ButtonRelease-1>", self._release)
        self.bind("<Enter>", lambda _e: self._set_hover(True))
        self.bind("<Leave>", lambda _e: self._set_hover(False))
        self.bind("<MouseWheel>", self._wheel)
        THEME_HOOKS.append(self.redraw)

    def set(self, lo, hi):
        self.lo, self.hi = float(lo), float(hi)
        self.redraw()

    def _set_hover(self, v):
        self._hover = v
        self.redraw()

    def _geom(self):
        L = self.winfo_height() if self.vert else self.winfo_width()
        T = self.winfo_width() if self.vert else self.winfo_height()
        return L, T

    def redraw(self):
        self.delete("all")
        super().configure(bg=PAL["well"])
        L, T = self._geom()
        if L < 12 or T < 4:
            return
        pad = self._pad
        th = max(4, T - 2 * pad)
        c = T / 2

        def seg(a0, a1, width, fill):
            if self.vert:
                self.create_line(c, a0, c, a1, width=width, fill=fill, capstyle="round")
            else:
                self.create_line(a0, c, a1, c, width=width, fill=fill, capstyle="round")
        g = max(2, th // 3)
        seg(pad + g / 2, L - pad - g / 2, g, mix(PAL["well"], PAL["border"], 0.6))
        span = self.hi - self.lo
        usable = L - 2 * pad
        if span >= 0.9999 or usable <= 0:
            self._t0, self._tl = pad, 0
            return
        tl = min(usable, max(self.MIN, span * usable))
        free = usable - tl
        start = pad + (self.lo / (1 - span)) * free if span < 1 else pad
        start = max(pad, min(pad + free, start))
        self._t0, self._tl = start, tl
        col = PAL["accent_hi"] if self._drag else PAL["accent"] if self._hover else mix(PAL["accent"], PAL["well"], 0.45)
        a0, a1 = start + th / 2, start + tl - th / 2
        if a1 < a0:
            a1 = a0
        seg(a0, a1, th, col)
        seg(a0, a1, max(2, th // 4), mix(col, "#ffffff", 0.35))  # the bright "neon core"

    def _pos(self, e):
        return e.y if self.vert else e.x

    def _press(self, e):
        p = self._pos(e)
        if self._t0 <= p <= self._t0 + self._tl:
            self._off = p - self._t0
        else:
            self._off = self._tl / 2
            self._move(p)
        self._drag = True
        self.redraw()

    def _motion(self, e):
        if self._drag:
            self._move(self._pos(e))

    def _release(self, _e):
        self._drag = False
        self.redraw()

    def _move(self, p):
        L, _ = self._geom()
        usable = L - 2 * self._pad
        free = usable - self._tl
        span = self.hi - self.lo
        if free <= 0 or span >= 1 or not self.command:
            return
        start = max(self._pad, min(self._pad + free, p - self._off))
        self.command("moveto", (start - self._pad) / free * (1 - span))

    def _wheel(self, e):
        if self.command:
            self.command("scroll", -int(e.delta / 120) * 3, "units")


class NeonBar(tk.Canvas):
    """A progress bar that is red when empty, shifts through yellow and ends up green when full."""

    def __init__(self, master, height=14, **kw):
        kw.pop("mode", None)
        kw.pop("orient", None)
        self._max = max(1e-9, float(kw.pop("maximum", 1) or 1))
        self._val = float(kw.pop("value", 0) or 0)
        self._shown = self._val
        self._job = None
        self._t = 0.0
        kw.setdefault("highlightthickness", 0)
        kw.setdefault("bd", 0)
        super().__init__(master, height=height, bg=PAL["panel"], **kw)
        self.bind("<Configure>", lambda _e: self.redraw())
        THEME_HOOKS.append(self.redraw)

    def configure(self, cnf=None, **kw):
        dirty = False
        if "maximum" in kw:
            self._max = max(1e-9, float(kw.pop("maximum")))
            dirty = True
        glide = False
        if "value" in kw:
            v = float(kw.pop("value"))
            glide = anim_on("anim_bar") and "maximum" not in kw and v > self._shown and self.winfo_ismapped()
            self._val = v
            if not glide:
                self._shown = v
            dirty = True
        if cnf or kw:
            super().configure(cnf, **kw)
        if glide:
            if self._job is None:
                self._t = time.perf_counter()
                self._job = self.after(8, self._glide)
        elif dirty:
            self._shown = self._val
            self.redraw()
    config = configure

    def _glide(self):
        self._job = None
        now = time.perf_counter()
        dt, self._t = now - self._t, now
        d = self._val - self._shown
        if abs(d) <= self._max * 0.0015 or not anim_on("anim_bar"):
            self._shown = self._val
            self.redraw()
            return
        self._shown += d * (1 - math.exp(-dt / 0.14))
        try:
            self.redraw()
            self._job = self.after(8, self._glide)
        except tk.TclError:
            pass

    def redraw(self):
        self.delete("all")
        super().configure(bg=PAL["panel"])
        w, h = self.winfo_width(), self.winfo_height()
        if w < 20 or h < 4:
            return
        pad = 2
        self.create_line(h / 2, h / 2, w - h / 2, h / 2, width=h - 2 * pad, fill=PAL["well"], capstyle="round")
        frac = max(0.0, min(1.0, self._shown / self._max))
        fw = frac * (w - 2 * pad)
        if fw < 1:
            return
        n = 56
        sw = (w - 2 * pad) / n
        for i in range(n):
            x0 = pad + i * sw
            if x0 >= pad + fw:
                break
            x1 = min(x0 + sw + 1, pad + fw)
            self.create_rectangle(x0, pad + 1, x1, h - pad - 1, outline="", fill=heat3(i / (n - 1)))
        self.create_line(pad + fw, pad + 1, pad + fw, h - pad - 1, fill=mix(heat3(frac), "#ffffff", 0.55), width=2)


class ColorWheel(tk.Canvas):
    """A hue/saturation wheel with a brightness bar underneath. Calls command(hex) as you drag."""
    BAR = 22

    def __init__(self, master, size=220, command=None):
        self.size = size
        super().__init__(master, width=size, height=size + self.BAR + 16, highlightthickness=0, bd=0,
                         bg=PAL["panel"])
        self.command = command
        self.h, self.s, self.v = 0.0, 0.0, 1.0
        self._mode = None
        self._img = None
        self._build_disc()
        self.bind("<ButtonPress-1>", self._press)
        self.bind("<B1-Motion>", self._drag)
        self.bind("<ButtonRelease-1>", lambda _e: setattr(self, "_mode", None))
        THEME_HOOKS.append(self._retheme)
        self.redraw()

    def _retheme(self):
        super().configure(bg=PAL["panel"])
        if PAL["panel"] != self._bgc:
            self._build_disc()
        self.redraw()

    def _build_disc(self):
        self._bgc = PAL["panel"]
        half = self.size // 2
        rad = half / 2 - 2
        img = tk.PhotoImage(width=half, height=half)
        bgc = PAL["panel"]
        rows = []
        for y in range(half):
            dy = y - half / 2 + 0.5
            row = []
            for x in range(half):
                dx = x - half / 2 + 0.5
                r = math.hypot(dx, dy)
                if r > rad:
                    row.append(bgc)
                else:
                    row.append(hsv_hex((math.atan2(-dy, dx) / (2 * math.pi)) % 1.0, r / rad, 1.0))
            rows.append("{" + " ".join(row) + "}")
        img.put(" ".join(rows))
        self._img = img.zoom(2, 2)

    def set_color(self, hx: str):
        if is_hex(hx):
            self.h, self.s, self.v = hex_hsv(hx)
            self.redraw()

    def get_color(self) -> str:
        return hsv_hex(self.h, self.s, self.v)

    def redraw(self):
        self.delete("all")
        cx = cy = self.size / 2
        rf = self.size / 2 - 4
        self.create_image(0, 0, anchor="nw", image=self._img)
        a = self.h * 2 * math.pi
        mx, my = cx + self.s * rf * math.cos(a), cy - self.s * rf * math.sin(a)
        cur = self.get_color()
        self.create_oval(mx - 9, my - 9, mx + 9, my + 9, outline="#000000", width=3)
        self.create_oval(mx - 8, my - 8, mx + 8, my + 8, outline="#ffffff", width=2, fill=cur)
        y0 = self.size + 12
        n = 44
        bw = self.size - 4
        for i in range(n):
            self.create_rectangle(2 + bw * i / n, y0, 2 + bw * (i + 1) / n + 1, y0 + self.BAR, outline="",
                                  fill=hsv_hex(self.h, self.s, i / (n - 1)))
        kx = 2 + bw * self.v
        self.create_rectangle(kx - 4, y0 - 3, kx + 4, y0 + self.BAR + 3, outline="#000000", width=3)
        self.create_rectangle(kx - 3, y0 - 2, kx + 3, y0 + self.BAR + 2, outline="#ffffff", width=1)

    def _press(self, e):
        self._mode = "wheel" if e.y <= self.size + 4 else "bar"
        self._drag(e)

    def _drag(self, e):
        if self._mode == "wheel":
            cx = cy = self.size / 2
            dx, dy = e.x - cx, e.y - cy
            self.s = min(1.0, math.hypot(dx, dy) / (self.size / 2 - 4))
            self.h = (math.atan2(-dy, dx) / (2 * math.pi)) % 1.0
        elif self._mode == "bar":
            self.v = max(0.0, min(1.0, (e.x - 2) / (self.size - 4)))
        else:
            return
        self.redraw()
        if self.command:
            self.command(self.get_color())


# --------------------------------------------------------------------------- #
#  Console colouring (the live console view)
# --------------------------------------------------------------------------- #
_PCT_RE = re.compile(r"(\d{1,3}(?:\.\d+)?)\s*%")
_ERR_WORDS = ("error", "failed", "fatal", "traceback", "exception", "denied", "not authorized", "couldn't",
              "cannot", "can't read")
_WARN_WORDS = ("slow down", "flood", "wait", "retry", "easing", "warning", "stalled", "timed out", "timeout",
               "speed limit", "premium", "!!", "paused", "not found")


def classify_console(plain: str) -> tuple[str, float | None]:
    """('progress', fraction) | 'ok' | 'warn' | 'err' | 'busy' | 'info' for one line of console text."""
    low = plain.lower().strip()
    if not low:
        return "blank", None
    stats_ok = re.sub(r"failed\s+0\b", "", low)
    if "done!" in low or low.startswith(("finished", "signed in", "done:")):
        return ("warn", None) if re.search(r"failed\s+[1-9]", low) else ("ok", None)
    if any(w in stats_ok for w in _ERR_WORDS):
        return "err", None
    m = _PCT_RE.search(plain)
    if m and ("[" in plain or "mb/s" in low or "eta" in low):
        try:
            p = float(m.group(1))
            if 0 <= p <= 100:
                return "progress", p / 100.0
        except ValueError:
            pass
    if any(w in low for w in _WARN_WORDS):
        return "warn", None
    if low.startswith("downloading") or re.search(r"\.\.\.\s*\[", plain):
        return "busy", None
    return "info", None


def flood_secs(plain: str) -> int | None:
    """Seconds of a 'Telegram asked us to slow down' / flood-wait line, or None if it isn't one."""
    low = plain.lower()
    if "slow down" not in low and "flood wait" not in low:
        return None
    if _PCT_RE.search(plain) and "[" in plain:
        return None
    m = re.search(r"sleeping for\s+(\d+)\s*s", low) or re.search(r"required[^0-9]*(\d+)\s*s", low) \
        or re.search(r"(\d+)\s*s\b", low)
    return int(m.group(1)) if m else 0


_RECONN = re.compile(r"server closed the connection|connection (was )?reset|winerror (64|10053|10054)|"
                     r"connection to telegram (was )?lost|0 bytes read on a total of", re.I)


def reconnect_kind(plain: str) -> str | None:
    """'net' = Windows dropped the link (WinError ...), 'eof' = Telegram's server closed it. None = not one."""
    if not _RECONN.search(plain or ""):
        return None
    return "net" if "winerror" in plain.lower() else "eof"


def fmt_dur(sec: int) -> str:
    sec = int(sec)
    if sec < 60:
        return f"{sec}s"
    if sec < 3600:
        return f"{sec // 60}m{sec % 60:02d}s"
    return f"{sec // 3600}h{(sec % 3600) // 60:02d}m"


def progress_key(plain: str) -> str:
    s = plain.strip()
    for sep in ("...", " ["):
        i = s.find(sep)
        if i > 0:
            return s[:i].strip().lower()
    return s[:40].lower()


def gradient_runs(text: str, frac: float, bg: str) -> list[tuple[str, str]]:
    """
    Splits a progress line into coloured runs: the part that is 'done' is green (glowing brighter at the
    leading edge) and the rest starts out red and warms through amber to yellow as the file nears the end.
    """
    n = len(text)
    if n == 0:
        return []
    frac = max(0.0, min(1.0, frac))
    ok, err, busy = PAL["green"], PAL["red"], PAL["yellow"]
    if frac >= 0.999:
        return [(text, ok)]
    k = frac * n
    full = int(k)
    part = k - full
    rem = mix(err, busy, min(1.0, frac * 1.25))
    dark, bright = mix(ok, bg, 0.35), mix(ok, "#ffffff", 0.25)
    cols = []
    for i in range(n):
        if i < full:
            cols.append(_quant(mix(dark, bright, (i / (full - 1)) ** 1.6 if full > 1 else 1.0)))
        elif i == full:
            cols.append(_quant(mix(rem, bright, part)))
        else:
            cols.append(_quant(rem))
    runs, start = [], 0
    for i in range(1, n + 1):
        if i == n or cols[i] != cols[start]:
            runs.append((text[start:i], cols[start]))
            start = i
    return runs


# --------------------------------------------------------------------------- #
#  Dock: every section is its own free box on a grid. Drag the title to move it, drag any edge or corner to
#  resize just that box (boxes next to it give way), and drop it onto another box to swap or split.
# --------------------------------------------------------------------------- #
SECTION_KEYS = ["save_loc", "what_save", "which_conv", "speed_safety", "queue", "controls",
                "tdl_console", "live_dl", "speed_graph", "activity_log"]
SECTION_MIN_H = {"save_loc": 140, "what_save": 112, "which_conv": 200, "speed_safety": 280, "queue": 150,
                 "controls": 96, "tdl_console": 120, "live_dl": 210, "speed_graph": 200, "activity_log": 96}
SECTION_MIN_W = 380
COLS, ROWS = 48, 60          # the grid every box snaps to (rows stretch to fit the window height)
GAP = 10                     # pixels between boxes


def _H(*kids, w=None):
    return {"o": "h", "c": list(kids), "w": list(w) if w else [1.0] * len(kids)}


def _V(*kids, w=None):
    return {"o": "v", "c": list(kids), "w": list(w) if w else [1.0] * len(kids)}


def layout_presets() -> dict:
    """Starting points only: each one is turned into independent boxes the moment you pick it."""
    return {
        "Command center (2 columns)": _H(
            _V("save_loc", "what_save", "which_conv", "speed_safety", "queue", w=[15, 10, 31, 22, 22]),
            _V("controls", "live_dl", "speed_graph", "tdl_console", "activity_log", w=[7, 15, 21, 10, 7]), w=[38, 62]),
        "Ultrawide (3 columns)": _H(
            _V("save_loc", "what_save", "speed_safety", "queue", w=[14, 11, 25, 28]),
            _V("which_conv", "controls", "live_dl", w=[34, 9, 52]),
            _V("speed_graph", "tdl_console", "activity_log", w=[36, 36, 28]), w=[27, 40, 33]),
        "Wide bands": _V(
            _H("save_loc", "what_save", "speed_safety", w=[40, 24, 36]),
            _H("which_conv", "queue", w=[56, 44]),
            "controls",
            _H(_V("live_dl", "speed_graph", w=[55, 45]), _V("tdl_console", "activity_log", w=[62, 38]), w=[58, 42]),
            w=[17, 25, 8, 50]),
        "Classic stack (1 column)": _V(*SECTION_KEYS[:5], "controls", "tdl_console", "live_dl", "speed_graph",
                                      "activity_log", w=[10, 8, 15, 12, 10, 6, 10, 15, 9, 8]),
    }


def tree_to_rects(tree, x=0, y=0, w=COLS, h=ROWS, out=None) -> dict:
    out = {} if out is None else out
    if isinstance(tree, str):
        out[tree] = [x, y, w, h]
        return out
    horiz = tree["o"] == "h"
    span = w if horiz else h
    tot = sum(tree["w"]) or 1.0
    edges, pos = [0], 0.0
    for wi in tree["w"]:
        pos += wi / tot * span
        edges.append(int(round(pos)))
    edges[-1] = span
    for i, c in enumerate(tree["c"]):
        a, b = edges[i], edges[i + 1]
        if horiz:
            tree_to_rects(c, x + a, y, b - a, h, out)
        else:
            tree_to_rects(c, x, y + a, w, b - a, out)
    return out


def _overlap(a, b) -> bool:
    return a[0] < b[0] + b[2] and b[0] < a[0] + a[2] and a[1] < b[1] + b[3] and b[1] < a[1] + a[3]


def grid_valid(rects: dict) -> bool:
    items = list(rects.items())
    for k, r in items:
        if len(r) != 4 or not all(isinstance(v, int) for v in r) or r[2] < 1 or r[3] < 1 or r[0] < 0 or r[1] < 0 \
                or r[0] + r[2] > COLS:
            return False
    for i in range(len(items)):
        for j in range(i + 1, len(items)):
            if _overlap(items[i][1], items[j][1]):
                return False
    return True


def grid_rows(rects: dict) -> int:
    return max([r[1] + r[3] for r in rects.values()] or [ROWS])


def grid_fill_holes(rects: dict, exclude: str | None = None) -> dict:
    """Empty space left behind is handed to the boxes that border it, as long as they fit it exactly."""
    skip = set()
    for _ in range(120):
        if not rects:
            return rects
        H = grid_rows(rects)
        occ = [[False] * COLS for _ in range(H)]
        for x, y, w, h in rects.values():
            for yy in range(y, y + h):
                for xx in range(x, x + w):
                    occ[yy][xx] = True
        hole = None
        for yy in range(H):
            for xx in range(COLS):
                if not occ[yy][xx] and (xx, yy) not in skip:
                    hole = (xx, yy)
                    break
            if hole:
                break
        if not hole:
            return rects
        hx, hy = hole
        hw = 0
        while hx + hw < COLS and not occ[hy][hx + hw]:
            hw += 1
        hh = 1
        while hy + hh < H and not any(occ[hy + hh][hx:hx + hw]):
            hh += 1
        sides = {"up": [], "down": [], "left": [], "right": []}
        for k, (x, y, w, h) in rects.items():
            if k == exclude:
                continue
            if hx <= x and x + w <= hx + hw:
                if y + h == hy:
                    sides["up"].append(k)
                elif y == hy + hh:
                    sides["down"].append(k)
            if hy <= y and y + h <= hy + hh:
                if x + w == hx:
                    sides["left"].append(k)
                elif x == hx + hw:
                    sides["right"].append(k)

        def covered(side):
            return sum((rects[k][2] if side in ("up", "down") else rects[k][3]) for k in sides[side])
        best = max(sides, key=covered)
        if not sides[best]:
            skip.add(hole)
            continue
        for k in sides[best]:
            r = rects[k]
            if best == "up":
                r[3] += hh
            elif best == "down":
                r[1] = hy
                r[3] += hh
            elif best == "left":
                r[2] += hw
            else:
                r[0] = hx
                r[2] += hw
    return rects


def grid_neighbor(rects: dict, key: str):
    """(box, side) describing where `key` sits next to another box, so it can be put back later."""
    x, y, w, h = rects[key]
    best, score = None, 0
    for k, (ox, oy, ow, oh) in rects.items():
        if k == key:
            continue
        if ox + ow == x or ox == x + w:
            s = min(y + h, oy + oh) - max(y, oy)
            if s > score:
                best, score = (k, "right" if ox + ow == x else "left"), s
        if oy + oh == y or oy == y + h:
            s = min(x + w, ox + ow) - max(x, ox)
            if s > score:
                best, score = (k, "bottom" if oy + oh == y else "top"), s
    return best


def grid_insert(rects: dict, key: str, target: str, side: str) -> dict:
    """Take `key` out of its place and set it beside `target` (the target's box is halved)."""
    R = {k: list(v) for k, v in rects.items() if k != key}
    grid_fill_holes(R)
    if target not in R:
        return grid_insert_root(rects, key, "bottom")
    x, y, w, h = R[target]
    if side in ("left", "right"):
        a = max(1, w // 2)
        R[key], R[target] = ([x, y, a, h], [x + a, y, w - a, h]) if side == "left" else \
            ([x + w - a, y, a, h], [x, y, w - a, h])
    else:
        a = max(1, h // 2)
        R[key], R[target] = ([x, y, w, a], [x, y + a, w, h - a]) if side == "top" else \
            ([x, y + h - a, w, a], [x, y, w, h - a])
    return R


def grid_insert_root(rects: dict, key: str, side: str) -> dict:
    """`key` takes a band along one whole edge of the window; everything else is squeezed into what's left."""
    R = {k: list(v) for k, v in rects.items() if k != key}
    grid_fill_holes(R)
    if not R:
        return {key: [0, 0, COLS, ROWS]}
    H = grid_rows(R)
    if side in ("left", "right"):
        band = max(8, int(round(COLS * 0.3)))
        s = (COLS - band) / COLS
        off = band if side == "left" else 0
        for r in R.values():
            a, b = int(round(off + r[0] * s)), int(round(off + (r[0] + r[2]) * s))
            r[0], r[2] = a, max(1, b - a)
        R[key] = [0, 0, band, H] if side == "left" else [COLS - band, 0, band, H]
    else:
        band = max(6, int(round(H * 0.3)))
        s = (H - band) / H
        off = band if side == "top" else 0
        for r in R.values():
            a, b = int(round(off + r[1] * s)), int(round(off + (r[1] + r[3]) * s))
            r[1], r[3] = a, max(1, b - a)
        R[key] = [0, 0, COLS, band] if side == "top" else [0, H - band, COLS, band]
    return R


def grid_occ(rects: dict, skip: str | None = None) -> list:
    H = max(ROWS, grid_rows(rects)) if rects else ROWS
    occ = [[False] * COLS for _ in range(H)]
    for k, (x, y, w, h) in rects.items():
        if k == skip:
            continue
        for yy in range(max(0, y), min(H, y + h)):
            row = occ[yy]
            for xx in range(max(0, x), min(COLS, x + w)):
                row[xx] = True
    return occ


def grid_free_rect(rects: dict, minw: int = 1, minh: int = 1, skip: str | None = None):
    """The biggest empty rectangle at least minw x minh, or None."""
    occ = grid_occ(rects, skip)
    heights = [0] * COLS
    best = None
    for y in range(len(occ)):
        for x in range(COLS):
            heights[x] = 0 if occ[y][x] else heights[x] + 1
        for x0 in range(COLS):
            mh = 1 << 30
            for x1 in range(x0, COLS):
                mh = min(mh, heights[x1])
                if mh == 0:
                    break
                w = x1 - x0 + 1
                if w >= minw and mh >= minh and (best is None or w * mh > best[2] * best[3]):
                    best = [x0, y - mh + 1, w, mh]
    return best


def grid_place_free(rects: dict, key: str, cx: int, cy: int):
    """Drop `key` into the empty space around cell (cx, cy): its own size, or less if the space is smaller."""
    occ = grid_occ(rects, skip=key)
    H = len(occ)
    if not (0 <= cy < H and 0 <= cx < COLS) or occ[cy][cx]:
        return None
    tw, th = rects[key][2], rects[key][3]
    x0 = x1 = cx
    y0 = y1 = cy

    def free(xa, ya, xb, yb):
        if xa < 0 or ya < 0 or xb >= COLS or yb >= H:
            return False
        return not any(occ[yy][xx] for yy in range(ya, yb + 1) for xx in range(xa, xb + 1))
    grew = True
    while grew:
        grew = False
        if x1 - x0 + 1 < tw and free(x1 + 1, y0, x1 + 1, y1):
            x1, grew = x1 + 1, True
        if x1 - x0 + 1 < tw and free(x0 - 1, y0, x0 - 1, y1):
            x0, grew = x0 - 1, True
        if y1 - y0 + 1 < th and free(x0, y1 + 1, x1, y1 + 1):
            y1, grew = y1 + 1, True
        if y1 - y0 + 1 < th and free(x0, y0 - 1, x1, y0 - 1):
            y0, grew = y0 - 1, True
    R = {k: list(v) for k, v in rects.items()}
    R[key] = [x0, y0, x1 - x0 + 1, y1 - y0 + 1]
    return R


def grid_swap(rects: dict, a: str, b: str) -> dict:
    R = {k: list(v) for k, v in rects.items()}
    R[a], R[b] = R[b], R[a]
    return R


def grid_resize(rects: dict, key: str, ex: int, ey: int, du: int, dv: int, minw: dict, minh: dict) -> dict:
    """
    Drags one edge / corner of one box. Only boxes that are in the way give way: they shrink (never below
    their minimum), and the dragged box stops when they can't give any more.
    """
    R = {k: list(v) for k, v in rects.items()}
    x0, y0, w0, h0 = R[key]
    H = grid_rows(R)
    x, y, w, h = x0, y0, w0, h0
    mw, mh = min(minw[key], w0), min(minh[key], h0)
    if ex > 0:
        w = max(mw, min(COLS - x0, w0 + du))
    elif ex < 0:
        x = max(0, min(x0 + w0 - mw, x0 + du))
        w = x0 + w0 - x
    if ey > 0:
        h = max(mh, min(H - y0, h0 + dv))
    elif ey < 0:
        y = max(0, min(y0 + h0 - mh, y0 + dv))
        h = y0 + h0 - y

    def em(d, k, i):  # smallest size box k may be squeezed to
        return min(d[k], R[k][i])

    # vertical first (against the boxes that share its columns), then horizontal (against the final rows)
    if ey > 0:
        lim = y + h
        for k, o in R.items():
            if k != key and o[1] >= y0 + h0 and o[0] < x + w and x < o[0] + o[2]:
                lim = min(lim, o[1] + o[3] - em(minh, k, 3))
        if lim < y + h:
            h = max(h0, lim - y)
        for k, o in R.items():
            if k != key and o[1] >= y0 + h0 and o[0] < x + w and x < o[0] + o[2] and y + h > o[1]:
                o[3] = o[1] + o[3] - (y + h)
                o[1] = y + h
    elif ey < 0:
        lim = y
        for k, o in R.items():
            if k != key and o[1] + o[3] <= y0 and o[0] < x + w and x < o[0] + o[2]:
                lim = max(lim, o[1] + em(minh, k, 3))
        if lim > y:
            y, h = lim, y0 + h0 - lim
        for k, o in R.items():
            if k != key and o[1] + o[3] <= y0 and o[0] < x + w and x < o[0] + o[2] and o[1] + o[3] > y:
                o[3] = y - o[1]
    if ex > 0:
        lim = x + w
        for k, o in R.items():
            if k != key and o[0] >= x0 + w0 and o[1] < y + h and y < o[1] + o[3]:
                lim = min(lim, o[0] + o[2] - em(minw, k, 2))
        if lim < x + w:
            w = max(w0, lim - x)
        for k, o in R.items():
            if k != key and o[0] >= x0 + w0 and o[1] < y + h and y < o[1] + o[3] and x + w > o[0]:
                o[2] = o[0] + o[2] - (x + w)
                o[0] = x + w
    elif ex < 0:
        lim = x
        for k, o in R.items():
            if k != key and o[0] + o[2] <= x0 and o[1] < y + h and y < o[1] + o[3]:
                lim = max(lim, o[0] + em(minw, k, 2))
        if lim > x:
            x, w = lim, x0 + w0 - lim
        for k, o in R.items():
            if k != key and o[0] + o[2] <= x0 and o[1] < y + h and y < o[1] + o[3] and o[0] + o[2] > x:
                o[2] = x - o[0]
    R[key] = [x, y, w, h]
    return R


def grab_client_area(widget):
    """
    Windows: picture of the window's client area taken with PrintWindow, so it is the app's own pixels even
    when another window lies on top of it. Returns (PIL image, screen x, screen y of its top-left) or None.
    """
    if not IS_WINDOWS:
        return None
    try:
        import ctypes
        from ctypes import wintypes
        from PIL import Image
    except Exception:  # noqa: BLE001
        return None
    u, g = ctypes.WinDLL("user32"), ctypes.WinDLL("gdi32")   # own handles: argtypes set here stay here
    H = ctypes.c_void_p
    u.GetParent.restype, u.GetParent.argtypes = H, [H]
    u.GetDC.restype, u.GetDC.argtypes = H, [H]
    u.ReleaseDC.argtypes = [H, H]
    u.GetClientRect.argtypes = [H, ctypes.POINTER(wintypes.RECT)]
    u.ClientToScreen.argtypes = [H, ctypes.POINTER(wintypes.POINT)]
    u.PrintWindow.argtypes = [H, H, wintypes.UINT]
    g.CreateCompatibleDC.restype, g.CreateCompatibleDC.argtypes = H, [H]
    g.CreateCompatibleBitmap.restype, g.CreateCompatibleBitmap.argtypes = H, [H, ctypes.c_int, ctypes.c_int]
    g.SelectObject.restype, g.SelectObject.argtypes = H, [H, H]
    g.DeleteObject.argtypes = [H]
    g.DeleteDC.argtypes = [H]
    g.GetDIBits.argtypes = [H, H, wintypes.UINT, wintypes.UINT, ctypes.c_void_p, ctypes.c_void_p, wintypes.UINT]

    class BIH(ctypes.Structure):
        _fields_ = [("biSize", wintypes.DWORD), ("biWidth", wintypes.LONG), ("biHeight", wintypes.LONG),
                    ("biPlanes", wintypes.WORD), ("biBitCount", wintypes.WORD), ("biCompression", wintypes.DWORD),
                    ("biSizeImage", wintypes.DWORD), ("biXPelsPerMeter", wintypes.LONG),
                    ("biYPelsPerMeter", wintypes.LONG), ("biClrUsed", wintypes.DWORD),
                    ("biClrImportant", wintypes.DWORD)]

    top = widget.winfo_toplevel()
    hwnd = u.GetParent(top.winfo_id()) or top.winfo_id()
    rc = wintypes.RECT()
    u.GetClientRect(hwnd, ctypes.byref(rc))
    w, h = rc.right - rc.left, rc.bottom - rc.top
    if w <= 0 or h <= 0:
        return None
    hdc = u.GetDC(hwnd)
    mdc = g.CreateCompatibleDC(hdc)
    bmp = g.CreateCompatibleBitmap(hdc, w, h)
    old = g.SelectObject(mdc, bmp)
    try:
        if not u.PrintWindow(hwnd, mdc, 3):            # PW_CLIENTONLY | PW_RENDERFULLCONTENT
            return None
        bi = BIH(ctypes.sizeof(BIH), w, -h, 1, 32, 0, 0, 0, 0, 0, 0)
        buf = ctypes.create_string_buffer(w * h * 4)
        if not g.GetDIBits(mdc, bmp, 0, h, buf, ctypes.byref(bi), 0):
            return None
        img = Image.frombuffer("RGB", (w, h), buf, "raw", "BGRX", 0, 1).copy()
    finally:
        g.SelectObject(mdc, old)
        g.DeleteObject(bmp)
        g.DeleteDC(mdc)
        u.ReleaseDC(hwnd, hdc)
    pt = wintypes.POINT(0, 0)
    u.ClientToScreen(hwnd, ctypes.byref(pt))
    return img, pt.x, pt.y


class Dock:
    """
    Owns the boxes. Sections are frames created by the app; this decides where each one sits.

    Moving, resizing and switching layouts never shove the real sections around frame by frame (that is what
    made Tk tear and leave ghost pixels). Instead a light "blueprint" layer is laid over the area and animated
    at ~240 frames a second; the real layout is applied once, underneath it, and the layer lifts away when
    everything below has finished drawing.
    """

    FPS_MS = 4            # ~240 Hz for the blueprint / morph animations
    EASE = 0.030          # seconds: how quickly the blueprint glides to where it is going
    CORNER = 22           # near a corner, the gap grabs both edges at once
    CURSORS = {(1, 0): "sb_h_double_arrow", (-1, 0): "sb_h_double_arrow", (0, 1): "sb_v_double_arrow",
               (0, -1): "sb_v_double_arrow", (1, 1): "size_nw_se", (-1, -1): "size_nw_se",
               (1, -1): "size_ne_sw", (-1, 1): "size_ne_sw"}

    def __init__(self, app, area, sections: dict, layout, hidden: dict):
        self.app, self.area, self.sections = app, area, sections
        self.hidden: dict = {k: v for k, v in (hidden or {}).items() if k in sections}
        self.rects: dict = {}
        self.ox = self.oy = 0           # scroll offsets, only used when the window is too small for the layout
        self._settled = False           # first real layout pass: repair a layout that cannot fit its minimums
        self._view = (0, 0)             # virtual size of the layout in pixels
        self._keep = None               # (window w, h, scrolled w, h) to hold steady while you edit
        self._m: dict | None = None     # metrics of the last layout pass
        self._placed: dict = {}         # key -> geometry last given to place(): unchanged boxes are left alone
        self._boxes_px: dict = {}       # key -> (x, y, w, h) on screen, area coordinates
        self._vs = NeonScrollbar(area, orient="vertical", command=self._yview, thickness=12)
        self._hs = NeonScrollbar(area, orient="horizontal", command=self._xview, thickness=12)
        # hover guides: thin accent bars drawn *in the gap*, never on top of a box
        self._guides = [tk.Frame(area, bd=0, highlightthickness=0) for _ in range(2)]
        for gw in self._guides:
            themed(gw, bg="accent")
        self._hover = None
        # the blueprint layer
        self.bp = tk.Canvas(area, highlightthickness=0, bd=0)
        themed(self.bp, bg="bg")
        self._bp_on = False
        self._bp_closing = False
        self._bp_dirty = False
        self._bp_cur: dict = {}
        self._bp_tgt: dict = {}
        self._bp_items: dict = {}
        self._bp_gone: set = set()
        self._ghost: dict | None = None
        self._snap: dict = {}           # key -> PIL image of the box as it looked when the drag began
        self._PIL = None                # ImageTk once Pillow is found; False when it isn't there
        self._tick_job = None
        self._last_t = 0.0
        self._hi = False
        self.drag: dict | None = None
        self.rs: dict | None = None
        self._job = None
        self.set_layout(layout, save=False, render=False)
        area.bind("<Configure>", self._on_area_cfg)
        area.bind("<Motion>", self._area_motion)
        area.bind("<Leave>", lambda _e: self._set_hover(None))
        area.bind("<ButtonPress-1>", self._area_press)
        area.bind("<B1-Motion>", self._rs_move)
        area.bind("<ButtonRelease-1>", self._rs_end)
        area.winfo_toplevel().bind("<Escape>", self._cancel, add="+")

    # -- state ------------------------------------------------------------------------------ #
    def state(self) -> dict:
        return {"v": 2, "rects": {k: list(v) for k, v in self.rects.items()},
                "hidden": {k: list(v) for k, v in self.hidden.items()}}

    def _visible(self) -> set:
        return set(self.sections) - set(self.hidden)

    def set_layout(self, layout, save=True, render=True):
        """`layout` is a preset tree, a saved {'rects': ...} state, or None."""
        R = self._build(layout)
        self.ox = self.oy = 0
        self._keep = None
        if render:
            self._morph(R)
        else:
            self.rects = R
        if save:
            self.app.save_dock()

    def apply_state(self, st: dict):
        """A saved layout: its boxes *and* which sections it had hidden."""
        self.hidden = {k: list(v) for k, v in (st.get("hidden") or {}).items() if k in self.sections}
        self.set_layout(st)

    def set_tree(self, tree):
        self.set_layout(tree)

    def _build(self, layout) -> dict:
        keys = self._visible()
        R = None
        if isinstance(layout, dict) and isinstance(layout.get("rects"), dict):
            try:
                R = {k: [int(n) for n in v] for k, v in layout["rects"].items() if k in keys}
            except (TypeError, ValueError):
                R = None
        elif isinstance(layout, (dict, str)):
            try:
                R = {k: v for k, v in tree_to_rects(layout).items() if k in keys}
            except (KeyError, TypeError, ValueError):
                R = None
        if R is None or not grid_valid(R):
            R = {k: v for k, v in tree_to_rects(layout_presets()["Command center (2 columns)"]).items() if k in keys}
        grid_fill_holes(R)
        for k in SECTION_KEYS:
            if k in keys and k not in R:
                R = grid_insert(R, k, "live_dl", "bottom") if k == "speed_graph" and "live_dl" in R \
                    else grid_insert_root(R, k, "bottom")
        return R

    # -- fitting: a box must never be smaller than its minimum, so a layout that is too big scrolls ----- #
    @staticmethod
    def need(R: dict) -> tuple:
        """Pixels of width and height the layout needs so that every box keeps its minimum size."""
        if not R:
            return 0.0, 0.0
        H = max(ROWS, grid_rows(R))
        cpn = max((SECTION_MIN_W + GAP) / max(1, r[2]) for r in R.values())
        rpn = max((SECTION_MIN_H.get(k, 90) * ui_scale() + GAP) / max(1, r[3]) for k, r in R.items())
        return cpn * COLS, rpn * H

    def _auto_repair(self, aw: int, ah: int):
        """Runs once, on the first real layout: if the saved layout can't fit its boxes in this window
        (squashed boxes, hidden content), switch to whichever starting layout fits best."""
        def score(R):
            nw, nh = self.need(R)
            return max(nw / max(1, aw), nh / max(1, ah))
        cur = score(self.rects)
        if cur <= 1.01 or not UI.get("auto_fix", True):
            return
        best, best_s = None, cur
        for name, tree in layout_presets().items():
            R = self._build(tree)
            sc = score(R)
            if sc < best_s - 0.02:
                best, best_s = (name, R), sc
        if best:
            self._keep = None
            self.rects = best[1]
            self.app.log(f"Your saved layout didn't fit this window (some boxes were squashed), "
                         f"so I switched to '{best[0]}'. Pick any layout from the Layout menu.", "warn")
            self.app.save_dock()

    def base_height(self) -> int:
        """Shortest the layout gets before it scrolls instead of squashing (window made shorter)."""
        try:
            v = int(UI.get("layout_h", 0))
        except (TypeError, ValueError):
            v = 0
        if v >= 400:
            return v
        try:   # auto: about as tall as the layout is when the window is maximised on this screen
            return max(500, self.area.winfo_screenheight() - 210)
        except tk.TclError:
            return 900

    def _metrics(self, R: dict | None = None) -> dict:
        R = self.rects if R is None else R
        aw, ah = self.area.winfo_width(), self.area.winfo_height()
        nw, nh = self.need(R)
        if UI.get("win_shrink", "scroll") == "scroll":
            # a shorter window scrolls the layout: the sections keep their size (a taller one still fills)
            nh = max(nh, self.base_height())
        H = max(ROWS, grid_rows(R)) if R else ROWS
        bar = 12
        needv, needh = nh > ah + 2, nw > aw + 2
        for _ in range(2):          # a scrollbar takes room, which can make the other one necessary
            needh = nw > aw - (bar if needv else 0) + 2
            needv = nh > ah - (bar if needh else 0) + 2
        keep = self._keep
        if keep and keep[0] == aw and keep[1] == ah:
            # Same window size as last time: never shrink the scrolled area just because one box got
            # bigger (that rescaled every other box). It still grows if a box needs more room.
            nw, nh = max(nw, keep[2]), max(nh, keep[3])
            needh = nw > aw - (bar if needv else 0) + 2
            needv = nh > ah - (bar if needh else 0) + 2
        avw, avh = aw - (bar if needv else 0), ah - (bar if needh else 0)
        vw, vh = max(avw, int(nw)), max(avh, int(nh))
        return {"aw": aw, "ah": ah, "avw": avw, "avh": avh, "vw": vw, "vh": vh, "needv": needv,
                "needh": needh, "cp": vw / COLS, "rp": vh / H, "bar": bar}

    def _boxes(self, R: dict, m: dict) -> dict:
        g = GAP // 2
        ox, oy = int(self.ox), int(self.oy)
        out = {}
        for k, r in R.items():
            X0, X1 = int(round(r[0] * m["cp"])), int(round((r[0] + r[2]) * m["cp"]))
            Y0, Y1 = int(round(r[1] * m["rp"])), int(round((r[1] + r[3]) * m["rp"]))
            out[k] = (X0 + g - ox, Y0 + g - oy, max(40, X1 - X0 - 2 * g), max(40, Y1 - Y0 - 2 * g))
        return out

    def _yview(self, *a):
        vw, vh = self._view
        span = max(0, vh - (self._m or {}).get("avh", self.area.winfo_height()))
        if a[0] == "moveto":
            self.oy = float(a[1]) * vh
        elif a[0] == "scroll":
            self.oy += int(a[1]) * 60 * (1 if a[2] == "units" else 6)
        self.oy = max(0, min(span, self.oy))
        self.layout()

    def _xview(self, *a):
        vw, vh = self._view
        span = max(0, vw - (self._m or {}).get("avw", self.area.winfo_width()))
        if a[0] == "moveto":
            self.ox = float(a[1]) * vw
        elif a[0] == "scroll":
            self.ox += int(a[1]) * 60 * (1 if a[2] == "units" else 6)
        self.ox = max(0, min(span, self.ox))
        self.layout()

    def wheel(self, e) -> None:
        """Mouse wheel scrolls the layout, but only where nothing else would use the wheel."""
        if self._bp_on or not self._m or not self._m["needv"] or not UI.get("wheel_scroll", True):
            return
        try:
            if e.widget.winfo_toplevel() is not self.area.winfo_toplevel():
                return
        except (tk.TclError, AttributeError):
            return
        try:
            cls = e.widget.winfo_class()
        except (tk.TclError, AttributeError):
            return
        if cls in ("Text", "Treeview", "Listbox", "Canvas", "TCombobox", "Scrollbar", "TScrollbar"):
            return
        self._yview("scroll", -1 if e.delta > 0 else 1, "units")

    # -- drawing ---------------------------------------------------------------------------- #
    def render(self):
        self.layout()

    def layout(self):
        aw, ah = self.area.winfo_width(), self.area.winfo_height()
        if aw < 60 or ah < 60:
            return
        if not self._settled and aw >= 700 and ah >= 420 and self.rects:
            self._settled = True
            self._auto_repair(aw, ah)
        m = self._metrics()
        self._m = m
        self._view = (m["vw"], m["vh"])
        self._keep = (aw, ah, m["vw"] if m["needh"] else 0, m["vh"] if m["needv"] else 0)
        self.ox = max(0, min(self.ox, m["vw"] - m["avw"]))
        self.oy = max(0, min(self.oy, m["vh"] - m["avh"]))
        bar = m["bar"]
        if m["needv"]:
            self._vs.place(x=aw - bar, y=0, width=bar, height=m["avh"])
            self._vs.set(self.oy / m["vh"], (self.oy + m["avh"]) / m["vh"])
        else:
            self._vs.place_forget()
        if m["needh"]:
            self._hs.place(x=0, y=ah - bar, width=m["avw"], height=bar)
            self._hs.set(self.ox / m["vw"], (self.ox + m["avw"]) / m["vw"])
        else:
            self._hs.place_forget()
        boxes = self._boxes(self.rects, m)
        for k, sec in self.sections.items():
            o = sec["outer"]
            b = boxes.get(k)
            if b is None:
                if self._placed.pop(k, None) is not None or o.winfo_manager():
                    o.place_forget()
                continue
            if self._placed.get(k) != b:      # only boxes that actually moved are touched
                o.place(x=b[0], y=b[1], width=b[2], height=b[3])
                self._placed[k] = b
        self._boxes_px = boxes
        for w in (self._vs, self._hs):
            tk.Misc.lift(w)
        if self._bp_on:
            tk.Misc.lift(self.bp)
        elif self._hover and not self.rs:
            self._show_guides(self._hover)

    def schedule_weights(self):
        self.area.after(60, self.layout)

    def _on_area_cfg(self, _e):
        if self._job is None:
            self._job = self.area.after_idle(self._cfg_run)

    def _cfg_run(self):
        self._job = None
        self.layout()

    # -- changes ---------------------------------------------------------------------------- #
    def hide(self, key: str) -> bool:
        if key in self.hidden or key not in self.rects or len(self.rects) <= 1:
            return False
        nb = grid_neighbor(self.rects, key)
        self.hidden[key] = list(nb) if nb else [next(k for k in self.rects if k != key), "bottom"]
        R = {k: list(v) for k, v in self.rects.items() if k != key}
        self._morph(grid_fill_holes(R) if UI.get("auto_size", False) else R)
        self.app.save_dock()
        return True

    def show(self, key: str):
        pos = self.hidden.pop(key, None)
        spot = None
        if self.rects and not UI.get("auto_size", False):
            # come back into empty space if there's room, without touching anything else
            mw, mh = self._mins(self._m or self._metrics())
            spot = grid_free_rect(self.rects, mw.get(key, 4), mh.get(key, 3))
        if not self.rects:
            R = {key: [0, 0, COLS, ROWS]}
        elif spot:
            R = {k: list(v) for k, v in self.rects.items()}
            R[key] = spot
        elif pos and pos[0] in self.rects:
            R = grid_insert(self.rects, key, pos[0], pos[1])
        else:
            R = grid_insert_root(self.rects, key, "bottom")
        self._morph(R)
        self.app.save_dock()
        if hasattr(self.app, "flash_section"):
            self.app.flash_section(key)

    def tidy(self):
        self._morph(grid_fill_holes({k: list(v) for k, v in self.rects.items()}))
        self.app.save_dock()

    # -- the blueprint layer ------------------------------------------------------------------ #
    def _hires(self, on: bool):
        """Windows' timer normally ticks every ~15.6 ms; ask for 1 ms while animating so frames land on time."""
        if not IS_WINDOWS or on == self._hi:
            return
        self._hi = on
        try:
            import ctypes
            (ctypes.windll.winmm.timeBeginPeriod if on else ctypes.windll.winmm.timeEndPeriod)(1)
        except Exception:  # noqa: BLE001
            pass

    def _bp_make(self, k: str, focus: bool) -> dict:
        """Canvas items for one box: its real content (a snapshot) when we have one, a drawn card otherwise."""
        c, P = self.bp, PAL
        f = "Segoe UI" if IS_WINDOWS else "TkDefaultFont"
        it: dict = {"focus": focus}
        if k in self._snap:
            it["body"] = c.create_rectangle(0, 0, 1, 1, fill=P["panel"], outline=P["border"])
            it["img"] = c.create_image(0, 0, anchor="nw")
        else:
            body = mix(P["panel"], P["accent"], 0.10) if focus else P["panel"]
            it["body"] = c.create_rectangle(0, 0, 1, 1, fill=body, outline=P["border"])
            it["hdr"] = c.create_rectangle(0, 0, 1, 1, fill=mix(P["panel2"], P["accent"], 0.2 if focus else 0),
                                           outline="")
            it["rule"] = c.create_line(0, 0, 1, 0, fill=P["line"])
            it["title"] = c.create_text(0, 0, anchor="w", fill=P["accent_hi"], font=(f, 10, "bold"),
                                        text="⠿   " + self.app.section_title(k))
        if focus:
            it["ring"] = c.create_rectangle(0, 0, 1, 1, outline=P["accent"], width=2)
            it["pill"] = c.create_rectangle(0, 0, 1, 1, fill=P["accent"], outline="")
            it["size"] = c.create_text(0, 0, anchor="se", fill=P["accent_ink"], font=(f, 9, "bold"), text="")
        return it

    def _snapshot(self):
        """Grab what the boxes look like right now, so the blueprint moves the real content around."""
        self._snap = {}
        if self._PIL is False or not anim_on("anim_snap"):
            return
        try:
            from PIL import ImageGrab, ImageTk
            self._PIL = ImageTk
            self.area.update_idletasks()
            ax, ay = self.area.winfo_rootx(), self.area.winfo_rooty()
            aw, ah = self.area.winfo_width(), self.area.winfo_height()
            shot = grab_client_area(self.area)
            if shot:            # the window's own pixels, even if something is lying on top of it
                full, cx, cy = shot
                img = full.crop((ax - cx, ay - cy, ax - cx + aw, ay - cy + ah))
            else:
                img = ImageGrab.grab(bbox=(ax, ay, ax + aw, ay + ah), all_screens=True)
            for k, (x, y, w, h) in self._boxes_px.items():
                if w > 8 and h > 8 and x >= 0 and y >= 0 and x + w <= img.width and y + h <= img.height:
                    self._snap[k] = img.crop((x, y, x + w, y + h))
        except Exception:  # noqa: BLE001 - no Pillow, or the screen can't be read: plain cards instead
            self._PIL = False
            self._snap = {}

    def _bp_fit(self):
        """Crop each snapshot to the smaller of where the box is and where it's going, so content never spills."""
        if not self._snap or not self._PIL:
            return
        for k, it in self._bp_items.items():
            src = self._snap.get(k)
            if src is None or "img" not in it:
                continue
            cur, tgt = self._bp_cur.get(k), self._bp_tgt.get(k, self._bp_cur.get(k))
            w = int(min(cur[2], tgt[2], src.width)) - 1     # minus its own border: the card outline draws that
            h = int(min(cur[3], tgt[3], src.height)) - 1
            if (w, h) == it.get("crop"):
                continue
            it["crop"] = (w, h)
            if w < 12 or h < 12:
                self.bp.itemconfigure(it["img"], image="")
                it["photo"] = None
                continue
            it["photo"] = self._PIL.PhotoImage(src.crop((0, 0, w, h)), master=self.bp)
            self.bp.itemconfigure(it["img"], image=it["photo"])

    def _bp_open(self, focus: str | None = None):
        c = self.bp
        self._set_hover(None)
        self._snapshot()
        c.delete("all")
        c.configure(bg=PAL["bg"])
        self._bp_items, self._bp_gone = {}, set()
        m = self._m or self._metrics()
        # faint grid so it reads as "layout mode"
        gcol = mix(PAL["bg"], PAL["accent"], 0.07)
        for i in (range(0, COLS + 1, 4) if UI.get("anim_grid", True) else ()):
            x = int(round(i * m["cp"])) - int(self.ox)
            c.create_line(x, 0, x, m["vh"], fill=gcol)
        for j in (range(0, max(ROWS, grid_rows(self.rects) if self.rects else ROWS) + 1, 5) if UI.get("anim_grid", True)
                  else ()):
            y = int(round(j * m["rp"])) - int(self.oy)
            c.create_line(0, y, m["vw"], y, fill=gcol)
        self._bp_cur = {k: [float(v) for v in b] for k, b in self._boxes_px.items()}
        self._bp_tgt = {k: list(v) for k, v in self._bp_cur.items()}
        for k in self._bp_cur:
            self._bp_items[k] = self._bp_make(k, k == focus)
        if focus in self._bp_items:                  # the box you're holding sits on top
            for item in [v for kk, v in self._bp_items[focus].items() if isinstance(v, int) and kk != "focus"]:
                c.tag_raise(item)
        self._bp_fit()
        self._ghost = None
        self._bp_on, self._bp_closing, self._bp_dirty = True, False, True
        self._bp_draw()
        c.place(x=0, y=0, relwidth=1, relheight=1)
        tk.Misc.lift(c)
        c.update_idletasks()
        self._hires(True)
        self._tick_on()

    def _bp_draw(self):
        c = self.bp
        for k, geo in self._bp_cur.items():
            it = self._bp_items.get(k)
            if not it:
                continue
            x, y, w, h = (int(round(v)) for v in geo)
            if it.get("last") == (x, y, w, h):     # untouched boxes cost nothing: no repaint at all
                continue
            it["last"] = (x, y, w, h)
            x1, y1 = x + w, y + h
            c.coords(it["body"], x, y, x1 - 1, y1 - 1)
            if "img" in it:
                c.coords(it["img"], x, y)
            else:
                hh = min(33, max(0, h - 2))
                c.coords(it["hdr"], x + 1, y + 1, x1 - 1, y + hh)
                c.coords(it["rule"], x + 1, y + hh, x1 - 1, y + hh)
                c.coords(it["title"], x + 12, y + hh / 2 + 1)
            if "ring" in it:
                c.coords(it["ring"], x + 1, y + 1, x1 - 1, y1 - 1)
                txt = f"{w} × {h}" if w > 120 and h > 70 and UI.get("anim_sizes", True) else ""
                if it.get("txt") != txt:
                    it["txt"] = txt
                    c.itemconfigure(it["size"], text=txt)
                c.coords(it["size"], x1 - 14, y1 - 10)
                bb = c.bbox(it["size"]) if txt else None
                c.coords(it["pill"], *((bb[0] - 8, bb[1] - 3, bb[2] + 8, bb[3] + 3) if bb else (0, 0, 0, 0)))
        if self._ghost:
            g = self._ghost
            c.coords(g["text"], g["x"] + 30, g["y"] + 20)
            bb = c.bbox(g["text"])
            if bb:
                c.coords(g["pill"], bb[0] - 12, bb[1] - 7, bb[2] + 12, bb[3] + 7)
            c.tag_raise(g["pill"])
            c.tag_raise(g["text"])

    @staticmethod
    def _fms() -> float:
        try:
            return 1000.0 / max(30, int(UI.get("fps", 240)))
        except (TypeError, ValueError):
            return 1000.0 / 240

    def _tick_on(self):
        if self._tick_job is None:
            self._last_t = time.perf_counter()
            self._tick_job = self.area.after(max(1, int(self._fms())), self._tick)

    def _tick(self):
        self._tick_job = None
        if not self._bp_on:
            return
        now = time.perf_counter()
        dt = min(0.05, now - self._last_t)
        self._last_t = now
        ease = max(0.004, float(UI.get("anim_speed", 30)) / 1000.0) if anim_on() else 0.0005
        a = 1.0 - math.exp(-dt / ease)
        moving = False
        for k, cur in self._bp_cur.items():
            tgt = self._bp_tgt.get(k, cur)
            for i in range(4):
                d = tgt[i] - cur[i]
                if abs(d) > 0.3:
                    cur[i] += d * a
                    moving = True
                elif d:
                    cur[i] = tgt[i]
                    moving = True
        if moving or self._bp_dirty:
            self._bp_dirty = False
            self._bp_draw()
        if self._bp_closing and not moving:
            self._bp_close()
            return
        try:
            self.bp.update_idletasks()             # paint this frame now, then sleep only what's left of it
        except tk.TclError:
            return
        spent = (time.perf_counter() - now) * 1000.0
        self._tick_job = self.area.after(max(1, int(self._fms() - spent)), self._tick)

    def _bp_close(self):
        self._bp_on = self._bp_closing = False
        if self._tick_job:
            try:
                self.area.after_cancel(self._tick_job)
            except (tk.TclError, ValueError):
                pass
            self._tick_job = None
        try:
            self.area.update_idletasks()          # everything underneath is fully drawn before we lift off
        except tk.TclError:
            pass
        self.bp.place_forget()
        self.bp.delete("all")
        self._bp_items, self._ghost, self._snap = {}, None, {}
        self._hires(False)

    def _commit(self, R: dict):
        """Apply `R` to the real sections (underneath the blueprint), then glide the blueprint onto it."""
        self.rects = R
        self.layout()
        tgt = {k: [float(v) for v in b] for k, b in self._boxes_px.items()}
        for k, b in tgt.items():
            if k not in self._bp_cur:           # a box that appears grows out of its own centre
                cx, cy = b[0] + b[2] / 2, b[1] + b[3] / 2
                self._bp_cur[k] = [cx - 30, cy - 20, 60.0, 40.0]
                self._bp_items[k] = self._bp_make(k, True)
        for k, cur in self._bp_cur.items():
            if k not in tgt:                    # one that goes away folds into its centre
                tgt[k] = [cur[0] + cur[2] / 2, cur[1] + cur[3] / 2, 0.0, 0.0]
        if self._ghost:
            self.bp.delete(self._ghost["pill"], self._ghost["text"])
            self._ghost = None
        self._bp_tgt = tgt
        self._bp_fit()
        self._bp_closing = True
        self._bp_dirty = True
        self._tick_on()

    def _morph(self, R: dict):
        """Switch to another arrangement with an animated transition."""
        try:
            ok = bool(self._boxes_px) and self.area.winfo_viewable() and not self.rs and not self.drag \
                and anim_on("anim_layout")
        except tk.TclError:
            ok = False
        if not ok:
            self.rects = R
            self.layout()
            return
        if not self._bp_on:
            self._bp_open()
        self._commit(R)

    def _cancel(self, _e=None):
        s, d = self.rs, self.drag
        self.rs = self.drag = None
        if s:
            self._commit(s["rects"])
        elif d and d.get("on"):
            self._commit(d["rects"])

    # -- hovering the gaps: which edge would a drag grab? -------------------------------------------- #
    INNER = 9            # px inside a box's border that also grab its edge (on top of the whole gap)

    def _edge_at(self, x: int, y: int):
        best = None
        T, C, I = GAP + 2, self.CORNER, self.INNER
        for k, (X, Y, W, H) in self._boxes_px.items():
            if not (X - T <= x < X + W + T and Y - T <= y < Y + H + T):
                continue
            if X + I <= x < X + W - I and Y + I <= y < Y + H - I:
                continue
            # inside the band along the border counts as that edge too
            ex = -1 if x < X + I else 1 if x >= X + W - I else 0
            ey = -1 if y < Y + I else 1 if y >= Y + H - I else 0
            if ex and not ey:
                ey = -1 if y < Y + C else 1 if y >= Y + H - C else 0
            elif ey and not ex:
                ex = -1 if x < X + C else 1 if x >= X + W - C else 0
            dx = abs(x - X) if ex < 0 else abs(x - (X + W)) if ex > 0 else 0
            dy = abs(y - Y) if ey < 0 else abs(y - (Y + H)) if ey > 0 else 0
            d = max(dx, dy)
            if best is None or d < best[0]:
                best = (d, k, ex, ey)
        return best[1:] if best else None

    def _set_hover(self, hit):
        if hit == self._hover:
            return
        self._hover = hit
        cur = self.CURSORS.get((hit[1], hit[2]), "") if hit else ""
        for w in {self.area, getattr(self, "_cur_w", None)}:
            if w is None:
                continue
            try:
                w.configure(cursor=cur if (w is self.area or hit) else "")
            except tk.TclError:
                pass
        if not hit:
            self._cur_w = None
        self._show_guides(hit)

    def _show_guides(self, hit):
        for gw in self._guides:
            gw.place_forget()
        if not hit or hit[0] not in self._boxes_px:
            return
        k, ex, ey = hit
        X, Y, W, H = self._boxes_px[k]
        g = GAP // 2
        bars = []
        if ex:
            bars.append((X + W + g - 1 if ex > 0 else X - g - 1, Y, 3, H))
        if ey:
            bars.append((X, Y + H + g - 1 if ey > 0 else Y - g - 1, W, 3))
        for gw, (bx, by, bw, bh) in zip(self._guides, bars):
            gw.configure(bg=PAL["accent"])
            gw.place(x=bx, y=by, width=bw, height=bh)
            tk.Misc.lift(gw)

    def _area_motion(self, e):
        if self.rs or self.drag or self._bp_on:
            return
        self._set_hover(self._edge_at(e.x, e.y))

    # -- resizing a box by the gap around it -------------------------------------------------------- #
    def _mins(self, m: dict):
        mw = {k: max(4, int(math.ceil((SECTION_MIN_W + GAP) / m["cp"]))) for k in self.sections}
        mh = {k: max(3, int(math.ceil((SECTION_MIN_H.get(k, 90) * ui_scale() + GAP) / m["rp"]))) for k in self.sections}
        return mw, mh

    def _local(self, e):
        return e.x_root - self.area.winfo_rootx(), e.y_root - self.area.winfo_rooty()

    def edge_motion(self, e) -> bool:
        """Pointer moving over a section's own frame: near its border it shows the resize cursor."""
        if self.rs:
            self._rs_move(e)
            return True
        if self.drag or self._bp_on:
            return bool(self.drag)
        hit = self._edge_at(*self._local(e))
        if hit and getattr(self, "_cur_w", None) is not e.widget:
            old = getattr(self, "_cur_w", None)
            if old is not None:
                try:
                    old.configure(cursor="")
                except tk.TclError:
                    pass
            self._cur_w = e.widget
            self._hover = None
        self._set_hover(hit)
        return bool(hit)

    def edge_press(self, e) -> bool:
        if self.drag or self.rs:
            return False
        hit = self._edge_at(*self._local(e))
        if not hit:
            return False
        if self._bp_on:
            self._bp_close()
        k, ex, ey = hit
        m = self._m or self._metrics()
        self.rs = {"key": k, "ex": ex, "ey": ey, "x": e.x_root, "y": e.y_root, "m": m,
                   "rects": {kk: list(v) for kk, v in self.rects.items()}, "target": None, "duv": None}
        self.rs["target"] = self.rs["rects"]
        self._bp_open(focus=k)
        return True

    def edge_release(self, e) -> bool:
        if self.rs:
            self._rs_end(e)
            return True
        return False

    def sense(self, widget, header: bool = False):
        """Lets a section's frame (not the controls inside it) grab the box's edge near its border."""
        widget.bind("<Motion>", lambda e: self.edge_motion(e) and None, add="+")
        widget.bind("<Leave>", lambda e: self.rs or self._set_hover(None), add="+")
        if header:
            return                      # the title bar's own press / drag / release handle this
        widget.bind("<ButtonPress-1>", lambda e: "break" if self.edge_press(e) else None, add="+")
        widget.bind("<B1-Motion>", lambda e: "break" if self.rs and self.edge_motion(e) else None, add="+")
        widget.bind("<ButtonRelease-1>", lambda e: "break" if self.edge_release(e) else None, add="+")

    def _area_press(self, e):
        if self.drag or self.rs:
            return
        if self._bp_on:
            self._bp_close()
        hit = self._edge_at(e.x, e.y)
        if not hit:
            return
        k, ex, ey = hit
        m = self._m or self._metrics()
        self.rs = {"key": k, "ex": ex, "ey": ey, "x": e.x_root, "y": e.y_root, "m": m,
                   "rects": {kk: list(v) for kk, v in self.rects.items()}, "target": None, "duv": None}
        self.rs["target"] = self.rs["rects"]
        self._bp_open(focus=k)

    def _rs_move(self, e):
        s = self.rs
        if not s:
            return
        m = s["m"]
        du = int(round((e.x_root - s["x"]) / m["cp"]))
        dv = int(round((e.y_root - s["y"]) / m["rp"]))
        if (du, dv) == s["duv"]:
            return
        s["duv"] = (du, dv)
        mw, mh = self._mins(m)
        if not UI.get("auto_size", False):
            # only the box you hold changes: everything around it keeps its size, so it stops at them
            R0 = s["rects"]
            mw = {k: (v if k == s["key"] or k not in R0 else max(v, R0[k][2])) for k, v in mw.items()}
            mh = {k: (v if k == s["key"] or k not in R0 else max(v, R0[k][3])) for k, v in mh.items()}
        s["target"] = grid_resize(s["rects"], s["key"], s["ex"], s["ey"], du, dv, mw, mh)
        self._bp_tgt = {k: [float(v) for v in b] for k, b in self._boxes(s["target"], m).items()}
        self._bp_fit()
        self._tick_on()

    def _rs_end(self, _e):
        s, self.rs = self.rs, None
        if not s:
            return
        R = {k: list(v) for k, v in s["target"].items()}
        self._commit(grid_fill_holes(R, exclude=s["key"]) if UI.get("auto_size", False) else R)
        self.app.save_dock()

    # -- dragging a section by its title bar --------------------------------------------------------- #
    def bind_handle(self, widget, key: str):
        widget.bind("<ButtonPress-1>", lambda e, k=key: self._start(k, e))
        widget.bind("<B1-Motion>", self._move)
        widget.bind("<ButtonRelease-1>", self._end)

    def _start(self, key, e):
        if self.rs:
            return
        if self._bp_on:
            self._bp_close()
        self.drag = {"key": key, "x": e.x_root, "y": e.y_root, "on": False, "hit": None, "res": None}

    def _hit(self, px, py, key, boxes, aw, ah):
        """(kind, target, side) of the drop spot under the pointer (area coordinates), or None."""
        if not (0 <= px <= aw and 0 <= py <= ah):
            return None
        edge = 30
        if px < edge:
            return ("root", None, "left")
        if aw - px < edge:
            return ("root", None, "right")
        if py < edge:
            return ("root", None, "top")
        if ah - py < edge:
            return ("root", None, "bottom")
        for k, (x, y, w, h) in boxes.items():
            if not (x <= px < x + w and y <= py < y + h):
                continue
            if k == key:
                return None
            rx, ry = (px - x) / max(1, w), (py - y) / max(1, h)
            if 0.28 < rx < 0.72 and 0.28 < ry < 0.72:
                return ("swap", k, "")
            dist = {"left": rx, "right": 1 - rx, "top": ry, "bottom": 1 - ry}
            return ("edge", k, min(dist, key=dist.get))
        m = self._m or self._metrics()
        cx, cy = int((px + self.ox) / m["cp"]), int((py + self.oy) / m["rp"])
        if grid_place_free(self.drag["rects"] if self.drag and "rects" in self.drag else self.rects, key, cx, cy):
            return ("empty", None, (cx, cy))
        return None

    def _hit_text(self, hit) -> str:
        if not hit:
            return "drop it on another box"
        kind, t, side = hit
        if kind == "empty":
            return "into the empty space"
        if kind == "swap":
            return "swap with  " + self.app.section_title(t)
        if kind == "edge":
            return {"left": "left of  ", "right": "right of  ", "top": "above  ", "bottom": "below  "}[side] + \
                self.app.section_title(t)
        return f"full {'height' if side in ('left', 'right') else 'width'} along the {side} edge"

    def _move(self, e):
        d = self.drag
        if not d:
            return
        if not d["on"]:
            if abs(e.x_root - d["x"]) + abs(e.y_root - d["y"]) < 6:
                return
            d["on"] = True
            d["rects"] = {k: list(v) for k, v in self.rects.items()}
            d["boxes"] = dict(self._boxes_px)
            self._bp_open(focus=d["key"])
            c = self.bp
            f = "Segoe UI" if IS_WINDOWS else "TkDefaultFont"
            self._ghost = {"x": 0, "y": 0,
                           "pill": c.create_rectangle(0, 0, 1, 1, fill=PAL["accent"], outline=""),
                           "text": c.create_text(0, 0, anchor="nw", fill=PAL["accent_ink"], font=(f, 10, "bold"),
                                                 text="")}
        px, py = e.x_root - self.area.winfo_rootx(), e.y_root - self.area.winfo_rooty()
        hit = self._hit(px, py, d["key"], d["boxes"], self.area.winfo_width(), self.area.winfo_height())
        g = self._ghost
        if g:
            g["x"], g["y"] = px, py
            if hit != d["hit"] or d["res"] is None:
                self.bp.itemconfigure(g["text"], text="✥  " + self.app.section_title(d["key"]) + "   →   " +
                                      self._hit_text(hit))
        if hit != d["hit"] or d["res"] is None:
            d["hit"] = hit
            R = d["rects"]
            if hit:
                kind, t, side = hit
                if kind == "empty":
                    R = grid_place_free(R, d["key"], *side) or R
                else:
                    R = grid_swap(R, d["key"], t) if kind == "swap" else grid_insert(R, d["key"], t, side) \
                        if kind == "edge" else grid_insert_root(R, d["key"], side)
            d["res"] = R
            self._bp_tgt = {k: [float(v) for v in b] for k, b in self._boxes(R, self._metrics(R)).items()}
            self._bp_fit()
        self._bp_dirty = True
        self._tick_on()

    def _end(self, _e):
        d, self.drag = self.drag, None
        if not d or not d["on"]:
            return
        self._commit(d["res"] if d["hit"] and d["res"] else d["rects"])
        if d["hit"]:
            self.app.save_dock()


# --------------------------------------------------------------------------- #
#  Download graphs: speed and amount downloaded, drawn in the current theme's colours
# --------------------------------------------------------------------------- #
GRAPH_MODES = ["Speed", "Data downloaded", "Both - one graph", "Both - two graphs"]
GRAPH_STYLES = ["Glow area", "Smooth curve", "Gradient area", "Line", "Neon line", "Steps", "Skyline", "Bars",
                "Heat bars", "Lollipops", "Dots"]
GRAPH_DIPS = ["Smoothed", "Raw (show every dip)", "Smoothed + raw dips"]
GRAPH_RANGES = {"Last 30 sec": 30, "Last 1 min": 60, "Last 2 min": 120, "Last 5 min": 300, "Last 10 min": 600,
                "Last 15 min": 900, "Last 30 min": 1800, "Last hour": 3600, "Last 2 hours": 7200,
                "Last 6 hours": 21600, "Last 12 hours": 43200, "Last 24 hours": 86400, "Whole run": 0}
GRAPH_RATES = {"Live · 0.25 s": 250, "Fast · 0.5 s": 500, "Normal · 1 s": 1000, "Relaxed · 2 s": 2000,
               "Slow · 5 s": 5000}
CUSTOM = "Custom..."
GRAPH_DEFAULT = {"mode": GRAPH_MODES[2], "style": GRAPH_STYLES[0], "dips": GRAPH_DIPS[2], "range": "Last 10 min",
                 "rate": "Normal · 1 s", "theme": "app", "custom_range": 2700, "rate_ms": 1000}
DIP_FLOOR = 100 * 1024       # a second slower than this counts as a "dip" for the no-dips average
SMOOTH_SECS = 5.0

# Graph colour themes: every one is dark. QD-OLED ones sit on true black (#000) so the pixels switch off and
# the lines glow; "Dark" ones use a deep tinted background. s = speed line, d = data-downloaded line.
GRAPH_THEMES: dict = {
    "qd_cyber": dict(n="Cyber Cyan", g="QD-OLED", bg="#000000", s="#00e5ff", d="#ff2bd6"),
    "qd_acid": dict(n="Acid Rain", g="QD-OLED", bg="#000000", s="#b4ff39", d="#a066ff"),
    "qd_solar": dict(n="Solar Flare", g="QD-OLED", bg="#000000", s="#ffe600", d="#00d9ff"),
    "qd_blood": dict(n="Blood Moon", g="QD-OLED", bg="#000000", s="#ff2a36", d="#ffb000"),
    "qd_ultra": dict(n="Ultraviolet", g="QD-OLED", bg="#000000", s="#a066ff", d="#00ffc8"),
    "qd_synth": dict(n="Synthwave", g="QD-OLED", bg="#000000", s="#ff2e93", d="#00d9ff"),
    "qd_matrix": dict(n="Matrix", g="QD-OLED", bg="#000000", s="#39ff7a", d="#c8f7d2"),
    "qd_ember": dict(n="Ember", g="QD-OLED", bg="#000000", s="#ff7b1c", d="#ffd36e"),
    "qd_aurora": dict(n="Aurora", g="QD-OLED", bg="#000000", s="#00ffa3", d="#7a5cff"),
    "qd_plasma": dict(n="Plasma", g="QD-OLED", bg="#000000", s="#ff3df5", d="#ffb000"),
    "qd_cobalt": dict(n="Cobalt", g="QD-OLED", bg="#000000", s="#3d7bff", d="#00e5ff"),
    "qd_toxic": dict(n="Toxic", g="QD-OLED", bg="#000000", s="#c6ff00", d="#ff00a8"),
    "qd_ice": dict(n="Glacier", g="QD-OLED", bg="#000000", s="#7dd3fc", d="#f5f5f5"),
    "qd_rose": dict(n="Rose Gold", g="QD-OLED", bg="#000000", s="#f3b9aa", d="#e8bf45"),
    "qd_lava": dict(n="Lava Lamp", g="QD-OLED", bg="#000000", s="#ff4d00", d="#ff1f8e"),
    "qd_mono": dict(n="Mono White", g="QD-OLED", bg="#000000", s="#f2f2f2", d="#7d7d7d"),
    "dk_nord": dict(n="Nord Night", g="Dark", bg="#0e1117", s="#88c0d0", d="#b48ead"),
    "dk_dracula": dict(n="Dracula", g="Dark", bg="#13121b", s="#bd93f9", d="#50fa7b"),
    "dk_tokyo": dict(n="Tokyo Night", g="Dark", bg="#0b0d16", s="#7aa2f7", d="#f7768e"),
    "dk_gruv": dict(n="Gruvbox", g="Dark", bg="#110f0e", s="#fe8019", d="#b8bb26"),
    "dk_mocha": dict(n="Catppuccin", g="Dark", bg="#0f0f17", s="#cba6f7", d="#a6e3a1"),
    "dk_ocean": dict(n="Deep Ocean", g="Dark", bg="#020d12", s="#2dd4bf", d="#60a5fa"),
    "dk_wine": dict(n="Wine Cellar", g="Dark", bg="#0d0508", s="#f43f5e", d="#fbbf24"),
}


def _nice_max(v: float) -> float:
    if v <= 0:
        return 1.0
    p = 10 ** math.floor(math.log10(v))
    for m in (1, 1.5, 2, 2.5, 3, 4, 5, 6, 8, 10):
        if v <= m * p:
            return m * p
    return 10 * p


def _fmt_rate_axis(bps: float) -> str:
    mb = 1024 * 1024
    if bps >= mb:
        v = bps / mb
        return f"{v:.0f} MB/s" if v >= 10 or abs(v - round(v)) < 0.05 else f"{v:.1f} MB/s"
    return f"{bps / 1024:.0f} KB/s"


def _fmt_rate_live(bps: float) -> str:
    mb = 1024 * 1024
    return f"{bps / mb:.2f} MB/s" if bps >= mb else f"{bps / 1024:.0f} KB/s"


def _fmt_ago(sec: float) -> str:
    sec = max(0, int(round(sec)))
    if sec == 0:
        return "now"
    return "-" + (f"{sec}s" if sec < 60 else f"{sec // 60}m{sec % 60:02d}s" if sec < 3600 else f"{sec // 3600}h{sec % 3600 // 60:02d}m")


def _fmt_span(sec: float) -> str:
    sec = float(sec)
    if sec < 1:
        return f"{int(round(sec * 1000))} ms"
    if sec < 60:
        return f"{sec:g} s"
    if sec < 3600:
        return f"{sec / 60:g} min"
    return f"{sec / 3600:g} h"


def _complement(col: str) -> str:
    r, g, b = _rgb(col)
    h, s, v = colorsys.rgb_to_hsv(r / 255, g / 255, b / 255)
    h = (h + 0.42) % 1.0
    r2, g2, b2 = colorsys.hsv_to_rgb(h, max(0.55, s), max(0.8, v))
    return _hex(int(r2 * 255), int(g2 * 255), int(b2 * 255))


def ask_amount(parent, title: str, prompt: str, units: list, value, unit: str):
    """Small themed dialog: a number and a unit (e.g. 750 + ms). Returns (number, unit) or None."""
    win = tk.Toplevel(parent)
    win.withdraw()
    win.title(title)
    win.resizable(False, False)
    win.transient(parent.winfo_toplevel())
    themed(win, bg="panel")
    dark_title_bar(win)
    body = ttk.Frame(win, padding=(20, 16, 20, 16))
    body.pack(fill="both", expand=True)
    ttk.Label(body, text=title, style="Head.TLabel").pack(anchor="w")
    ttk.Label(body, text=prompt, style="Muted.TLabel", justify="left").pack(anchor="w", pady=(4, 10))
    row = ttk.Frame(body)
    row.pack(fill="x")
    var = tk.StringVar(value=f"{value:g}" if isinstance(value, (int, float)) else str(value))
    ent = ttk.Entry(row, textvariable=var, width=10, font=("Segoe UI", 12) if IS_WINDOWS else None)
    ent.pack(side="left", ipady=2)
    seg = Segmented(row, [(u, u) for u in units], unit, style_bg="TFrame")
    seg.pack(side="left", padx=(10, 0))
    note = tk.StringVar()
    ttk.Label(body, textvariable=note, style="Err.TLabel").pack(anchor="w", pady=(6, 0))
    out: dict = {}

    def ok(*_):
        try:
            v = float(var.get().replace(",", "."))
            if v <= 0:
                raise ValueError
        except ValueError:
            note.set("Type a number bigger than 0.")
            return
        out["v"] = (v, seg.value)
        win.destroy()
    bar = ttk.Frame(body)
    bar.pack(fill="x", pady=(12, 0))
    ttk.Button(bar, text="OK", style="Accent.TButton", command=ok).pack(side="right")
    ttk.Button(bar, text="Cancel", command=win.destroy).pack(side="right", padx=(0, 8))
    win.bind("<Return>", ok)
    win.bind("<Escape>", lambda _e: win.destroy())
    win.update_idletasks()
    r = parent.winfo_toplevel()
    win.geometry(f"+{r.winfo_rootx() + max(0, (r.winfo_width() - win.winfo_reqwidth()) // 2)}"
                 f"+{r.winfo_rooty() + max(0, (r.winfo_height() - win.winfo_reqheight()) // 3)}")
    win.deiconify()
    fade_in(win)
    ent.focus_set()
    ent.select_range(0, "end")
    try:
        win.grab_set()
    except tk.TclError:
        pass
    win.wait_window()
    return out.get("v")


class GraphPanel(tk.Frame):
    """
    Samples come in up to four times a second (as fast as the update rate asks for). Each sample is the real
    throughput since the last one (bytes that landed / seconds), so short drops to ~0 show up honestly under
    "raw"; "smoothed" is a 5 s rolling average that hides them. The tiles on top use the whole run.
    """

    def __init__(self, master, settings: dict, on_change):
        super().__init__(master, bd=0, highlightthickness=0)
        themed(self, bg="panel")
        self.cfg = dict(GRAPH_DEFAULT)
        for k, v in (settings or {}).items():
            if k in self.cfg and isinstance(v, type(GRAPH_DEFAULT[k])):
                self.cfg[k] = v
        for k, allowed in (("mode", GRAPH_MODES), ("style", GRAPH_STYLES), ("dips", GRAPH_DIPS),
                           ("range", list(GRAPH_RANGES) + ["Custom"]), ("rate", list(GRAPH_RATES) + ["Custom"])):
            if self.cfg[k] not in allowed:
                self.cfg[k] = GRAPH_DEFAULT[k]
        if self.cfg["theme"] != "app" and self.cfg["theme"] not in GRAPH_THEMES:
            self.cfg["theme"] = "app"
        self.cfg["custom_range"] = max(10, int(self.cfg["custom_range"]))
        self.cfg["rate_ms"] = max(100, int(self.cfg["rate_ms"]))
        self.on_change = on_change
        self.samples: list[list] = []   # [t, raw bps, smoothed bps, cumulative bytes, paused]
        self._last_t: float | None = None
        self._last_key = None
        self._last_d = 0
        self._t0: float | None = None
        self._cum = 0
        self._hover: list = []
        self._job = None
        self._drawn = 0.0
        self._gal = None

        tiles = ttk.Frame(self)
        tiles.pack(fill="x")
        self.tile_vars: dict[str, tk.StringVar] = {}
        tl = []
        for key, cap in (("now", "Now"), ("avg", "Average"), ("avg2", "Avg, no dips"), ("peak", "Peak"),
                         ("total", "Downloaded")):
            f = ttk.Frame(tiles)
            v = tk.StringVar(value="-")
            self.tile_vars[key] = v
            ttk.Label(f, text=cap, style="Muted.TLabel").pack(side="left", padx=(0, 5))
            ttk.Label(f, textvariable=v, style="Eta.TLabel").pack(side="left", padx=(0, 12))
            tl.append(f)
        flow(tiles, tl, gap=4)
        ctl = ttk.Frame(self)
        ctl.pack(fill="x", pady=(4, 2))
        self.vars: dict = {}
        self.boxes: dict = {}
        pieces = []
        for key, label, values, width in (("mode", "Show", GRAPH_MODES, 18), ("style", "Style", GRAPH_STYLES, 13),
                                          ("dips", "Dips", GRAPH_DIPS, 19),
                                          ("range", "Range", self._range_values(), 16),
                                          ("rate", "Update", self._rate_values(), 14)):
            f = ttk.Frame(ctl)
            ttk.Label(f, text=label, style="Muted.TLabel").pack(side="left", padx=(0, 4))
            var = tk.StringVar(value=self._shown(key))
            cb = ttk.Combobox(f, textvariable=var, values=values, state="readonly", width=width)
            cb.pack(side="left", padx=(0, 6))
            cb.bind("<<ComboboxSelected>>", lambda _e, k=key: self._changed(k))
            self.vars[key], self.boxes[key] = var, cb
            pieces.append(f)
        cf = ttk.Frame(ctl)
        self.col_btn = ttk.Button(cf, text="◐  " + self._theme_name(), style="Toggle.TButton",
                                  command=self.open_colors)
        self.col_btn.pack(side="left")
        pieces.append(cf)
        flow(ctl, pieces, gap=4)
        self.cv = tk.Canvas(self, highlightthickness=0, bd=0, height=70)
        self.cv.configure(bg=self.gp()["bg"])
        self.cv.pack(fill="both", expand=True, pady=(2, 0))
        self.cv.bind("<Configure>", lambda _e: self.schedule(now=True))
        self.cv.bind("<Motion>", self._motion)
        self.cv.bind("<Leave>", lambda _e: self.cv.delete("hv"))
        THEME_HOOKS.append(self.redraw)

    # -- settings ---------------------------------------------------------------------------- #
    def gp(self) -> dict:
        """Colours for the graph: its own theme, or the app's."""
        th = GRAPH_THEMES.get(self.cfg.get("theme"))
        if th:
            bg, s, d = th["bg"], th["s"], th["d"]
        else:
            bg, s, d = PAL["well"], PAL["accent"], _complement(PAL["accent"])
        return {"bg": bg, "s": s, "d": d, "grid": mix(bg, mix(s, "#9a9a9a", 0.6), 0.20),
                "text": mix(bg, "#ffffff", 0.80), "muted": mix(bg, "#ffffff", 0.48),
                "tip": mix(bg, s, 0.10), "ink": "#0b0b0b" if luma(s) > 0.5 else "#ffffff",
                "ink_d": "#0b0b0b" if luma(d) > 0.5 else "#ffffff"}

    def _theme_name(self) -> str:
        th = GRAPH_THEMES.get(self.cfg.get("theme"))
        return ("Colour: " + th["n"]) if th else "Colour: match app"

    def _range_values(self):
        vals = list(GRAPH_RANGES)
        if self.cfg["range"] == "Custom":
            vals.append(self._shown("range"))
        return vals + [CUSTOM]

    def _rate_values(self):
        vals = list(GRAPH_RATES)
        if self.cfg["rate"] == "Custom":
            vals.append(self._shown("rate"))
        return vals + [CUSTOM]

    def _shown(self, key) -> str:
        if key == "range" and self.cfg["range"] == "Custom":
            return f"Custom · {_fmt_span(self.cfg['custom_range'])}"
        if key == "rate" and self.cfg["rate"] == "Custom":
            return f"Custom · {_fmt_span(self.cfg['rate_ms'] / 1000)}"
        return self.cfg[key]

    def span(self) -> float:
        if self.cfg["range"] == "Custom":
            return float(self.cfg["custom_range"])
        return float(GRAPH_RANGES.get(self.cfg["range"], 0))

    def rate_ms(self) -> int:
        if self.cfg["rate"] == "Custom":
            return max(100, int(self.cfg["rate_ms"]))
        return GRAPH_RATES.get(self.cfg["rate"], 1000)

    def sample_interval(self) -> float:
        """How often the download monitor should measure, for this update rate (0.25 s .. 1 s)."""
        return max(0.25, min(1.0, self.rate_ms() / 1000.0))

    def _changed(self, key):
        val = self.vars[key].get()
        if key in ("range", "rate") and val.startswith("Custom"):
            if val == CUSTOM:
                if key == "range":
                    cur = self.cfg["custom_range"]
                    u = "hours" if cur >= 3600 and cur % 3600 == 0 else "minutes" if cur >= 60 else "seconds"
                    got = ask_amount(self, "Custom range", "How far back should the graph show?",
                                     ["seconds", "minutes", "hours"], cur / {"seconds": 1, "minutes": 60, "hours": 3600}[u], u)
                    if got:
                        secs = got[0] * {"seconds": 1, "minutes": 60, "hours": 3600}[got[1]]
                        self.cfg["custom_range"] = int(max(10, min(7 * 86400, secs)))
                        self.cfg["range"] = "Custom"
                else:
                    cur = self.cfg["rate_ms"]
                    u = "minutes" if cur >= 60000 else "seconds" if cur >= 1000 else "ms"
                    got = ask_amount(self, "Custom update rate", "How often should the graph redraw?\n"
                                     "(It measures at most 4 times a second; slower rates just redraw less often.)",
                                     ["ms", "seconds", "minutes"], cur / {"ms": 1, "seconds": 1000, "minutes": 60000}[u], u)
                    if got:
                        ms = got[0] * {"ms": 1, "seconds": 1000, "minutes": 60000}[got[1]]
                        self.cfg["rate_ms"] = int(max(100, min(3600000, ms)))
                        self.cfg["rate"] = "Custom"
        else:
            self.cfg[key] = val
        for k in ("range", "rate"):
            self.boxes[k].configure(values=self._range_values() if k == "range" else self._rate_values())
            self.vars[k].set(self._shown(k))
        self.on_change(dict(self.cfg))
        self.redraw()

    def set_theme(self, tid: str):
        self.cfg["theme"] = tid
        self.col_btn.configure(text="◐  " + self._theme_name())
        self.on_change(dict(self.cfg))
        self.redraw()

    def open_colors(self):
        """A gallery of graph colour themes, each card a tiny live preview. Click one to use it."""
        if self._gal is not None:
            try:
                self._gal.lift()
                return
            except tk.TclError:
                self._gal = None
        win = tk.Toplevel(self)
        self._gal = win
        win.withdraw()
        win.title("Graph colours")
        win.transient(self.winfo_toplevel())
        themed(win, bg="panel")
        dark_title_bar(win)
        win.protocol("WM_DELETE_WINDOW", lambda: (setattr(self, "_gal", None), win.destroy()))
        win.bind("<Escape>", lambda _e: (setattr(self, "_gal", None), win.destroy()))
        outer = ttk.Frame(win, padding=(18, 14, 18, 14))
        outer.pack(fill="both", expand=True)
        ttk.Label(outer, text="GRAPH COLOURS", style="SetKicker.TLabel").pack(anchor="w")
        ttk.Label(outer, text="Dark and QD-OLED themes for the graph", style="SetTitle.TLabel").pack(anchor="w")
        ttk.Label(outer, text="QD-OLED themes sit on true black, so those pixels switch off and the lines glow. "
                              "Click a card to use it; the graph changes right away.",
                  style="Muted.TLabel").pack(anchor="w", pady=(2, 8))
        cards: dict = {}

        def mark():
            for tid, cv in cards.items():
                on = tid == self.cfg["theme"]
                cv.configure(highlightbackground=PAL["accent"] if on else PAL["border"], highlightthickness=2 if on else 1)

        def card(parent, tid, th, r, c):
            bg, s, d = (th["bg"], th["s"], th["d"]) if th else (PAL["well"], PAL["accent"], _complement(PAL["accent"]))
            cv = tk.Canvas(parent, width=186, height=92, bg=bg, highlightthickness=1, bd=0, cursor="hand2")
            cv.grid(row=r, column=c, padx=5, pady=5)
            ys = [62, 48, 54, 34, 40, 26, 44, 30, 22, 36]
            xs = [10 + i * 18.5 for i in range(len(ys))]
            for b in range(8):            # little gradient area
                top = 20 + 52 * b / 8
                pts = []
                for x, y in zip(xs, ys):
                    pts += [x, max(y, top)]
                pts += [xs[-1], 72, xs[0], 72]
                cv.create_polygon(*pts, fill=mix(bg, s, 0.05 + 0.30 * b / 7), outline="")
            line = [v for p in zip(xs, ys) for v in p]
            cv.create_line(*line, fill=mix(bg, s, 0.3), width=6, smooth=True)
            cv.create_line(*line, fill=s, width=2, smooth=True)
            dl = [v for p in zip(xs, [64 - i * 4.4 for i in range(len(xs))]) for v in p]
            cv.create_line(*dl, fill=d, width=2)
            cv.create_oval(xs[-1] - 3, 64 - 9 * 4.4 - 3, xs[-1] + 3, 64 - 9 * 4.4 + 3, fill=d, outline="")
            cv.create_text(10, 84, text=(th["n"] if th else "Match app theme"), anchor="w",
                           fill=mix(bg, "#ffffff", 0.85), font=("Segoe UI", 9, "bold") if IS_WINDOWS else None)
            cv.bind("<Button-1>", lambda _e: (self.set_theme(tid), mark()))
            cards[tid] = cv

        sec = ttk.Frame(outer)
        sec.pack(fill="x")
        card(sec, "app", None, 0, 0)
        for gname in ("QD-OLED", "Dark"):
            ttk.Label(outer, text=gname.upper(), style="SetHead.TLabel").pack(anchor="w", pady=(10, 2))
            grid = ttk.Frame(outer)
            grid.pack(fill="x")
            items = [(k, v) for k, v in GRAPH_THEMES.items() if v["g"] == gname]
            for i, (tid, th) in enumerate(items):
                card(grid, tid, th, i // 4, i % 4)
        bar = ttk.Frame(outer)
        bar.pack(fill="x", pady=(12, 0))
        ttk.Button(bar, text="Done", style="Accent.TButton",
                   command=lambda: (setattr(self, "_gal", None), win.destroy())).pack(side="right")
        mark()
        win.update_idletasks()
        r = self.winfo_toplevel()
        win.geometry(f"+{r.winfo_rootx() + max(0, (r.winfo_width() - win.winfo_reqwidth()) // 2)}"
                     f"+{r.winfo_rooty() + max(0, (r.winfo_height() - win.winfo_reqheight()) // 4)}")
        win.deiconify()
        fade_in(win)

    # -- data ------------------------------------------------------------------------------- #
    def new_run(self):
        self.samples, self._last_t, self._last_key, self._last_d, self._t0, self._cum = [], None, None, 0, None, 0
        self.redraw()

    def feed(self, s: dict):
        now = time.monotonic()
        key, d = s.get("label"), int(s.get("downloaded") or 0)
        if self._t0 is None:
            self._t0 = now
        if self._last_t is None:
            self._last_t, self._last_key, self._last_d = now, key, d
            self._cum = d
            return
        dt = now - self._last_t
        if dt < 0.18:
            return
        delta = d - self._last_d if key == self._last_key else d
        delta = max(0, delta)
        self._cum += delta
        raw = delta / dt
        paused = bool(s.get("paused"))
        recent = [x[1] for x in self.samples if now - self._t0 - x[0] < SMOOTH_SECS] + [raw]
        self.samples.append([now - self._t0, raw, sum(recent) / len(recent), self._cum, paused])
        if len(self.samples) > 120000:
            del self.samples[:20000]
        self._last_t, self._last_key, self._last_d = now, key, d
        self.schedule()

    def stats(self) -> dict:
        sm = self.samples
        if not sm:
            return {}
        run = [x for x in sm if not x[4]]
        dur = 0.0
        prev = 0.0
        mov_b = mov_t = 0.0
        for x in sm:
            span = x[0] - prev
            prev = x[0]
            if x[4]:
                continue
            dur += span
            if x[1] >= DIP_FLOOR:
                mov_t += span
                mov_b += x[1] * span
        return {"now": sm[-1][2], "avg": (sm[-1][3] / dur) if dur > 0 else 0.0,
                "avg2": (mov_b / mov_t) if mov_t > 0 else 0.0, "peak": max([x[2] for x in run] or [0.0]),
                "total": sm[-1][3]}

    def _window(self):
        sm = self.samples
        if not sm:
            return [], 0.0, 1.0
        span = self.span()
        t_end = sm[-1][0]
        t_start = max(t_end - span, sm[0][0] - 1.0) if span else sm[0][0] - 1.0
        win = [x for x in sm if x[0] >= t_start]
        if t_end - t_start < 20:
            t_start = t_end - 20
        return win, t_start, t_end

    # -- drawing ---------------------------------------------------------------------------- #
    def schedule(self, now: bool = False):
        """Redraws at the chosen update rate (and right away when the box is resized)."""
        if self._job:
            if not now:
                return
            try:
                self.after_cancel(self._job)
            except (tk.TclError, ValueError):
                pass
        wait = 30 if now else max(30, int(self.rate_ms() - (time.monotonic() - self._drawn) * 1000))
        self._job = self.after(wait, self._run_job)

    def _run_job(self):
        self._job = None
        self.redraw()

    def redraw(self):
        self._drawn = time.monotonic()
        g = self.gp()
        try:
            c = self.cv
            c.delete("all")
            c.configure(bg=g["bg"])
            w, h = c.winfo_width(), c.winfo_height()
        except tk.TclError:
            return
        st = self.stats()
        fmt = {"now": _fmt_rate_axis, "avg": _fmt_rate_axis, "avg2": _fmt_rate_axis, "peak": _fmt_rate_axis,
               "total": fmt_size}
        for k, var in self.tile_vars.items():
            var.set(fmt[k](st[k]) if st else "-")
        if w < 120 or h < 60:
            return
        win, t0, t1 = self._window()
        mode = self.cfg["mode"]
        col_s, col_d = g["s"], g["d"]
        self._hover = []
        self._tags: list = []
        if not win:
            self._grid(c, 64, 12, w - 14, h - 22, 4, _fmt_rate_axis, 1024 * 1024 * 4, col_s, "SPEED")
            c.create_text(w / 2, h / 2, text="Start a download and the graph fills in here",
                          fill=g["muted"], font=("Segoe UI", 10) if IS_WINDOWS else None)
            return
        base_cum = win[0][3] if self.span() else 0
        if mode == "Speed":
            self._plot(c, win, t0, t1, (64, 12, w - 14, h - 22), "speed", col_s, base_cum, True)
        elif mode == "Data downloaded":
            self._plot(c, win, t0, t1, (64, 12, w - 14, h - 22), "data", col_d, base_cum, True)
        elif mode == "Both - one graph":
            box = (64, 12, w - 70, h - 22)
            self._plot(c, win, t0, t1, box, "speed", col_s, base_cum, True)
            self._plot(c, win, t0, t1, box, "data", col_d, base_cum, False, right_axis=True)
        else:
            mid = (h - 8) // 2
            self._plot(c, win, t0, t1, (64, 10, w - 14, mid - 12), "speed", col_s, base_cum, True, xlabels=False)
            self._plot(c, win, t0, t1, (64, mid + 10, w - 14, h - 22), "data", col_d, base_cum, True)
        self._draw_tags(c)

    def _grid(self, c, x0, y0, x1, y1, n, fmt, vmax, col, title, right=False, draw_lines=True):
        g = self.gp()
        f8 = ("Segoe UI", 8) if IS_WINDOWS else None
        for i in range(n + 1):
            y = y1 - (y1 - y0) * i / n
            if draw_lines:
                c.create_line(x0, y, x1, y, fill=g["grid"], dash=(2, 5) if 0 < i else ())
            txt = fmt(vmax * i / n)
            # each axis is labelled in its own line's colour: speed in MB/s on the left, data on the right
            lab = mix(g["bg"], col, 0.85)
            if right:
                c.create_text(x1 + 6, y, text=txt, anchor="w", fill=lab, font=f8)
            else:
                c.create_text(x0 - 6, y, text=txt, anchor="e", fill=lab, font=f8)
        fb = ("Segoe UI", 8, "bold") if IS_WINDOWS else None
        if right:
            c.create_text(x1 - 8, y0 + 2, text=title, anchor="ne", fill=col, font=fb)
        else:
            c.create_text(x0 + 8, y0 + 2, text=title, anchor="nw", fill=col, font=fb)

    def _plot(self, c, win, t0, t1, box, kind, col, base_cum, with_grid, right_axis=False, xlabels=True):
        g = self.gp()
        bg = g["bg"]
        x0, y0, x1, y1 = box
        pw = max(10, x1 - x0)
        span = max(1.0, t1 - t0)
        nb = max(8, int(pw // 3))          # about one point per 3 px
        pts_raw: list = []
        if len(win) > nb:
            step = len(win) / nb
            for i in range(nb):
                chunk = win[int(i * step): max(int(i * step) + 1, int((i + 1) * step))]
                pts_raw.append([chunk[-1][0], sum(x[1] for x in chunk) / len(chunk),
                                sum(x[2] for x in chunk) / len(chunk), chunk[-1][3]])
        else:
            pts_raw = [[x[0], x[1], x[2], x[3]] for x in win]
        dips = self.cfg["dips"]
        if kind == "speed":
            main = [p[1] if dips.startswith("Raw") else p[2] for p in pts_raw]
            raw = [p[1] for p in pts_raw] if dips.startswith("Smoothed +") else None
            fmt, title = _fmt_rate_axis, "SPEED"
        else:
            main = [max(0, p[3] - base_cum) for p in pts_raw]
            raw = None
            fmt = fmt_size
            title = "DOWNLOADED" + ("" if not self.span() else f"  ({self._shown('range').lower()})")
        vmax = _nice_max(max(max(main), max(raw) if raw else 0, 1) * 1.08)
        ph = y1 - y0
        ticks = 4 if ph >= 110 else 2 if ph >= 50 else 1
        self._grid(c, x0, y0, x1, y1, ticks, fmt, vmax, col, title, right=right_axis, draw_lines=with_grid)

        def X(t):
            return x0 + (t - t0) / span * pw

        def Y(v):
            return y1 - (y1 - y0) * min(1.0, v / vmax)
        xs = [X(p[0]) for p in pts_raw]
        ys = [Y(v) for v in main]
        style = "Neon line" if right_axis else self.cfg["style"]
        glow = style in ("Glow area", "Smooth curve", "Neon line", "Steps", "Skyline")
        if raw:
            rl = [v for p in zip(xs, [Y(v) for v in raw]) for v in p]
            if len(rl) >= 4:
                c.create_line(*rl, fill=mix(bg, col, 0.40), width=1)
        if style in ("Bars", "Heat bars"):
            bw = max(2.0, pw / max(1, len(xs)) * 0.72)
            for x, y, v in zip(xs, ys, main):
                f = min(1.0, v / vmax)
                fill = heat3(f) if style == "Heat bars" else mix(mix(bg, col, 0.18), col, 0.25 + 0.75 * f)
                c.create_rectangle(x - bw / 2, y, x + bw / 2, y1, fill=fill, width=0)
                c.create_rectangle(x - bw / 2, y, x + bw / 2, y + 2, fill=mix(fill, "#ffffff", 0.35), width=0)
        elif style == "Lollipops":
            for x, y in zip(xs[::2], ys[::2]):
                c.create_line(x, y1, x, y, fill=mix(bg, col, 0.45), width=1)
                c.create_oval(x - 3, y - 3, x + 3, y + 3, fill=col, width=0)
        else:
            if style in ("Steps", "Skyline"):
                sx, sy = [], []
                for i, (x, y) in enumerate(zip(xs, ys)):
                    if i:
                        sx.append(x)
                        sy.append(sy[-1])
                    sx.append(x)
                    sy.append(y)
                xs2, ys2 = sx, sy
            else:
                xs2, ys2 = xs, ys
            if style in ("Glow area", "Smooth curve", "Gradient area", "Steps"):
                self._fill(c, xs2, ys2, y0, y1, col, strong=False)
            elif style == "Skyline":
                self._fill(c, xs2, ys2, y0, y1, col, strong=True)
            line = [v for p in zip(xs2, ys2) for v in p]
            smooth = style == "Smooth curve"
            if len(line) >= 4 and style != "Dots":
                if glow:
                    c.create_line(*line, fill=mix(bg, col, 0.14), width=10, capstyle="round", joinstyle="round",
                                  smooth=smooth)
                    c.create_line(*line, fill=mix(bg, col, 0.36), width=5, capstyle="round", joinstyle="round",
                                  smooth=smooth)
                c.create_line(*line, fill=col, width=2 if style != "Line" else 1.6, capstyle="round",
                              joinstyle="round", smooth=smooth)
            if style == "Dots":
                for x, y in zip(xs, ys):
                    c.create_oval(x - 4, y - 4, x + 4, y + 4, fill=mix(bg, col, 0.25), width=0)
                    c.create_oval(x - 2, y - 2, x + 2, y + 2, fill=mix(col, "#ffffff", 0.3), width=0)
        # leading marker + live value tag (constantly updated)
        ex, ey = xs[-1], ys[-1]
        c.create_oval(ex - 7, ey - 7, ex + 7, ey + 7, fill=mix(bg, col, 0.3), width=0)
        c.create_oval(ex - 3.5, ey - 3.5, ex + 3.5, ey + 3.5, fill=mix(col, "#ffffff", 0.55), width=0)
        if kind == "speed":
            val = _fmt_rate_live(main[-1])
        elif self.span():
            val = f"+{fmt_size(main[-1])} in range  ·  {fmt_size(pts_raw[-1][3])} total"
        else:
            val = f"{fmt_size(pts_raw[-1][3])} downloaded"
        self._tags.append({"x": ex, "y": ey, "text": val, "col": col, "kind": kind, "y0": y0, "y1": y1,
                           "ink": g["ink"] if kind == "speed" else g["ink_d"]})
        if xlabels:
            for i in range(6):
                p = i / 5
                tx = x0 + pw * p
                c.create_text(tx, y1 + 4, text=_fmt_ago((1 - p) * span),
                              anchor="n" if 0 < i < 5 else ("nw" if i == 0 else "ne"),
                              fill=g["muted"], font=("Segoe UI", 8) if IS_WINDOWS else None)
        if kind == "speed" or not right_axis:
            self._hover.append({"kind": kind, "x0": x0, "x1": x1, "y0": y0, "y1": y1, "col": col, "xs": xs,
                                "pts": pts_raw, "t1": t1, "base": base_cum})

    def _draw_tags(self, c):
        """Pills next to the newest point of each line with its live value; kept from overlapping."""
        f = ("Segoe UI", 9, "bold") if IS_WINDOWS else None
        placed: list = []
        for tg in sorted(self._tags, key=lambda t: t["y"]):
            tid = c.create_text(0, 0, text=tg["text"], font=f, anchor="e", fill=tg["ink"])
            bb = c.bbox(tid)
            tw, th = (bb[2] - bb[0], bb[3] - bb[1]) if bb else (60, 14)
            x = tg["x"] - 12
            y = min(max(tg["y"], tg["y0"] + th / 2 + 3), tg["y1"] - th / 2 - 3)
            for py in placed:
                if abs(y - py) < th + 8:
                    y = py + th + 8 if y >= py else py - th - 8
            y = min(max(y, tg["y0"] + th / 2 + 3), tg["y1"] - th / 2 - 3)
            placed.append(y)
            c.coords(tid, x - 8, y)
            r = c.create_rectangle(x - tw - 16, y - th / 2 - 3, x, y + th / 2 + 3, fill=tg["col"], outline="")
            c.tag_raise(tid, r)
            c.create_line(x, y, tg["x"] - 6, tg["y"], fill=tg["col"], width=1)

    def _fill(self, c, xs, ys, y0, y1, col, strong=False):
        if len(xs) < 2:
            return
        bg = self.gp()["bg"]
        nb = 14
        hgt = y1 - y0
        for b in range(nb):
            top = y0 + hgt * b / nb
            bot = y0 + hgt * (b + 1) / nb
            pts = []
            hit = False
            for x, y in zip(xs, ys):
                cy = min(max(y, top), bot)
                if y < bot:
                    hit = True
                pts += [x, cy]
            if not hit:
                continue
            pts += [xs[-1], bot, xs[0], bot]
            f = (0.22 + 0.40 * (b / (nb - 1))) if strong else (0.05 + 0.30 * (b / (nb - 1)))
            c.create_polygon(*pts, fill=mix(bg, col, f), outline="")

    def _motion(self, e):
        c = self.cv
        c.delete("hv")
        g = self.gp()
        for hv in self._hover:
            if hv["x0"] <= e.x <= hv["x1"] and hv["y0"] - 4 <= e.y <= hv["y1"] + 4 and hv["xs"]:
                i = min(range(len(hv["xs"])), key=lambda j: abs(hv["xs"][j] - e.x))
                p = hv["pts"][i]
                x = hv["xs"][i]
                c.create_line(x, hv["y0"], x, hv["y1"], fill=mix(g["bg"], g["text"], 0.4), dash=(3, 3), tags="hv")
                lines = [_fmt_ago(hv["t1"] - p[0]), f"speed  {_fmt_rate_axis(p[1])}  (avg {_fmt_rate_axis(p[2])})",
                         f"total  {fmt_size(p[3])}"]
                tx = x + 12
                wbox = 190
                if tx + wbox > hv["x1"] + 10:
                    tx = x - wbox - 12
                ty = hv["y0"] + 6
                c.create_rectangle(tx, ty, tx + wbox, ty + 18 * len(lines) + 6, fill=g["tip"], outline=hv["col"],
                                   tags="hv")
                for k, ln in enumerate(lines):
                    c.create_text(tx + 8, ty + 4 + 18 * k, text=ln, anchor="nw", fill=g["text"] if k else hv["col"],
                                  font=("Consolas", 9) if IS_WINDOWS else None, tags="hv")
                break


# --------------------------------------------------------------------------- #
#  GUI
# --------------------------------------------------------------------------- #
STATUS_TEXT = {"active": "Downloading", "stalled": "Waiting on Telegram", "paused": "Paused",
               "done": "Done", "error": "Failed - press Start again to retry"}


def row_values(r: dict) -> tuple:
    done, total = r["done"], r["total"]
    if r["status"] == "done":
        prog = f"Done  -  {fmt_size(done)}"
    elif r["status"] == "error":
        prog = STATUS_TEXT["error"]
    else:
        if total:
            pct = min(100, done * 100 // max(1, total))
            amount = f"{fmt_size(done)} / {fmt_size(total)}  ({pct}%)"
        else:
            amount = fmt_size(done)
        prog = f"{STATUS_TEXT[r['status']]}  -  {amount}"
    speed = fmt_speed(r["speed"]) if r["status"] in ("active", "stalled") else ""
    eta = fmt_eta(r.get("eta")) if r["status"] == "active" and r.get("eta") is not None else ""
    return (r["name"], r["type"], prog, speed, eta)


# --------------------------------------------------------------------------- #
#  Preferences: everything the Settings window can change, and the small animated widgets it is built from
# --------------------------------------------------------------------------- #
UI_DEFAULTS: dict = {
    # display
    "accent": "", "glow": True, "glow_strength": 70, "density": "comfortable", "scale": 100, "font": "segoe",
    "outline": "subtle", "title_case": "title", "hints": True, "hide_buttons": True, "scrollbar": "normal",
    "opacity": 100, "topmost": False, "titlebar_tint": True, "header_icons": True,
    # animation
    "anim": True, "anim_layout": True, "anim_snap": True, "anim_sizes": True, "anim_grid": True,
    "anim_speed": 30, "fps": 240, "anim_fade": True, "fade_ms": 180, "anim_bar": True, "anim_shimmer": True,
    "anim_flash": True, "anim_theme": True, "anim_hover": True, "anim_switch": True, "anim_tabs": True,
    # layout
    "gap": 10, "min_w": 380, "sec_scrollbars": False, "sec_select": True, "remember_geo": True, "start_max": False, "auto_fix": False, "auto_size": False, "win_shrink": "scroll", "layout_h": 0, "wheel_scroll": True,
    # sections
    "titles": {},
    # panels
    "con_font": "Consolas", "con_size": 10, "con_wrap": False, "con_flood": True, "con_reconn": True, "con_follow": True,
    "log_size": 10, "log_time": True, "log_clock": "24", "log_max": 3000, "legend": True, "pbar_h": 14,
    # behaviour
    "confirm_quit": True, "popup_done": True, "sound_done": True, "sound_err": False, "flash_done": True,
    "open_done": False, "remember_folder": False,
}
UI: dict = dict(UI_DEFAULTS)

UI_FONTS = {"segoe": ("Segoe UI", "Segoe UI"), "variable": ("Segoe UI Variable", "Segoe UI Variable Text"),
            "bahnschrift": ("Bahnschrift", "Bahnschrift"), "mono": ("Mono", "Cascadia Mono")}
CONSOLE_FONTS = ["Consolas", "Cascadia Mono", "Lucida Console", "Courier New"]
_FAMILIES: set = set()


def _have_font(name: str) -> bool:
    global _FAMILIES
    if not _FAMILIES:
        try:
            from tkinter import font as tkfont
            _FAMILIES = {f.lower() for f in tkfont.families()}
        except Exception:  # noqa: BLE001
            return True
    return name.lower() in _FAMILIES


def ui_family() -> str:
    fam = UI_FONTS.get(UI.get("font"), UI_FONTS["segoe"])[1]
    return fam if _have_font(fam) else "Segoe UI"


def ui_scale() -> float:
    try:
        return max(0.7, min(1.6, float(UI.get("scale", 100)) / 100.0))
    except (TypeError, ValueError):
        return 1.0


def ui_compact() -> bool:
    return UI.get("density") == "compact"


def anim_on(key: str | None = None) -> bool:
    return bool(UI.get("anim", True)) and (key is None or bool(UI.get(key, True)))


def ui_palette(th: dict) -> dict:
    """The theme's palette, with the accent swapped for your own colour if you picked one."""
    acc = UI.get("accent") or ""
    if is_hex(acc):
        th = dict(th)
        th["accent"] = acc
    return pal_from_theme(th)


def ease_after(widget, ms: int, steps_fn, done_fn=None, fps: int = 120):
    """Runs steps_fn(t) with t going 0 -> 1 (ease-out) over `ms` milliseconds, then done_fn()."""
    if not anim_on() or ms <= 0:
        try:
            steps_fn(1.0)
            if done_fn:
                done_fn()
        except tk.TclError:
            pass
        return
    t0 = time.perf_counter()
    dt = max(4, int(1000 / fps))

    def step():
        p = min(1.0, (time.perf_counter() - t0) * 1000.0 / ms)
        e = 1 - (1 - p) ** 3
        try:
            steps_fn(e)
        except tk.TclError:
            return
        if p < 1.0:
            widget.after(dt, step)
        elif done_fn:
            try:
                done_fn()
            except tk.TclError:
                pass
    step()


def fade_in(win, ms: int | None = None, target: float | None = None):
    """Windows fade in instead of popping up."""
    target = (UI.get("opacity", 100) / 100.0) if target is None else target
    ms = int(UI.get("fade_ms", 180)) if ms is None else ms
    if not anim_on("anim_fade"):
        try:
            win.attributes("-alpha", target)
        except tk.TclError:
            pass
        return
    try:
        win.attributes("-alpha", 0.0)
    except tk.TclError:
        return
    ease_after(win, ms, lambda e: win.attributes("-alpha", target * e))


class Switch(tk.Canvas):
    """An on/off switch whose knob slides across (and whose track fills with the accent) when you click it."""
    W, H = 44, 24

    def __init__(self, master, value=False, command=None, bg_key="panel2"):
        super().__init__(master, width=self.W, height=self.H, highlightthickness=0, bd=0, cursor="hand2",
                         bg=PAL[bg_key], takefocus=1)
        self.bg_key, self.command = bg_key, command
        self.value = bool(value)
        self._pos = 1.0 if self.value else 0.0
        self._hover = False
        self.bind("<Button-1>", self.toggle)
        self.bind("<space>", self.toggle)
        self.bind("<Enter>", lambda _e: self._hov(True))
        self.bind("<Leave>", lambda _e: self._hov(False))
        THEME_HOOKS.append(self.redraw)
        self.redraw()

    def _hov(self, on):
        self._hover = on
        self.redraw()

    def set(self, v: bool, animate: bool = True):
        v = bool(v)
        if v == self.value and self._pos == (1.0 if v else 0.0):
            return
        self.value = v
        start = self._pos
        end = 1.0 if v else 0.0
        self._gen = getattr(self, "_gen", 0) + 1
        gen = self._gen
        if not (animate and anim_on("anim_switch")):
            self._pos = end
            self.redraw()
            return

        def st(e):
            if gen != self._gen:        # clicked again mid-slide: the newer slide wins
                return
            self._pos = start + (end - start) * e
            self.redraw()
        ease_after(self, 160, st, fps=240)

    def toggle(self, _e=None):
        self.set(not self.value)
        if self.command:
            self.command(self.value)
        return "break"

    def redraw(self):
        self.delete("all")
        self.configure(bg=PAL[self.bg_key])
        W, H, p = self.W, self.H, self._pos
        on, off = PAL["accent"], PAL["field"]
        r = H / 2
        edge = mix(PAL["border"], on, p) if not self._hover else mix(PAL["accent"], PAL["border"], 0.35 * (1 - p))
        for inset, col in ((0, edge), (1, mix(off, on, p))):
            self.create_oval(inset, inset, H - inset, H - inset, fill=col, outline="")
            self.create_oval(W - H + inset, inset, W - inset, H - inset, fill=col, outline="")
            self.create_rectangle(r, inset, W - r, H - inset, fill=col, outline="")
        kx = r + p * (W - 2 * r)
        kr = r - 4
        self.create_oval(kx - kr, r - kr, kx + kr, r + kr, outline="",
                         fill=mix(PAL["muted"], PAL["accent_ink"], p))


class Segmented(ttk.Frame):
    """A row of joined buttons where exactly one is chosen (like Comfortable | Compact)."""

    def __init__(self, master, options, value, command=None, style_bg="SetCard.TFrame"):
        super().__init__(master, style=style_bg)
        self.command = command
        self.value = value
        self.btns = {}
        for v, label in options:
            b = ttk.Button(self, text=label, style="Seg.TButton", width=-max(3, len(str(label)) + 1),
                           command=lambda v=v: self.pick(v))
            b.pack(side="left", padx=(0, 2))
            self.btns[v] = b
        self._mark()

    def _mark(self):
        for v, b in self.btns.items():
            b.configure(style="SegOn.TButton" if v == self.value else "Seg.TButton")

    def set(self, v):
        self.value = v
        self._mark()

    def pick(self, v):
        if v == self.value:
            return
        self.set(v)
        if self.command:
            self.command(v)


class Slider(tk.Canvas):
    """A slim slider: a rounded track that fills with the accent and a round knob. Click, drag, wheel or arrows."""

    def __init__(self, master, lo, hi, step, value, on_move=None, on_release=None, width=210, bg_key="panel2"):
        super().__init__(master, width=width, height=26, highlightthickness=0, bd=0, cursor="hand2",
                         bg=PAL[bg_key], takefocus=1)
        self.lo, self.hi, self.step, self.bg_key = lo, hi, step, bg_key
        self.value = self._snap(value)
        self.on_move, self.on_release = on_move, on_release
        self._hover = self._drag = False
        self.bind("<Configure>", lambda _e: self.redraw())
        self.bind("<ButtonPress-1>", self._press)
        self.bind("<B1-Motion>", self._motion)
        self.bind("<ButtonRelease-1>", self._release)
        self.bind("<Enter>", lambda _e: self._hov(True))
        self.bind("<Leave>", lambda _e: self._hov(False))
        self.bind("<MouseWheel>", self._wheel)
        self.bind("<Left>", lambda _e: self._nudge(-1))
        self.bind("<Right>", lambda _e: self._nudge(1))
        THEME_HOOKS.append(self.redraw)

    def _snap(self, v):
        v = max(self.lo, min(self.hi, round(float(v) / self.step) * self.step))
        return int(v) if float(self.step).is_integer() else v

    def _x(self, v):
        w = self.winfo_width()
        return 10 + (w - 20) * (v - self.lo) / max(1e-9, self.hi - self.lo)

    def _v(self, x):
        w = self.winfo_width()
        return self._snap(self.lo + (x - 10) / max(1, w - 20) * (self.hi - self.lo))

    def set(self, v):
        self.value = self._snap(v)
        self.redraw()

    def _hov(self, on):
        self._hover = on
        self.redraw()

    def _change(self, v, final):
        v = self._snap(v)
        changed = v != self.value
        self.value = v
        self.redraw()
        if changed and self.on_move:
            self.on_move(v)
        if final and self.on_release:
            self.on_release(v)

    def _press(self, e):
        self.focus_set()
        self._drag = True
        self._change(self._v(e.x), False)

    def _motion(self, e):
        if self._drag:
            self._change(self._v(e.x), False)

    def _release(self, e):
        if self._drag:
            self._drag = False
            self._change(self._v(e.x), True)

    def _nudge(self, d):
        self._change(self.value + d * self.step, True)
        return "break"

    def _wheel(self, e):
        self._nudge(1 if e.delta > 0 else -1)
        return "break"

    def redraw(self):
        self.delete("all")
        self.configure(bg=PAL[self.bg_key])
        w, cy = self.winfo_width(), 13
        if w < 30:
            return
        kx = self._x(self.value)
        self.create_line(10, cy, w - 10, cy, width=5, capstyle="round", fill=PAL["well"])
        self.create_line(10, cy, kx, cy, width=5, capstyle="round", fill=PAL["accent"])
        r = 9 if (self._hover or self._drag) else 8
        if self._hover or self._drag:
            self.create_oval(kx - r - 3, cy - r - 3, kx + r + 3, cy + r + 3, outline="",
                             fill=mix(PAL[self.bg_key], PAL["accent"], 0.25))
        self.create_oval(kx - r, cy - r, kx + r, cy + r, outline=PAL[self.bg_key], width=2,
                         fill=PAL["accent_hi"] if self._drag else PAL["accent"])


def flash_taskbar(root) -> None:
    if not IS_WINDOWS:
        return
    try:
        import ctypes
        from ctypes import wintypes

        class FLASHWINFO(ctypes.Structure):
            _fields_ = [("cbSize", wintypes.UINT), ("hwnd", wintypes.HWND), ("dwFlags", wintypes.DWORD),
                        ("uCount", wintypes.UINT), ("dwTimeout", wintypes.DWORD)]
        hwnd = ctypes.windll.user32.GetParent(root.winfo_id())
        fi = FLASHWINFO(ctypes.sizeof(FLASHWINFO), hwnd, 0x3 | 0xC, 0, 0)   # caption + tray, until focused
        ctypes.windll.user32.FlashWindowEx(ctypes.byref(fi))
    except Exception:  # noqa: BLE001
        pass


def play_sound(kind: str) -> None:
    if not IS_WINDOWS:
        return
    try:
        import winsound
        winsound.MessageBeep(winsound.MB_ICONASTERISK if kind == "done" else winsound.MB_ICONHAND)
    except Exception:  # noqa: BLE001
        pass


class SettingsWindow:
    """The Settings window: every preference in tabs, searchable, applied the moment you change it."""

    TABS = [("display", "Display"), ("anim", "Animation"), ("layout", "Layout"), ("sections", "Sections"),
            ("panels", "Panels"), ("behaviour", "Behaviour"), ("data", "Data")]
    SEC_NOTES = {
        "save_loc": "Where new files go, and the reference folder to skip duplicates",
        "what_save": "Photos, videos, voice, files ... which kinds to download",
        "which_conv": "The chat / channel / group list and the topic filters",
        "speed_safety": "Connections, files at once, auto-tune, takeout and keep-awake",
        "queue": "Downloads lined up to run one after another",
        "controls": "Start, pause, stop, save and load",
        "tdl_console": "A live mirror of the engine's console window",
        "live_dl": "Speed, ETA and every file that's downloading right now",
        "speed_graph": "Speed and amount downloaded over time",
        "activity_log": "What the app did and when",
    }

    def __init__(self, app, tab: str = "display"):
        self.app = app
        self.win = win = tk.Toplevel(app.root)
        win.withdraw()
        win.title("Settings")
        win.minsize(660, 520)
        sw, sh = win.winfo_screenwidth(), win.winfo_screenheight()
        W, H = min(860, sw - 80), min(900, sh - 120)
        r = app.root
        x = r.winfo_rootx() + max(0, (r.winfo_width() - W) // 2)
        y = r.winfo_rooty() + max(0, (r.winfo_height() - H) // 3)
        win.geometry(f"{W}x{H}+{max(0, x)}+{max(0, y)}")
        themed(win, bg="panel")
        win.transient(app.root)
        dark_title_bar(win)
        self.rows: list = []          # [tab, card, row, separator, haystack]
        self.cards: list = []         # [tab, heading, note, card]
        self.ctrls: dict = {}         # ui key -> control (so a reset can move them back)
        self.tab = None
        self._ind = [0.0, 0.0]

        outer = ttk.Frame(win, padding=(24, 16, 24, 14))
        outer.pack(fill="both", expand=True)
        hd = ttk.Frame(outer)
        hd.pack(fill="x")
        left = ttk.Frame(hd)
        left.pack(side="left")
        ttk.Label(left, text="SETTINGS", style="SetKicker.TLabel").pack(anchor="w")
        ttk.Label(left, text="Preferences", style="SetTitle.TLabel").pack(anchor="w")
        srch = ttk.Frame(hd)
        srch.pack(side="right", anchor="s", pady=(0, 4))
        ttk.Label(srch, text="⌕", style="Muted.TLabel", font=("Segoe UI Symbol", 13) if IS_WINDOWS else None
                  ).pack(side="left", padx=(0, 6))
        self.q = tk.StringVar()
        self.search = ttk.Entry(srch, textvariable=self.q, width=30)
        self.search.pack(side="left")
        self.ph = ttk.Label(srch, text="Search settings", style="Placeholder.TLabel", cursor="xterm")
        self.ph.place(in_=self.search, x=8, rely=0.5, anchor="w")
        self.ph.bind("<Button-1>", lambda _e: self.search.focus_set())

        tabrow = ttk.Frame(outer)
        tabrow.pack(fill="x", pady=(14, 0))
        self.tabrow = tabrow
        self.tab_btns: dict = {}
        for key, label in self.TABS:
            b = ttk.Button(tabrow, text=label, style="Tab.TButton", command=lambda k=key: self.show(k))
            b.pack(side="left", padx=(0, 4))
            self.tab_btns[key] = b
        self.ind = tk.Canvas(outer, height=3, highlightthickness=0, bd=0)
        themed(self.ind, bg="panel")
        self.ind.pack(fill="x", pady=(5, 0))
        self.ind_bar = self.ind.create_rectangle(0, 0, 0, 3, outline="", fill=PAL["accent"])
        line = tk.Frame(outer, height=1, bd=0, highlightthickness=0)
        themed(line, bg="line")
        line.pack(fill="x")

        body = ttk.Frame(outer)
        body.pack(fill="both", expand=True, pady=(2, 0))
        self.cv = tk.Canvas(body, highlightthickness=0, bd=0)
        themed(self.cv, bg="panel")
        sb = NeonScrollbar(body, orient="vertical", command=self.cv.yview, thickness=12)
        self.cv.configure(yscrollcommand=sb.set)
        sb.pack(side="right", fill="y", padx=(6, 0))
        self.cv.pack(side="left", fill="both", expand=True)
        self.inner_id = self.cv.create_window(0, 0, anchor="nw")
        self.cv.bind("<Configure>", self._cv_cfg)
        self.pages: dict = {}
        for key, _label in self.TABS:
            pg = ttk.Frame(self.cv, padding=(2, 4, 8, 24))
            pg.bind("<Configure>", lambda _e: self._sr())
            self.pages[key] = pg
        self.build_display(self.pages["display"])
        self.build_anim(self.pages["anim"])
        self.build_layout(self.pages["layout"])
        self.build_sections(self.pages["sections"])
        self.build_panels(self.pages["panels"])
        self.build_behaviour(self.pages["behaviour"])
        self.build_data(self.pages["data"])

        foot = ttk.Frame(outer)
        foot.pack(fill="x", pady=(12, 0))
        ttk.Label(foot, text="Changes apply instantly and are saved automatically.", style="Muted.TLabel"
                  ).pack(side="left")
        ttk.Button(foot, text="Close", style="Accent.TButton", command=self.close).pack(side="right")
        ttk.Button(foot, text="Reset this page", command=self.reset_page).pack(side="right", padx=(0, 8))

        win.bind("<MouseWheel>", self._wheel)
        win.bind("<Escape>", lambda _e: self.close())
        win.bind("<Control-f>", lambda _e: (self.search.focus_set(), "break")[1])
        win.protocol("WM_DELETE_WINDOW", self.close)
        self.q.trace_add("write", lambda *_: self._filter())
        self.search.bind("<FocusIn>", lambda _e: self._ph())
        self.search.bind("<FocusOut>", lambda _e: self._ph())
        self.show(tab if tab in self.pages else "display", animate=False)
        win.deiconify()
        fade_in(win)
        win.after(60, lambda: self._move_ind(animate=False))

    # -- plumbing --------------------------------------------------------------------------- #
    def _cv_cfg(self, e):
        self.cv.itemconfigure(self.inner_id, width=e.width)
        self._sr()

    def _sr(self):
        try:
            self.cv.configure(scrollregion=(0, 0, self.cv.winfo_width(),
                                            max(self.cv.winfo_height(), self.pages[self.tab].winfo_reqheight())))
        except (tk.TclError, KeyError):
            pass

    def _wheel(self, e):
        try:
            cls = e.widget.winfo_class()
        except (tk.TclError, AttributeError):
            cls = ""
        if cls in ("TCombobox", "Text"):
            return
        self.cv.yview_scroll(-1 if e.delta > 0 else 1, "units")
        return "break"

    def _ph(self):
        try:
            if self.q.get() or self.win.focus_get() is self.search:
                self.ph.place_forget()
            else:
                self.ph.place(in_=self.search, x=8, rely=0.5, anchor="w")
        except (tk.TclError, KeyError):
            pass

    def show(self, key: str, animate: bool = True):
        self.tab = key
        for k, b in self.tab_btns.items():
            b.configure(style="TabOn.TButton" if k == key else "Tab.TButton")
        self.cv.itemconfigure(self.inner_id, window=self.pages[key])
        self.cv.yview_moveto(0)
        self.win.after_idle(self._sr)
        self.win.after(10, lambda: self._move_ind(animate))

    def _move_ind(self, animate=True):
        try:
            b = self.tab_btns[self.tab]
            x0 = b.winfo_x() + self.tabrow.winfo_x() - self.ind.winfo_x()
            x1 = x0 + b.winfo_width()
        except (tk.TclError, KeyError):
            return
        a0, a1 = self._ind
        self.ind.itemconfigure(self.ind_bar, fill=PAL["accent"])
        if not (animate and anim_on("anim_tabs")) or a1 <= 0:
            self._ind = [x0, x1]
            self.ind.coords(self.ind_bar, x0 + 6, 0, x1 - 6, 3)
            return

        def st(e):
            l, r = a0 + (x0 - a0) * e, a1 + (x1 - a1) * e
            self._ind = [l, r]
            self.ind.coords(self.ind_bar, l + 6, 0, r - 6, 3)
        ease_after(self.ind, 240, st, fps=240)

    def close(self):
        try:
            self.app._settings_win = None
            self.win.destroy()
        except tk.TclError:
            pass

    # -- row builders ----------------------------------------------------------------------- #
    def group(self, page, tab, title, note=None):
        h = ttk.Label(page, text=title.upper(), style="SetHead.TLabel")
        h.pack(anchor="w", pady=(20, 6))
        n = None
        if note:
            n = ttk.Label(page, text=note, style="SetNote.TLabel", wraplength=720, justify="left")
            n.pack(anchor="w", pady=(0, 8), fill="x")
            autowrap(n, pad=10)
        card = tk.Frame(page, highlightthickness=1, bd=0)
        themed(card, bg="panel2", highlightbackground="border")
        card.pack(fill="x")
        self.cards.append([tab, h, n, card])
        return card

    def row(self, card, tab, name, desc, make):
        sep = None
        if any(r[1] is card for r in self.rows):
            sep = tk.Frame(card, height=1, bd=0, highlightthickness=0)
            themed(sep, bg="line")
            sep.pack(fill="x", padx=14)
        r = ttk.Frame(card, style="SetCard.TFrame", padding=(16, 11, 14, 11))
        r.pack(fill="x")
        ctl = make(r)
        if ctl is not None:
            ctl.pack(side="right", padx=(18, 0))
        txt = ttk.Frame(r, style="SetCard.TFrame")
        txt.pack(side="left", fill="x", expand=True)
        ttk.Label(txt, text=name, style="SetName.TLabel").pack(anchor="w")
        if desc:
            d = ttk.Label(txt, text=desc, style="SetDesc.TLabel", justify="left", wraplength=420)
            d.pack(anchor="w", fill="x", pady=(1, 0))
            autowrap(d, pad=4)
        self.rows.append([tab, card, r, sep, (name + " " + (desc or "")).lower()])
        return r

    def toggle(self, card, tab, key, name, desc=None, after=None):
        def make(parent):
            sw = Switch(parent, UI.get(key), command=lambda v: (self.app.set_ui(key, v), after and after(v)))
            self.ctrls[key] = sw
            return sw
        return self.row(card, tab, name, desc, make)

    def seg(self, card, tab, key, name, options, desc=None):
        def make(parent):
            s = Segmented(parent, options, UI.get(key), command=lambda v: self.app.set_ui(key, v))
            self.ctrls[key] = s
            return s
        return self.row(card, tab, name, desc, make)

    def slider(self, card, tab, key, name, lo, hi, step, fmt, desc=None, live=True):
        def make(parent):
            f = ttk.Frame(parent, style="SetCard.TFrame")
            lbl = ttk.Label(f, text=fmt(UI.get(key)), style="SetValue.TLabel", width=8, anchor="e")
            job = {"id": None}

            def moved(v):
                lbl.configure(text=fmt(v))
                if live:
                    if job["id"]:
                        f.after_cancel(job["id"])
                    job["id"] = f.after(40, lambda: (job.update(id=None), self.app.set_ui(key, v)))

            def released(v):
                lbl.configure(text=fmt(v))
                self.app.set_ui(key, v)
            sl = Slider(f, lo, hi, step, UI.get(key), on_move=moved, on_release=released)
            sl.pack(side="left")
            lbl.pack(side="left", padx=(10, 0))
            f.set_value = lambda v: (sl.set(v), lbl.configure(text=fmt(v)))
            self.ctrls[key] = f
            return f
        return self.row(card, tab, name, desc, make)

    def buttons(self, card, tab, name, desc, specs):
        def make(parent):
            f = ttk.Frame(parent, style="SetCard.TFrame")
            for text, cmd, *style in specs:
                ttk.Button(f, text=text, command=cmd, style=style[0] if style else "TButton").pack(side="left", padx=(6, 0))
            return f
        return self.row(card, tab, name, desc, make)

    # -- search ------------------------------------------------------------------------------ #
    def _filter(self):
        self._ph()
        words = self.q.get().strip().lower().split()
        counts = {k: 0 for k in self.pages}
        for pg in self.pages.values():
            for w in pg.pack_slaves():
                w.pack_forget()
        for tab, h, n, card in self.cards:
            rows = [rw for rw in self.rows if rw[1] is card]
            head = h.cget("text").lower()
            hits = [rw for rw in rows if all(w in rw[4] or w in head for w in words)]
            for rw in rows:
                rw[2].pack_forget()
                if rw[3] is not None:
                    rw[3].pack_forget()
            for i, rw in enumerate(hits):
                if i and rw[3] is not None:
                    rw[3].pack(fill="x", padx=14)
                rw[2].pack(fill="x")
            if hits or not rows:
                h.pack(anchor="w", pady=(20, 6))
                if n is not None:
                    n.pack(anchor="w", pady=(0, 8), fill="x")
                card.pack(fill="x")
            counts[tab] += len(hits)
        for k, lab in self.TABS:
            self.tab_btns[k].configure(text=f"{lab}  {counts[k]}" if words else lab)
        if words and counts.get(self.tab, 0) == 0:
            best = max(counts, key=counts.get)
            if counts[best]:
                self.show(best)
        self._sr()

    # -- pages ------------------------------------------------------------------------------ #
    def build_display(self, pg):
        T = "display"
        app = self.app
        c = self.group(pg, T, "Colour")

        def accent_ctl(parent):
            f = ttk.Frame(parent, style="SetCard.TFrame")
            sw = tk.Frame(f, width=34, height=24, highlightthickness=2, cursor="hand2")
            sw.configure(bg=PAL["accent"], highlightbackground=PAL["border"])
            THEME_HOOKS.append(lambda: sw.configure(bg=PAL["accent"], highlightbackground=PAL["border"]))
            sw.pack(side="left")
            sw.bind("<Button-1>", lambda _e: pick())
            ttk.Button(f, text="Pick colour...", command=lambda: pick()).pack(side="left", padx=(8, 0))
            ttk.Button(f, text="Use theme colour", style="Toggle.TButton",
                       command=lambda: app.set_ui("accent", "")).pack(side="left", padx=(6, 0))

            def pick():
                from tkinter import colorchooser
                col = colorchooser.askcolor(color=PAL["accent"], parent=self.win, title="Accent colour")
                if col and col[1]:
                    app.set_ui("accent", col[1])
            return f
        self.row(c, T, "Accent colour", "Buttons, highlights, glow and selection. Leave it on the theme's own colour, "
                                        "or pick any colour.", accent_ctl)
        self.buttons(c, T, "Theme", "Themes stay in their own window: the gallery, QD-OLED themes and the theme "
                                    "studio with the colour wheel.", [("◐  Open themes...", app.open_theme_studio)])

        c = self.group(pg, T, "Glow")
        self.toggle(c, T, "glow", "Background glow", "The neon line under the title, glowing card frames when you "
                                                      "point at a section, and the shimmer while downloading.")
        self.slider(c, T, "glow_strength", "Glow strength", 10, 100, 5, lambda v: f"{int(v)} %",
                    "How far the neon line glows before it fades out.")
        self.toggle(c, T, "titlebar_tint", "Tinted title bar", "Windows 11: colour the window's own title bar "
                                                                "and border to match the theme.")

        c = self.group(pg, T, "Text & shape")
        self.seg(c, T, "font", "Font", [("segoe", "Segoe"), ("variable", "Variable"), ("bahnschrift", "Bahnschrift"),
                                        ("mono", "Mono")], "The typeface for buttons, labels and titles.")
        self.slider(c, T, "scale", "Interface scale", 80, 140, 5, lambda v: f"{int(v)} %",
                    "Makes all text and controls bigger or smaller, like browser zoom.", live=False)
        self.seg(c, T, "density", "Density", [("comfortable", "Comfortable"), ("compact", "Compact")],
                 "Compact fits more on screen: tighter padding, shorter rows, smaller buttons.")
        self.seg(c, T, "outline", "Section outlines", [("subtle", "Subtle"), ("bold", "Bold"), ("none", "None")],
                 "The frame drawn around every section.")
        self.seg(c, T, "title_case", "Section titles", [("title", "Title case"), ("upper", "UPPERCASE")])
        self.seg(c, T, "scrollbar", "Scrollbars", [("slim", "Slim"), ("normal", "Normal"), ("wide", "Wide")],
                 "Wide is easier to grab; slim stays out of the way.")

        c = self.group(pg, T, "Window")
        self.slider(c, T, "opacity", "Window opacity", 60, 100, 1, lambda v: f"{int(v)} %",
                    "See through the app to what's behind it.")
        self.toggle(c, T, "topmost", "Always on top", "Keep this window above every other window.")
        self.toggle(c, T, "hints", "Hints in the header", "The small 'drag a title to move it' help line.")
        self.toggle(c, T, "hide_buttons", "'Hide' buttons on section titles",
                    "Turn off for cleaner title bars. Sections can still be hidden here, in the Sections tab.")
        self.toggle(c, T, "header_icons", "Grip icons on section titles", "The ⠿ handle you can drag a section by.")

    def build_anim(self, pg):
        T = "anim"
        app = self.app
        c = self.group(pg, T, "Motion", "Everything that moves is drawn on its own layer and timed to your screen, so "
                                        "sections never tear or leave trails behind.")
        self.toggle(c, T, "anim", "Animations", "Master switch. Off = everything snaps into place instantly "
                                                "(the 'reduce motion' setting).")
        self.slider(c, T, "anim_speed", "Glide time", 10, 120, 5, lambda v: f"{int(v)} ms",
                    "How long boxes take to glide into place. Lower is snappier, higher is floatier.")
        self.seg(c, T, "fps", "Frame rate", [(60, "60"), (120, "120"), (144, "144"), (165, "165"), (240, "240"),
                                             (360, "360")],
                 "Match your monitor's refresh rate (Hz). Higher only costs CPU while something is moving.")
        self.buttons(c, T, "Preview", "Plays the animations once so you can see the settings in action.",
                     [("▶  Play preview", app.play_anim_preview)])

        c = self.group(pg, T, "Layout")
        self.toggle(c, T, "anim_layout", "Animate layout changes", "Switching layouts, hiding and showing sections "
                                                                  "glide instead of jumping.")
        self.toggle(c, T, "anim_snap", "Real content while dragging", "Boxes carry a picture of what's in them "
                                                                      "while you move or resize. Off = plain cards.")
        self.toggle(c, T, "anim_sizes", "Sizes while resizing", "The 640 × 420 label on the box you're resizing.")
        self.toggle(c, T, "anim_grid", "Grid while arranging", "Faint grid lines behind the boxes while you drag.")

        c = self.group(pg, T, "Windows & controls")
        self.toggle(c, T, "anim_fade", "Fade windows in", "The app, Settings and dialogs fade in instead of popping up.")
        self.slider(c, T, "fade_ms", "Fade length", 60, 500, 10, lambda v: f"{int(v)} ms")
        self.toggle(c, T, "anim_theme", "Smooth theme switching", "A quick dip-and-return when a theme is applied.")
        self.toggle(c, T, "anim_flash", "Highlight sections that appear", "A section you show or locate glows "
                                                                          "for a moment so your eye finds it.")
        self.toggle(c, T, "anim_hover", "Soft hover", "Section frames fade to the accent when you point at a title.")
        self.toggle(c, T, "anim_switch", "Sliding switches", "The knobs on switches like these slide across.")
        self.toggle(c, T, "anim_tabs", "Sliding tab underline", "The accent line under these tabs glides.")

        c = self.group(pg, T, "While downloading")
        self.toggle(c, T, "anim_bar", "Smooth progress bars", "Bars glide to the new value instead of stepping.")
        self.toggle(c, T, "anim_shimmer", "Shimmer on the header line", "A light runs along the neon line while a "
                                                                        "download is going. Needs Background glow.")

    def build_layout(self, pg):
        T = "layout"
        app = self.app
        c = self.group(pg, T, "Arrangement",
                       "Drag a section by its title and drop it on another box: the middle swaps them, an edge puts "
                       "it beside, the window edge makes a full band. Drag the gap between boxes to resize just "
                       "that box. Esc cancels a drag. The starting layouts:")
        desc = {"Command center (2 columns)": "Setup on the left; live download, graphs and console on the right",
                "Ultrawide (3 columns)": "Three columns for 21:9 and wider screens",
                "Wide bands": "Rows that run the full width of the window",
                "Classic stack (1 column)": "Every section full width, one under another"}
        for name in layout_presets():
            self.buttons(c, T, name.split(" (")[0], desc.get(name, ""),
                         [("Apply", lambda n=name: app.apply_preset(n))])
        self.saved_card = self.group(pg, T, "Your layouts", "Saved with the name you choose. They're also in the "
                                                            "Layout menu, under 'Your layouts'.")
        self._fill_saved()
        c = self.group(pg, T, "When the window gets shorter")
        self.seg(c, T, "win_shrink", "Sections", [("scroll", "Keep their size and scroll"), ("fit", "Shrink to fit")],
                 "Keep their size: making the window shorter adds a scrollbar instead of squashing every section. "
                 "Making it taller still fills the window.")
        self.slider(c, T, "layout_h", "Shortest layout before scrolling", 0, 2400, 20,
                    lambda v: "Auto" if v < 400 else f"{int(v)} px",
                    "Auto = about the height of the window maximised on this screen.", live=False)
        c = self.group(pg, T, "Automatic resizing")
        self.toggle(c, T, "auto_size", "Resize other boxes automatically",
                    "Off (default): only the box you drag changes. Growing a box stops at its neighbours, "
                    "shrinking one leaves empty space, hiding one leaves its space empty, and a section you show "
                    "again goes into empty space when there is room. You can drop a box into empty space either "
                    "way. On: neighbours shrink to make room and grow into gaps.")
        c = self.group(pg, T, "Tidy")
        self.buttons(c, T, "Tidy up gaps", "Hands empty space to the boxes around it.", [("Tidy", app.dock.tidy)])
        self.buttons(c, T, "Show every section", "Brings back everything you've hidden.",
                     [("Show all", lambda: (app.show_all_sections(), self.refresh_sections()))])
        c = self.group(pg, T, "Spacing")
        self.slider(c, T, "gap", "Space between sections", 4, 24, 1, lambda v: f"{int(v)} px")
        self.slider(c, T, "min_w", "Narrowest a section may get", 300, 520, 10, lambda v: f"{int(v)} px",
                    "If the window is too small for every section at this width, the layout scrolls instead "
                    "of squashing them.", live=False)
        c = self.group(pg, T, "Window")
        self.toggle(c, T, "remember_geo", "Remember size and position", "Open where you closed it.")
        self.toggle(c, T, "start_max", "Start maximised")
        self.toggle(c, T, "auto_fix", "Fix layouts that don't fit", "On start, a saved layout that would squash boxes "
                                                                    "in this window is swapped for one that fits.")
        c2 = self.group(pg, T, "Scrolling inside sections",
                        "When a box is smaller than what's in it, its content scrolls inside the box. Click a "
                        "section to select it; the mouse wheel then scrolls that section (lists and text boxes "
                        "still scroll themselves when the pointer is on them).")
        self.toggle(c2, T, "sec_scrollbars", "Show scrollbars inside sections", "Hidden by default: the wheel "
                                                                                 "still scrolls them.")
        self.toggle(c2, T, "sec_select", "Mark the selected section", "The line under its title turns the "
                                                                      "accent colour.")
        self.toggle(c, T, "wheel_scroll", "Mouse wheel scrolls the layout", "When the window is smaller than the "
                                                                            "layout, the wheel scrolls it (outside lists).")

    def _fill_saved(self):
        card = self.saved_card
        for rw in [r for r in self.rows if r[1] is card]:
            self.rows.remove(rw)
        for w in card.winfo_children():
            w.destroy()
        saved = self.app.saved_layouts()
        for name in sorted(saved, key=str.lower):
            st = saved[name]
            n = len((st.get("rects") or {}))
            self.buttons(card, "layout", "★  " + name, f"{n} sections on screen, {len(st.get('hidden') or {})} hidden",
                         [("Apply", lambda n_=name: self.app.apply_saved_layout(n_)),
                          ("Delete", lambda n_=name: self._del_saved(n_), "Toggle.TButton")])
        self.buttons(card, "layout", "Save the current layout", "Give it a name; where every box sits and which "
                                                               "sections are hidden are both kept.",
                     [("Save as...", self._save_as, "Accent.TButton")])

    def _save_as(self):
        dlg = self.app.save_layout_as()
        if dlg is not None:
            self.win.wait_window(dlg)
        if self.win.winfo_exists():
            self._fill_saved()
            self.win.lift()

    def _del_saved(self, name):
        self.app.delete_saved_layout(name)
        self._fill_saved()

    def build_sections(self, pg):
        T = "sections"
        app = self.app
        c = self.group(pg, T, "Sections", "Turn sections on or off, give them your own names, or find one on screen. "
                                          "Rename by typing and pressing Enter.")
        self.sec_switch: dict = {}
        for key in SECTION_KEYS:
            if key not in app.sections:
                continue

            def make(parent, key=key):
                f = ttk.Frame(parent, style="SetCard.TFrame")
                var = tk.StringVar(value=(UI.get("titles") or {}).get(key) or app.sections[key]["title"])
                e = ttk.Entry(f, textvariable=var, width=20)
                e.pack(side="left")

                def commit(_e=None):
                    t = dict(UI.get("titles") or {})
                    v = var.get().strip()[:40]
                    if v and v != app.sections[key]["title"]:
                        t[key] = v
                    else:
                        t.pop(key, None)
                        var.set(app.sections[key]["title"])
                    app.set_ui("titles", t)
                e.bind("<Return>", commit)
                e.bind("<FocusOut>", commit)
                ttk.Button(f, text="Locate", style="Toggle.TButton",
                           command=lambda: app.locate_section(key)).pack(side="left", padx=(8, 12))
                sw = Switch(f, key not in app.dock.hidden, command=lambda v: self._sec_vis(key, v))
                sw.pack(side="left")
                self.sec_switch[key] = sw
                return f
            self.row(c, T, app.sections[key]["title"], self.SEC_NOTES.get(key, ""), make)
        c = self.group(pg, T, "All sections")
        self.buttons(c, T, "Reset names", "Every section goes back to its own name.",
                     [("Reset", self._reset_names)])
        self.buttons(c, T, "Show every section", None,
                     [("Show all", lambda: (app.show_all_sections(), self.refresh_sections()))])

    def _sec_vis(self, key, on):
        d = self.app.dock
        if on:
            if key in d.hidden:
                d.show(key)
        elif not d.hide(key):
            self.app.status.set("At least one section has to stay visible.")
            self.win.after(200, lambda: self.sec_switch[key].set(True))

    def refresh_sections(self):
        for key, sw in getattr(self, "sec_switch", {}).items():
            try:
                sw.set(key not in self.app.dock.hidden)
            except tk.TclError:
                pass

    def _reset_names(self):
        self.app.set_ui("titles", {})
        self.win.destroy()
        self.app._settings_win = None
        self.app.open_settings("sections")

    def build_panels(self, pg):
        T = "panels"
        c = self.group(pg, T, "Live download")
        self.toggle(c, T, "legend", "Colour legend", "The 'Yellow = downloading, Green = done ...' line under the list.")
        self.slider(c, T, "pbar_h", "Progress bar height", 6, 28, 1, lambda v: f"{int(v)} px")
        c = self.group(pg, T, "tdl / console view")
        fonts = [(f, f.replace(" Mono", "").replace("Lucida Console", "Lucida").replace("Courier New", "Courier"))
                 for f in CONSOLE_FONTS if _have_font(f)]
        self.seg(c, T, "con_font", "Font", fonts)
        self.slider(c, T, "con_size", "Text size", 8, 18, 1, lambda v: f"{int(v)} pt")
        self.toggle(c, T, "con_wrap", "Wrap long lines", "Off keeps one line per message with a sideways scrollbar.")
        self.toggle(c, T, "con_flood", "Collapse 'slow down' spam", "Telegram's flood waits become one counting "
                                                                     "line (×12) instead of a wall of text.")
        self.toggle(c, T, "con_reconn", "Collapse reconnect messages", "'Server closed the connection' / WinError 64 "
                                                                       "lines become one counting line. The engine "
                                                                       "reconnects on its own either way.")
        self.toggle(c, T, "con_follow", "Follow new output", "Keep scrolling to the newest line while you're at "
                                                             "the bottom.")
        c = self.group(pg, T, "Activity log")
        self.toggle(c, T, "log_time", "Timestamps")
        self.seg(c, T, "log_clock", "Clock", [("24", "24-hour"), ("12", "12-hour")])
        self.slider(c, T, "log_size", "Text size", 8, 16, 1, lambda v: f"{int(v)} pt")
        self.slider(c, T, "log_max", "Keep at most", 500, 20000, 500, lambda v: f"{int(v):,}",
                    "Lines kept in the log before the oldest are dropped (the technical log keeps everything).",
                    live=False)

    def build_behaviour(self, pg):
        T = "behaviour"
        app = self.app
        c = self.group(pg, T, "When a download finishes")
        self.toggle(c, T, "popup_done", "Pop-up message", "The 'All done' box (never shown while a queue continues).")
        self.toggle(c, T, "sound_done", "Play a sound")
        self.toggle(c, T, "flash_done", "Flash the taskbar button", "Only when the app isn't the window you're using.")
        self.toggle(c, T, "open_done", "Open the save folder")
        self.toggle(c, T, "sound_err", "Sound when something fails")
        self.buttons(c, T, "Try it", "Plays the finish sound and flashes the taskbar button.",
                     [("Test", lambda: (play_sound("done"), flash_taskbar(app.root)))])
        c = self.group(pg, T, "Starting & closing")
        self.toggle(c, T, "remember_folder", "Skip the folder question", "Start with the folder you used last time "
                                                                         "instead of asking every time.")
        self.toggle(c, T, "confirm_quit", "Ask before quitting mid-download", "Closing while a download runs asks "
                                                                              "first. Finished files are always kept.")

    def build_data(self, pg):
        T = "data"
        app = self.app
        c = self.group(pg, T, "Where things are saved")
        self.buttons(c, T, "Settings, layouts, themes", str(SETTINGS_FILE),
                     [("Open folder", lambda: app.open_path(APP_DIR))])
        if TLOG.path:
            self.buttons(c, T, "Technical logs", str(Path(TLOG.path).parent),
                         [("Open folder", lambda: app.open_path(Path(TLOG.path).parent))])
        c = self.group(pg, T, "Backup")
        self.buttons(c, T, "Export settings", "Everything in one .json file: preferences, themes, saved layouts.",
                     [("Export...", app.export_settings)])
        self.buttons(c, T, "Import settings", "Loads a file made with Export. Applies right away.",
                     [("Import...", app.import_settings)])
        c = self.group(pg, T, "Housekeeping")
        n, size = app.leftover_files()
        self.clean_row = self.buttons(c, T, "Old console & launcher files",
                                      f"{n} files ({size / 1024:.0f} KB) left behind by earlier runs." if n else
                                      "Nothing left behind by earlier runs.",
                                      [("Clean up", self._clean)])
        c = self.group(pg, T, "Reset")
        self.buttons(c, T, "Reset display & animation", "Every setting in this window goes back to its default. "
                                                        "Your layout, themes and downloads aren't touched.",
                     [("Reset", lambda: self._reset(all_ui=True))])
        self.buttons(c, T, "Reset the layout", "Back to the 'Command center' starting layout, everything shown.",
                     [("Reset", lambda: (app.dock.hidden.clear(),
                                         app.apply_preset("Command center (2 columns)"), self.refresh_sections()))])

    def _clean(self):
        if self.app.clean_leftovers():
            self.win.destroy()
            self.app._settings_win = None
            self.app.open_settings("data")

    def _reset(self, all_ui=False, keys=None):
        if all_ui:
            if not messagebox.askyesno("Reset", "Put every setting in this window back to its default?",
                                       parent=self.win):
                return
            keys = [k for k in UI_DEFAULTS]
        self.app.reset_ui(keys or [])
        tab = self.tab
        self.win.destroy()
        self.app._settings_win = None
        self.app.open_settings(tab)

    def reset_page(self):
        page_keys = {"display": ["accent", "glow", "glow_strength", "titlebar_tint", "font", "scale", "density",
                                 "outline", "title_case", "scrollbar", "opacity", "topmost", "hints", "hide_buttons",
                                 "header_icons"],
                     "anim": [k for k in UI_DEFAULTS if k.startswith("anim") or k in ("fps", "fade_ms")],
                     "layout": ["gap", "min_w", "remember_geo", "start_max", "auto_fix", "auto_size", "wheel_scroll",
                                "win_shrink", "layout_h",
                                "sec_scrollbars", "sec_select"],
                     "sections": ["titles"],
                     "panels": ["legend", "pbar_h", "con_font", "con_size", "con_wrap", "con_flood", "con_follow",
                                "log_time", "log_clock", "log_size", "log_max", "con_reconn"],
                     "behaviour": ["popup_done", "sound_done", "flash_done", "open_done", "sound_err",
                                   "remember_folder", "confirm_quit"],
                     "data": []}
        keys = page_keys.get(self.tab, [])
        if keys:
            self._reset(keys=keys)



class App:
    def __init__(self):
        TLOG.open()
        self.install_crash_hooks()
        tlog("app", f"Telegram Media Saver - Fast starting  pid={os.getpid()}")
        tlog("app", f"python={sys.version.split()[0]} exe={sys.executable} platform={sys.platform} "
                    f"script={Path(__file__).resolve()} cwd={os.getcwd()}")
        tlog("app", f"app data={APP_DIR}  tech log={TLOG.path}  engine file={ENGINE_FILE} "
                    f"(exists={ENGINE_FILE.exists()})")
        self.root = tk.Tk()
        self.root.withdraw()
        self.q: queue.Queue = queue.Queue()
        self.settings = load_settings()
        tlog("app", "settings: " + json.dumps(self.settings, ensure_ascii=False))
        UI.clear()
        UI.update(copy.deepcopy(UI_DEFAULTS))
        UI.update({k: v for k, v in (self.settings.get("ui") or {}).items() if k in UI_DEFAULTS})
        global GAP, SECTION_MIN_W
        GAP, SECTION_MIN_W = max(2, int(UI["gap"])), max(240, int(UI["min_w"]))
        self._ui_save_job = None
        self._shim_job = None
        self._settings_win = None
        all_t = self.all_themes()
        self.theme_id = self.settings.get("theme") if self.settings.get("theme") in all_t else DEFAULT_THEME
        PAL.clear()
        PAL.update(ui_palette(all_t[self.theme_id]))
        apply_ttk_theme(self.root)
        self.chats: list[dict] = []
        self.shown: list[int] = []
        self.runner: Runner | None = None
        self.running = False
        self.mon_thread: MonitorThread | None = None
        self.row_ids: dict[str, str] = {}   # row key -> Treeview item id
        self.row_keys: dict[str, str] = {}  # Treeview item id -> row key
        self.row_status: dict[str, str] = {}  # row key -> last status (for the tech log / progress state)
        self.awake = False
        self.job_state: JobState | None = None   # what the current / last job read and did
        self.loaded_save: dict | None = None     # a save file loaded with 'Load save', used by the next Start
        self.current_spec: dict | None = None
        self.queue_items: list[dict] = self.load_queue()
        self.console_seen: collections.deque = collections.deque(maxlen=4000)
        self.console_seen_set: set[str] = set()
        self.last_live_log = 0.0

        last = str(self.settings.get("folder") or "")
        if UI.get("remember_folder") and last and Path(last).is_dir():
            folder = last
        else:
            folder = filedialog.askdirectory(parent=self.root, title="Choose where to save the Telegram media")
        if folder:
            self.settings["folder"] = folder
        if not folder:
            tlog("app", "no save folder chosen - exiting")
            sys.exit(0)
        tlog("app", f"save folder: {folder}")

        self.tdl = find_tdl(self.settings.get("tdl_path", ""))
        self.build_ui(folder)
        self.root.report_callback_exception = self.on_tk_error
        self.status.trace_add("write", lambda *_: tlog("status", self.status.get()))
        try:
            self.root.attributes("-alpha", 0.0 if anim_on("anim_fade") else UI["opacity"] / 100.0)
        except tk.TclError:
            pass
        self.root.deiconify()
        if UI.get("start_max"):
            try:
                self.root.state("zoomed")
            except tk.TclError:
                pass
        dark_title_bar(self.root)
        self.root.after(30, lambda: fade_in(self.root, max(160, int(UI.get("fade_ms", 180)) + 80)))
        self.update_engine_ui()
        self.load_cached_chats()
        if self.builtin():
            self.log("Engine: Built-in (Python/Telethon)")
            if not self.chats:
                self.load_chats()
        elif not self.tdl:
            self.log("tdl wasn't found. Click 'Find tdl.exe...' and point me at it "
                     "(it's usually C:\\tdl\\tdl.exe), or switch Engine to Built-in.", "warn")
            if not self.chats:
                self.status.set("tdl not found - click 'Find tdl.exe...' or pick the Built-in engine.")
        else:
            self.log(f"Using tdl at {self.tdl}")
            if not self.chats:
                self.load_chats()
        self.root.after(100, self.poll)

    # -- layout ------------------------------------------------------------- #
    def make_section(self, parent, title: str, key: str, expand: bool = False, pady=4, extra=None) -> ttk.Frame:
        """
        A bordered section: a title bar you can grab to drag it somewhere else (left / right / above /
        below any other section), an optional row of extra buttons, and a Hide button. Where it sits is
        decided by the Dock, not by this function.
        """
        outer = tk.Frame(parent, highlightthickness=1, bd=0)
        themed(outer, bg="panel", highlightbackground="border", highlightcolor="border")
        hdr = ttk.Frame(outer, style="SectionHdr.TFrame", padding=(8, 5, 6, 5))
        hdr.pack(fill="x")
        grip = ttk.Label(hdr, text="⠿", style="Grip.TLabel", cursor="fleur")
        grip.pack(side="left", padx=(2, 8))
        lbl = ttk.Label(hdr, text=title.strip(), style="SectionTitle.TLabel", cursor="fleur")
        lbl.pack(side="left")
        btn = ttk.Button(hdr, text="Hide", style="Toggle.TButton", command=lambda k=key: self.toggle_section(k))
        btn.pack(side="right")
        if extra:
            extra(hdr)
        rule = tk.Frame(outer, height=1, bd=0, highlightthickness=0)
        themed(rule, bg="line")
        rule.pack(fill="x")

        hv = {"on": False, "p": 0.0, "gen": 0}

        def paint(p):
            hv["p"] = p
            outer.configure(highlightbackground=mix(PAL["border"], PAL["accent"], 0.6 * p))
            rule.configure(bg=mix(self._rule_col(key), PAL["accent"], 0.45 * p))

        def hover(on: bool):
            # the card's frame lights up while the pointer is on its title bar: "you can grab this"
            if on == hv["on"]:
                return
            hv["on"] = on
            hv["gen"] += 1
            gen = hv["gen"]
            try:
                grip.configure(foreground=PAL["accent"] if on else "")
                if not UI.get("glow", True):
                    paint(0.0)
                    return
                a, b = hv["p"], 1.0 if on else 0.0
                if anim_on("anim_hover"):
                    ease_after(outer, 140, lambda e: gen == hv["gen"] and paint(a + (b - a) * e), fps=120)
                else:
                    paint(b)
            except tk.TclError:
                pass

        def leave(_e):
            try:
                w = hdr.winfo_containing(*hdr.winfo_pointerxy())
            except (tk.TclError, KeyError):
                w = None
            if w is None or not str(w).startswith(str(hdr)):
                hover(False)
        hdr.bind("<Enter>", lambda _e: hover(True), add="+")
        hdr.bind("<Leave>", leave, add="+")
        for wdg in (hdr, grip, lbl):
            wdg.bind("<ButtonPress-1>", lambda e, k=key: None if self.dock.edge_press(e)
                     else (hover(False), self.dock._start(k, e)))
            wdg.bind("<B1-Motion>", lambda e: self.dock.edge_motion(e) if self.dock.rs else self.dock._move(e))
            wdg.bind("<ButtonRelease-1>", lambda e: self.dock.edge_release(e) or self.dock._end(e))
        view = tk.Frame(outer, bd=0, highlightthickness=0)
        themed(view, bg="panel")
        view.pack(fill="both", expand=True)
        body = ttk.Frame(view, padding=(12, 10, 12, 12))
        body.place(x=0, y=0, relwidth=1, relheight=1)
        vsb = NeonScrollbar(view, orient="vertical", thickness=10,
                            command=lambda *a, k=key: self._sec_yview(k, *a))
        view.bind("<Configure>", lambda _e, k=key: self._sec_fit(k), add="+")
        self.root.after_idle(lambda: [self.dock.sense(w) for w in (outer, view, body, rule)] and
                             self.dock.sense(hdr, header=True))
        self.sections[key] = {"outer": outer, "body": body, "btn": btn, "title": title.strip(), "expand": expand,
                              "hdr": hdr, "grip": grip, "lbl": lbl, "rule": rule, "view": view, "vsb": vsb,
                              "off": 0, "over": False, "geo": None}
        return body

    def save_graph_cfg(self, cfg: dict):
        self.settings["graph"] = cfg
        mt = getattr(self, "mon_thread", None)
        if mt is not None and hasattr(self, "graph"):
            mt.interval = self.graph.sample_interval()     # a faster graph measures more often
        try:
            save_settings(self.settings)
        except Exception:  # noqa: BLE001
            pass

    def toggle_section(self, key: str):
        if not self.dock.hide(key):
            self.status.set("At least one section has to stay visible.")

    def save_dock(self):
        self.settings["dock"] = self.dock.state()
        self.refresh_chips()
        if self._dock_job is not None:
            try:
                self.root.after_cancel(self._dock_job)
            except (tk.TclError, ValueError):
                pass
        self._dock_job = self.root.after(400, lambda: save_settings(self.settings))

    def refresh_chips(self):
        if not hasattr(self, "chip_frame"):
            return
        for w in self.chip_frame.winfo_children():
            w.destroy()
        for key in list(self.dock.hidden):
            ttk.Button(self.chip_frame, text="+ " + self.section_title(key), style="Toggle.TButton",
                       command=lambda k=key: self.dock.show(k)).pack(side="left", padx=3)

    def apply_preset(self, name: str):
        tree = layout_presets().get(name)
        if tree:
            self.dock.set_tree(tree)
            self.log(f"Layout: {name}", "ok")

    # -- your own named layouts (kept next to the starting layouts in the Layout menu) ------------ #
    def saved_layouts(self) -> dict:
        sv = self.settings.get("saved_layouts")
        if not isinstance(sv, dict):
            sv = self.settings["saved_layouts"] = {}
        return sv

    def build_layout_menu(self):
        m, saved = self.lay_menu, self.saved_layouts()
        m.delete(0, "end")
        m.add_command(label="STARTING LAYOUTS", state="disabled")
        for name in layout_presets():
            m.add_command(label="    " + name, command=lambda n=name: self.apply_preset(n))
        m.add_separator()
        m.add_command(label="YOUR LAYOUTS", state="disabled")
        names = sorted(saved, key=str.lower)
        for name in names:
            m.add_command(label="    ★  " + name, command=lambda n=name: self.apply_saved_layout(n))
        if not names:
            m.add_command(label="    (none yet)", state="disabled")
        m.add_command(label="    +  Save current layout as...", command=self.save_layout_as)
        d = self.lay_del_menu
        d.delete(0, "end")
        for name in names:
            d.add_command(label=name, command=lambda n=name: self.delete_saved_layout(n))
        if names:
            m.add_cascade(label="    ✕  Delete a saved layout", menu=d)
        m.add_separator()
        m.add_command(label="Tidy up gaps between boxes", command=lambda: self.dock.tidy())
        m.add_command(label="Show all hidden sections", command=self.show_all_sections)

    def apply_saved_layout(self, name: str):
        st = self.saved_layouts().get(name)
        if isinstance(st, dict) and isinstance(st.get("rects"), dict):
            self.dock.apply_state(st)
            self.log(f"Layout: {name}", "ok")

    def delete_saved_layout(self, name: str):
        if name not in self.saved_layouts():
            return
        if not messagebox.askyesno("Delete layout", f"Delete your saved layout '{name}'?\n\n"
                                                    "This only removes the saved copy - the window stays as it is.",
                                   parent=self.root):
            return
        self.saved_layouts().pop(name, None)
        save_settings(self.settings)
        self.log(f"Deleted saved layout '{name}'.")

    def save_layout_as(self):
        saved = self.saved_layouts()
        win = tk.Toplevel(self.root)
        win.withdraw()
        win.title("Save layout")
        win.resizable(False, False)
        win.transient(self.root)
        themed(win, bg="panel")
        dark_title_bar(win)
        body = ttk.Frame(win, padding=(22, 18, 22, 18))
        body.pack(fill="both", expand=True)
        ttk.Label(body, text="Save this layout", style="Head.TLabel").pack(anchor="w")
        ttk.Label(body, text="It is added to the Layout menu under 'Your layouts', next to the starting ones.\n"
                             "Where every box sits and which sections are hidden are both saved.",
                  style="Muted.TLabel", justify="left").pack(anchor="w", pady=(4, 12))
        n = 1
        while f"My layout {n}" in saved:
            n += 1
        var = tk.StringVar(value=f"My layout {n}")
        ent = ttk.Entry(body, textvariable=var, width=44, font=("Segoe UI", 11) if IS_WINDOWS else None)
        ent.pack(fill="x", ipady=3)
        note = tk.StringVar(value="")
        ttk.Label(body, textvariable=note, style="Muted.TLabel").pack(anchor="w", pady=(6, 0))
        bar = ttk.Frame(body)
        bar.pack(fill="x", pady=(14, 0))

        def done(*_):
            nm = re.sub(r"\s+", " ", var.get()).strip()[:60]
            if not nm:
                return
            saved[nm] = json.loads(json.dumps(self.dock.state()))
            save_settings(self.settings)
            self.log(f"Saved layout '{nm}' - it's in the Layout menu.", "ok")
            win.destroy()
        ok = ttk.Button(bar, text="Save", style="Accent.TButton", command=done)
        ok.pack(side="right")
        ttk.Button(bar, text="Cancel", command=win.destroy).pack(side="right", padx=(0, 8))

        def check(*_):
            nm = re.sub(r"\s+", " ", var.get()).strip()
            if not nm:
                note.set("Type a name.")
                ok.state(["disabled"])
            elif nm in saved:
                note.set("You already have a layout with this name - saving replaces it.")
                ok.configure(text="Replace")
                ok.state(["!disabled"])
            else:
                note.set("")
                ok.configure(text="Save")
                ok.state(["!disabled"])
        var.trace_add("write", check)
        check()
        win.bind("<Return>", done)
        win.bind("<Escape>", lambda _e: win.destroy())
        win.update_idletasks()
        r = self.root
        x = r.winfo_rootx() + (r.winfo_width() - win.winfo_reqwidth()) // 2
        y = r.winfo_rooty() + (r.winfo_height() - win.winfo_reqheight()) // 3
        win.geometry(f"+{max(0, x)}+{max(0, y)}")
        win.deiconify()
        fade_in(win)
        ent.focus_set()
        ent.select_range(0, "end")
        try:
            win.grab_set()
        except tk.TclError:
            pass
        return win

    def show_all_sections(self):
        for k in list(self.dock.hidden):
            self.dock.show(k)

    def draw_neon(self):
        c = self.neon
        c.delete("all")
        w = c.winfo_width()
        if w < 10:
            return
        if not UI.get("glow", True):
            c.create_rectangle(0, 1, w, 2, outline="", fill=PAL["border"])
            return
        n = max(20, min(160, w // 5))
        expo = 0.3 + 1.5 * max(0.1, min(1.0, float(UI.get("glow_strength", 70)) / 100.0))
        for i in range(n):
            t = i / (n - 1)
            c.create_rectangle(w * i / n, 0, w * (i + 1) / n + 1, 3, outline="",
                               fill=mix(PAL["accent"], PAL["bg"], min(0.96, t ** expo)))

    def build_ui(self, folder: str):
        r = self.root
        r.title("Telegram Media Saver - Fast")
        geo = str(self.settings.get("geometry") or "")
        m = re.fullmatch(r"(\d+)x(\d+)([+-]-?\d+[+-]-?\d+)?", geo)
        sw, sh = r.winfo_screenwidth(), r.winfo_screenheight()
        if m and UI.get("remember_geo", True) and 700 <= int(m.group(1)) <= sw + 40 and 500 <= int(m.group(2)) <= sh + 40:
            r.geometry(geo)
        else:
            r.geometry(f"{min(1560, sw - 80)}x{min(980, sh - 90)}+30+20")
        r.minsize(900, 620)
        r.protocol("WM_DELETE_WINDOW", self.on_close)
        self.sections: dict[str, dict] = {}
        self._dock_job = None
        self._gtags: set[str] = set()
        self._console_lines: list = []
        self.console_mtime: int = 0

        # ---- banner: title, theme + layout buttons, chips for hidden sections --------------------
        top = tk.Frame(r)
        themed(top, bg="bg")
        top.pack(fill="x", padx=14, pady=(10, 0))
        ttk.Label(top, text="TELEGRAM MEDIA SAVER", style="Title.TLabel").pack(side="left")
        self.title_acc_lbl = ttk.Label(top, text="  FAST", style="TitleAccent.TLabel")
        self.title_acc_lbl.pack(side="left")
        self.hint_lbl = ttk.Label(top, text="   drag a title to move it  •  drag the gap between boxes to resize  •  "
                                            "Esc cancels", style="Sub.TLabel")
        self.hint_lbl.pack(side="left", padx=(14, 0), pady=(8, 0))
        right = tk.Frame(top)
        themed(right, bg="bg")
        right.pack(side="right")
        self.chip_frame = tk.Frame(right)
        themed(self.chip_frame, bg="bg")
        self.chip_frame.pack(side="left", padx=(0, 10))
        lay_mb = ttk.Menubutton(right, text="▦  Layout")
        lay_menu = tk.Menu(lay_mb, tearoff=False, bd=0, relief="flat")
        themed(lay_menu, bg="panel2", fg="fg", activebackground="accent", activeforeground="accent_ink",
               disabledforeground="dim")
        self.lay_menu = lay_menu
        self.lay_del_menu = tk.Menu(lay_menu, tearoff=False, bd=0, relief="flat")
        themed(self.lay_del_menu, bg="panel2", fg="fg", activebackground="red", activeforeground="bg")
        lay_menu.configure(postcommand=self.build_layout_menu)
        self.build_layout_menu()
        lay_mb["menu"] = lay_menu
        lay_mb.pack(side="left", padx=(0, 8))
        ttk.Button(right, text="◐  Themes...", command=self.open_theme_studio).pack(side="left")
        ttk.Button(right, text="⚙  Settings", command=self.open_settings).pack(side="left", padx=(8, 0))
        r.bind("<Control-comma>", lambda _e: self.open_settings())
        self.neon = tk.Canvas(r, height=3, highlightthickness=0, bd=0)
        themed(self.neon, bg="bg")
        self.neon.pack(fill="x", padx=14, pady=(9, 8))
        self.neon.bind("<Configure>", lambda _e: self.draw_neon())
        THEME_HOOKS.append(self.draw_neon)

        self.area = tk.Frame(r)
        themed(self.area, bg="bg")
        self.area.pack(fill="both", expand=True, padx=12, pady=(0, 12))
        main = self.area

        f1 = self.make_section(main, "Save location", "save_loc", expand=False)
        self.save_var = tk.StringVar(value=folder)
        self.ref_var = tk.StringVar(value=str(self.settings.get("ref_folder") or ""))
        r1_save = ttk.Frame(f1)
        r1_save.pack(fill="x")
        ttk.Label(r1_save, text="Save new files to:", width=20).pack(side="left")
        ttk.Entry(r1_save, textvariable=self.save_var, state="readonly").pack(side="left", fill="x", expand=True)
        self.change_btn = ttk.Button(r1_save, text="Change...", command=self.pick_folder)
        self.change_btn.pack(side="left", padx=(8, 0))
        self.open_btn = ttk.Button(r1_save, text="Open folder", command=self.open_folder)
        self.open_btn.pack(side="left", padx=(8, 0))

        r1_ref = ttk.Frame(f1)
        r1_ref.pack(fill="x", pady=(5, 0))
        ttk.Label(r1_ref, text="Reference folder (skip):", width=20).pack(side="left")
        self.ref_entry = ttk.Entry(r1_ref, textvariable=self.ref_var)
        self.ref_entry.pack(side="left", fill="x", expand=True)
        self.ref_browse_btn = ttk.Button(r1_ref, text="Browse...", command=self.pick_ref_folder)
        self.ref_browse_btn.pack(side="left", padx=(8, 0))
        self.ref_clear_btn = ttk.Button(r1_ref, text="Clear", command=self.clear_ref_folder)
        self.ref_clear_btn.pack(side="left", padx=(8, 0))
        hint = ttk.Label(
            f1,
            text="Optional: point 'Reference folder' to an earlier folder (e.g. on another drive) so anything already "
                 "in that folder is skipped without downloading duplicates. Separate multiple folders with ;",
            style="Muted.TLabel", wraplength=500, justify="left")
        hint.pack(anchor="w", pady=(4, 0), fill="x")
        autowrap(hint)

        f2 = self.make_section(main, "What do you want to save?", "what_save", expand=False)
        self.vars: dict[str, tk.BooleanVar] = {}
        self.cbs: dict[str, ttk.Checkbutton] = {}
        for key, label in CATEGORIES:
            self.vars[key] = tk.BooleanVar(value=False)
            self.cbs[key] = ttk.Checkbutton(f2, text=label, variable=self.vars[key])
        self.every = tk.BooleanVar(value=False)
        self.every_cb = ttk.Checkbutton(f2, text="Everything", variable=self.every, command=self.on_everything)
        flow(f2, list(self.cbs.values()) + [self.every_cb], gap=14)  # wraps onto more rows in a narrow panel

        f3 = self.make_section(main, "Which conversation?", "which_conv", expand=True)
        row = ttk.Frame(f3)
        row.pack(fill="x")
        ttk.Label(row, text="Search").pack(side="left")
        self.search_var = tk.StringVar()
        self.search_var.trace_add("write", lambda *_: self.refresh_list())
        self.search_entry = ttk.Entry(row, textvariable=self.search_var)
        self.search_entry.pack(side="left", fill="x", expand=True, padx=8)
        self.reload_btn = ttk.Button(row, text="Reload list", command=self.load_chats)
        self.reload_btn.pack(side="left")
        lbf = ttk.Frame(f3)
        lbf.pack(fill="both", expand=True, pady=(6, 0))
        self.chat_list = tk.Listbox(lbf, exportselection=False, height=2)
        dark_tk_widget(self.chat_list, "list")
        self.chat_list.bind("<<ListboxSelect>>", lambda *_: self.update_topic_filter_ui())
        sb = NeonScrollbar(lbf, orient="vertical", command=self.chat_list.yview)
        self.chat_list.configure(yscrollcommand=sb.set)
        self.chat_list.pack(side="left", fill="both", expand=True)
        sb.pack(side="left", fill="y", padx=(4, 0))

        tflt = ttk.Frame(f3)
        tflt.pack(fill="x", pady=(6, 0))
        self.topic_inc_var = tk.StringVar(value=str(self.settings.get("topic_include", "")))
        self.topic_exc_var = tk.StringVar(value=str(self.settings.get("topic_exclude", "")))
        self.topic_inc_var.trace_add("write", lambda *_: self.update_topic_filter_ui())
        self.topic_exc_var.trace_add("write", lambda *_: self.update_topic_filter_ui())
        ttk.Label(tflt, text="Include topics").grid(row=0, column=0, sticky="w")
        self.topic_inc_entry = ttk.Entry(tflt, textvariable=self.topic_inc_var)
        self.topic_inc_entry.grid(row=0, column=1, sticky="ew", padx=(6, 10))
        ttk.Label(tflt, text="Exclude topics").grid(row=1, column=0, sticky="w", pady=(4, 0))
        self.topic_exc_entry = ttk.Entry(tflt, textvariable=self.topic_exc_var)
        self.topic_exc_entry.grid(row=1, column=1, sticky="ew", padx=(6, 10), pady=(4, 0))
        self.preview_topics_btn = ttk.Button(tflt, text="Preview topics / Verify...", command=self.preview_topics)
        self.preview_topics_btn.grid(row=0, column=2, rowspan=2, sticky="e")
        tflt.columnconfigure(1, weight=1)
        self.topic_filter_var = tk.StringVar(
            value='Forum topic filter:  "house " + num   |   "house " + word   |   "house " + *   |   "house " + * + *   (; for multiple)'
        )
        self.topic_filter_lbl = ttk.Label(f3, textvariable=self.topic_filter_var, style="Muted.TLabel",
                                          wraplength=500, justify="left")
        self.topic_filter_lbl.pack(anchor="w", pady=(4, 0), fill="x")
        autowrap(self.topic_filter_lbl)
        acc = ttk.Frame(f3)
        acc.pack(fill="x", pady=(6, 0))
        self.engine_var = tk.StringVar(value=self.settings.get("engine", "tdl"))
        eng_lbl = ttk.Label(acc, text="Engine")
        self.eng_tdl_rb = ttk.Radiobutton(acc, text="tdl", value="tdl", variable=self.engine_var,
                                          command=self.on_engine)
        self.eng_py_rb = ttk.Radiobutton(acc, text="Built-in (Python)", value="builtin",
                                         variable=self.engine_var, command=self.on_engine)
        self.find_btn = ttk.Button(acc, text="Find tdl.exe...", command=self.pick_tdl)
        self.login_desk_btn = ttk.Button(acc, text="Log in (use Telegram Desktop)",
                                         command=lambda: self.login(["login"]))
        self.login_code_btn = ttk.Button(acc, text="Log in (phone + code)",
                                         command=lambda: self.login(["login", "-T", "code"]))
        flow(acc, [eng_lbl, self.eng_tdl_rb, self.eng_py_rb, self.find_btn, self.login_desk_btn,
                   self.login_code_btn])

        f4 = self.make_section(main, "Speed & safety", "speed_safety", expand=False)
        self.threads_var = tk.IntVar(value=int(self.settings.get("threads", 4)))
        self.limit_var = tk.IntVar(value=int(self.settings.get("limit", 2)))
        self.auto_speed_var = tk.BooleanVar(value=bool(self.settings.get("auto_speed", True)))
        self.takeout_var = tk.BooleanVar(value=bool(self.settings.get("takeout", False)))
        self.awake_var = tk.BooleanVar(value=bool(self.settings.get("keep_awake", True)))
        self.reuse_var = tk.BooleanVar(value=False)
        ttk.Label(f4, text="Connections per file").grid(row=0, column=0, sticky="w")
        self.threads_sp = ttk.Spinbox(f4, from_=1, to=16, width=4, textvariable=self.threads_var)
        self.threads_sp.grid(row=0, column=1, sticky="w", padx=8)
        ttk.Label(f4, text="Files at the same time").grid(row=1, column=0, sticky="w", pady=(4, 0))
        self.limit_sp = ttk.Spinbox(f4, from_=1, to=MAX_FILES_AT_ONCE, width=4, textvariable=self.limit_var)
        self.limit_sp.grid(row=1, column=1, sticky="w", padx=8, pady=(4, 0))
        self.apply_btn = ttk.Button(f4, text="Apply now", command=self.on_apply_speed)
        self.apply_btn.grid(row=0, column=2, rowspan=2, sticky="e", padx=(12, 0))
        self.apply_btn.state(["disabled"])
        f4.columnconfigure(2, weight=1)
        sp_hint = ttk.Label(f4, style="Muted.TLabel", justify="left", wraplength=400,
                            text="Connections: 4 = default; higher = big files faster, but more 'slow down' waits.   "
                                 "Files at once: 2 = default; higher helps chats with lots of small files.")
        sp_hint.grid(row=2, column=0, columnspan=3, sticky="we", pady=(4, 0))
        autowrap(sp_hint)
        self.auto_speed_cb = ttk.Checkbutton(
            f4, variable=self.auto_speed_var, command=self.on_auto_speed_toggle,
            text="Auto-tune speed by file size")
        self.auto_speed_cb.grid(row=3, column=0, columnspan=3, sticky="w", pady=(6, 0))
        tiers = ttk.Label(f4, style="Muted.TLabel", justify="left", wraplength=400,
                          text="<25 MB: 3x12  |  25-100: 4x10  |  100-350: 6x8  |  350+: 8x6")
        tiers.grid(row=4, column=0, columnspan=3, sticky="w", padx=(24, 0))
        self.takeout_cb = ttk.Checkbutton(
            f4, variable=self.takeout_var,
            text="Use Telegram's official export (takeout) mode - gentler rate limits")
        self.takeout_cb.grid(row=5, column=0, columnspan=3, sticky="w")
        self.awake_cb = ttk.Checkbutton(f4, variable=self.awake_var,
                                        text="Keep the PC from going to sleep while downloading")
        self.awake_cb.grid(row=6, column=0, columnspan=3, sticky="w")
        self.reuse_cb = ttk.Checkbutton(
            f4, variable=self.reuse_var,
            text="After a crash: reuse last time's message list (skips the rescan)")
        self.reuse_cb.grid(row=7, column=0, columnspan=3, sticky="w")

        # queue: more jobs (any chat, or the same chat with other types / topics / folder)
        fq = self.make_section(main, "Queue", "queue", expand=True)
        qlf = ttk.Frame(fq)
        qlf.pack(fill="both", expand=True)
        self.queue_list = tk.Listbox(qlf, exportselection=False, height=2)
        dark_tk_widget(self.queue_list, "list")
        self.queue_list.bind("<Double-Button-1>", lambda _e: self.edit_queue_item())
        qsb = NeonScrollbar(qlf, orient="vertical", command=self.queue_list.yview)
        self.queue_list.configure(yscrollcommand=qsb.set)
        self.queue_list.pack(side="left", fill="both", expand=True)
        qsb.pack(side="left", fill="y", padx=(4, 0))
        qb = ttk.Frame(fq)
        qb.pack(fill="x", pady=(8, 0))
        q_btns = [ttk.Button(qb, text="Add to queue...", command=self.open_queue_dialog),
                  ttk.Button(qb, text="Edit...", command=self.edit_queue_item),
                  ttk.Button(qb, text="Remove", command=self.remove_queue_item),
                  ttk.Button(qb, text="Move up", command=lambda: self.move_queue_item(-1)),
                  ttk.Button(qb, text="Move down", command=lambda: self.move_queue_item(1)),
                  ttk.Button(qb, text="Clear", command=self.clear_queue)]
        self.queue_start_btn = ttk.Button(qb, text="Start queue now", command=self.start_next_in_queue)
        flow(qb, q_btns + [self.queue_start_btn])
        self.queue_info_var = tk.StringVar()
        ttk.Label(fq, textvariable=self.queue_info_var, style="Muted.TLabel").pack(anchor="w", pady=(2, 0))

        # controls: start / pause / stop + the status line
        fc = self.make_section(main, "Controls", "controls", expand=False)
        bar = ttk.Frame(fc)
        bar.pack(fill="x")
        self.start_btn = ttk.Button(bar, text="▶  Start download", style="Accent.TButton", command=self.on_start)
        self.start_btn.state(["disabled"])
        self.pause_btn = ttk.Button(bar, text="Pause", command=self.on_pause)
        self.pause_btn.state(["disabled"])
        self.stop_btn = ttk.Button(bar, text="Stop", command=self.on_stop)
        self.stop_btn.state(["disabled"])
        self.load_save_btn = ttk.Button(bar, text="Load save", command=self.load_save_dialog)
        self.save_btn = ttk.Button(bar, text="Save", command=self.save_progress)
        self.verify_bar_btn = ttk.Button(bar, text="Verify / Topics...", command=self.preview_topics)
        self.dedup_bar_btn = ttk.Button(bar, text="Clean duplicates...", command=self.clean_duplicates_dialog)
        self.techlog_btn = ttk.Button(bar, text="Open tech log", style="Toggle.TButton", command=self.open_tech_log)
        flow(bar, [self.start_btn, self.pause_btn, self.stop_btn, self.load_save_btn, self.save_btn,
                   self.verify_bar_btn, self.dedup_bar_btn, self.techlog_btn])
        self.status = tk.StringVar(value="Loading your chats from tdl ...")
        st_lbl = ttk.Label(fc, textvariable=self.status, style="Muted.TLabel", wraplength=500, justify="left")
        st_lbl.pack(anchor="w", fill="x", pady=(2, 0))
        autowrap(st_lbl)

        # live tdl / console mirror panel
        con = self.make_section(
            main, "tdl / Console live view", "tdl_console", expand=True,
            extra=lambda h: ttk.Button(h, text="Open in editor", style="Toggle.TButton",
                                       command=self.open_console_log).pack(side="right", padx=(0, 6)))
        con_top = ttk.Frame(con)
        con_top.pack(fill="x", pady=(0, 4))
        self.console_title_var = tk.StringVar(value="Mirrors everything shown in the tdl / console window in real time.")
        ct_lbl = ttk.Label(con_top, textvariable=self.console_title_var, style="Muted.TLabel")
        ct_lbl.pack(side="left")
        ttk.Button(con_top, text="Jump to bottom", style="Toggle.TButton", command=self.jump_console_bottom).pack(side="right")
        ctf = ttk.Frame(con)
        ctf.pack(fill="both", expand=True)
        self.console_text = tk.Text(
            ctf, height=3, state="disabled", wrap="none",
            font=("Consolas", 10) if IS_WINDOWS else ("Monospace", 10))
        dark_tk_widget(self.console_text, "text")
        for col_idx, pal_key in CONSOLE_KEY.items():
            themed_tag(self.console_text, f"c{col_idx}", foreground=pal_key)
        for kind, pal_key in (("ok", "green"), ("warn", "orange"), ("err", "red"), ("busy", "yellow"), ("info", "fg")):
            themed_tag(self.console_text, f"k_{kind}", foreground=pal_key)
        themed_tag(self.console_text, "k_pill", foreground="bg", background="orange")
        themed_tag(self.console_text, "k_rcpill", foreground="bg", background="blue")
        themed_tag(self.console_text, "k_dim", foreground="border")
        self.console_text.tag_configure("k_pill", font=("Consolas", 10, "bold") if IS_WINDOWS else ("Monospace", 10, "bold"))
        csb_y = NeonScrollbar(ctf, orient="vertical", command=self.console_text.yview)
        csb_x = NeonScrollbar(con, orient="horizontal", command=self.console_text.xview, thickness=14)
        self.console_text.configure(yscrollcommand=csb_y.set, xscrollcommand=csb_x.set)
        self.console_text.pack(side="left", fill="both", expand=True)
        csb_y.pack(side="left", fill="y", padx=(4, 0))
        csb_x.pack(fill="x", pady=(4, 0))

        # live download panel
        live = self.make_section(main, "Live download", "live_dl", expand=True)
        stats = ttk.Frame(live)
        stats.pack(fill="x")
        self.speed_var = tk.StringVar(value="-")
        self.active_var = tk.StringVar(value="Downloading now: -")
        self.done_var = tk.StringVar(value="Finished: -")
        self.err_var = tk.StringVar(value="")
        self.jump_btn = ttk.Button(stats, text="Jump to latest", style="Toggle.TButton", command=self.jump_latest)
        self.jump_btn.pack(side="right")
        ttk.Label(stats, textvariable=self.speed_var, style="Speed.TLabel", width=12).pack(side="left")
        ttk.Label(stats, textvariable=self.active_var).pack(side="left", padx=(6, 18))
        ttk.Label(stats, textvariable=self.done_var).pack(side="left")
        ttk.Label(stats, textvariable=self.err_var, style="Err.TLabel").pack(side="left", padx=(18, 0))
        eta_row = ttk.Frame(live)
        eta_row.pack(fill="x", pady=(4, 0))
        self.eta_var = tk.StringVar(value="ETA: -")
        self.eta_all_var = tk.StringVar(value="")
        self.eta_label = ttk.Label(eta_row, textvariable=self.eta_var, style="Eta.TLabel")
        self.eta_label.pack(side="left")
        ttk.Label(eta_row, textvariable=self.eta_all_var, style="Muted.TLabel").pack(side="left", padx=(18, 0))
        self.pbar = NeonBar(live, height=14, maximum=1, value=0)
        self.pbar.pack(fill="x", pady=(6, 6))
        tf = ttk.Frame(live)
        tf.pack(fill="both", expand=True)
        self.files_frame = tf
        cols = ("file", "type", "progress", "speed", "eta")
        self.files = ttk.Treeview(tf, columns=cols, show="headings", height=2)
        for c, text, w, anchor in (("file", "File", 260, "w"), ("type", "Type", 100, "w"),
                                   ("progress", "Status", 260, "w"), ("speed", "Speed", 95, "e"),
                                   ("eta", "ETA", 80, "e")):
            self.files.heading(c, text=text, anchor=anchor)
            self.files.column(c, width=w, anchor=anchor, stretch=(c in ("file", "progress")))
        themed_tag(self.files, "done", foreground="green")
        themed_tag(self.files, "error", foreground="red")
        themed_tag(self.files, "stalled", foreground="orange")
        themed_tag(self.files, "paused", foreground="blue")
        themed_tag(self.files, "active", foreground="yellow")
        fsb = NeonScrollbar(tf, orient="vertical", command=self.files.yview)
        self.files.configure(yscrollcommand=fsb.set)
        self.files.pack(side="left", fill="both", expand=True)
        fsb.pack(side="left", fill="y", padx=(4, 0))
        legend = ttk.Label(live, style="Muted.TLabel", wraplength=500, justify="left",
                           text="Yellow = downloading   Green = done   Orange = waiting on Telegram   "
                                "Red = failed (retried on next Start)   Scroll up to look back; "
                                "'Jump to latest' to follow again.")
        legend.pack(anchor="w", pady=(4, 0), fill="x")
        autowrap(legend)
        self.legend_lbl = legend

        gbody = self.make_section(main, "Download graphs", "speed_graph", expand=True)
        self.graph = GraphPanel(gbody, self.settings.get("graph"), self.save_graph_cfg)
        self.graph.pack(fill="both", expand=True)

        lf = self.make_section(
            main, "Activity log", "activity_log", expand=True,
            extra=lambda h: ttk.Button(h, text="Open in editor", style="Toggle.TButton",
                                       command=self.open_activity_log).pack(side="right", padx=(0, 6)))
        lbody = ttk.Frame(lf)
        lbody.pack(fill="both", expand=True)
        self.log_text = tk.Text(lbody, height=2, state="disabled", wrap="word")
        dark_tk_widget(self.log_text, "text")
        for tag, key in (("ok", "green"), ("warn", "orange"), ("err", "red"), ("time", "muted")):
            themed_tag(self.log_text, tag, foreground=key)
        lsb = NeonScrollbar(lbody, orient="vertical", command=self.log_text.yview)
        self.log_text.configure(yscrollcommand=lsb.set)
        self.log_text.pack(side="left", fill="both", expand=True)
        lsb.pack(side="left", fill="y", padx=(4, 0))

        presets = layout_presets()
        d = self.settings.get("dock") or {}
        self.dock = Dock(self, self.area, self.sections,
                         d if d.get("rects") else (d.get("tree") or presets["Command center (2 columns)"]),
                         d.get("hidden") or {})
        self.dock.render()
        self.root.bind_all("<MouseWheel>", self.on_wheel, add="+")
        self.root.bind_all("<ButtonPress-1>", self._click_select, add="+")
        self.sel_section = None
        self.root.after(400, self._sec_poll)
        self.refresh_chips()
        self.refresh_queue_list()
        self.apply_ui()
        if TLOG.path:
            self.log(f"Technical log for this session: {TLOG.path}")

    # -- themes ------------------------------------------------------------- #
    def all_themes(self) -> dict:
        out = dict(THEMES)
        for name, core in (self.settings.get("custom_themes") or {}).items():
            if isinstance(core, dict) and all(is_hex(core.get(k)) for k, _ in CORE_KEYS):
                out["custom:" + str(name)] = finish_theme(core, str(name))
                THEME_GROUP["custom:" + str(name)] = "custom"
        return out

    def set_theme(self, th: dict, tid: str | None = None, persist: bool = False):
        if persist and tid not in (None, "preview") and anim_on("anim_theme") and not getattr(self, "_dipping", False):
            def now():
                self._dipping = True        # the real switch, half-way through the dip (no second dip)
                try:
                    self.set_theme(th, tid, persist)
                finally:
                    self._dipping = False
            self._dip(now)
            return
        PAL.clear()
        PAL.update(ui_palette(th))
        apply_ttk_theme(self.root)
        retheme_widgets()
        run_theme_hooks()
        self.after_theme()
        if tid is not None:
            self.theme_id = tid
        if persist and tid not in (None, "preview"):
            self.settings["theme"] = tid
            save_settings(self.settings)

    def after_theme(self):
        if hasattr(self, "sections"):
            self._mark_selected()
        if hasattr(self, "console_text"):
            for g in list(self._gtags):
                try:
                    self.console_text.tag_delete(g)
                except tk.TclError:
                    pass
            self._gtags.clear()
            self.render_console()

    def open_theme_studio(self):
        old = getattr(self, "_studio", None)
        try:
            if old is not None and old.winfo_exists():
                old.lift()
                old.focus_force()
                return
        except tk.TclError:
            pass
        win = tk.Toplevel(self.root)
        self._studio = win
        win.title("Themes - pick one or build your own")
        win.geometry("1180x800")
        win.minsize(1000, 680)
        themed(win, bg="panel")
        dark_title_bar(win)
        nb = ttk.Notebook(win)
        nb.pack(fill="both", expand=True, padx=10, pady=10)

        # ---------------- gallery ----------------
        gal = ttk.Frame(nb)
        nb.add(gal, text="  Gallery  ")
        gc = tk.Canvas(gal, highlightthickness=0, bd=0)
        themed(gc, bg="panel")
        gsb = NeonScrollbar(gal, orient="vertical", command=gc.yview, thickness=18)
        gc.configure(yscrollcommand=gsb.set)
        gsb.pack(side="right", fill="y")
        gc.pack(side="left", fill="both", expand=True)
        inner = ttk.Frame(gc)
        gwin = gc.create_window(0, 0, window=inner, anchor="nw")
        inner.bind("<Configure>", lambda _e: gc.configure(scrollregion=gc.bbox("all")))
        gc.bind("<Configure>", lambda e: gc.itemconfigure(gwin, width=e.width))
        cards: dict[str, tuple] = {}

        def mark():
            for tid, (f, th) in cards.items():
                try:
                    f.configure(highlightbackground=th["accent"] if tid == self.theme_id else th["line2"],
                                highlightthickness=3 if tid == self.theme_id else 2)
                except tk.TclError:
                    pass

        def pick(tid):
            th = self.all_themes().get(tid)
            if th:
                self.set_theme(th, tid, persist=True)
                mark()
                load_editor_from(th)

        def make_card(parent, tid, th, r, c):
            sel = tid == self.theme_id
            f = tk.Frame(parent, bg=th["bg"], highlightthickness=3 if sel else 2, cursor="hand2",
                         highlightbackground=th["accent"] if sel else th["line2"])
            cv = tk.Canvas(f, width=228, height=62, bg=th["bg"], highlightthickness=0, cursor="hand2")
            cv.create_rectangle(6, 6, 148, 56, fill=th["panel"], outline=th["line2"])
            cv.create_rectangle(7, 7, 147, 17, fill=th["panel2"], outline="")
            cv.create_rectangle(12, 26, 54, 38, fill=th["accent"], outline="")
            cv.create_rectangle(60, 27, 118, 31, fill=th["ink"], outline="")
            cv.create_rectangle(60, 34, 100, 37, fill=th["muted"], outline="")
            cv.create_rectangle(12, 45, 142, 50, fill=th["raised"], outline="")
            cv.create_rectangle(12, 45, 92, 50, fill=th["accent"], outline="")
            for i, key in enumerate(("ok", "busy", "warn", "err")):
                cv.create_oval(160, 8 + i * 13, 170, 18 + i * 13, fill=th[key], outline="")
            cv.create_rectangle(184, 8, 220, 56, fill=th["raised"], outline=th["line2"])
            cv.create_text(202, 32, text="Aa", fill=th["ink"], font=("Segoe UI", 12, "bold"))
            lab = tk.Label(f, text=th["n"], bg=th["bg"], fg=th["ink"], anchor="w", padx=8, pady=5,
                           font=("Segoe UI", 10, "bold"), cursor="hand2")
            cv.pack()
            lab.pack(fill="x")
            for wdg in (f, cv, lab):
                wdg.bind("<Button-1>", lambda _e, t=tid: pick(t))
            f.grid(row=r, column=c, padx=7, pady=7, sticky="n")
            cards[tid] = (f, th)

        def fill_gallery():
            for w in inner.winfo_children():
                w.destroy()
            cards.clear()
            allt = self.all_themes()
            row = 0
            for grp, head in (("classic", "Classic themes  -  17 well-known dark colour schemes"),
                              ("qd", "QD-OLED themes  -  true-black backgrounds so the pixels switch off and the accents glow"),
                              ("custom", "My themes")):
                ids = [t for t in allt if THEME_GROUP.get(t) == grp]
                if not ids:
                    continue
                ttk.Label(inner, text=head, style="Eta.TLabel").grid(row=row, column=0, columnspan=4, sticky="w",
                                                                      padx=8, pady=(12, 2))
                row += 1
                for i, tid in enumerate(ids):
                    make_card(inner, tid, allt[tid], row + i // 4, i % 4)
                row += (len(ids) + 3) // 4
        fill_gallery()

        # ---------------- create your own ----------------
        ed = ttk.Frame(nb, padding=12)
        nb.add(ed, text="  Create your own  ")
        edit = core_of(self.all_themes().get(self.theme_id) or THEMES[DEFAULT_THEME])
        sel = {"k": "accent"}
        left = ttk.Frame(ed)
        left.pack(side="left", fill="y")
        ttk.Label(left, text="1.  Pick what to colour", style="Eta.TLabel").pack(anchor="w", pady=(0, 6))
        rows: dict[str, tuple] = {}
        hex_v = tk.StringVar()
        name_v = tk.StringVar(value="My theme")
        pending = [False]

        def mark_rows():
            for k, (rw, sw_, hl) in rows.items():
                try:
                    rw.configure(highlightbackground=PAL["accent"] if k == sel["k"] else PAL["panel"])
                    sw_.configure(bg=edit[k])
                    hl.configure(text=edit[k].upper())
                except tk.TclError:
                    pass

        def choose(k):
            sel["k"] = k
            wheel.set_color(edit[k])
            hex_v.set(edit[k].upper())
            mark_rows()

        for key, label in CORE_KEYS:
            rw = tk.Frame(left, highlightthickness=2, cursor="hand2")
            themed(rw, bg="panel", highlightbackground="panel")
            sw_ = tk.Frame(rw, width=34, height=22, bg=edit[key], highlightthickness=1, cursor="hand2")
            themed(sw_, highlightbackground="fg")
            sw_.pack(side="left", padx=(6, 8), pady=4)
            sw_.pack_propagate(False)
            tl = ttk.Label(rw, text=label, width=20, cursor="hand2")
            tl.pack(side="left")
            hl = ttk.Label(rw, text=edit[key].upper(), style="Muted.TLabel", cursor="hand2")
            hl.pack(side="left", padx=(4, 8))
            rw.pack(fill="x", pady=1)
            for wdg in (rw, sw_, tl, hl):
                wdg.bind("<Button-1>", lambda _e, k=key: choose(k))
            rows[key] = (rw, sw_, hl)

        mid = ttk.Frame(ed)
        mid.pack(side="left", padx=26, anchor="n")
        ttk.Label(mid, text="2.  Drag on the wheel", style="Eta.TLabel").pack(anchor="w", pady=(0, 6))

        def apply_now():
            pending[0] = False
            th = finish_theme(dict(edit), name_v.get().strip() or "Custom")
            self.set_theme(th, "preview", persist=False)
            mark_rows()
            render_sample()

        def apply_soon():
            if not pending[0]:
                pending[0] = True
                win.after(45, apply_now)

        def on_wheel(hx):
            edit[sel["k"]] = hx
            hex_v.set(hx.upper())
            apply_soon()
        wheel = ColorWheel(mid, size=240, command=on_wheel)
        wheel.pack()
        hr = ttk.Frame(mid)
        hr.pack(fill="x", pady=(10, 0))
        ttk.Label(hr, text="Hex").pack(side="left")
        hex_e = ttk.Entry(hr, textvariable=hex_v, width=10)
        hex_e.pack(side="left", padx=8)

        def on_hex(_e=None):
            v = hex_v.get().strip()
            if re.fullmatch(r"[0-9a-fA-F]{6}", v):
                v = "#" + v
            if is_hex(v):
                edit[sel["k"]] = v.lower()
                wheel.set_color(v)
                apply_now()
        hex_e.bind("<Return>", on_hex)
        hex_e.bind("<FocusOut>", on_hex)

        right = ttk.Frame(ed)
        right.pack(side="left", fill="both", expand=True)
        ttk.Label(right, text="3.  Randomise, then save", style="Eta.TLabel").pack(anchor="w", pady=(0, 6))
        last = {"i": -1}

        def load_editor_from(th):
            edit.update(core_of(th))
            name_v.set(th["n"] if not str(th["n"]).startswith("My theme") else "My theme")
            choose(sel["k"])

        def rand():
            i = random.randrange(len(RANDOM_POOL))
            while len(RANDOM_POOL) > 1 and i == last["i"]:
                i = random.randrange(len(RANDOM_POOL))
            last["i"] = i
            th = RANDOM_POOL[i]
            edit.update(core_of(th))
            name_v.set(th["n"])
            choose(sel["k"])
            apply_now()
        ttk.Button(right, text="⚄  Random Theme", style="Accent.TButton", command=rand).pack(fill="x")
        ttk.Label(right, text="Loads one of the hand-built dark themes below into the editor - "
                              "tweak any colour, then save it.", style="Muted.TLabel", wraplength=300,
                  justify="left").pack(anchor="w", pady=(4, 12))
        nr = ttk.Frame(right)
        nr.pack(fill="x")
        ttk.Label(nr, text="Name").pack(side="left")
        ttk.Entry(nr, textvariable=name_v).pack(side="left", fill="x", expand=True, padx=(8, 0))

        def refill_saved():
            lb.delete(0, "end")
            for n in sorted((self.settings.get("custom_themes") or {}), key=str.lower):
                lb.insert("end", n)

        def save():
            name = name_v.get().strip()
            if not name:
                messagebox.showinfo("Name it", "Give your theme a name first.", parent=win)
                return
            self.settings.setdefault("custom_themes", {})[name] = dict(edit)
            tid = "custom:" + name
            self.set_theme(finish_theme(dict(edit), name), tid, persist=True)
            self.log(f"Saved theme '{name}'.", "ok")
            fill_gallery()
            refill_saved()
            mark()

        def delete():
            s = lb.curselection()
            if not s:
                return
            name = lb.get(s[0])
            if not messagebox.askyesno("Delete theme", f"Delete your theme '{name}'?", parent=win):
                return
            (self.settings.get("custom_themes") or {}).pop(name, None)
            THEME_GROUP.pop("custom:" + name, None)
            if self.theme_id == "custom:" + name:
                self.set_theme(THEMES[DEFAULT_THEME], DEFAULT_THEME, persist=True)
            else:
                save_settings(self.settings)
            fill_gallery()
            refill_saved()
        br = ttk.Frame(right)
        br.pack(fill="x", pady=(8, 8))
        ttk.Button(br, text="Save theme", command=save).pack(side="left")
        ttk.Button(br, text="Delete selected", command=delete).pack(side="left", padx=8)
        ttk.Label(right, text="My saved themes", style="Muted.TLabel").pack(anchor="w")
        lf_ = ttk.Frame(right)
        lf_.pack(fill="both", expand=True, pady=(2, 8))
        lb = tk.Listbox(lf_, exportselection=False, height=4)
        dark_tk_widget(lb, "list")
        lsb_ = NeonScrollbar(lf_, orient="vertical", command=lb.yview)
        lb.configure(yscrollcommand=lsb_.set)
        lb.pack(side="left", fill="both", expand=True)
        lsb_.pack(side="left", fill="y", padx=(4, 0))

        def on_saved(_e=None):
            s = lb.curselection()
            if s:
                th = self.all_themes().get("custom:" + lb.get(s[0]))
                if th:
                    load_editor_from(th)
                    apply_now()
        lb.bind("<<ListboxSelect>>", on_saved)
        refill_saved()

        ttk.Label(right, text="Preview", style="Muted.TLabel").pack(anchor="w")
        sample = tk.Text(right, height=9, state="disabled", wrap="none",
                         font=("Consolas", 10) if IS_WINDOWS else ("Monospace", 10))
        dark_tk_widget(sample, "text")
        sample.pack(fill="x", pady=(2, 0))
        sample_tags: set[str] = set()
        for _tag, _key in (("k_ok", "green"), ("k_warn", "orange"), ("k_err", "red"), ("k_busy", "yellow"),
                           ("k_info", "fg")):
            themed_tag(sample, _tag, foreground=_key)

        def render_sample():
            for g in list(sample_tags):
                try:
                    sample.tag_delete(g)
                except tk.TclError:
                    pass
            sample_tags.clear()
            sample.configure(state="normal")
            sample.delete("1.0", "end")
            lines = [("k_info", "Connections: 8   pieces at once per file: 4   files at once: 2"),
                     ("k_ok", "done!  1204_5531_holiday.mp4  42.1 MB  6.2 MB/s   [31/80]"),
                     ("k_warn", "Telegram asked us to slow down: a wait of 12s is required"),
                     ("k_err", "1204_5532_clip.mov error: FileReferenceExpiredError"),
                     ("k_busy", "downloading  1204_5533_big_file.mkv  1.4 GB")]
            for tag, txt in lines:
                sample.insert("end", txt + "\n", (tag,))
            for p in (0.07, 0.46, 0.83):
                txt = f"1204_5533_big_file.mkv... [{'#' * int(p * 20):.<20}] {p * 100:.1f}% [{p * 1400:.0f} MB; 5.1 MB/s]"
                for seg, col in gradient_runs(txt, p, PAL["well"]):
                    name = "g" + col[1:]
                    if name not in sample_tags:
                        sample.tag_configure(name, foreground=col)
                        sample_tags.add(name)
                    sample.insert("end", seg, (name,))
                sample.insert("end", "\n")
            sample.configure(state="disabled")

        def on_wheel_scroll(e):
            try:
                if nb.index("current") == 0:
                    gc.yview_scroll(-int(e.delta / 120) * 2, "units")
            except tk.TclError:
                pass
        win.bind("<MouseWheel>", on_wheel_scroll)

        def close():
            if self.theme_id == "preview":  # an unsaved experiment: go back to the theme you had
                tid = self.settings.get("theme") or DEFAULT_THEME
                allt = self.all_themes()
                self.set_theme(allt.get(tid) or THEMES[DEFAULT_THEME], tid if tid in allt else DEFAULT_THEME)
            win.destroy()
        win.protocol("WM_DELETE_WINDOW", close)
        choose("accent")
        render_sample()

    # -- open text in the default editor ------------------------------------- #
    def open_in_editor(self, path: Path, what: str = "file") -> None:
        try:
            if IS_WINDOWS:
                try:
                    os.startfile(str(path))  # noqa  (the default app for that file type)
                except OSError:
                    subprocess.Popen(["notepad.exe", str(path)])
            else:
                subprocess.Popen(["xdg-open", str(path)])
        except Exception as e:  # noqa: BLE001
            messagebox.showerror("Open in editor", f"Couldn't open the {what}: {e}\n\nIt's here:\n{path}")

    def open_text_external(self, text: str, stem: str) -> None:
        base = TLOG.path.parent if TLOG.path else APP_DIR
        try:
            base.mkdir(parents=True, exist_ok=True)
            p = base / f"{time.strftime('%Y-%m-%d_%H-%M-%S', TLOG.started)}_{stem}.txt"
            p.write_text(text, encoding="utf-8-sig")  # BOM so every Notepad version reads it as UTF-8
        except OSError as e:
            messagebox.showerror("Open in editor", f"Couldn't write the file: {e}")
            return
        tlog("app", f"opened {stem} text in the default editor: {p}")
        self.open_in_editor(p, stem)

    def open_activity_log(self):
        self.open_text_external(self.log_text.get("1.0", "end-1c"), "activity-log")

    def open_console_log(self):
        lines = []
        for row in self._console_lines:
            if isinstance(row, list):
                lines.append("".join(str(s[0]) for s in row if isinstance(s, list) and len(s) == 2).rstrip())
        self.open_text_external("\n".join(lines), "console")

    # -- helpers ------------------------------------------------------------ #
    def log(self, text: str, level: str = ""):
        tlog("activity", f"{level.upper() + ': ' if level else ''}{text}")
        t = self.log_text
        t.configure(state="normal")
        if UI.get("log_time", True):
            t.insert("end", time.strftime("%I:%M:%S %p  " if UI.get("log_clock") == "12" else "%H:%M:%S  "), ("time",))
        t.insert("end", text + "\n", (level,) if level else ())
        try:
            mx = max(200, int(UI.get("log_max", 3000)))
            n = int(t.index("end-1c").split(".")[0])
            if n > mx:
                t.delete("1.0", f"{n - int(mx * 0.8)}.0")
        except Exception:  # noqa: BLE001
            pass
        t.see("end")
        t.configure(state="disabled")

    def on_everything(self):
        for v in self.vars.values():
            v.set(self.every.get())
        self.lock_checkboxes()

    def lock_checkboxes(self):
        locked = self.running or self.every.get()
        for cb in self.cbs.values():
            cb.state(["disabled"] if locked else ["!disabled"])
        self.every_cb.state(["disabled"] if self.running else ["!disabled"])

    def set_running(self, running: bool):
        self.running = running
        self._shimmer_kick()
        on, off = (["disabled"], ["!disabled"])
        for w in (self.start_btn, self.change_btn, self.reload_btn, self.find_btn, self.login_desk_btn,
                  self.login_code_btn, self.search_entry,
                  self.eng_tdl_rb, self.eng_py_rb,
                  self.takeout_cb, self.reuse_cb, self.awake_cb,
                  self.load_save_btn, self.queue_start_btn):
            w.state(on if running else off)
        # speed boxes stay editable while running; "Apply now" restarts just the download with them
        self.apply_btn.state(off if running else on)
        self.stop_btn.state(off if running else on)
        self.pause_btn.state(off if running else on)
        if not running:
            self.pause_btn.configure(text="Pause")
        self.chat_list.configure(state="disabled" if running else "normal")
        self.lock_checkboxes()
        if not running:
            self.update_engine_ui()
        if running and self.awake_var.get():
            keep_awake(True)
            self.awake = True
        elif not running and self.awake:
            keep_awake(False)
            self.awake = False

    def refresh_list(self):
        needle = self.search_var.get().strip().lower()
        self.chat_list.delete(0, "end")
        self.shown = []
        for i, c in enumerate(self.chats):
            n_topics = len(c.get("topics") or [])
            kind = f"forum, {n_topics} topics" if n_topics else c.get("type", "?")
            label = (f"{c.get('visible_name') or '-'}   [{kind}]"
                     + (f"   @{c['username']}" if c.get("username") else ""))
            if needle in label.lower():
                self.shown.append(i)
                self.chat_list.insert("end", label)
        self.update_topic_filter_ui()

    def selected_chat(self) -> dict | None:
        sel = self.chat_list.curselection()
        if not sel or sel[0] >= len(self.shown):
            return None
        return self.chats[self.shown[sel[0]]]

    def update_topic_filter_ui(self):
        if not hasattr(self, "topic_filter_var"):
            return
        inc_s = self.topic_inc_var.get().strip()
        exc_s = self.topic_exc_var.get().strip()
        inc_r, exc_r = parse_topic_rules(inc_s), parse_topic_rules(exc_s)
        c = self.selected_chat()
        topics = [t for t in ((c or {}).get("topics") or []) if isinstance(t, dict)]
        if not topics:
            if inc_r or exc_r:
                self.topic_filter_var.set(
                    'Active filter will apply to forum topics  (syntax:  "house " + num  |  "house " + word  |  "house " + *  |  ; for multiple)'
                )
            else:
                self.topic_filter_var.set(
                    'Forum topic filter:  "house " + num   |   "house " + word   |   "house " + *   |   "house " + * + *   (; for multiple)'
                )
            return
        if not inc_r and not exc_r:
            self.topic_filter_var.set(
                f'Forum with {len(topics):,} topics - all {len(topics):,} will be downloaded.  '
                f'(Syntax: "house " + num  |  "house " + word  |  "house " + *)'
            )
            return
        kept, skipped = [], []
        for t in topics:
            title = str(t.get("title") or f"Topic {t.get('id')}")
            (kept if topic_matches(title, inc_r, exc_r) else skipped).append(title)
        kept_ex = ", ".join(kept[:4]) + (" ..." if len(kept) > 4 else "")
        skip_ex = ", ".join(skipped[:4]) + (" ..." if len(skipped) > 4 else "")
        msg = f"Matching {len(kept):,} of {len(topics):,} forum topics"
        if kept_ex:
            msg += f"  (keeping: {kept_ex})"
        if skip_ex:
            msg += f"  |  skipping {len(skipped):,}: {skip_ex}"
        self.topic_filter_var.set(msg)

    def _resolve_chat_dir(self, dest_root: Path, chat: dict | None) -> Path:
        if not chat:
            return dest_root
        cname = safe_name(chat.get("visible_name") or chat.get("username") or str(chat.get("id") or "chat"))
        cand = dest_root / cname
        if cand.is_dir():
            return cand
        if (dest_root / ".tms").is_dir() or any((dest_root / fn).is_dir() for fn in FOLDER_NAMES.values()):
            return dest_root
        return cand

    def _scan_disk_for_verify(
        self, dest_root: Path, chat: dict, media: list[dict] | None = None,
        ref_spec: str | Path | None = None
    ) -> tuple[Path, dict[int, tuple[Path, int, bool]]]:
        """
        Finds the conversation's download folder inside `dest_root` (or `dest_root` itself if you pointed
        directly at the conversation folder), plus any optional reference folder(s) `ref_spec` on other drives,
        and maps every downloaded / half-downloaded file on disk by message ID -> (Path, size_in_bytes, is_tmp).
        Recognizes both new filenames (<chat_id>_<msg_id>_<name>) and older TMSF filenames
        (<YYYY-MM-DD>_<HH-MM-SS>_<msg_id>_<name> or <YYYY-MM-DD>_<HH-MM-SS>_<name_or_doc_id>).
        """
        chat_dir = self._resolve_chat_dir(dest_root, chat)
        found: dict[int, tuple[Path, int, bool]] = {}
        scan_roots: list[Path] = []
        if chat_dir.exists():
            scan_roots.append(chat_dir)
        for rdir in resolve_ref_dirs(ref_spec, chat):
            if rdir.exists() and all(
                os.path.normcase(os.path.abspath(str(rdir))) != os.path.normcase(os.path.abspath(str(x)))
                for x in scan_roots
            ):
                scan_roots.append(rdir)
        if not scan_roots:
            return chat_dir, found

        by_doc_id: dict[int, list[tuple[Path, int]]] = {}
        by_tail: dict[str, list[tuple[Path, int]]] = {}
        by_date_size: dict[tuple[int, str], tuple[Path, int]] = {}

        def _record_mid(mid: int, p: Path, sz: int, is_tmp: bool):
            prev = found.get(mid)
            if prev is None or (prev[2] and not is_tmp) or (prev[2] == is_tmp and sz > prev[1]):
                found[mid] = (p, sz, is_tmp)

        stack = list(scan_roots)
        while stack:
            cur_d = stack.pop()
            try:
                with os.scandir(cur_d) as it:
                    for e in it:
                        try:
                            if e.is_dir(follow_symlinks=False):
                                if e.name != ".tms":
                                    stack.append(Path(e.path))
                            elif e.is_file(follow_symlinks=False):
                                n = e.name
                                is_tmp = n.endswith(".tmp")
                                stem = n[:-4] if is_tmp else n
                                p = Path(e.path)
                                sz = e.stat().st_size
                                m = _TDL_NAME.match(stem)
                                if m:
                                    _record_mid(int(m.group(1)), p, sz, is_tmp)
                                if not is_tmp and sz > 0:
                                    for did in _extract_doc_ids(stem):
                                        by_doc_id.setdefault(did, []).append((p, sz))
                                    _mid_p, tail_p, is_old = _strip_known_prefix(stem)
                                    for t in (_norm_media_tail(tail_p, True), _norm_media_tail(tail_p, False)):
                                        if t:
                                            by_tail.setdefault(t, []).append((p, sz))
                                    if is_old:
                                        ext = os.path.splitext(stem)[1].lower()
                                        if ext:
                                            by_date_size[(sz, ext)] = (p, sz)
                        except OSError:
                            continue
            except OSError:
                continue

        if media:
            for item in media:
                mid = int(item["id"])
                prev = found.get(mid)
                if prev is not None and not prev[2] and prev[1] > 0:
                    continue
                exp_sz = int(item.get("size") or 0)
                fname = str(item.get("file") or "")

                def _pick_hit(cands: list[tuple[Path, int]]) -> tuple[Path, int] | None:
                    for cp, csz in cands:
                        if exp_sz <= 0 or csz == exp_sz or abs(csz - exp_sz) <= 1024:
                            return cp, csz
                    return None

                hit = None
                did = int(item.get("doc_id") or 0)
                if did and did in by_doc_id:
                    hit = _pick_hit(by_doc_id[did])
                if hit is None:
                    for f_did in _extract_doc_ids(fname):
                        if f_did in by_doc_id:
                            hit = _pick_hit(by_doc_id[f_did])
                            if hit is not None:
                                break
                if hit is None:
                    nt = _norm_media_tail(fname, True)
                    nt_mid = _norm_media_tail(f"{mid}_{fname}", True)
                    if nt and nt not in ("media", "file", "video", "photo"):
                        hit = _pick_hit(by_tail.get(nt, [])) or _pick_hit(by_tail.get(nt_mid, []))
                if hit is None and exp_sz >= 32768:
                    ext = os.path.splitext(fname)[1].lower()
                    if ext and (exp_sz, ext) in by_date_size:
                        hit = by_date_size[(exp_sz, ext)]
                if hit is not None:
                    _record_mid(mid, hit[0], hit[1], False)

        return chat_dir, found

    def clean_duplicates_dialog(self, initial_folder: Path | None = None, parent_win=None):
        """
        Scans a conversation folder (or any folder you choose) for duplicate files created when an older
        version of TMSF used YYYY-MM-DD_HH-MM-SS_... filenames and the newer version used <chat_id>_<msg_id>_...,
        or ' (2)' copies with identical byte size & content. Lets you review and delete the extra copies.
        """
        parent = parent_win or self.root
        ch = self.selected_chat()
        base = initial_folder or self._resolve_chat_dir(Path(self.save_var.get()), ch)
        if not base.exists():
            base = Path(self.save_var.get())

        win = tk.Toplevel(parent)
        win.title("Find & Clean Duplicate Media Files")
        win.geometry("920x620")
        win.minsize(760, 480)
        themed(win, bg="panel")
        dark_title_bar(win)
        outer = ttk.Frame(win, padding=12)
        outer.pack(fill="both", expand=True)

        ttk.Label(
            outer,
            text="Finds files downloaded twice in the same folder (for example, once by an older TMSF version as "
                 "YYYY-MM-DD_HH-MM-SS_... and once as <chat_id>_<msg_id>_..., or ' (2)' copies) that have the exact "
                 "same byte size and identical file content.",
            style="Muted.TLabel", wraplength=880
        ).pack(anchor="w", pady=(0, 8))

        top = ttk.Frame(outer)
        top.pack(fill="x", pady=(0, 4))
        folder_var = tk.StringVar(value=str(base))
        ttk.Label(top, text="Folder to scan:", width=22).pack(side="left")
        ttk.Entry(top, textvariable=folder_var).pack(side="left", fill="x", expand=True, padx=(8, 6))

        def pick_dir():
            f = filedialog.askdirectory(parent=win, initialdir=folder_var.get(),
                                        title="Choose folder to scan for duplicate media files")
            if f:
                folder_var.set(f)
                scan_now()
        ttk.Button(top, text="Browse...", command=pick_dir).pack(side="left")

        ref_row = ttk.Frame(outer)
        ref_row.pack(fill="x", pady=(0, 6))
        ref_dup_var = tk.StringVar(value=self.ref_var.get().strip())
        ttk.Label(ref_row, text="Reference folder (keep):", width=22).pack(side="left")
        ttk.Entry(ref_row, textvariable=ref_dup_var).pack(side="left", fill="x", expand=True, padx=(8, 6))

        def pick_ref_dup():
            f = filedialog.askdirectory(parent=win, initialdir=ref_dup_var.get() or folder_var.get(),
                                        title="Choose reference folder whose files should be kept")
            if f:
                ref_dup_var.set(f)
                scan_now()
        ttk.Button(ref_row, text="Browse...", command=pick_ref_dup).pack(side="left")
        ttk.Button(ref_row, text="Clear", command=lambda: (ref_dup_var.set(""), scan_now())).pack(side="left", padx=(6, 0))

        opt_row = ttk.Frame(outer)
        opt_row.pack(fill="x", pady=(0, 6))
        keep_var = tk.StringVar(value="new")
        ttk.Label(opt_row, text="Which copy to keep:").pack(side="left", padx=(0, 8))
        ttk.Radiobutton(
            opt_row, text="Keep new <chat_id>_<msg_id>_... filenames (recommended)",
            value="new", variable=keep_var, command=lambda: scan_now()
        ).pack(side="left", padx=(0, 14))
        ttk.Radiobutton(
            opt_row, text="Keep old YYYY-MM-DD_HH-MM-SS_... filenames",
            value="old", variable=keep_var, command=lambda: scan_now()
        ).pack(side="left")
        ttk.Button(opt_row, text="Rescan", command=lambda: scan_now()).pack(side="right")

        status_var = tk.StringVar(value="Scanning...")
        ttk.Label(outer, textvariable=status_var, style="Eta.TLabel").pack(anchor="w", pady=(0, 6))

        tf = ttk.Frame(outer)
        tf.pack(fill="both", expand=True)
        cols = ("remove", "keep", "size", "folder")
        tree = ttk.Treeview(tf, columns=cols, show="headings", height=14)
        for c, txt, w, anc in (
            ("remove", "Duplicate to Remove", 290, "w"),
            ("keep", "Copy to Keep", 290, "w"),
            ("size", "Size", 95, "e"),
            ("folder", "Folder", 200, "w"),
        ):
            tree.heading(c, text=txt, anchor=anc)
            tree.column(c, width=w, anchor=anc, stretch=(c in ("remove", "keep", "folder")))
        themed_tag(tree, "dup", foreground="orange")
        sb = NeonScrollbar(tf, orient="vertical", command=tree.yview)
        tree.configure(yscrollcommand=sb.set)
        tree.pack(side="left", fill="both", expand=True)
        sb.pack(side="left", fill="y")

        state_d: dict[str, list[tuple[Path, Path, int]]] = {"dups": []}

        btn_bar = ttk.Frame(outer)
        btn_bar.pack(fill="x", pady=(8, 0))
        del_btn = ttk.Button(btn_bar, text="Delete duplicate copies", style="Accent.TButton", state="disabled")
        del_btn.pack(side="left")
        ttk.Button(btn_bar, text="Close", command=win.destroy).pack(side="right")

        def scan_now():
            tree.delete(*tree.get_children())
            target_dir = Path(folder_var.get().strip())
            if not target_dir.exists():
                status_var.set(f"Folder does not exist yet: {target_dir}")
                state_d["dups"] = []
                del_btn.state(["disabled"])
                return
            dups = find_duplicate_files(
                target_dir, prefer_new=(keep_var.get() == "new"),
                ref_spec=ref_dup_var.get().strip(), chat=ch
            )
            state_d["dups"] = dups
            total_bytes = sum(sz for _, _, sz in dups)
            for p_keep, p_rem, sz in dups[:4000]:
                tree.insert("", "end", values=(p_rem.name, p_keep.name, fmt_size(sz), str(p_rem.parent)), tags=("dup",))
            if dups:
                status_var.set(
                    f"Found {len(dups):,} duplicate file(s) wasting {fmt_size(total_bytes)} in {target_dir}."
                )
                del_btn.state(["!disabled"])
            else:
                status_var.set(f"No duplicate files found in {target_dir}.")
                del_btn.state(["disabled"])

        def delete_dups():
            dups = state_d["dups"]
            if not dups:
                return
            total_bytes = sum(sz for _, _, sz in dups)
            if not messagebox.askyesno(
                "Delete duplicate copies?",
                f"Delete {len(dups):,} duplicate file(s) ({fmt_size(total_bytes)})?\n\n"
                "One verified copy of every file will be kept.",
                parent=win
            ):
                return
            removed = 0
            freed = 0
            for p_keep, p_rem, sz in dups:
                try:
                    if p_keep.exists() and p_rem.exists() and p_keep != p_rem:
                        os.remove(p_rem)
                        removed += 1
                        freed += sz
                        tlog("dedup", f"Removed duplicate {p_rem} (kept {p_keep}, {sz} bytes)")
                except OSError as e:
                    tlog("dedup", f"Failed to remove {p_rem}: {e}")
            self.log(f"Cleaned up {removed:,} duplicate file(s), freed {fmt_size(freed)}.", "ok")
            scan_now()

        del_btn.configure(command=delete_dups)
        scan_now()

    def preview_topics(self):
        """
        Bundled 'Preview Topics & Verify Downloaded Media' window.
        Can be opened and used at any time - even while a download is actively running in the main window.
        """
        win = tk.Toplevel(self.root)
        c0 = self.selected_chat() or (self.chats[0] if self.chats else None)
        win.title("Preview Forum Topics & Verify Downloaded Media")
        win.geometry("1320x960")
        win.minsize(900, 640)
        themed(win, bg="panel")
        dark_title_bar(win)
        outer = ttk.Frame(win, padding=12)
        outer.pack(fill="both", expand=True)
        # the two halves sit in a vertical pane: drag the gap between them to give the results more room
        pw = tk.PanedWindow(outer, orient="vertical", sashwidth=9, sashrelief="flat", bd=0, opaqueresize=True)
        themed(pw, bg="panel")
        pw.pack(fill="both", expand=True)

        # ---- Top: Forum Topics Preview ----
        top_box = box(outer)
        pw.add(top_box, minsize=110, stretch="never")
        top_hdr = ttk.Frame(top_box, style="SectionHdr.TFrame", padding=(8, 4))
        top_hdr.pack(fill="x")
        ttk.Label(top_hdr, text=" 1. Forum Topics Preview ", style="SectionTitle.TLabel").pack(side="left")
        summary_var = tk.StringVar()
        ttk.Label(top_hdr, textvariable=summary_var, style="Muted.TLabel").pack(side="left", padx=(14, 0))
        top_body = ttk.Frame(top_box, padding=(10, 6, 10, 8))
        top_body.pack(fill="both", expand=True)

        flt_row = ttk.Frame(top_body)
        flt_row.pack(fill="x", pady=(0, 6))
        ttk.Label(flt_row, text="Include topics").grid(row=0, column=0, sticky="w")
        ttk.Entry(flt_row, textvariable=self.topic_inc_var).grid(row=0, column=1, sticky="ew", padx=(6, 14))
        ttk.Label(flt_row, text="Exclude topics").grid(row=0, column=2, sticky="w")
        ttk.Entry(flt_row, textvariable=self.topic_exc_var).grid(row=0, column=3, sticky="ew", padx=(6, 0))
        flt_row.columnconfigure(1, weight=1)
        flt_row.columnconfigure(3, weight=1)

        tf = ttk.Frame(top_body)
        tf.pack(fill="both", expand=True)
        tree = ttk.Treeview(tf, columns=("status", "topic"), show="headings", height=3)
        tree.heading("status", text="Action", anchor="w")
        tree.heading("topic", text="Topic / Subject", anchor="w")
        tree.column("status", width=130, anchor="w", stretch=False)
        tree.column("topic", width=650, anchor="w", stretch=True)
        themed_tag(tree, "keep", foreground="green")
        themed_tag(tree, "skip", foreground="red")
        sb = NeonScrollbar(tf, orient="vertical", command=tree.yview)
        tree.configure(yscrollcommand=sb.set)
        tree.pack(side="left", fill="both", expand=True)
        sb.pack(side="left", fill="y", padx=(4, 0))

        # ---- Bottom: Verify Downloaded Media ----
        vbox = box(outer)
        pw.add(vbox, minsize=320, stretch="always")
        vhdr = ttk.Frame(vbox, style="SectionHdr.TFrame", padding=(8, 4))
        vhdr.pack(fill="x")
        ttk.Label(vhdr, text=" 2. Verify Downloaded Media (works even while a download is running) ",
                  style="SectionTitle.TLabel").pack(side="left")
        vbody = ttk.Frame(vbox, padding=(10, 6, 10, 8))
        vbody.pack(fill="both", expand=True)

        chosen = {"chat": c0}
        v_folder_var = tk.StringVar(value=self.save_var.get())
        v_ref_var = tk.StringVar(value=self.ref_var.get())
        v_mode_var = tk.StringVar(value="log")  # "log" = use saved media log, "live" = read directly from Telegram
        v_log_var = tk.StringVar(value="")

        # Row A: Destination folder + Reference folder + Conversation selector
        cfg_grid = ttk.Frame(vbody)
        cfg_grid.pack(fill="x", pady=(0, 6))
        ttk.Label(cfg_grid, text="Downloaded media folder").grid(row=0, column=0, sticky="w")
        ttk.Entry(cfg_grid, textvariable=v_folder_var).grid(row=0, column=1, sticky="ew", padx=(8, 6))

        def pick_v_folder():
            f = filedialog.askdirectory(parent=win, initialdir=v_folder_var.get(),
                                        title="Choose folder where downloaded media is stored")
            if f:
                v_folder_var.set(f)
                auto_find_log()
        ttk.Button(cfg_grid, text="Browse...", command=pick_v_folder).grid(row=0, column=2, sticky="e")

        ttk.Label(cfg_grid, text="Reference folder (optional)").grid(row=1, column=0, sticky="w", pady=(4, 0))
        v_ref_row = ttk.Frame(cfg_grid)
        v_ref_row.grid(row=1, column=1, columnspan=2, sticky="ew", padx=(8, 0), pady=(4, 0))
        ttk.Entry(v_ref_row, textvariable=v_ref_var).pack(side="left", fill="x", expand=True)

        def pick_v_ref():
            f = filedialog.askdirectory(parent=win, initialdir=v_ref_var.get() or v_folder_var.get(),
                                        title="Choose reference folder on another drive to also include in verification")
            if f:
                cur_r = v_ref_var.get().strip()
                v_ref_var.set(f"{cur_r}; {f}" if cur_r else f)
        ttk.Button(v_ref_row, text="Browse...", command=pick_v_ref).pack(side="left", padx=(6, 0))
        ttk.Button(v_ref_row, text="Clear", command=lambda: v_ref_var.set("")).pack(side="left", padx=(6, 0))

        ttk.Label(cfg_grid, text="Conversation to verify").grid(row=2, column=0, sticky="w", pady=(6, 0))
        conv_row = ttk.Frame(cfg_grid)
        conv_row.grid(row=2, column=1, columnspan=2, sticky="ew", padx=(8, 0), pady=(6, 0))
        v_search_var = tk.StringVar()
        ttk.Label(conv_row, text="Search").pack(side="left")
        ttk.Entry(conv_row, textvariable=v_search_var, width=22).pack(side="left", padx=(6, 10))
        v_conv_combo = ttk.Combobox(conv_row, state="readonly")
        v_conv_combo.pack(side="left", fill="x", expand=True)
        cfg_grid.columnconfigure(1, weight=1)

        shown_v: list[dict] = []

        def fill_v_chats(*_):
            needle = v_search_var.get().strip().lower()
            shown_v.clear()
            labels = []
            sel_idx = 0
            ch = chosen["chat"]
            pool = list(self.chats)
            if ch and not any(str(c.get("id")) == str(ch.get("id")) for c in pool):
                pool.insert(0, ch)
            for c in pool:
                n_topics = len(c.get("topics") or [])
                kind = f"forum, {n_topics} topics" if n_topics else c.get("type", "?")
                lbl = f"{c.get('visible_name') or '-'}   [{kind}]" + (f"   @{c['username']}" if c.get("username") else "")
                if needle in lbl.lower():
                    if ch and str(c.get("id")) == str(ch.get("id")):
                        sel_idx = len(shown_v)
                    shown_v.append(c)
                    labels.append(lbl)
            v_conv_combo["values"] = labels
            if labels:
                v_conv_combo.current(sel_idx)
                chosen["chat"] = shown_v[sel_idx]

        def refresh_preview(*_):
            if not win.winfo_exists():
                return
            tree.delete(*tree.get_children())
            ch = chosen["chat"]
            topics = [t for t in ((ch or {}).get("topics") or []) if isinstance(t, dict)]
            if not topics:
                summary_var.set(f"{(ch or {}).get('visible_name') or 'Selected conversation'}: not a forum (no topics)")
                return
            inc_r = parse_topic_rules(self.topic_inc_var.get())
            exc_r = parse_topic_rules(self.topic_exc_var.get())
            kept_n = 0
            for t in topics:
                title = str(t.get("title") or f"Topic {t.get('id')}")
                ok = topic_matches(title, inc_r, exc_r)
                if ok:
                    kept_n += 1
                tree.insert("", "end", values=("Include" if ok else "Skip", title),
                            tags=("keep" if ok else "skip",))
            summary_var.set(f"{ch.get('visible_name')}: {kept_n:,} of {len(topics):,} topics match  "
                            f"({len(topics) - kept_n:,} skipped)")

        def auto_find_log(*_):
            ch = chosen["chat"]
            if not ch:
                return
            base = Path(v_folder_var.get().strip() or self.save_var.get())
            cname = safe_name(ch.get("visible_name") or ch.get("username") or str(ch.get("id") or "chat"))
            for d in (base / cname / ".tms", base / ".tms", base / cname, base):
                try:
                    if not d.is_dir():
                        continue
                    saves = sorted(d.glob(f"*{SAVE_EXT}"), key=lambda p: p.stat().st_mtime, reverse=True)
                    if saves:
                        v_log_var.set(str(saves[0]))
                        return
                    exp = d / "export.json"
                    if exp.is_file():
                        v_log_var.set(str(exp))
                        return
                except OSError:
                    continue

        def on_conv_pick(*_):
            idx = v_conv_combo.current()
            if 0 <= idx < len(shown_v):
                chosen["chat"] = shown_v[idx]
                refresh_preview()
                auto_find_log()
        v_conv_combo.bind("<<ComboboxSelected>>", on_conv_pick)
        v_search_var.trace_add("write", fill_v_chats)

        # Row B: File types to verify
        t_frame = ttk.Frame(vbody)
        t_frame.pack(fill="x", pady=(2, 6))
        ttk.Label(t_frame, text="File types to verify:").grid(row=0, column=0, sticky="w", padx=(0, 8))
        init_sel = set(ALL_KEYS) if self.every.get() else {k for k, v in self.vars.items() if v.get()}
        if not init_sel:
            init_sel = set(ALL_KEYS)
        v_tvars = {k: tk.BooleanVar(value=k in init_sel) for k, _ in CATEGORIES}
        v_every = tk.BooleanVar(value=init_sel == set(ALL_KEYS))

        def on_v_every():
            for v in v_tvars.values():
                v.set(v_every.get())
        for i, (k, label) in enumerate(CATEGORIES):
            ttk.Checkbutton(t_frame, text=label, variable=v_tvars[k]).grid(row=0, column=i + 1, sticky="w", padx=5)
        ttk.Checkbutton(t_frame, text="Everything", variable=v_every, command=on_v_every).grid(
            row=0, column=len(CATEGORIES) + 1, sticky="w", padx=6)

        # Row C: Media log vs Verify directly from Telegram without media log
        src_frame = ttk.Frame(vbody)
        src_frame.pack(fill="x", pady=(2, 6))
        ttk.Radiobutton(src_frame, text="Use saved media log (.tmsave.json or export.json):",
                        value="log", variable=v_mode_var).grid(row=0, column=0, sticky="w")
        v_log_entry = ttk.Entry(src_frame, textvariable=v_log_var)
        v_log_entry.grid(row=0, column=1, sticky="ew", padx=(8, 6))

        def pick_v_log():
            p = filedialog.askopenfilename(
                parent=win, title="Choose a saved media log or export.json",
                initialdir=v_folder_var.get(),
                filetypes=[("Media logs & exports", f"*{SAVE_EXT} *.json"), ("All files", "*.*")])
            if p:
                v_log_var.set(p)
                v_mode_var.set("log")
                try:
                    data = read_save_file(p)
                    if isinstance(data.get("chat"), dict):
                        chosen["chat"] = dict(data["chat"])
                        fill_v_chats()
                        refresh_preview()
                    if data.get("save_folder"):
                        v_folder_var.set(str(data["save_folder"]))
                except Exception:  # noqa: BLE001
                    pass
        ttk.Button(src_frame, text="Browse log...", command=pick_v_log).grid(row=0, column=2, sticky="e")
        ttk.Button(src_frame, text="Auto-find", command=auto_find_log).grid(row=0, column=3, sticky="e", padx=(6, 0))
        ttk.Radiobutton(
            src_frame,
            text="Verify without media log (read messages directly from Telegram & actively verify files on disk)",
            value="live", variable=v_mode_var
        ).grid(row=1, column=0, columnspan=4, sticky="w", pady=(4, 0))
        src_frame.columnconfigure(1, weight=1)

        # Row D: Start / Stop / Filter / Save verified log bar
        vbar = ttk.Frame(vbody)
        vbar.pack(fill="x", pady=(4, 6))
        v_start_btn = ttk.Button(vbar, text="Start verify", style="Accent.TButton")
        v_start_btn.pack(side="left")
        v_stop_btn = ttk.Button(vbar, text="Stop", state="disabled")
        v_stop_btn.pack(side="left", padx=(8, 12))
        v_filter_var = tk.StringVar(value="all")
        for fval, flbl in (("all", "All"), ("missing", "Missing only"),
                           ("partial", "Incomplete"), ("ok", "Verified OK")):
            ttk.Radiobutton(vbar, text=flbl, value=fval, variable=v_filter_var).pack(side="left", padx=4)
        v_save_btn = ttk.Button(vbar, text="Save verified media log...", state="disabled")
        v_save_btn.pack(side="right")
        focus_btn = ttk.Button(vbar, text="Hide setup (bigger results)", style="Toggle.TButton")
        focus_btn.pack(side="right", padx=(0, 8))
        ttk.Button(
            vbar, text="Clean duplicates...",
            command=lambda: self.clean_duplicates_dialog(
                self._resolve_chat_dir(Path(v_folder_var.get().strip() or self.save_var.get()), chosen["chat"]),
                parent_win=win
            )
        ).pack(side="right", padx=(0, 8))

        v_status_var = tk.StringVar(value="Pick your folder, file types, conversation, and media log (or live Telegram read), then click 'Start verify'.")
        v_status_lbl = ttk.Label(vbody, textvariable=v_status_var, style="Eta.TLabel", wraplength=920, justify="left")
        v_status_lbl.pack(anchor="w", pady=(0, 4), fill="x")
        autowrap(v_status_lbl)
        v_pbar = NeonBar(vbody, height=14, maximum=1, value=0)
        v_pbar.pack(fill="x", pady=(0, 6))

        # Row E: Verification results table (+ a navigation bar: jump to the top / bottom / next problem)
        nav = ttk.Frame(vbody)
        nav.pack(fill="x", pady=(0, 4))
        v_count_var = tk.StringVar(value="")
        vtf = ttk.Frame(vbody)
        vtf.pack(fill="both", expand=True)
        vcols = ("status", "id", "topic", "type", "file", "size", "path")
        vtree = ttk.Treeview(vtf, columns=vcols, show="headings", height=14)
        for c, txt, w, anc in (
            ("status", "Result", 135, "w"),
            ("id", "Msg ID", 75, "e"),
            ("topic", "Topic", 140, "w"),
            ("type", "Type", 95, "w"),
            ("file", "File Name", 230, "w"),
            ("size", "Disk / Expected", 140, "e"),
            ("path", "Location on Disk", 220, "w"),
        ):
            vtree.heading(c, text=txt, anchor=anc)
            vtree.column(c, width=w, anchor=anc, stretch=(c in ("file", "path")))
        themed_tag(vtree, "ok", foreground="green")
        themed_tag(vtree, "partial", foreground="orange")
        themed_tag(vtree, "missing", foreground="red")
        vsb = NeonScrollbar(vtf, orient="vertical", command=vtree.yview, thickness=20)
        vhs = NeonScrollbar(vbody, orient="horizontal", command=vtree.xview, thickness=14)
        vtree.configure(yscrollcommand=vsb.set, xscrollcommand=vhs.set)
        vsb.pack(side="right", fill="y", padx=(4, 0))
        vtree.pack(side="left", fill="both", expand=True)
        vhs.pack(fill="x", pady=(4, 0))

        def v_jump(where):
            kids = vtree.get_children()
            if not kids:
                return
            tgt = kids[0] if where == "top" else kids[-1]
            vtree.see(tgt)
            vtree.yview_moveto(0.0 if where == "top" else 1.0)
            vtree.selection_set(tgt)

        def v_problem(step):
            kids = list(vtree.get_children())
            if not kids:
                return
            cur = vtree.selection()
            i = kids.index(cur[0]) if cur and cur[0] in kids else (-1 if step > 0 else len(kids))
            for _ in range(len(kids)):
                i = (i + step) % len(kids)
                if "ok" not in vtree.item(kids[i], "tags"):
                    vtree.selection_set(kids[i])
                    vtree.see(kids[i])
                    return
            v_status_var.set("Nothing to fix here - every row shown is Verified OK.")

        def v_open_editor():
            flt = v_filter_var.get()
            out = [f"Verification results - {time.strftime('%Y-%m-%d %H:%M:%S')}", v_status_var.get(), ""]
            out += [" | ".join(str(x) for x in r["vals"]) for r in v_state["rows"] if flt == "all" or r["tag"] == flt]
            self.open_text_external("\n".join(out), "verify-results")
        ttk.Button(nav, text="\u21e7 Top", style="Toggle.TButton", command=lambda: v_jump("top")).pack(side="left")
        ttk.Button(nav, text="\u21e9 Bottom", style="Toggle.TButton", command=lambda: v_jump("bottom")).pack(side="left", padx=(6, 0))
        ttk.Button(nav, text="\u25b2 Prev problem", style="Toggle.TButton", command=lambda: v_problem(-1)).pack(side="left", padx=(14, 0))
        ttk.Button(nav, text="\u25bc Next problem", style="Toggle.TButton", command=lambda: v_problem(1)).pack(side="left", padx=(6, 0))
        ttk.Label(nav, textvariable=v_count_var, style="Muted.TLabel").pack(side="left", padx=(16, 0))
        ttk.Button(nav, text="Open results in editor", style="Toggle.TButton", command=v_open_editor).pack(side="right")

        def toggle_focus(force=None):
            on = (not v_focus["on"]) if force is None else force
            if on == v_focus["on"]:
                return
            v_focus["on"] = on
            if on:
                for w in (cfg_grid, t_frame, src_frame):
                    w.pack_forget()
                try:
                    pw.forget(top_box)
                except tk.TclError:
                    pass
                focus_btn.configure(text="Show setup")
            else:
                pw.add(top_box, before=vbox, minsize=110, stretch="never")
                cfg_grid.pack(fill="x", pady=(0, 6), before=vbar)
                t_frame.pack(fill="x", pady=(2, 6), before=vbar)
                src_frame.pack(fill="x", pady=(2, 6), before=vbar)
                focus_btn.configure(text="Hide setup (bigger results)")
        v_focus = {"on": False}
        focus_btn.configure(command=toggle_focus)

        v_state = {"running": False, "stop": False, "proc": None, "rows": [], "verified_save": None}

        def render_v_rows(*_):
            if not win.winfo_exists():
                return
            vtree.delete(*vtree.get_children())
            flt = v_filter_var.get()
            shown_count = 0
            for r in v_state["rows"]:
                if flt != "all" and r["tag"] != flt:
                    continue
                shown_count += 1
                if shown_count <= 60000:
                    vtree.insert("", "end", values=r["vals"], tags=(r["tag"],))
            v_count_var.set(f"{min(shown_count, 60000):,} of {shown_count:,} rows shown" if shown_count else "")
        v_filter_var.trace_add("write", render_v_rows)

        def save_verified_log():
            vs = v_state.get("verified_save")
            if not vs:
                return
            ch = vs["chat"]
            init_name = f"{safe_name(ch.get('visible_name') or 'chat', 50)}_verified_{time.strftime('%Y-%m-%d_%H-%M')}{SAVE_EXT}"
            p = filedialog.asksaveasfilename(
                parent=win, title="Save verified media log", defaultextension=SAVE_EXT,
                initialdir=v_folder_var.get(), initialfile=init_name,
                filetypes=[("Telegram Media Saver save", f"*{SAVE_EXT}"), ("JSON", "*.json"), ("All files", "*.*")])
            if not p:
                return
            try:
                write_save_file(Path(p), vs)
                tlog("verify", f"Saved verified media log to {p}")
                self.log(f"Saved verified media log: {p}", "ok")
                messagebox.showinfo("Saved", f"Verified media log saved to:\n{p}\n\n"
                                             "You can load this file with 'Load save' or in the Queue to download "
                                             "just the missing/incomplete files.", parent=win)
            except OSError as e:
                messagebox.showerror("Couldn't save", str(e), parent=win)
        v_save_btn.configure(command=save_verified_log)

        def stop_verify():
            v_state["stop"] = True
            p = v_state.get("proc")
            if p is not None and p.poll() is None:
                try:
                    p.terminate()
                except OSError:
                    pass
        v_stop_btn.configure(command=stop_verify)

        def run_verify():
            if v_state["running"]:
                return
            ch = chosen["chat"]
            if not ch:
                messagebox.showinfo("Verify", "Pick a conversation first.", parent=win)
                return
            sel_types = set(ALL_KEYS) if v_every.get() else {k for k, v in v_tvars.items() if v.get()}
            if not sel_types:
                messagebox.showinfo("Verify", "Tick at least one file type to verify.", parent=win)
                return
            dest_root = Path(v_folder_var.get().strip() or self.save_var.get())
            mode = v_mode_var.get()
            log_path = v_log_var.get().strip()
            if mode == "log" and not log_path:
                messagebox.showinfo("Verify", "Pick a saved media log file (or switch to 'Verify without media log').",
                                    parent=win)
                return
            inc_spec = self.topic_inc_var.get().strip()
            exc_spec = self.topic_exc_var.get().strip()

            toggle_focus(True)
            v_state["running"] = True
            v_state["stop"] = False
            v_state["rows"] = []
            v_state["verified_save"] = None
            v_start_btn.state(["disabled"])
            v_stop_btn.state(["!disabled"])
            v_save_btn.state(["disabled"])
            vtree.delete(*vtree.get_children())
            v_pbar.configure(maximum=1, value=0)
            tlog("verify", f"Starting verify: chat={ch.get('visible_name')} id={ch.get('id')} "
                           f"folder={dest_root} types={sorted(sel_types)} mode={mode} log={log_path!r}")

            def post_ui(fn):
                if win.winfo_exists():
                    win.after(0, fn)

            def evaluate_and_display(chat_id: int, media: list[dict], source_desc: str, is_final: bool = True):
                chat_dir, disk_map = self._scan_disk_for_verify(dest_root, ch, media, ref_spec=v_ref_var.get().strip())
                topics = [t for t in (ch.get("topics") or []) if isinstance(t, dict)]
                raw_titles = {int(t["id"]): str(t.get("title") or "") for t in topics if "id" in t}
                raw_titles.setdefault(GENERAL_TOPIC, "General")
                inc_r, exc_r = parse_topic_rules(inc_spec), parse_topic_rules(exc_spec)

                rows_out = []
                ok_n = miss_n = part_n = 0
                ok_bytes = miss_bytes = 0
                verified_media = []

                for m in media:
                    mid = int(m["id"])
                    cats = [c for c in (m.get("cats") or []) if c in FOLDER_NAMES]
                    cat = wanted(cats, sel_types)
                    tid = int(m.get("topic") or GENERAL_TOPIC)
                    t_title = raw_titles.get(tid) or f"Topic {tid}"
                    exp_sz = int(m.get("size") or 0)
                    fname = str(m.get("file") or f"message_{mid}")
                    disk_hit = disk_map.get(mid)

                    if cat is None:
                        verified_media.append({**m, "status": m.get("status", "not_selected")})
                        continue
                    if (inc_r or exc_r) and topics and not topic_matches(t_title, inc_r, exc_r):
                        verified_media.append({**m, "status": "filtered"})
                        continue

                    if disk_hit is not None:
                        dpath, dsz, is_tmp = disk_hit
                        if not is_tmp and dsz > 0 and (exp_sz <= 0 or dsz == exp_sz or abs(dsz - exp_sz) <= 1024):
                            tag, st_txt, m_st = "ok", "Verified OK", "done"
                            ok_n += 1
                            ok_bytes += dsz
                        else:
                            tag = "partial"
                            st_txt = "Half-downloaded (.tmp)" if is_tmp else "Size mismatch"
                            m_st = "pending"
                            part_n += 1
                            miss_bytes += max(0, exp_sz - dsz)
                        sz_txt = f"{fmt_size(dsz)} / {fmt_size(exp_sz)}" if exp_sz else fmt_size(dsz)
                        loc_txt = str(dpath.parent)
                    else:
                        tag, st_txt, m_st = "missing", "Missing", "pending"
                        miss_n += 1
                        miss_bytes += exp_sz
                        sz_txt = f"0 B / {fmt_size(exp_sz)}" if exp_sz else "0 B"
                        loc_txt = str(chat_dir / (t_title if topics else "") / FOLDER_NAMES[cat])

                    verified_media.append({"id": mid, "status": m_st, "file": fname, "cats": cats,
                                           "topic": tid, "size": exp_sz})
                    rows_out.append({
                        "tag": tag,
                        "vals": (st_txt, mid, t_title if topics else "-", FOLDER_NAMES[cat], fname, sz_txt, loc_txt),
                    })

                total_checked = ok_n + miss_n + part_n
                vs_dict = {
                    "format": SAVE_FORMAT, "version": 1, "saved_at": now_iso(), "created": now_iso(),
                    "chat": {k: ch.get(k) for k in ("id", "type", "visible_name", "username", "topics") if k in ch},
                    "chat_id": chat_id, "save_folder": str(dest_root), "selected_types": sorted(sel_types),
                    "topic_include": inc_spec, "topic_exclude": exc_spec, "engine": "verify",
                    "source": source_desc, "result": "verified",
                    "summary": {"done": ok_n, "pending": miss_n + part_n},
                    "status_meaning": STATUS_HELP,
                    "history": [[now_iso(), f"Verified against {chat_dir}: {ok_n} OK, {miss_n} missing, {part_n} incomplete"]],
                    "media_count": len(verified_media), "media": verified_media,
                }
                if is_final:
                    tlog("verify", f"Done ({source_desc}): checked={total_checked} ok={ok_n} "
                                   f"missing={miss_n} incomplete={part_n} folder={chat_dir}")

                def _upd():
                    if not win.winfo_exists():
                        return
                    v_state["rows"] = rows_out
                    v_state["verified_save"] = vs_dict
                    v_pbar.configure(maximum=max(1, total_checked), value=ok_n)
                    prefix = "Verification complete" if is_final else "Live verifying from Telegram"
                    v_status_var.set(
                        f"{prefix} ({chat_dir.name}):  {ok_n:,} / {total_checked:,} Verified OK ({fmt_size(ok_bytes)})   |   "
                        f"{miss_n:,} Missing ({fmt_size(miss_bytes)})   |   {part_n:,} Incomplete"
                    )
                    render_v_rows()
                    if is_final and verified_media:
                        v_save_btn.state(["!disabled"])
                post_ui(_upd)

            def worker():
                try:
                    if mode == "log":
                        p = Path(log_path)
                        raw = json.loads(p.read_text(encoding="utf-8"))
                        if isinstance(raw, dict) and raw.get("format") == SAVE_FORMAT and isinstance(raw.get("media"), list):
                            cid = int(raw.get("chat_id") or ch.get("id") or 0)
                            media = list(raw["media"])
                        else:
                            cid, media = read_media_index(p)
                        evaluate_and_display(cid, media, f"media log {p.name}", is_final=True)
                    else:
                        # Live read from Telegram without a saved media log (works while downloading too!)
                        APP_DIR.mkdir(parents=True, exist_ok=True)
                        tmp_exp = APP_DIR / f"verify_export_{os.getpid()}_{int(time.time())}.json"
                        target = ch.get("username") or str(ch["id"])
                        if ENGINE_FILE.exists() and (APP_DIR / "config.json").exists():
                            cmd = [python_exe(), str(ENGINE_FILE), "chat", "export", "-c", target, "--raw", "-o", str(tmp_exp)]
                        elif self.tdl and not self.running:
                            cmd = [self.tdl, "chat", "export", "-c", target, "--raw", "-o", str(tmp_exp), "--ntp", "pool.ntp.org"]
                        else:
                            cmd = [python_exe(), str(ENGINE_FILE), "chat", "export", "-c", target, "--raw", "-o", str(tmp_exp)]
                        post_ui(lambda: v_status_var.set(
                            f"Reading messages directly from Telegram for '{ch.get('visible_name')}' and actively verifying on disk ..."
                        ))
                        kw = {"creationflags": subprocess.CREATE_NO_WINDOW} if IS_WINDOWS else {}
                        env = dict(os.environ, PYTHONIOENCODING="utf-8", PYTHONUTF8="1")
                        proc = subprocess.Popen(cmd, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                                                stderr=subprocess.STDOUT, text=True, encoding="utf-8",
                                                errors="replace", env=env, **kw)
                        v_state["proc"] = proc

                        def try_partial_verify():
                            if not tmp_exp.exists():
                                return
                            cid_p, media_p = int(ch.get("id") or 0), []
                            try:
                                for kind, val in iter_export(tmp_exp):
                                    if kind == "id":
                                        cid_p = val
                                    else:
                                        raw_m = val.get("raw")
                                        cats = classify_raw(raw_m)
                                        if cats and isinstance(val.get("id"), int):
                                            media_p.append({"id": val["id"], "file": val.get("file") or "media",
                                                            "cats": cats, "topic": topic_of(raw_m),
                                                            "size": media_size(raw_m),
                                                            "doc_id": media_doc_id(raw_m)})
                            except Exception:  # noqa: BLE001 (partial JSON at EOF is expected mid-write)
                                pass
                            if media_p:
                                evaluate_and_display(cid_p, media_p, "live Telegram scan (in progress)", is_final=False)

                        try:
                            last_part = time.monotonic()
                            while proc.poll() is None:
                                if v_state["stop"]:
                                    proc.terminate()
                                    break
                                line = proc.stdout.readline() if proc.stdout else ""
                                if line:
                                    s_ln = line.strip()
                                    tlog("verify", f"[live export] {s_ln}")
                                    post_ui(lambda msg=s_ln: v_status_var.set(f"Reading from Telegram: {msg}"))
                                if time.monotonic() - last_part >= 2.5:
                                    last_part = time.monotonic()
                                    try_partial_verify()
                            rest = proc.stdout.read() if proc.stdout else ""
                            if rest:
                                tlog("verify", f"[live export] {rest.strip()}")
                            if v_state["stop"]:
                                post_ui(lambda: v_status_var.set("Verification stopped."))
                                return
                            if proc.returncode != 0 or not tmp_exp.exists():
                                post_ui(lambda: v_status_var.set(
                                    "Couldn't read messages from Telegram (see Activity / Tech log)."
                                ))
                                return
                            cid, media = read_media_index(tmp_exp)
                            evaluate_and_display(cid, media, "live Telegram scan", is_final=True)
                        finally:
                            try:
                                tmp_exp.unlink(missing_ok=True)
                            except OSError:
                                pass
                except Exception as e:  # noqa: BLE001
                    tlog("verify", "verify error:\n" + traceback.format_exc())
                    post_ui(lambda err=f"{type(e).__name__}: {e}": v_status_var.set(f"Verify failed: {err}"))
                finally:
                    def _done():
                        v_state["running"] = False
                        v_state["proc"] = None
                        if win.winfo_exists():
                            v_start_btn.state(["!disabled"])
                            v_stop_btn.state(["disabled"])
                    post_ui(_done)

            threading.Thread(target=worker, daemon=True, name="verify-worker").start()

        v_start_btn.configure(command=run_verify)

        fill_v_chats()
        refresh_preview()
        auto_find_log()
        win.after(120, lambda: pw.sash_place(0, 1, 190) if win.winfo_exists() and not v_focus["on"] else None)
        t1 = self.topic_inc_var.trace_add("write", refresh_preview)
        t2 = self.topic_exc_var.trace_add("write", refresh_preview)

        def on_close_preview():
            v_state["stop"] = True
            p = v_state.get("proc")
            if p is not None and p.poll() is None:
                try:
                    p.terminate()
                except OSError:
                    pass
            try:
                self.topic_inc_var.trace_remove("write", t1)
                self.topic_exc_var.trace_remove("write", t2)
            except Exception:  # noqa: BLE001
                pass
            win.destroy()

        win.protocol("WM_DELETE_WINDOW", on_close_preview)

    def pick_folder(self):
        f = filedialog.askdirectory(parent=self.root, initialdir=self.save_var.get(),
                                    title="Choose where to save the Telegram media")
        if f:
            self.save_var.set(f)
            self.settings["folder"] = f
            save_settings(self.settings)

    def pick_ref_folder(self):
        init_d = self.ref_var.get().split(";")[0].strip() or self.save_var.get()
        f = filedialog.askdirectory(
            parent=self.root, initialdir=init_d,
            title="Choose reference folder (files already in this folder will be skipped)"
        )
        if f:
            self.ref_var.set(f)
            self.settings["ref_folder"] = f
            save_settings(self.settings)
            self.log(f"Reference folder set: {f} (files already in this folder will be skipped)")

    def clear_ref_folder(self):
        self.ref_var.set("")
        self.settings["ref_folder"] = ""
        save_settings(self.settings)
        self.log("Reference folder cleared.")

    def pick_tdl(self):
        types = [("tdl", "tdl.exe"), ("All files", "*.*")] if IS_WINDOWS else [("All files", "*")]
        f = filedialog.askopenfilename(parent=self.root, title="Find tdl", filetypes=types)
        if f:
            self.tdl = f
            self.settings["tdl_path"] = f
            save_settings(self.settings)
            self.log(f"Using tdl at {f}")
            self.load_chats()

    def open_folder(self):
        p = self.save_var.get()
        try:
            if IS_WINDOWS:
                os.startfile(p)  # noqa
            else:
                subprocess.Popen(["xdg-open", p])
        except Exception:  # noqa: BLE001
            pass

    def builtin(self) -> bool:
        return self.engine_var.get() == "builtin"

    def engine_cmd(self) -> list[str]:
        return [python_exe(), str(ENGINE_FILE)] if self.builtin() else [self.tdl]

    def engine_exe(self) -> str:
        return python_exe() if self.builtin() else (self.tdl or "tdl.exe")

    def on_engine(self):
        self.settings["engine"] = self.engine_var.get()
        save_settings(self.settings)
        self.update_engine_ui()
        self.log("Engine: " + ("Built-in (Python/Telethon) - uses its own login, not Telegram Desktop's"
                               if self.builtin() else "tdl"))
        if self.chats:
            # Conversations are the same across engines - keep them ready so switching to tdl never gets stuck
            self.start_btn.state(["!disabled"])
            self.status.set("Ready. Tick what to save, pick a conversation, press Start.")
        else:
            self.load_chats()

    def update_engine_ui(self):
        b = self.builtin()
        self.find_btn.state(["disabled"] if b else ["!disabled"])
        self.login_desk_btn.state(["disabled"] if b else ["!disabled"])
        self.takeout_cb.state(["disabled"] if b else ["!disabled"])

    def need_tdl(self) -> bool:
        if self.builtin():
            if not ENGINE_FILE.exists():
                messagebox.showinfo("Built-in engine missing",
                                    f"Put tg_engine.py in the same folder as this app:\n{ENGINE_FILE.parent}")
                return False
            return True
        if not self.tdl:
            messagebox.showinfo("tdl not found", "Click 'Find tdl.exe...' first.")
            return False
        return True

    def ask_from_worker(self, text: str) -> bool:
        """Lets the download thread ask a yes/no question in the window and wait for the answer."""
        ev, box = threading.Event(), {}
        self.q.put(("ask", text, ev, box))
        ev.wait()
        return bool(box.get("yes"))

    # -- live file list ---------------------------------------------------- #
    def at_bottom(self) -> bool:
        if not self.files.get_children():
            return True
        try:
            return float(self.files.yview()[1]) >= 0.999
        except Exception:  # noqa: BLE001
            return True

    def jump_latest(self):
        kids = self.files.get_children()
        if kids:
            self.files.see(kids[-1])
            self.files.yview_moveto(1.0)

    def apply_live(self, s: dict):
        if "error" in s and "rows" not in s:
            self.log(f"[live view] {s['error']}", "warn")
            return
        follow = self.at_bottom()  # only auto-scroll if you're already looking at the newest rows
        tree = self.files
        st = self.job_state
        for r in s["rows"]:
            iid = self.row_ids.get(r["key"])
            vals = row_values(r)
            if iid is not None and tree.exists(iid):
                tree.item(iid, values=vals, tags=(r["status"],))
            else:
                iid = tree.insert("", "end", values=vals, tags=(r["status"],))
                self.row_ids[r["key"]] = iid
                self.row_keys[iid] = r["key"]
            prev_st = self.row_status.get(r["key"])
            if prev_st != r["status"]:
                self.row_status[r["key"]] = r["status"]
                tlog("file", f"status={r['status']} mid={r.get('mid')} type={r['type']!r} "
                             f"done={r['done']} total={r['total']} speed={fmt_speed(r.get('speed', 0.0))} "
                             f"file={r['name']!r}")
                if st is not None and r.get("mid") is not None:
                    if r["status"] == "done":
                        st.mark(r["mid"], "done")
                    elif r["status"] == "error":
                        st.mark(r["mid"], "failed", "download failed or file disappeared before completion")
                    elif r["status"] in ("active", "stalled", "paused"):
                        st.mark(r["mid"], "downloading")
        if st is not None:
            st.autosave()
        now_m = time.monotonic()
        if now_m - self.last_live_log >= 5.0:
            self.last_live_log = now_m
            tlog("live", f"{s['label']}: {s['finished']}/{s['wanted']} done, active={len(s['active'])}, "
                         f"speed={fmt_speed(s['speed'])}, downloaded={fmt_size(s['downloaded'])}, "
                         f"errors={s['errors']}, eta={fmt_eta(s.get('eta'))}")
        for r in s["active"]:  # files still downloading stay pinned at the bottom
            iid = self.row_ids.get(r["key"])
            if iid is not None:
                tree.move(iid, "", "end")
        excess = len(self.row_ids) - MAX_ROWS
        if excess > 0:  # drop the oldest finished rows so the list stays fast
            for iid in tree.get_children():
                if excess <= 0:
                    break
                if tree.item(iid, "tags") and tree.item(iid, "tags")[0] in ("done", "error"):
                    tree.delete(iid)
                    self.row_ids.pop(self.row_keys.pop(iid, ""), None)
                    excess -= 1
        if follow and s["rows"]:
            self.jump_latest()

        paused = s.get("paused")
        try:
            self.graph.feed(s)
        except Exception as ex:  # noqa: BLE001  (a graph hiccup must never disturb the download view)
            tlog("graph", f"feed failed: {ex!r}")
        self.speed_var.set("Paused" if paused else fmt_speed(s["speed"]))
        n = len(s["active"])
        self.active_var.set(f"Downloading now: {n} file{'s' if n != 1 else ''}")
        if not paused and n > 0 and self.auto_speed_var.get() and self.runner and not self.runner.paused:
            self.check_live_auto_speed(s["active"])
        step = f"  (type {s.get('step')} of {s.get('steps')})" if s.get("steps", 1) > 1 else ""
        self.done_var.set(f"{s['label']}: {s['finished']:,} / {s['wanted']:,} done{step}"
                          f"   -   {fmt_size(s['downloaded'])} this run")
        self.err_var.set(f"{s['errors']:,} failed" if s["errors"] else "")
        self.pbar.configure(maximum=max(1, s["wanted"]), value=s["finished"])
        left = f"{fmt_size(s.get('remaining', 0))} left"
        if paused:
            self.eta_var.set(f"ETA: paused  ({left})")
        elif s.get("eta") is None:
            self.eta_var.set(f"ETA {s['label']}: working it out...  ({left})")
        else:
            self.eta_var.set(f"ETA {s['label']}: {fmt_eta(s['eta'])}  ({left})")
        if s.get("later"):
            all_left = fmt_size(s.get("remaining", 0) + s["later"])
            self.eta_all_var.set(f"Whole job: {'-' if s.get('eta_all') is None or paused else fmt_eta(s['eta_all'])}"
                                 f"  ({all_left} left in total)")
        else:
            self.eta_all_var.set("")
        self.show_waiting(s, paused)
        if s.get("final"):
            self.speed_var.set("-")
            self.active_var.set("Downloading now: -")
            self.eta_var.set("ETA: -")
            self.eta_all_var.set("")
            self.reset_idle()

    WAIT_AFTER = 6.0  # seconds with no progress at all before we call it "waiting on Telegram"

    def reset_idle(self):
        self.idle_sig, self.idle_since, self.last_progress = None, None, None
        try:
            self.eta_label.configure(style="Eta.TLabel")
        except Exception:  # noqa: BLE001
            pass

    def show_waiting(self, s: dict, paused: bool):
        """
        Telegram's "slow down" pauses often happen BETWEEN files (while asking for the next ones), when no
        file is half-downloaded - so no row can turn orange. Detect "nothing moved at all" instead.
        """
        now = time.monotonic()
        sig = (s.get("downloaded"), s.get("finished"), tuple(sorted((r["key"], r["done"]) for r in s.get("active", []))))
        if getattr(self, "idle_sig", None) != sig or paused:
            if getattr(self, "idle_since", None) is not None and not paused:
                waited = now - self.idle_since
                if waited >= self.WAIT_AFTER:
                    self.log(f"Telegram made us wait about {waited:.0f}s (its rate limit) - carried on by itself.", "warn")
                    self.waits = getattr(self, "waits", 0) + 1
            self.idle_sig, self.idle_since = sig, None
            self.last_progress = now
            self.eta_label.configure(style="Eta.TLabel")
            return
        if self.idle_since is None:
            self.idle_since = getattr(self, "last_progress", None) or now
        idle = now - self.idle_since
        if idle >= self.WAIT_AFTER and s.get("finished", 0) < s.get("wanted", 0):
            self.speed_var.set("Waiting")
            self.eta_var.set(f"Waiting on Telegram - {idle:.0f}s so far (its rate limit; it carries on by itself)")
            self.eta_label.configure(style="Wait.TLabel")

    # -- actions ------------------------------------------------------------ #
    def load_cached_chats(self):
        """Loads last saved chat list immediately on startup so you never have to wait to press Start."""
        try:
            raw = json.loads(CHATS_CACHE_FILE.read_text(encoding="utf-8"))
            if isinstance(raw, list) and raw:
                self.chats = sorted([d for d in raw if isinstance(d, dict) and "id" in d],
                                    key=lambda c: (c.get("visible_name") or "").lower())
                if self.chats:
                    self.refresh_list()
                    self.start_btn.state(["!disabled"])
                    self.status.set(f"Ready ({len(self.chats)} conversations loaded - click 'Reload list' to refresh).")
        except (OSError, ValueError):
            pass

    def load_chats(self):
        if not self.need_tdl():
            return
        self.status.set("Loading your chats ...")
        self.start_btn.state(["disabled"])
        cmd = self.engine_cmd()
        is_builtin = self.builtin()
        exe_name = self.engine_exe()

        def run_py_fallback(reason: str) -> bool:
            if is_builtin or not ENGINE_FILE.exists():
                return False
            try:
                py_cmd = [python_exe(), str(ENGINE_FILE), "chat", "ls", "-o", "json"]
                c2, out2 = Runner().capture(py_cmd, timeout=180)
                if c2 == 0:
                    parsed = parse_chat_list(out2)
                    self.q.put(("log_warn",
                                f"tdl chat list {reason} - loaded your {len(parsed)} conversations using the "
                                "Built-in Python engine instead (tdl is still active for downloading)."))
                    self.q.put(("chats", parsed))
                    return True
            except Exception:  # noqa: BLE001
                pass
            return False

        def work():
            # If we're idle and using tdl, clear any stuck background tdl.exe holding ~/.tdl/data lock
            if not is_builtin and IS_WINDOWS and not self.running:
                try:
                    subprocess.run(["taskkill", "/F", "/IM", Path(exe_name).name],
                                   stdin=subprocess.DEVNULL, capture_output=True,
                                   creationflags=subprocess.CREATE_NO_WINDOW)
                except OSError:
                    pass
            try:
                # Give tdl 15s to list chats (with --ntp pool.ntp.org); if it hangs, fall back to Python engine
                t_lim = 180 if is_builtin else (15 if (ENGINE_FILE.exists() and (APP_DIR / "config.json").exists()) else 60)
                ls_args = cmd + ["chat", "ls", "-o", "json"] + ([] if is_builtin else ["--ntp", "pool.ntp.org"])
                code, out = Runner().capture(ls_args, timeout=t_lim)
                if code != 0:
                    if run_py_fallback("returned an error"):
                        return
                    self.q.put(("chats_error", out))
                    return
                self.q.put(("chats", parse_chat_list(out)))
            except subprocess.TimeoutExpired:
                if not is_builtin and IS_WINDOWS and not self.running:
                    try:
                        subprocess.run(["taskkill", "/F", "/IM", Path(exe_name).name],
                                       stdin=subprocess.DEVNULL, capture_output=True,
                                       creationflags=subprocess.CREATE_NO_WINDOW)
                    except OSError:
                        pass
                if run_py_fallback("took too long"):
                    return
                self.q.put(("chats_error", "tdl timed out while listing your chats."))
            except Exception as e:  # noqa: BLE001
                if run_py_fallback("failed"):
                    return
                self.q.put(("chats_error", f"{type(e).__name__}: {e}"))
        threading.Thread(target=work, daemon=True).start()

    def login(self, extra: list[str]):
        if not self.need_tdl():
            return
        self.log("Opening a window to log in - follow the instructions there.")
        cmd, builtin = self.engine_cmd(), self.builtin()

        def work():
            login_args = ["login"] if builtin else (extra + ["--ntp", "pool.ntp.org"])
            code = Runner().visible("Telegram Media Saver - log in", cmd + login_args)
            self.q.put(("log", "Log-in finished." if code == 0 else "Log-in didn't finish (see the tdl window)."))
            if code == 0:
                self.q.put(("reload", None))
        threading.Thread(target=work, daemon=True).start()

    def on_start(self):
        sel = self.chat_list.curselection()
        if not sel:
            messagebox.showinfo("Pick a conversation", "Select a conversation in the list first.")
            return
        selected = set(ALL_KEYS) if self.every.get() else {k for k, v in self.vars.items() if v.get()}
        if not selected:
            messagebox.showinfo("Nothing selected", "Tick at least one media type (or 'Everything').")
            return
        chat = self.chats[self.shown[sel[0]]]
        spec = {"chat": chat, "folder": self.save_var.get(),
                "ref_folder": self.ref_var.get().strip(),
                "selected": sorted(selected),
                "topic_include": self.topic_inc_var.get().strip(),
                "topic_exclude": self.topic_exc_var.get().strip(),
                "reuse": bool(self.reuse_var.get()), "source": "Start button"}
        ls = self.loaded_save
        if ls is not None:
            if int(ls.get("chat", {}).get("id") or 0) == int(chat.get("id") or 0):
                spec["preloaded"] = ls
            else:
                self.log("The loaded save file is for a different conversation - reading this one normally.", "warn")
            self.loaded_save = None
        self.start_job(spec)

    def start_job(self, spec: dict) -> bool:
        """Starts one download job. `spec` comes from the main window (Start) or from the queue."""
        if self.running:
            return False
        try:
            threads = max(1, min(16, int(self.threads_var.get())))
            limit = max(1, min(MAX_FILES_AT_ONCE, int(self.limit_var.get())))
        except (tk.TclError, ValueError, TypeError):
            messagebox.showinfo("Speed", "Speed settings must be whole numbers.")
            return False
        chat, selected = spec["chat"], set(spec["selected"])
        folder = Path(spec["folder"])
        ref_folder = str(spec.get("ref_folder") if "ref_folder" in spec else self.ref_var.get()).strip()
        topic_inc, topic_exc = spec.get("topic_include", ""), spec.get("topic_exclude", "")
        auto_sp = bool(self.auto_speed_var.get())
        # show what's running in the main window
        self.save_var.set(str(folder))
        self.ref_var.set(ref_folder)
        self.every.set(selected == set(ALL_KEYS))
        for k, v in self.vars.items():
            v.set(k in selected)
        self.topic_inc_var.set(topic_inc)
        self.topic_exc_var.set(topic_exc)
        self.select_chat_by_id(chat.get("id"))
        self.settings.update(threads=threads, limit=limit, takeout=bool(self.takeout_var.get()),
                             keep_awake=bool(self.awake_var.get()),
                             topic_include=topic_inc, topic_exclude=topic_exc, auto_speed=auto_sp,
                             ref_folder=ref_folder)
        save_settings(self.settings)

        who = "Built-in engine" if self.builtin() else "tdl"
        self.job_state = JobState(chat, folder, selected, topic_inc, topic_exc, who, ref_dir=ref_folder)
        self.job_state.event(f"Job started from {spec.get('source', '?')}: "
                             f"{chat.get('visible_name') or chat.get('id')} -> {folder}"
                             + (f"  (ref: {ref_folder})" if ref_folder else "")
                             + f"  types={sorted(selected)}")
        self.current_spec = spec
        self.row_status.clear()
        self.graph.new_run()
        self.runner = Runner(self.engine_exe())
        self.runner.auto_speed = auto_sp
        self.runner.cur_speed = (threads, limit)
        self.last_auto_shift = time.monotonic()
        self.set_running(True)
        self.err_var.set("")
        self.log(f"Starting: {chat.get('visible_name') or chat['id']}  ->  {folder}"
                 + (f"  (skipping files in reference: {ref_folder})" if ref_folder else "")
                 + (f"  (from the queue, {len(self.queue_items)} more waiting)" if spec.get("source") == "queue" else ""))
        tlog("job", "spec: " + json.dumps({k: v for k, v in spec.items() if k not in ("preloaded", "chat")},
                                          ensure_ascii=False)
             + f"  chat_id={chat.get('id')} threads={threads} limit={limit} auto={auto_sp} engine={who} "
               f"takeout={bool(self.takeout_var.get())}")
        args = (self.runner, self.engine_cmd(), chat, folder, selected, threads, limit,
                bool(self.takeout_var.get()), bool(spec.get("reuse")))
        state, preloaded = self.job_state, spec.get("preloaded")

        def work():
            try:
                result = run_job(*args, ui=lambda *m: self.q.put(m), ask=self.ask_from_worker,
                                 topic_include=topic_inc, topic_exclude=topic_exc,
                                 state=state, preloaded=preloaded, ref_dir=ref_folder)
            except Exception as e:  # noqa: BLE001
                tlog("crash", "run_job failed:\n" + traceback.format_exc())
                result = f"error:{type(e).__name__}: {e}"
            self.q.put(("done", result))
        threading.Thread(target=work, daemon=True, name="download-job").start()
        return True

    def select_chat_by_id(self, cid) -> bool:
        if cid is None:
            return False
        for pos, idx in enumerate(self.shown):
            if str(self.chats[idx].get("id")) == str(cid):
                break
        else:
            if self.search_var.get():
                self.search_var.set("")  # the chat may just be hidden by the search box
            for pos, idx in enumerate(self.shown):
                if str(self.chats[idx].get("id")) == str(cid):
                    break
            else:
                return False
        st = str(self.chat_list.cget("state"))
        self.chat_list.configure(state="normal")
        self.chat_list.selection_clear(0, "end")
        self.chat_list.selection_set(pos)
        self.chat_list.see(pos)
        self.chat_list.configure(state=st)
        self.update_topic_filter_ui()
        return True

    # -- progress save files ------------------------------------------------- #
    def default_save_name(self) -> str:
        st = self.job_state
        name = (st.chat.get("visible_name") if st else "") or "chat"
        return f"{safe_name(name, 50)}_{time.strftime('%Y-%m-%d_%H-%M')}{SAVE_EXT}"

    def save_progress(self) -> bool:
        st = self.job_state
        if st is None or not st.media:
            messagebox.showinfo("Nothing to save yet",
                                "Start a download first - once the chat's message list has been read it can be saved.")
            return False
        chat_dir = Path(st.base_dir) / safe_name(st.chat.get("visible_name") or st.chat.get("username")
                                                 or str(st.chat.get("id")))
        path = filedialog.asksaveasfilename(
            parent=self.root, title="Save download progress", defaultextension=SAVE_EXT,
            initialdir=str(chat_dir if chat_dir.exists() else st.base_dir), initialfile=self.default_save_name(),
            filetypes=[("Telegram Media Saver save", f"*{SAVE_EXT}"), ("JSON", "*.json"), ("All files", "*.*")])
        if not path:
            tlog("save", "save dialog cancelled")
            return False
        try:
            st.event(f"Saved by you to {path}")
            st.save(path)
        except OSError as e:
            messagebox.showerror("Couldn't save", f"{e}")
            return False
        c = st.counts()
        self.log(f"Progress saved: {path}  ({c.get('done', 0):,} done, {c.get('failed', 0):,} failed, "
                 f"{c.get('pending', 0) + c.get('downloading', 0):,} left)", "ok")
        return True

    def offer_save(self, why: str) -> None:
        st = self.job_state
        if st is None or not st.media:
            return
        c = st.counts()
        if messagebox.askyesno(
                "Save progress?",
                f"Download {why}.\n\nSave a progress file? It keeps this chat's message list and what has / hasn't "
                f"downloaded ({c.get('done', 0):,} done, {c.get('failed', 0):,} failed, "
                f"{c.get('pending', 0) + c.get('downloading', 0):,} left), so 'Load save' can pick up later "
                "without reading the chat again.\n\n(An automatic copy is also kept in the chat's .tms folder.)"):
            self.save_progress()

    def load_save_dialog(self):
        if self.running:
            messagebox.showinfo("Busy", "Stop the current download first (or add the save file to the queue).")
            return
        path = filedialog.askopenfilename(
            parent=self.root, title="Load a download progress save",
            initialdir=self.save_var.get(),
            filetypes=[("Telegram Media Saver save", f"*{SAVE_EXT}"), ("JSON", "*.json"), ("All files", "*.*")])
        if not path:
            return
        try:
            data = read_save_file(path)
        except (OSError, ValueError) as e:
            tlog("save", f"load failed {path}: {e}")
            messagebox.showerror("Couldn't load", str(e))
            return
        tlog("save", f"loaded save file {path}  summary={data.get('summary')}")
        chat = dict(data["chat"])
        if not any(str(c.get("id")) == str(chat.get("id")) for c in self.chats):
            self.chats.append(chat)
            self.chats.sort(key=lambda c: (c.get("visible_name") or "").lower())
            self.refresh_list()
        if data.get("save_folder"):
            self.save_var.set(str(data["save_folder"]))
        if "reference_folder" in data and data.get("reference_folder"):
            self.ref_var.set(str(data["reference_folder"]))
        sel = set(data.get("selected_types") or [])
        self.every.set(sel == set(ALL_KEYS))
        for k, v in self.vars.items():
            v.set(k in sel)
        self.lock_checkboxes()
        self.topic_inc_var.set(data.get("topic_include") or "")
        self.topic_exc_var.set(data.get("topic_exclude") or "")
        self.select_chat_by_id(chat.get("id"))
        self.loaded_save = data
        c = collections.Counter(m.get("status", "pending") for m in data["media"])
        left = c.get("pending", 0) + c.get("downloading", 0) + c.get("failed", 0)
        self.log(f"Loaded save: {chat.get('visible_name')} - {len(data['media']):,} media messages, "
                 f"{c.get('done', 0):,} done, {c.get('failed', 0):,} failed, {left:,} to (re)try. "
                 f"Saved {data.get('saved_at', '?')}.", "ok")
        self.status.set("Save loaded - press Start to pick up where it left off (no rescan).")
        if messagebox.askyesno("Save loaded", f"Loaded the save for '{chat.get('visible_name')}'.\n\n"
                                              f"{c.get('done', 0):,} done, {left:,} still to download.\n\n"
                                              "Start downloading now?"):
            self.on_start()

    # -- technical log --------------------------------------------------------- #
    def open_tech_log(self):
        p = TLOG.path
        if not p or not p.exists():
            messagebox.showinfo("Technical log", "The technical log couldn't be created this session.")
            return
        tlog("app", "tech log opened by you")
        self.open_in_editor(p, "technical log")

    def install_crash_hooks(self):
        def hook(et, ev, tb):
            tlog("crash", "".join(traceback.format_exception(et, ev, tb)))
            sys.__excepthook__(et, ev, tb)

        def thook(a):
            tlog("crash", f"thread {getattr(a.thread, 'name', '?')}:\n"
                 + "".join(traceback.format_exception(a.exc_type, a.exc_value, a.exc_traceback)))
        sys.excepthook = hook
        threading.excepthook = thook

    def on_tk_error(self, et, ev, tb):
        tlog("crash", "window callback:\n" + "".join(traceback.format_exception(et, ev, tb)))
        try:
            self.log(f"[internal] {et.__name__}: {ev}", "err")
        except Exception:  # noqa: BLE001
            pass

    # -- queue ----------------------------------------------------------------- #
    def load_queue(self) -> list[dict]:
        try:
            data = json.loads(QUEUE_FILE.read_text(encoding="utf-8"))
            items = [d for d in data if isinstance(d, dict) and isinstance(d.get("chat"), dict)]
            tlog("queue", f"loaded {len(items)} queued job(s) from {QUEUE_FILE}")
            return items
        except (OSError, ValueError, TypeError):
            return []

    def save_queue(self):
        try:
            APP_DIR.mkdir(parents=True, exist_ok=True)
            tmp = QUEUE_FILE.with_suffix(".tmp")
            tmp.write_text(json.dumps(self.queue_items, ensure_ascii=False, indent=1), encoding="utf-8")
            os.replace(tmp, QUEUE_FILE)
        except OSError as e:
            tlog("queue", f"couldn't save the queue: {e}")

    @staticmethod
    def queue_label(i: int, it: dict) -> str:
        sel = it.get("selected") or []
        types = "Everything" if set(sel) == set(ALL_KEYS) else ", ".join(FOLDER_NAMES.get(k, k) for k in sel)
        s = f"{i}. {it['chat'].get('visible_name') or it['chat'].get('id')}   |   {types}   |   -> {it.get('folder')}"
        if it.get("ref_folder"):
            s += f"   |   ref: {it['ref_folder']}"
        if it.get("topic_include"):
            s += f"   |   include: {it['topic_include']}"
        if it.get("topic_exclude"):
            s += f"   |   exclude: {it['topic_exclude']}"
        if it.get("save_file"):
            s += f"   |   from save: {Path(it['save_file']).name}"
        elif it.get("reuse"):
            s += "   |   reuse last list"
        return s

    def refresh_queue_list(self):
        self.queue_list.delete(0, "end")
        for i, it in enumerate(self.queue_items, 1):
            self.queue_list.insert("end", self.queue_label(i, it))
        n = len(self.queue_items)
        self.queue_info_var.set(
            "Queue is empty. 'Add to queue...' sets up another download (any conversation - or the same one with "
            "other types, topics or folder)." if not n else
            f"{n} job(s) waiting. When the current download finishes, the next one starts by itself "
            "(pressing Stop pauses the queue; 'Start queue now' carries on). Double-click a job to edit it.")

    def queue_sel(self) -> int | None:
        s = self.queue_list.curselection()
        return s[0] if s and s[0] < len(self.queue_items) else None

    def edit_queue_item(self):
        i = self.queue_sel()
        if i is None:
            messagebox.showinfo("Queue", "Pick a job in the queue first.")
            return
        self.open_queue_dialog(i)

    def remove_queue_item(self):
        i = self.queue_sel()
        if i is None:
            return
        it = self.queue_items.pop(i)
        tlog("queue", f"removed: {self.queue_label(i + 1, it)}")
        self.save_queue()
        self.refresh_queue_list()

    def move_queue_item(self, d: int):
        i = self.queue_sel()
        if i is None or not 0 <= i + d < len(self.queue_items):
            return
        q = self.queue_items
        q[i], q[i + d] = q[i + d], q[i]
        self.save_queue()
        self.refresh_queue_list()
        self.queue_list.selection_set(i + d)
        tlog("queue", f"moved job {i + 1} -> {i + d + 1}")

    def clear_queue(self):
        if self.queue_items and messagebox.askyesno("Clear queue", f"Remove all {len(self.queue_items)} queued job(s)?"):
            self.queue_items.clear()
            self.save_queue()
            self.refresh_queue_list()
            tlog("queue", "cleared")

    def start_next_in_queue(self):
        if self.running:
            return
        while self.queue_items:
            it = self.queue_items.pop(0)
            self.save_queue()
            self.refresh_queue_list()
            spec = {"chat": it["chat"], "folder": it.get("folder") or self.save_var.get(),
                    "ref_folder": it.get("ref_folder", self.ref_var.get()).strip(),
                    "selected": it.get("selected") or [], "topic_include": it.get("topic_include", ""),
                    "topic_exclude": it.get("topic_exclude", ""), "reuse": bool(it.get("reuse")),
                    "source": "queue"}
            if not spec["selected"]:
                self.log(f"Queue: skipped '{it['chat'].get('visible_name')}' - no media types ticked.", "warn")
                continue
            if it.get("save_file"):
                try:
                    data = read_save_file(it["save_file"])
                    if str(data["chat"].get("id")) == str(it["chat"].get("id")):
                        spec["preloaded"] = data
                    else:
                        self.log("Queue: that job's save file is for another chat - reading the chat normally.", "warn")
                except (OSError, ValueError) as e:
                    self.log(f"Queue: couldn't read the save file ({e}) - reading the chat normally.", "warn")
            tlog("queue", f"starting next job: {self.queue_label(1, it)}")
            if not self.start_job(spec):
                self.queue_items.insert(0, it)
                self.save_queue()
                self.refresh_queue_list()
            return
        self.log("The queue is empty.")

    def open_queue_dialog(self, index: int | None = None):
        """A full setup window for one queued job: folder, types, conversation, topic filter, save file."""
        editing = index is not None
        it = dict(self.queue_items[index]) if editing else {}
        win = tk.Toplevel(self.root)
        win.title("Edit queued download" if editing else "Add a download to the queue")
        win.geometry("760x720")
        themed(win, bg="panel")
        win.transient(self.root)
        dark_title_bar(win)
        frm = ttk.Frame(win, padding=12)
        frm.pack(fill="both", expand=True)

        # defaults: the job being edited, otherwise whatever the main window is set to right now
        cur = self.selected_chat()
        folder_v = tk.StringVar(value=it.get("folder") or self.save_var.get())
        ref_v = tk.StringVar(value=it.get("ref_folder", "") if editing else self.ref_var.get())
        sel0 = set(it["selected"]) if editing else (
            set(ALL_KEYS) if self.every.get() else {k for k, v in self.vars.items() if v.get()})
        inc_v = tk.StringVar(value=it.get("topic_include", "") if editing else self.topic_inc_var.get())
        exc_v = tk.StringVar(value=it.get("topic_exclude", "") if editing else self.topic_exc_var.get())
        save_v = tk.StringVar(value=it.get("save_file", ""))
        reuse_v = tk.BooleanVar(value=bool(it.get("reuse", False)))
        chosen = {"chat": it.get("chat") or cur}

        ttk.Label(frm, text="Save to", style="Head.TLabel").pack(anchor="w")
        r1 = ttk.Frame(frm)
        r1.pack(fill="x", pady=(2, 6))
        ttk.Entry(r1, textvariable=folder_v).pack(side="left", fill="x", expand=True)

        def browse_folder():
            f = filedialog.askdirectory(parent=win, initialdir=folder_v.get(), title="Where should this job save to?")
            if f:
                folder_v.set(f)
        ttk.Button(r1, text="Browse...", command=browse_folder).pack(side="left", padx=(8, 0))

        ttk.Label(frm, text="Reference folder (optional - skip files already in this folder on another drive)",
                  style="Head.TLabel").pack(anchor="w")
        r1_ref = ttk.Frame(frm)
        r1_ref.pack(fill="x", pady=(2, 8))
        ttk.Entry(r1_ref, textvariable=ref_v).pack(side="left", fill="x", expand=True)

        def browse_ref_q():
            f = filedialog.askdirectory(parent=win, initialdir=ref_v.get() or folder_v.get(),
                                        title="Choose reference folder whose files should be skipped")
            if f:
                ref_v.set(f)
        ttk.Button(r1_ref, text="Browse...", command=browse_ref_q).pack(side="left", padx=(8, 0))
        ttk.Button(r1_ref, text="Clear", command=lambda: ref_v.set("")).pack(side="left", padx=(6, 0))

        ttk.Label(frm, text="What to save", style="Head.TLabel").pack(anchor="w")
        r2 = ttk.Frame(frm)
        r2.pack(fill="x", pady=(2, 8))
        tvars = {k: tk.BooleanVar(value=k in sel0) for k, _ in CATEGORIES}
        every_v = tk.BooleanVar(value=sel0 == set(ALL_KEYS))

        def on_every():
            for v in tvars.values():
                v.set(every_v.get())
        for i, (k, label) in enumerate(CATEGORIES):
            ttk.Checkbutton(r2, text=label, variable=tvars[k]).grid(row=i // 4, column=i % 4, sticky="w", padx=8, pady=2)
        ttk.Checkbutton(r2, text="Everything", variable=every_v, command=on_every).grid(row=1, column=3, sticky="w",
                                                                                       padx=8, pady=2)
        for c in range(4):
            r2.columnconfigure(c, weight=1)

        ttk.Label(frm, text="Conversation", style="Head.TLabel").pack(anchor="w")
        r3 = ttk.Frame(frm)
        r3.pack(fill="x", pady=(2, 4))
        ttk.Label(r3, text="Search").pack(side="left")
        qsearch = tk.StringVar()
        ttk.Entry(r3, textvariable=qsearch).pack(side="left", fill="x", expand=True, padx=8)
        lf = ttk.Frame(frm)
        lf.pack(fill="both", expand=True)
        lb = tk.Listbox(lf, exportselection=False, height=8)
        dark_tk_widget(lb, "list")
        lsb = NeonScrollbar(lf, orient="vertical", command=lb.yview)
        lb.configure(yscrollcommand=lsb.set)
        lb.pack(side="left", fill="both", expand=True)
        lsb.pack(side="left", fill="y")
        chosen_v = tk.StringVar()
        ttk.Label(frm, textvariable=chosen_v, style="Muted.TLabel").pack(anchor="w", pady=(2, 8))
        shown_q: list[dict] = []

        def fill_list(*_):
            needle = qsearch.get().strip().lower()
            lb.delete(0, "end")
            shown_q.clear()
            pool = list(self.chats)
            ch = chosen["chat"]
            if ch and not any(str(c.get("id")) == str(ch.get("id")) for c in pool):
                pool.insert(0, ch)
            for c in pool:
                n_topics = len(c.get("topics") or [])
                kind = f"forum, {n_topics} topics" if n_topics else c.get("type", "?")
                label = f"{c.get('visible_name') or '-'}   [{kind}]" + (f"   @{c['username']}" if c.get("username") else "")
                if needle in label.lower():
                    shown_q.append(c)
                    lb.insert("end", label)
                    if ch and str(c.get("id")) == str(ch.get("id")):
                        lb.selection_set("end")
                        lb.see("end")

        def on_pick(*_):
            s = lb.curselection()
            if s and s[0] < len(shown_q):
                chosen["chat"] = shown_q[s[0]]
            update_info()
        lb.bind("<<ListboxSelect>>", on_pick)
        qsearch.trace_add("write", fill_list)

        ttk.Label(frm, text="Forum topics (optional)", style="Head.TLabel").pack(anchor="w")
        r4 = ttk.Frame(frm)
        r4.pack(fill="x", pady=(2, 2))
        ttk.Label(r4, text="Include").grid(row=0, column=0, sticky="w")
        ttk.Entry(r4, textvariable=inc_v).grid(row=0, column=1, sticky="ew", padx=(6, 14))
        ttk.Label(r4, text="Exclude").grid(row=0, column=2, sticky="w")
        ttk.Entry(r4, textvariable=exc_v).grid(row=0, column=3, sticky="ew", padx=(6, 0))
        r4.columnconfigure(1, weight=1)
        r4.columnconfigure(3, weight=1)
        match_v = tk.StringVar()
        ttk.Label(frm, textvariable=match_v, style="Muted.TLabel").pack(anchor="w", pady=(0, 8))

        ttk.Label(frm, text="Pick up from a save file (optional - skips reading the chat again)",
                  style="Head.TLabel").pack(anchor="w")
        r5 = ttk.Frame(frm)
        r5.pack(fill="x", pady=(2, 4))
        ttk.Entry(r5, textvariable=save_v).pack(side="left", fill="x", expand=True)

        def browse_save():
            p = filedialog.askopenfilename(parent=win, title="Pick a save file", initialdir=folder_v.get(),
                                           filetypes=[("Telegram Media Saver save", f"*{SAVE_EXT}"),
                                                      ("JSON", "*.json"), ("All files", "*.*")])
            if not p:
                return
            try:
                data = read_save_file(p)
            except (OSError, ValueError) as e:
                messagebox.showerror("Couldn't load", str(e), parent=win)
                return
            save_v.set(p)
            # fill the rest of the form in from the save
            chosen["chat"] = dict(data["chat"])
            if data.get("save_folder"):
                folder_v.set(str(data["save_folder"]))
            s = set(data.get("selected_types") or [])
            for k, v in tvars.items():
                v.set(k in s)
            every_v.set(s == set(ALL_KEYS))
            inc_v.set(data.get("topic_include") or "")
            exc_v.set(data.get("topic_exclude") or "")
            qsearch.set("")
            fill_list()
            update_info()
        ttk.Button(r5, text="Browse...", command=browse_save).pack(side="left", padx=(8, 0))
        ttk.Button(r5, text="Clear", command=lambda: save_v.set("")).pack(side="left", padx=(6, 0))
        ttk.Checkbutton(frm, variable=reuse_v,
                        text="Otherwise re-use the chat's last message list if there is one (skips the rescan)"
                        ).pack(anchor="w", pady=(2, 8))

        def update_info(*_):
            ch = chosen["chat"]
            chosen_v.set(f"Chosen: {ch.get('visible_name') or ch.get('id')}" if ch else "Chosen: (none - pick one above)")
            topics = [t for t in ((ch or {}).get("topics") or []) if isinstance(t, dict)]
            inc_r, exc_r = parse_topic_rules(inc_v.get()), parse_topic_rules(exc_v.get())
            if not topics:
                match_v.set("Not a forum - the topic filter is ignored for this conversation." if ch and (inc_r or exc_r)
                            else 'Syntax:  "house " + num   |   "house " + word   |   "house " + *   (; for several)')
            elif not inc_r and not exc_r:
                match_v.set(f"All {len(topics):,} topics will be downloaded.")
            else:
                kept = [str(t.get("title") or "") for t in topics if topic_matches(str(t.get("title") or ""), inc_r, exc_r)]
                match_v.set(f"Matching {len(kept):,} of {len(topics):,} topics"
                            + (f"  (e.g. {', '.join(kept[:4])})" if kept else ""))
        inc_v.trace_add("write", update_info)
        exc_v.trace_add("write", update_info)

        bt = ttk.Frame(frm)
        bt.pack(fill="x", pady=(6, 0))

        def ok():
            ch = chosen["chat"]
            sel = set(ALL_KEYS) if every_v.get() else {k for k, v in tvars.items() if v.get()}
            if not ch:
                messagebox.showinfo("Pick a conversation", "Choose a conversation in the list.", parent=win)
                return
            if not sel:
                messagebox.showinfo("Nothing selected", "Tick at least one media type.", parent=win)
                return
            if not folder_v.get().strip():
                messagebox.showinfo("Save to", "Choose where this job should save to.", parent=win)
                return
            item = {"chat": ch, "folder": folder_v.get().strip(), "ref_folder": ref_v.get().strip(),
                    "selected": [k for k in ALL_KEYS if k in sel],
                    "topic_include": inc_v.get().strip(), "topic_exclude": exc_v.get().strip(),
                    "reuse": bool(reuse_v.get()), "save_file": save_v.get().strip(), "added": now_iso()}
            if editing:
                self.queue_items[index] = item
            else:
                self.queue_items.append(item)
            self.save_queue()
            self.refresh_queue_list()
            pos = index if editing else len(self.queue_items) - 1
            tlog("queue", ("edited" if editing else "added") + f": {self.queue_label(pos + 1, item)}")
            self.log(("Queue job updated: " if editing else "Added to queue: ") + self.queue_label(pos + 1, item))
            win.destroy()
        ttk.Button(bt, text="Save changes" if editing else "Add to queue", style="Accent.TButton",
                   command=ok).pack(side="right")
        ttk.Button(bt, text="Cancel", command=win.destroy).pack(side="right", padx=(0, 8))
        fill_list()
        update_info()
        win.grab_set()

    def on_auto_speed_toggle(self):
        auto_sp = bool(self.auto_speed_var.get())
        self.settings["auto_speed"] = auto_sp
        save_settings(self.settings)
        if self.runner and self.running:
            self.runner.auto_speed = auto_sp
            if auto_sp:
                self.last_auto_shift = 0.0  # allow immediate shift if needed
                self.log("Auto-tune speed enabled: will adjust connections/file & files at once by file size.", "ok")
            else:
                self.log("Auto-tune speed turned off: using your manual speed boxes.")

    def check_live_auto_speed(self, active_rows: list[dict]):
        """Watches active downloads; if a wave of bigger/smaller files arrives and tdl isn't tuned for it, shifts."""
        r = self.runner
        if not r or not r.downloading or r.stopped:
            return
        now = time.monotonic()
        if now - getattr(self, "last_auto_shift", 0.0) < 30.0:
            return
        sizes_now = [int(row.get("total") or 0) for row in active_rows if int(row.get("total") or 0) > 0]
        if not sizes_now:
            return
        target_t, target_l, desc = auto_speed_for_sizes(sizes_now)
        if (target_t, target_l) == r.cur_speed:
            return
        # Don't interrupt if any active file already has > 60 MB downloaded on disk (let size-tier batching handle it)
        max_done = max((int(row.get("done") or 0) for row in active_rows), default=0)
        if max_done > 60 * _MB:
            return
        self.last_auto_shift = now
        r.cur_speed = (target_t, target_l)
        self.threads_var.set(target_t)
        self.limit_var.set(target_l)
        if r.apply_speed(target_t, target_l, auto_speed=True):
            self.pause_btn.configure(text="Pause")
            self.log(f"Auto-speed detected {desc}: switched to {target_t} connections/file, "
                     f"{target_l} files at once.", "ok")

    def on_apply_speed(self):
        r = self.runner
        if not r or not self.running:
            return
        try:
            threads = max(1, min(16, int(self.threads_var.get())))
            limit = max(1, min(MAX_FILES_AT_ONCE, int(self.limit_var.get())))
        except (tk.TclError, ValueError, TypeError):
            messagebox.showinfo("Speed", "Speed settings must be whole numbers.")
            return
        self.threads_var.set(threads)
        self.limit_var.set(limit)
        # Clicking "Apply now" applies your manual numbers (turns off auto-speed if you changed the numbers)
        auto_sp = bool(self.auto_speed_var.get())
        if (threads, limit) != r.cur_speed and auto_sp:
            auto_sp = False
            self.auto_speed_var.set(False)
        topic_inc = self.topic_inc_var.get().strip()
        topic_exc = self.topic_exc_var.get().strip()
        self.settings.update(threads=threads, limit=limit,
                             topic_include=topic_inc, topic_exclude=topic_exc,
                             auto_speed=auto_sp)
        save_settings(self.settings)
        r.cur_speed = (threads, limit)
        if r.apply_speed(threads, limit, topic_inc, topic_exc, auto_speed=auto_sp):
            self.pause_btn.configure(text="Pause")  # the restarted tdl isn't paused
            self.log(f"Applying {threads} connection(s) per file, {limit} file(s) at once"
                     + (" (and updated topic filter)" if (topic_inc or topic_exc) else "")
                     + " - restarting tdl on what's left (no rescan; files that were half-done start over).", "warn")
        else:
            self.log(f"Will use {threads} connection(s) per file, {limit} file(s) at once "
                     "as soon as downloading starts.")

    def on_pause(self):
        r = self.runner
        if not r or not self.running:
            return
        if r.paused:
            r.resume()
            self.pause_btn.configure(text="Pause")
            if self.job_state:
                self.job_state.event("Resumed by user")
                self.job_state.autosave(force=True)
            self.log("Resumed.")
        elif r.pause():
            self.pause_btn.configure(text="Resume")
            self.speed_var.set("Paused")
            if self.job_state:
                self.job_state.event("Paused by user")
                self.job_state.autosave(force=True)
            self.log("Paused. Half-downloaded files stay as they are. Press Resume to carry on "
                     "(after a long pause tdl may need a moment to reconnect).")
            self.offer_save("is paused")
        else:
            self.log("Couldn't pause right now (tdl is between steps) - try again in a second.", "warn")

    def on_stop(self):
        if self.runner:
            if self.job_state:
                self.job_state.event("Stopped by user")
                self.job_state.autosave(force=True)
            self.log("Stopping ... (finished files are kept; press Start again to continue)", "warn")
            self.runner.stop()

    def on_close(self):
        if self.running:
            if UI.get("confirm_quit", True) and not messagebox.askyesno(
                    "Quit", "A download is running. Stop it and quit?\n\n"
                            "Start it again later - finished files are skipped."):
                return
            if self.runner:
                self.runner.stop()
            if self.job_state:
                self.job_state.event("Window closed while running")
                self.job_state.autosave(force=True)
        if self.mon_thread:
            self.mon_thread.stop()
        keep_awake(False)
        try:
            if self.root.state() == "normal" and UI.get("remember_geo", True):
                self.settings["geometry"] = self.root.geometry()
            self.settings["folder"] = self.save_var.get()
            self.settings["dock"] = self.dock.state()
            save_settings(self.settings)
        except Exception:  # noqa: BLE001
            pass
        tlog("app", "closing")
        TLOG.close()
        self.root.destroy()

    # -- event pump ---------------------------------------------------------- #
    def jump_console_bottom(self):
        try:
            self.console_text.see("end")
            self.console_text.yview_moveto(1.0)
        except Exception:  # noqa: BLE001
            pass

    def poll_console(self):
        """Updates the embedded tdl / Console view whenever the live console snapshot changes."""
        try:
            st = CONSOLE_SNAPSHOT.stat()
        except OSError:
            return
        if st.st_mtime_ns == self.console_mtime:
            return
        self.console_mtime = st.st_mtime_ns
        try:
            data = json.loads(CONSOLE_SNAPSHOT.read_text(encoding="utf-8"))
        except (OSError, ValueError):
            return
        lines = data.get("lines")
        if not isinstance(lines, list):
            return
        title = data.get("title") or ""
        if title:
            self.console_title_var.set(f"Live mirror: {title}")
        for idx, row in enumerate(lines):  # keep the tech log's record of every distinct console line
            if isinstance(row, list):
                plain = "".join(str(sp[0]) for sp in row if isinstance(sp, list) and len(sp) == 2).strip()
                if plain and plain not in self.console_seen_set:
                    if len(self.console_seen) == self.console_seen.maxlen:
                        old = self.console_seen.popleft()
                        self.console_seen_set.discard(old)
                    self.console_seen.append(plain)
                    self.console_seen_set.add(plain)
                    tlog("console", plain)
        self.render_console(lines)

    def _gtag(self, col: str) -> str:
        name = "g" + col[1:]
        if name not in self._gtags:
            self.console_text.tag_configure(name, foreground=col)
            self._gtags.add(name)
        return name

    def _draw_flood(self, t, f: dict):
        """
        'Telegram asked us to slow down' x N as one line: the words glow from orange toward red the more it
        happens, a bright glint sits at a spot that moves with every new hit, a pill shows the count, and a
        little heat meter fills up. It goes back to normal output the moment something else is printed.
        """
        n, total, last = f["n"], f["total"], f["last"]
        heat = min(1.0, (n - 1) / 30.0)
        txt = f"◷  Telegram asked us to slow down  ·  {last}s  ·  {fmt_dur(total)} lost in all  "
        base = mix(PAL["orange"], PAL["red"], heat)
        glow = mix(base, "#ffffff", 0.55)
        pos = (n * 3) % max(1, len(txt))
        for j, ch in enumerate(txt):
            d = min(abs(j - pos), len(txt) - abs(j - pos))
            col = _quant(mix(base, glow, max(0.0, 1.0 - d / 6.0)))
            t.insert("end", ch, (self._gtag(col),))
        t.insert("end", f" ×{n} ", ("k_pill",))
        notches = 10
        lit = min(notches, 1 + n // 3)
        t.insert("end", "  ")
        for j in range(notches):
            if j < lit:
                t.insert("end", "█", (self._gtag(_quant(mix(PAL["orange"], PAL["red"], j / (notches - 1)))),))
            else:
                t.insert("end", "░", ("k_dim",))

    def _draw_reconn(self, t, f: dict):
        """
        'Server closed the connection' x N as one line. The engine reconnects by itself, so this is calm blue that
        warms toward orange only if it keeps happening. The dots are the last drops in order: grey = Telegram's
        server closed it, red = Windows / the network dropped it (WinError 64).
        """
        n, net, eof = f["n"], f["net"], f["eof"]
        col = _quant(mix(PAL["blue"], PAL["orange"], min(1.0, (n - 1) / 40.0)))
        t.insert("end", "⟳  Connection to Telegram dropped & came back  ", (self._gtag(col),))
        t.insert("end", f" ×{n} ", ("k_rcpill",))
        t.insert("end", "  ")
        for k in f["seq"][-18:]:
            t.insert("end", "●", (self._gtag(PAL["red"]) if k == "net" else self._gtag(_quant(PAL["muted"])),))
        parts = []
        if eof:
            parts.append(f"{eof} closed by Telegram")
        if net:
            parts.append(f"{net} network drop{'s' if net != 1 else ''} (WinError 64)")
        t.insert("end", "   " + "  ·  ".join(parts), (self._gtag(_quant(PAL["dim"])),))

    def render_console(self, lines=None):
        """
        Draws the console view with colour coding: green = done, orange = warnings / waiting on Telegram,
        red = errors, yellow = downloading. Progress lines become a loading bar made of letters: red when a
        file starts, and the letters turn green from left to right as it nears 100%.
        """
        if lines is None:
            lines = self._console_lines
        else:
            self._console_lines = lines
        t = self.console_text
        try:
            yv = t.yview()
            at_bot = float(yv[1]) >= 0.985 or not t.get("1.0", "end-1c")
        except Exception:  # noqa: BLE001
            yv, at_bot = (0.0, 1.0), True
        ents = []
        for row in lines:
            spans = []
            if isinstance(row, list):
                for sp in row:
                    if isinstance(sp, list) and len(sp) == 2:
                        spans.append((str(sp[0]), int(sp[1]) if isinstance(sp[1], int) else 7))
            ents.append(("".join(x[0] for x in spans), spans))
        kinds = [classify_console(p) for p, _ in ents]
        drop: set[int] = set()
        last_for: dict[str, int] = {}
        for i, (p, _) in enumerate(ents):  # progress lines of one file: only its newest one is shown
            if kinds[i][0] == "progress":
                key = progress_key(p)
                if key in last_for:
                    drop.add(last_for[key])
                last_for[key] = i
        ok_lines = [(i, p) for i, (p, _) in enumerate(ents) if kinds[i][0] == "ok"]
        for key, i in last_for.items():  # ...and none once that file has its 'done!' line
            if key and any(j > i and key in p.lower() for j, p in ok_lines):
                drop.add(i)
        # a run of "Telegram asked us to slow down" lines becomes ONE line with a live counter
        rows: list = []
        last_rc = None
        for i, (p, spans) in enumerate(ents):
            if i in drop:
                continue
            # dropped-and-reconnected messages: one counting line; progress lines in between don't break it
            rk = reconnect_kind(p) if UI.get("con_reconn", True) else None
            if rk:
                if last_rc is not None and all(r[0] == "line" and kinds[r[1]][0] == "progress"
                                               for r in rows[last_rc + 1:]):
                    f = rows[last_rc][1]
                    f["n"] += 1
                    f[rk] += 1
                    f["seq"].append(rk)
                else:
                    rows.append(("reconn", {"n": 1, "net": int(rk == "net"), "eof": int(rk == "eof"), "seq": [rk]}))
                    last_rc = len(rows) - 1
                continue
            secs = flood_secs(p) if UI.get("con_flood", True) else None
            if secs is not None:
                if rows and rows[-1][0] == "flood":
                    f = rows[-1][1]
                    f["n"] += 1
                    f["total"] += secs
                    f["last"] = secs
                else:
                    rows.append(("flood", {"n": 1, "total": secs, "last": secs}))
            else:
                rows.append(("line", i))
        t.configure(state="normal")
        t.delete("1.0", "end")
        first = True
        for what, i in rows:
            if not first:
                t.insert("end", "\n")
            first = False
            if what == "flood":
                self._draw_flood(t, i)
                continue
            if what == "reconn":
                self._draw_reconn(t, i)
                continue
            p, spans = ents[i]
            kind, frac = kinds[i]
            if kind == "progress":
                for seg, col in gradient_runs(p.rstrip(), frac, PAL["well"]):
                    t.insert("end", seg, (self._gtag(col),))
            elif kind in ("ok", "warn", "err", "busy"):
                t.insert("end", p.rstrip(), (f"k_{kind}",))
            else:
                for txt, col in spans:
                    t.insert("end", txt, (f"c{col & 15}",))
        t.configure(state="disabled")
        if at_bot and UI.get("con_follow", True):
            t.see("end")
            t.yview_moveto(1.0)
            t.xview_moveto(0.0)            # follow downwards, but keep the start of each line in view
        else:
            try:
                t.yview_moveto(yv[0])
            except Exception:  # noqa: BLE001
                pass

    def poll(self):
        handled = 0
        try:
            while handled < 500:  # stay responsive even if a burst of updates arrives
                self.handle(self.q.get_nowait())
                handled += 1
        except queue.Empty:
            pass
        self.poll_console()
        self.root.after(100, self.poll)

    def handle(self, item):
        kind = item[0]
        try:
            if kind == "log":
                self.log(item[1])
            elif kind in ("log_ok", "log_warn", "log_err"):
                self.log(item[1], {"log_ok": "ok", "log_warn": "warn", "log_err": "err"}[kind])
            elif kind == "status":
                self.status.set(item[1])
            elif kind == "speed_ui":
                self.threads_var.set(item[1])
                self.limit_var.set(item[2])
            elif kind == "reload":
                self.load_chats()
            elif kind == "ask":
                _, text, ev, box = item
                try:
                    box["yes"] = messagebox.askyesno("Telegram Media Saver", text)
                finally:
                    ev.set()
            elif kind == "watch":
                _, folder, sizes, label, step, steps, names, extra = item
                if self.mon_thread:
                    self.mon_thread.stop()
                mon = Monitor(folder, sizes, label, is_paused=lambda: bool(self.runner and self.runner.paused),
                              names=names, already=extra.get("already"), dest_for=extra.get("dest_for"),
                              topic_of=extra.get("topic_of"), later=extra.get("later", 0))
                self.mon_thread = MonitorThread(mon, self.q, {"step": step, "steps": steps},
                                                interval=self.graph.sample_interval())
                self.reset_idle()
                self.mon_thread.start()
            elif kind == "unwatch":
                if self.mon_thread:
                    # one last update; if tdl got through the whole list, anything missing is shown red
                    self.mon_thread.stop(mark_missing=bool(item[1]) if len(item) > 1 else False)
                    self.mon_thread = None
            elif kind == "live":
                self.apply_live(item[1])
            elif kind == "chats":
                self.chats = sorted(item[1], key=lambda c: (c.get("visible_name") or "").lower())
                try:
                    APP_DIR.mkdir(parents=True, exist_ok=True)
                    tmp_c = CHATS_CACHE_FILE.with_suffix(".tmp")
                    tmp_c.write_text(json.dumps(self.chats, ensure_ascii=False), encoding="utf-8")
                    os.replace(tmp_c, CHATS_CACHE_FILE)
                except OSError:
                    pass
                self.refresh_list()
                self.log(f"Loaded {len(self.chats)} conversations.")
                self.status.set("Ready. Tick what to save, pick a conversation, press Start.")
                if not self.running:
                    self.start_btn.state(["!disabled"])
            elif kind == "chats_error":
                text = item[1].strip()
                if self.chats:
                    self.status.set("Ready (using cached conversation list).")
                    if not self.running:
                        self.start_btn.state(["!disabled"])
                elif looks_logged_out(text):
                    self.status.set("Not logged in yet - click 'Log in (phone + code)'"
                                    + ("" if self.builtin() else " or 'Log in (use Telegram Desktop)'") + ".")
                else:
                    self.status.set("Couldn't load your chats from tdl - see the log.")
                self.log("tdl said: " + (text[-800:] or "(nothing)"), "err")
            elif kind == "done":
                self.finish(item[1])
        except Exception as e:  # noqa: BLE001  (one bad update must never freeze the window)
            self.log(f"[internal] {kind}: {type(e).__name__}: {e}", "err")

    def finish(self, r: str):
        self.set_running(False)
        if self.job_state:
            self.job_state.result = r
            self.job_state.event(f"Job finished with result={r}  counts={self.job_state.counts()}")
            self.job_state.autosave(force=True)
        has_queue = bool(self.queue_items)
        if r == "done" or r.startswith("incomplete:"):
            self.notify_finished(r == "done", has_queue)
        elif r not in ("nothing", "stopped", "no_space") and UI.get("sound_err"):
            play_sound("err")
        if r == "done":
            self.status.set("Finished - everything ticked is downloaded.")
            self.log("Finished.", "ok")
            if not has_queue and UI.get("popup_done", True):
                messagebox.showinfo("Finished", "All done - everything ticked is downloaded.")
        elif r.startswith("incomplete:"):
            n = int(r.split(":", 1)[1])
            self.status.set(f"Finished, but {n:,} file(s) didn't download. Press Start to retry just those.")
            if not has_queue and UI.get("popup_done", True):
                messagebox.showwarning("Almost done", f"{n:,} file(s) didn't download (Telegram refused them, or "
                                                      "they were deleted).\n\nPress Start again to retry just those.")
        elif r == "nothing":
            self.status.set("Nothing to download for the ticked types.")
        elif r == "no_space":
            self.status.set("Not started - free up some disk space (or pick another drive) and press Start.")
            return
        elif r == "stopped":
            self.status.set("Stopped. Press Start again to continue - finished files are skipped.")
            self.offer_save("was stopped")
            return
        elif r == "export_failed":
            self.status.set("Listing the chat failed - the tdl window shows why.")
            self.log("Listing the chat failed. Press Start to try again.", "err")
        elif r.startswith("dl_failed:"):
            self.status.set(f"Downloading {r.split(':', 1)[1]} stopped with an error - "
                            "the tdl window shows why. Press Start to continue.")
            self.log(self.status.get(), "err")
            if self.takeout_var.get():
                self.log("If the tdl window mentioned 'takeout', approve the request in Telegram "
                         "(or untick takeout mode) and press Start again.", "warn")
        else:
            self.status.set("Stopped by an error - see the log.")
            self.log(r, "err")
        if has_queue and r in ("done", "nothing") or (has_queue and r.startswith("incomplete:")):
            self.log(f"Starting next job in queue ({len(self.queue_items)} waiting) ...", "ok")
            self.root.after(400, self.start_next_in_queue)

    # -- preferences: change one, apply it everywhere, save it ------------------------------------ #
    RESTYLE_KEYS = {"accent", "density", "scale", "font", "titlebar_tint"}

    def open_settings(self, tab: str = "display"):
        w = getattr(self, "_settings_win", None)
        try:
            if w is not None and w.win.winfo_exists():
                w.win.deiconify()
                w.win.lift()
                w.show(tab)
                return
        except tk.TclError:
            pass
        self._settings_win = SettingsWindow(self, tab)

    def set_ui(self, key: str, value):
        if UI.get(key) == value:
            return
        UI[key] = value
        self.settings.setdefault("ui", {})[key] = value
        if self._ui_save_job:
            try:
                self.root.after_cancel(self._ui_save_job)
            except (tk.TclError, ValueError):
                pass
        self._ui_save_job = self.root.after(350, lambda: save_settings(self.settings))
        self.apply_ui(restyle=key in self.RESTYLE_KEYS, key=key)

    def reset_ui(self, keys: list):
        for k in keys:
            UI[k] = copy.deepcopy(UI_DEFAULTS[k])
            (self.settings.get("ui") or {}).pop(k, None)
        save_settings(self.settings)
        self.apply_ui(restyle=True)

    def section_title(self, key: str) -> str:
        base = (UI.get("titles") or {}).get(key) or self.sections[key]["title"]
        return base.upper() if UI.get("title_case") == "upper" else base

    def apply_ui(self, restyle: bool = False, key: str | None = None):
        """Puts every preference into effect. Cheap enough to run on each change."""
        global GAP, SECTION_MIN_W
        GAP = max(2, int(UI.get("gap", 10)))
        SECTION_MIN_W = max(240, int(UI.get("min_w", 380)))
        if restyle:
            self.set_theme(self.all_themes().get(self.theme_id) or THEMES[DEFAULT_THEME])
        r = self.root
        try:
            r.attributes("-alpha", max(0.3, min(1.0, float(UI.get("opacity", 100)) / 100.0)))
            r.attributes("-topmost", bool(UI.get("topmost")))
        except tk.TclError:
            pass
        if hasattr(self, "hint_lbl"):
            if UI.get("hints", True) and not self.hint_lbl.winfo_manager():
                self.hint_lbl.pack(side="left", padx=(14, 0), pady=(8, 0), after=self.title_acc_lbl)
            elif not UI.get("hints", True):
                self.hint_lbl.pack_forget()
        comp, sc = ui_compact(), ui_scale()
        thick = {"subtle": 1, "bold": 2, "none": 0}.get(UI.get("outline"), 1)
        for k, sec in self.sections.items():
            try:
                sec["body"].configure(padding=(8, 6, 8, 8) if comp else (12, 10, 12, 12))
                sec["hdr"].configure(padding=(6, 3, 4, 3) if comp else (8, 5, 6, 5))
                sec["outer"].configure(highlightthickness=thick, highlightbackground=PAL["border"])
                sec["lbl"].configure(text=self.section_title(k))
                hdr, btn, grip = sec["hdr"], sec["btn"], sec["grip"]
                if UI.get("hide_buttons", True) and not btn.winfo_manager():
                    rights = [w for w in hdr.pack_slaves() if w.pack_info().get("side") == "right"]
                    btn.pack(side="right", before=rights[0]) if rights else btn.pack(side="right")
                elif not UI.get("hide_buttons", True):
                    btn.pack_forget()
                if UI.get("header_icons", True) and not grip.winfo_manager():
                    grip.pack(side="left", padx=(2, 8), before=sec["lbl"])
                elif not UI.get("header_icons", True):
                    grip.pack_forget()
            except tk.TclError:
                pass
        cf = UI.get("con_font") if _have_font(str(UI.get("con_font"))) else "Consolas"
        cs = max(6, round(float(UI.get("con_size", 10)) * sc))
        try:
            self.console_text.configure(font=(cf, cs), wrap="word" if UI.get("con_wrap") else "none")
            self.console_text.tag_configure("k_pill", font=(cf, cs, "bold"))
            self.console_text.tag_configure("k_rcpill", font=(cf, cs, "bold"))
            self.log_text.configure(font=(ui_family(), max(6, round(float(UI.get("log_size", 10)) * sc))))
            self.pbar.configure(height=int(UI.get("pbar_h", 14)))
            if UI.get("legend", True) and not self.legend_lbl.winfo_manager():
                self.legend_lbl.pack(anchor="w", pady=(4, 0), fill="x", after=self.files_frame)
            elif not UI.get("legend", True):
                self.legend_lbl.pack_forget()
        except (tk.TclError, AttributeError):
            pass
        NeonScrollbar.resize_all()
        for sec in self.sections.values():
            sec["geo"] = None
        for k in self.sections:
            self._sec_fit(k)
        self._mark_selected()
        self.draw_neon()
        self._shimmer_kick()
        if hasattr(self, "dock"):
            self.dock._placed.clear()
            self.dock.layout()
        if key in ("con_flood", "con_reconn", "con_font", "con_size", "con_wrap") or restyle:
            self.render_console()
        self.refresh_chips()

    # -- sections whose content doesn't fit scroll inside their own box ----------------------------- #
    def _sec_fit(self, key: str):
        sec = self.sections.get(key)
        if not sec or "view" not in sec:
            return
        view, body, vsb = sec["view"], sec["body"], sec["vsb"]
        try:
            vw, vh = view.winfo_width(), view.winfo_height()
            if vw < 20 or vh < 10:
                return
            need = body.winfo_reqheight()
        except tk.TclError:
            return
        over = need > vh + 1
        show = over and bool(UI.get("sec_scrollbars", False))
        sbw = int(vsb.cget("width")) + 2 if show else 0
        off = max(0, min(int(sec["off"]), need - vh)) if over else 0
        sec["off"], sec["over"], sec["need"] = off, over, need
        geo = (off, vw, vh, need if over else vh, show)
        if sec["geo"] != geo:
            sec["geo"] = geo
            body.place_configure(x=0, y=-off, relwidth=0, relheight=0, width=vw - sbw,
                                 height=need if over else vh)
            if show:
                vsb.place(x=vw - sbw + 2, y=0, width=sbw - 2, height=vh)
                tk.Misc.lift(vsb)
            else:
                vsb.place_forget()
        if show:
            vsb.set(off / need, min(1.0, (off + vh) / need))

    def _sec_poll(self):
        """Content can grow without any event (a label wraps, rows appear), so check now and then."""
        for k in list(self.sections):
            self._sec_fit(k)
        self.root.after(350, self._sec_poll)

    def _sec_yview(self, key: str, *a):
        sec = self.sections[key]
        need, vh = sec.get("need", 0), sec["view"].winfo_height()
        if a[0] == "moveto":
            sec["off"] = float(a[1]) * need
        elif a[0] == "scroll":
            sec["off"] += int(a[1]) * (48 if a[2] == "units" else max(40, vh - 40))
        sec["off"] = int(max(0, min(sec["off"], need - vh)))
        self._sec_fit(key)

    def _section_of(self, w) -> str | None:
        outers = {str(sec["outer"]): k for k, sec in self.sections.items()}
        try:
            path = str(w)
        except Exception:  # noqa: BLE001
            return None
        while path:
            if path in outers:
                return outers[path]
            path = path.rsplit(".", 1)[0] if "." in path[1:] else ""
        return None

    def _rule_col(self, key: str) -> str:
        if UI.get("sec_select", True) and getattr(self, "sel_section", None) == key:
            return PAL["accent_lo"]
        return PAL["line"]

    def _mark_selected(self):
        for k, sec in self.sections.items():
            try:
                sec["rule"].configure(bg=self._rule_col(k))
            except (tk.TclError, KeyError):
                pass

    def _click_select(self, e):
        try:
            if e.widget.winfo_toplevel() is not self.root:
                return
        except (tk.TclError, AttributeError):
            return
        k = self._section_of(e.widget)
        if k and k != self.sel_section:
            self.sel_section = k
            self._mark_selected()

    def on_wheel(self, e):
        """The wheel scrolls lists and text boxes as usual. Elsewhere it scrolls the section under the pointer
        (or the one you clicked last) when its content doesn't fit, otherwise the whole layout."""
        w = e.widget
        try:
            if w.winfo_toplevel() is not self.root:
                return
            cls = w.winfo_class()
        except (tk.TclError, AttributeError):
            return
        if cls in ("Text", "Treeview", "Listbox", "TCombobox", "TSpinbox", "Spinbox", "Scrollbar", "TScrollbar") \
                or isinstance(w, (NeonScrollbar, Slider)) or self.dock._bp_on:
            return
        step = -1 if e.delta > 0 else 1
        for k in (self._section_of(w), self.sel_section):
            if k and self.sections[k].get("over"):
                self._sec_yview(k, "scroll", step, "units")
                return "break"
        self.dock.wheel(e)

    # -- small animations ------------------------------------------------------------------------- #
    def flash_section(self, key: str, delay: int = 280):
        if not anim_on("anim_flash") or key not in self.sections:
            return
        o = self.sections[key]["outer"]

        def go():
            try:
                thick = int(o.cget("highlightthickness"))
                if thick == 0:
                    o.configure(highlightthickness=1)
                a = mix(PAL["accent"], "#ffffff", 0.15)
                ease_after(o, 1100, lambda e: o.configure(highlightbackground=mix(a, PAL["border"], e)),
                           lambda: o.configure(highlightbackground=PAL["border"], highlightthickness=thick), fps=90)
            except tk.TclError:
                pass
        self.root.after(delay, go)

    def locate_section(self, key: str):
        d = self.dock
        self.root.deiconify()
        self.root.lift()
        if key in d.hidden:
            d.show(key)
            return
        b = d._boxes_px.get(key)
        if b and d._m and (b[1] < 0 or b[1] + 60 > d._m["avh"] or b[0] < 0 or b[0] + 60 > d._m["avw"]):
            d.oy = max(0, d.oy + b[1] - 20)
            d.ox = max(0, d.ox + b[0] - 20)
            d.layout()
        self.flash_section(key, delay=60)

    def _shimmer_kick(self):
        if getattr(self, "_shim_job", None) is None and self.running and anim_on("anim_shimmer") and UI.get("glow"):
            self._shim_job = self.root.after(16, self._shimmer)

    def _shimmer(self):
        self._shim_job = None
        c = getattr(self, "neon", None)
        if c is None:
            return
        try:
            c.delete("glint")
            if not (self.running and anim_on("anim_shimmer") and UI.get("glow", True)):
                return
            w = c.winfo_width()
            span = w + 360
            x = (time.perf_counter() * 520.0) % span - 180
            hi = mix(PAL["accent_hi"], "#ffffff", 0.45)
            for i in range(-6, 7):
                t = 1 - abs(i) / 7.0
                c.create_rectangle(x + i * 14, 0, x + i * 14 + 14, 3, outline="", tags="glint",
                                   fill=mix(PAL["accent"], hi, t * t))
        except tk.TclError:
            return
        self._shim_job = self.root.after(16, self._shimmer)

    def _dip(self, fn):
        """Smooth theme switch: the window dims a touch, the colours change, it comes back."""
        if not anim_on("anim_theme"):
            fn()
            return
        r = self.root
        top = max(0.3, min(1.0, float(UI.get("opacity", 100)) / 100.0))

        def back():
            fn()
            ease_after(r, 170, lambda e: r.attributes("-alpha", top * (0.6 + 0.4 * e)))
        ease_after(r, 90, lambda e: r.attributes("-alpha", top * (1 - 0.4 * e)), back)

    def play_anim_preview(self):
        keys = [k for k in SECTION_KEYS if k in self.dock.rects]
        for i, k in enumerate(keys):
            self.flash_section(k, delay=60 + i * 70)
        was = self.running
        self.running = True                    # borrow the downloading shimmer for two seconds
        self._shimmer_kick()

        def stop():
            self.running = was
        self.root.after(2000, stop)
        self._dip(lambda: None)

    # -- notifications ------------------------------------------------------------------------------ #
    def notify_finished(self, ok: bool, has_queue: bool):
        if UI.get("sound_done", True):
            play_sound("done" if ok else "err")
        try:
            focused = self.root.focus_displayof() is not None
        except (tk.TclError, KeyError):
            focused = False
        if UI.get("flash_done", True) and not focused:
            flash_taskbar(self.root)
        if UI.get("open_done") and not has_queue:
            self.root.after(300, self.open_folder)

    # -- files ------------------------------------------------------------------------------------------ #
    def open_path(self, p: Path):
        try:
            os.startfile(str(p)) if IS_WINDOWS else subprocess.Popen(["xdg-open", str(p)])
        except Exception as e:  # noqa: BLE001
            self.log(f"Couldn't open {p}: {e}", "err")

    def export_settings(self):
        f = filedialog.asksaveasfilename(parent=self.root, title="Export settings", defaultextension=".json",
                                         initialfile=f"TMS-settings-{time.strftime('%Y-%m-%d')}.json",
                                         filetypes=[("Settings", "*.json")])
        if not f:
            return
        try:
            self.settings["dock"] = self.dock.state()
            Path(f).write_text(json.dumps({"app": "TelegramMediaSaverFast", "settings": self.settings}, indent=2),
                               encoding="utf-8")
            self.log(f"Settings exported to {f}", "ok")
        except OSError as e:
            messagebox.showerror("Export", f"Couldn't write the file:\n{e}", parent=self.root)

    def import_settings(self):
        f = filedialog.askopenfilename(parent=self.root, title="Import settings", filetypes=[("Settings", "*.json")])
        if not f:
            return
        try:
            data = json.loads(Path(f).read_text(encoding="utf-8"))
            s = data.get("settings") if isinstance(data, dict) and "settings" in data else data
            if not isinstance(s, dict):
                raise ValueError("not a settings file")
        except (OSError, ValueError) as e:
            messagebox.showerror("Import", f"That file couldn't be read as settings:\n{e}", parent=self.root)
            return
        keep = {"tdl_path"}           # paths to programs on this PC stay as they are
        for k, v in s.items():
            if k not in keep:
                self.settings[k] = v
        save_settings(self.settings)
        UI.clear()
        UI.update(copy.deepcopy(UI_DEFAULTS))
        UI.update({k: v for k, v in (self.settings.get("ui") or {}).items() if k in UI_DEFAULTS})
        all_t = self.all_themes()
        if self.settings.get("theme") in all_t:
            self.theme_id = self.settings["theme"]
        self.apply_ui(restyle=True)
        d = self.settings.get("dock")
        if isinstance(d, dict) and isinstance(d.get("rects"), dict):
            self.dock.apply_state(d)
        self.log(f"Settings imported from {f}", "ok")
        w = getattr(self, "_settings_win", None)
        if w is not None:
            w.close()
            self.open_settings("data")

    def leftover_files(self) -> tuple:
        mine = str(os.getpid())
        files = [p for pat in ("run_*.cmd", "console_*.json") for p in APP_DIR.glob(pat)
                 if p.stem.split("_")[-1] != mine]
        size = 0
        for p in files:
            try:
                size += p.stat().st_size
            except OSError:
                pass
        return len(files), size

    def clean_leftovers(self) -> bool:
        n, size = self.leftover_files()
        if not n:
            return False
        if self.running:
            messagebox.showinfo("Clean up", "Wait until the download has finished.", parent=self.root)
            return False
        if not messagebox.askyesno("Clean up", f"Delete {n} old launcher / console files ({size / 1024:.0f} KB) "
                                               f"left by earlier runs?\n\nThey're only used while a download runs.",
                                   parent=self.root):
            return False
        mine = str(os.getpid())
        gone = 0
        for pat in ("run_*.cmd", "console_*.json"):
            for p in APP_DIR.glob(pat):
                if p.stem.split("_")[-1] == mine:
                    continue
                try:
                    p.unlink()
                    gone += 1
                except OSError:
                    pass
        self.log(f"Cleaned up {gone} old launcher / console files.", "ok")
        return True

    def run(self):
        self.root.mainloop()


if __name__ == "__main__":
    import argparse as _ap
    _cli = _ap.ArgumentParser(description="Telegram Media Saver Fast", add_help=True)
    _cli.add_argument("-r", "--ref-dir", "--reference-folder", dest="ref_dir", default=None,
                      help="Reference folder (or ';'-separated folders) to check and skip already-downloaded files from")
    _cli.add_argument("-d", "--dir", dest="save_dir", default=None,
                      help="Destination folder where new downloads should be saved")
    _args, _ = _cli.parse_known_args()
    if IS_WINDOWS:
        try:
            ctypes.windll.shcore.SetProcessDpiAwareness(1)
        except Exception:  # noqa: BLE001
            pass
    _app = App()
    if _args.ref_dir is not None:
        _app.ref_var.set(_args.ref_dir)
        _app.settings["ref_folder"] = _args.ref_dir
        save_settings(_app.settings)
    if _args.save_dir is not None:
        _app.save_var.set(_args.save_dir)
        _app.settings["folder"] = _args.save_dir
        save_settings(_app.settings)
    _app.run()
