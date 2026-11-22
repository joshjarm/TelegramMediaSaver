#!/usr/bin/env python3
"""
tg_engine.py - the "Built-in" download engine for Telegram Media Saver (no tdl needed).

Telegram Media Saver - Fast runs this instead of tdl when you pick  Engine: Built-in.
It understands the same few commands the app gives tdl and writes the same files, so the app's
sorting, live list, ETA, pause and forum folders all work the same way:

    tg_engine.py login                       sign in (phone + code + 2FA password) - first time only
    tg_engine.py chat ls -o json             list your chats (incl. forum topics)
    tg_engine.py chat export -c CHAT --raw -o FILE
    tg_engine.py dl -f LIST -d FOLDER -t N -l M [...]

Needs:  py -m pip install telethon cryptg      (cryptg = fast decryption; see the speed note below)

Speed notes
-----------
* Everything Telegram sends is encrypted and must be decrypted on your PC. Without a fast library
  Telethon does that in plain Python at well under 1 MB/s - which alone would cap your speed.
  This engine uses, in order: cryptg  ->  the OpenSSL library that ships with Python  ->  plain
  Python (slow, with a big warning). Install cryptg to be safe.
* Every file is fetched as 512 KB pieces, several at once ("connections per file"), spread over
  several separate connections to Telegram, and written to disk in order.
* Message details are fetched 100 at a time (tdl asks for them one by one).
* Uses its OWN login (the one the first Telegram Media Saver script created, if present), not
  Telegram Desktop's - so it can run while Telegram Desktop is open without the two clashing.
"""
from __future__ import annotations

import argparse
import asyncio
import copy
import ctypes
import ctypes.util
import getpass
import glob
import json
import os
import re
import sys
import time
import webbrowser
from pathlib import Path

try:
    sys.stdout.reconfigure(errors="replace")
    sys.stderr.reconfigure(errors="replace")
except Exception:  # noqa: BLE001
    pass

APP_DIR = Path(os.environ.get("APPDATA", str(Path.home()))) / "TelegramMediaSaver"
CONFIG_FILE = APP_DIR / "config.json"
SESSION_PATH = APP_DIR / "telegram_media_saver"  # same login as the first script (Telethon adds .session)
DC_KEYS_FILE = APP_DIR / "dc_keys.json"          # cached foreign-DC auth keys + clock offset (avoids ExportAuthorization flood waits)
CHUNK = 512 * 1024          # biggest piece Telegram serves per request
MAX_CLIENTS = 10            # separate connections opened for downloading
PIECE_TIMEOUT = 25.0        # seconds before a stalled 512 KB piece switches to another connection
RETRIES = 6
HISTORY_PACE = 1.0          # seconds between "next 100 messages" requests when listing a chat
BATCH_PACE = 0.5            # seconds between "details of 100 files" requests while downloading


def say(*a):
    print(*a, flush=True)


class Limiter:
    """
    How many file pieces may be in flight at once, across everything. Starts at what you set; when
    Telegram says "slow down" it halves (so we stop hammering it), then creeps back up by one every
    20 quiet seconds. This finds the fastest pace Telegram will tolerate on its own.
    """

    def __init__(self):
        self.max = 1
        self.limit = 1
        self.active = 0
        self.cond: asyncio.Condition | None = None
        self.last_flood = 0.0
        self.last_raise = 0.0

    def setup(self, n: int):
        self.max = self.limit = max(1, n)
        self.cond = asyncio.Condition()

    def on_flood(self):
        now = time.monotonic()
        if now - self.last_flood < 2:  # one wave of "slow down" replies counts once
            return
        self.last_flood = now
        new = max(1, self.limit // 2)
        if new < self.limit:
            self.limit = new
            say(f"  -> easing off: now {self.limit} piece(s) at once (was more)")

    def _maybe_raise(self):
        now = time.monotonic()
        if self.limit < self.max and now - self.last_flood > 20 and now - self.last_raise > 20:
            self.limit += 1
            self.last_raise = now
            say(f"  -> Telegram is quiet: trying {self.limit} piece(s) at once")

    async def __aenter__(self):
        if self.cond is None:
            return self
        async with self.cond:
            self._maybe_raise()
            await self.cond.wait_for(lambda: self.active < self.limit)
            self.active += 1
        return self

    async def __aexit__(self, *exc):
        if self.cond is None:
            return
        async with self.cond:
            self.active -= 1
            self.cond.notify_all()


LIMITER = Limiter()
PREMIUM_LIMIT_HITS = [0]


def show_telegram_waits():
    """Telethon sleeps through Telegram's 'slow down' (flood wait) replies silently; make them visible,
    say WHICH limit it is, and tell the limiter to ease off."""
    import logging
    from telethon import errors

    # Telegram has a separate speed limit for accounts without Premium (FLOOD_PREMIUM_WAIT). Telethon logs
    # it exactly like a normal flood wait, so catch the moment it's created to tell them apart.
    orig_init = errors.FloodPremiumWaitError.__init__

    def init(self, request, capture=0):
        orig_init(self, request, capture)
        PREMIUM_LIMIT_HITS[0] += 1
        if PREMIUM_LIMIT_HITS[0] in (1, 10, 50) or PREMIUM_LIMIT_HITS[0] % 200 == 0:
            say(f"  ** Telegram's FREE-ACCOUNT speed limit (FLOOD_PREMIUM_WAIT, {self.seconds}s) - "
                f"hit {PREMIUM_LIMIT_HITS[0]}x so far. Telegram Premium removes this limit. **")
    errors.FloodPremiumWaitError.__init__ = init

    class Show(logging.Handler):
        def emit(self, record):
            msg = record.getMessage()
            if "flood wait" in msg.lower() or "sleeping for" in msg.lower():
                if "early" not in msg:  # 'early' = repeats of a wait we already reported
                    say(f"  Telegram asked us to slow down: {msg}")
                if "GetFile" in msg:
                    LIMITER.on_flood()
    h = Show(level=logging.INFO)
    for name in ("telethon.client.users", "telethon.client.downloads"):
        lg = logging.getLogger(name)
        lg.setLevel(logging.INFO)
        lg.addHandler(h)


def fail(msg: str, code: int = 1):
    print(msg, file=sys.stderr, flush=True)
    sys.exit(code)


# --------------------------------------------------------------------------- #
#  Fast decryption
# --------------------------------------------------------------------------- #
def _load_libcrypto():
    """OpenSSL's libcrypto: Windows Python ships it as DLLs\\libcrypto-3*.dll."""
    names = []
    for base in {sys.base_prefix, sys.prefix, os.path.dirname(sys.executable)}:
        names += glob.glob(os.path.join(base, "DLLs", "libcrypto*.dll"))
        names += glob.glob(os.path.join(base, "libcrypto*.dll"))
    for n in ("crypto", "libcrypto-3-x64", "libcrypto-3", "libcrypto"):
        f = ctypes.util.find_library(n)
        if f:
            names.append(f)
    for n in names:
        try:
            lib = ctypes.CDLL(n)
            lib.AES_set_decrypt_key, lib.AES_set_encrypt_key, lib.AES_ige_encrypt  # noqa: B018
            return lib
        except (OSError, AttributeError):
            continue
    return None


def _make_ige(lib):
    class AES_KEY(ctypes.Structure):
        _fields_ = [("rd_key", ctypes.c_uint32 * 60), ("rounds", ctypes.c_uint)]

    lib.AES_ige_encrypt.argtypes = [ctypes.c_char_p, ctypes.c_char_p, ctypes.c_size_t,
                                    ctypes.POINTER(AES_KEY), ctypes.c_char_p, ctypes.c_int]
    lib.AES_ige_encrypt.restype = None

    def run(data, key, iv, enc):
        k = AES_KEY()
        (lib.AES_set_encrypt_key if enc else lib.AES_set_decrypt_key)(bytes(key), len(key) * 8, ctypes.byref(k))
        out = ctypes.create_string_buffer(len(data))
        ivb = ctypes.create_string_buffer(bytes(iv), len(iv))  # OpenSSL updates the IV in place
        lib.AES_ige_encrypt(bytes(data), out, len(data), ctypes.byref(k), ivb, 1 if enc else 0)
        return out.raw

    return (lambda d, k, i: run(d, k, i, False)), (lambda d, k, i: run(d, k, i, True))


def setup_crypto() -> str:
    """Make sure Telethon decrypts with a fast library. Returns a short description."""
    try:
        import cryptg  # noqa: F401
        return "cryptg (fast)"
    except ImportError:
        pass
    import telethon.crypto.libssl as L
    if L.decrypt_ige and L.encrypt_ige:
        return "system OpenSSL (fast)"
    lib = _load_libcrypto()
    if lib is not None:
        dec, enc = _make_ige(lib)
        # self-test against Telethon's own (slow, but correct) implementation before trusting it
        import pyaes  # noqa: F401
        import telethon.crypto.aes as A
        key, iv, data = os.urandom(32), os.urandom(32), os.urandom(4096)
        saved = (L.decrypt_ige, L.encrypt_ige)
        L.decrypt_ige = L.encrypt_ige = None
        try:
            ref = A.AES.decrypt_ige(data, key, iv)
        finally:
            L.decrypt_ige, L.encrypt_ige = saved
        if dec(data, key, iv) == ref and dec(enc(data, key, iv), key, iv) == data:
            L.decrypt_ige, L.encrypt_ige = dec, enc
            return "Python's bundled OpenSSL (fast)"
    return ""


# --------------------------------------------------------------------------- #
#  Login / client
# --------------------------------------------------------------------------- #
def load_config():
    try:
        cfg = json.loads(CONFIG_FILE.read_text(encoding="utf-8"))
        return int(cfg["api_id"]), str(cfg["api_hash"])
    except Exception:  # noqa: BLE001
        return None


def ask_config():
    say("First-time setup: you need an API ID + hash from Telegram (free, takes a minute).")
    say("Opening https://my.telegram.org/apps - log in, create an app (any name), then copy its values.")
    try:
        webbrowser.open("https://my.telegram.org/apps")
    except Exception:  # noqa: BLE001
        pass
    api_id = input("api_id: ").strip()
    api_hash = input("api_hash: ").strip()
    if not api_id.isdigit() or not api_hash:
        fail("That doesn't look right - run the log-in again.")
    APP_DIR.mkdir(parents=True, exist_ok=True)
    CONFIG_FILE.write_text(json.dumps({"api_id": int(api_id), "api_hash": api_hash}), encoding="utf-8")
    return int(api_id), api_hash


_dc_export_lock: asyncio.Lock | None = None
_dc_key_mem: dict[int, bytes] = {}
_known_time_offset: list[int] = [0]
_home_key_id: list[int | None] = [None]


def _load_dc_cache(home_key_id: int | None = None):
    try:
        data = json.loads(DC_KEYS_FILE.read_text(encoding="utf-8"))
    except Exception:  # noqa: BLE001
        return
    if isinstance(data.get("time_offset"), int):
        _known_time_offset[0] = int(data["time_offset"])
    if home_key_id is not None and data.get("home_key_id") == home_key_id:
        for k, v in (data.get("dcs") or {}).items():
            try:
                raw = bytes.fromhex(v)
                if len(raw) == 256:
                    _dc_key_mem[int(k)] = raw
            except Exception:  # noqa: BLE001
                pass


def _save_dc_cache():
    try:
        APP_DIR.mkdir(parents=True, exist_ok=True)
        payload = {
            "home_key_id": _home_key_id[0],
            "time_offset": _known_time_offset[0],
            "dcs": {str(k): v.hex() for k, v in _dc_key_mem.items() if len(v) == 256},
        }
        tmp = DC_KEYS_FILE.with_suffix(".tmp")
        tmp.write_text(json.dumps(payload, indent=2), encoding="utf-8")
        os.replace(tmp, DC_KEYS_FILE)
    except OSError:
        pass


def _install_dc_key_cache(client, exporter):
    """
    Replaces Telethon's per-client `_create_exported_sender` with a shared + disk-cached version.
    Without this, every one of the 10 download connections calls `auth.ExportAuthorizationRequest`
    from scratch on every run, which quickly triggers a 30-40 minute Telegram FloodWait.
    With this, `ExportAuthorizationRequest` is called at most ONCE per Data Center ever, and its
    256-byte auth_key is shared across all 10 connections and saved in `dc_keys.json` for future runs.
    """
    from telethon import errors, functions
    from telethon.crypto import AuthKey
    from telethon.network import MTProtoSender
    from telethon.tl.alltlobjects import LAYER

    async def _connect_cached(dc, key_bytes: bytes):
        sender = MTProtoSender(
            AuthKey(key_bytes),
            loggers=client._log,
            retries=client._connection_retries,
            delay=client._retry_delay,
            auto_reconnect=client._auto_reconnect,
            connect_timeout=client._timeout,
        )
        if _known_time_offset[0]:
            sender._state.time_offset = _known_time_offset[0]
        await sender.connect(client._connection(
            dc.ip_address, dc.port, dc.id,
            loggers=client._log, proxy=client._proxy, local_addr=client._local_addr
        ))
        init_req = copy.copy(client._init_request)
        init_req.query = functions.help.GetConfigRequest()
        req = functions.InvokeWithoutUpdatesRequest(init_req)
        await sender.send(functions.InvokeWithLayerRequest(LAYER, req))
        if sender._state.time_offset and sender._state.time_offset != _known_time_offset[0]:
            _known_time_offset[0] = sender._state.time_offset
            _save_dc_cache()
        return sender

    async def _create_exported_sender(dc_id: int):
        global _dc_export_lock
        if _dc_export_lock is None:
            _dc_export_lock = asyncio.Lock()
        dc = await client._get_dc(dc_id)

        # Fast path: reuse cached DC auth_key without calling ExportAuthorizationRequest
        cached = _dc_key_mem.get(dc_id)
        if cached:
            try:
                return await _connect_cached(dc, cached)
            except (errors.AuthKeyUnregisteredError, errors.AuthBytesInvalidError,
                    errors.BadMessageError, errors.SecurityError):
                _dc_key_mem.pop(dc_id, None)
                _save_dc_cache()

        async with _dc_export_lock:
            cached = _dc_key_mem.get(dc_id)
            if cached:
                try:
                    return await _connect_cached(dc, cached)
                except (errors.AuthKeyUnregisteredError, errors.AuthBytesInvalidError,
                        errors.BadMessageError, errors.SecurityError):
                    _dc_key_mem.pop(dc_id, None)
                    _save_dc_cache()

            sender = MTProtoSender(
                None,
                loggers=client._log,
                retries=client._connection_retries,
                delay=client._retry_delay,
                auto_reconnect=client._auto_reconnect,
                connect_timeout=client._timeout,
            )
            if _known_time_offset[0]:
                sender._state.time_offset = _known_time_offset[0]
            await sender.connect(client._connection(
                dc.ip_address, dc.port, dc.id,
                loggers=client._log, proxy=client._proxy, local_addr=client._local_addr
            ))
            while True:
                try:
                    auth = await exporter(functions.auth.ExportAuthorizationRequest(dc_id))
                    break
                except errors.FloodWaitError as e:
                    say(f"  Telegram asked us to wait {e.seconds}s on ExportAuthorizationRequest ...")
                    await asyncio.sleep(e.seconds + 1)
            init_req = copy.copy(client._init_request)
            init_req.query = functions.auth.ImportAuthorizationRequest(id=auth.id, bytes=auth.bytes)
            req = functions.InvokeWithoutUpdatesRequest(init_req)
            await sender.send(functions.InvokeWithLayerRequest(LAYER, req))
            if sender.auth_key and sender.auth_key.key and len(sender.auth_key.key) == 256:
                _dc_key_mem[dc_id] = sender.auth_key.key
                if sender._state.time_offset:
                    _known_time_offset[0] = sender._state.time_offset
                _save_dc_cache()
            return sender

    client._create_exported_sender = _create_exported_sender


def make_client(session=None, *, flood_threshold: int = 3600, extra_worker: bool = False):
    from telethon import TelegramClient
    cfg = load_config()
    if cfg is None:
        return None
    _load_dc_cache()
    c = TelegramClient(session if session is not None else str(SESSION_PATH), cfg[0], cfg[1],
                       flood_sleep_threshold=flood_threshold, connection_retries=-1, retry_delay=3,
                       request_retries=8, auto_reconnect=True, receive_updates=False)
    if _known_time_offset[0]:
        c._sender._state.time_offset = _known_time_offset[0]
    if extra_worker:
        # Worker download connections don't need to call get_me() / updates.GetState() on connect
        async def _noop_me(*_a, **_kw):
            return None
        c.get_me = _noop_me
    return c


def _ro_session_copy():
    """Copies the SQLite session (including cached peer entities) to a temp file so Verify / chat ls
    never locks the main session while a download is running."""
    import atexit
    import shutil
    src = Path(str(SESSION_PATH) + ".session")
    if not src.exists():
        return None
    dst_base = APP_DIR / f"ro_{os.getpid()}"
    dst = Path(str(dst_base) + ".session")
    try:
        shutil.copy2(src, dst)
    except OSError:
        return None

    def _cleanup():
        for ext in (".session", ".session-journal", ".session-wal", ".session-shm"):
            try:
                Path(str(dst_base) + ext).unlink(missing_ok=True)
            except OSError:
                pass
    atexit.register(_cleanup)
    return str(dst_base)


async def connect_authorized(readonly: bool = False, flood_threshold: int = 3600):
    sess = _ro_session_copy() if readonly else None
    client = make_client(sess, flood_threshold=flood_threshold)
    if client is None:
        fail("not authorized, please login first (no API ID saved yet)")
    try:
        await client.connect()
    except Exception as e:  # noqa: BLE001
        if "database is locked" in str(e):
            sess = _ro_session_copy()
            if sess is not None:
                client = make_client(sess, flood_threshold=flood_threshold)
                await client.connect()
            else:
                fail("The login file is in use - close the first Telegram Media Saver script and try again.")
        else:
            raise
    if not await client.is_user_authorized():
        await client.disconnect()
        fail("not authorized, please login first")
    if client.session.auth_key and client.session.auth_key.key_id:
        _home_key_id[0] = client.session.auth_key.key_id
        _load_dc_cache(_home_key_id[0])
    if client._sender._state.time_offset and client._sender._state.time_offset != _known_time_offset[0]:
        _known_time_offset[0] = client._sender._state.time_offset
        _save_dc_cache()
    _install_dc_key_cache(client, client)
    return client


async def cmd_login(_args):
    if load_config() is None:
        ask_config()
    client = make_client()
    say("Signing in to Telegram (the code arrives in your Telegram app) ...")
    await client.start(phone=lambda: input("Phone number with country code (e.g. +14155550123): "),
                       password=lambda: getpass.getpass("Two-step verification password: "))
    me = await client.get_me()
    say(f"Signed in as {me.first_name or me.username}. You can close this window.")
    await client.disconnect()


# --------------------------------------------------------------------------- #
#  chat ls
# --------------------------------------------------------------------------- #
async def fetch_topics(client, entity) -> list[dict]:
    from telethon import functions
    out, seen = [], set()
    od, oid, ot = None, 0, 0
    for _ in range(200):  # up to 20,000 topics
        res = await client(functions.messages.GetForumTopicsRequest(
            peer=entity, offset_date=od, offset_id=oid, offset_topic=ot, limit=100))
        new = 0
        for t in res.topics:
            tid = getattr(t, "id", None)
            if tid is None or tid in seen:
                continue
            seen.add(tid)
            new += 1
            out.append({"id": tid, "title": getattr(t, "title", "") or f"Topic {tid}"})
        if not new or len(res.topics) < 100:
            break
        last = res.topics[-1]
        ot = last.id
        oid = getattr(last, "top_message", 0) or 0
        msgs = {m.id: m for m in getattr(res, "messages", [])}
        od = getattr(msgs.get(oid), "date", None)
    if 1 not in seen:
        out.insert(0, {"id": 1, "title": "General"})
    return out


async def cmd_chat_ls(_args):
    from telethon import types
    client = await connect_authorized(readonly=True)
    result = []
    try:
        async for d in client.iter_dialogs():
            e = d.entity
            kind = "private" if d.is_user else ("group" if d.is_group else "channel")
            name = "Saved Messages" if getattr(e, "is_self", False) else (d.name or "")
            item = {"id": abs(int(getattr(e, "id", 0))), "type": kind, "visible_name": name or "-",
                    "username": getattr(e, "username", None) or ""}
            if isinstance(e, types.Channel) and getattr(e, "forum", False):
                try:
                    item["topics"] = await fetch_topics(client, e)
                except Exception as ex:  # noqa: BLE001
                    print(f"warning: couldn't read topics of {name}: {ex}", file=sys.stderr)
            result.append(item)
    finally:
        await client.disconnect()
    print(json.dumps(result, ensure_ascii=False, indent="\t"), flush=True)


# --------------------------------------------------------------------------- #
#  chat export
# --------------------------------------------------------------------------- #
async def resolve(client, target: str):
    from telethon import types
    t = target.strip()
    if not re.fullmatch(r"-?\d+", t):
        return await client.get_entity(t.lstrip("@"))
    cid = abs(int(t))
    for peer in (types.PeerChannel(cid), types.PeerUser(cid), types.PeerChat(cid)):
        try:
            return await client.get_entity(peer)
        except Exception:  # noqa: BLE001
            continue
    async for d in client.iter_dialogs():  # not cached yet: look it up in your chat list
        if abs(int(getattr(d.entity, "id", 0))) == cid:
            return d.entity
    fail(f"CHAT_ID_INVALID: no chat with id {cid} in your chat list")


def media_name(msg) -> str:
    f = msg.file
    if msg.photo is not None:
        return f"{msg.photo.id}.jpg"
    name = (f.name if f else None) or ""
    if not name:
        ext = (f.ext if f else "") or ""
        name = f"{msg.document.id}{ext}"
    return name


def raw_of(msg):
    """Telegram's message data in the same shape tdl's --raw export uses (only the fields the app reads)."""
    from telethon import types
    media = msg.media
    rt = msg.reply_to
    out = {"ID": msg.id, "ReplyTo": None}
    if isinstance(rt, types.MessageReplyHeader):
        out["ReplyTo"] = {"ForumTopic": bool(rt.forum_topic), "ReplyToMsgID": rt.reply_to_msg_id or 0,
                          "ReplyToTopID": rt.reply_to_top_id or 0}
    if isinstance(media, types.MessageMediaPhoto) and isinstance(media.photo, types.Photo):
        sizes = []
        for s in media.photo.sizes or []:
            if isinstance(s, types.PhotoSize):
                sizes.append({"Type": s.type, "Size": s.size})
            elif isinstance(s, types.PhotoSizeProgressive):
                sizes.append({"Type": s.type, "Sizes": list(s.sizes)})
        out["Media"] = {"Photo": {"ID": media.photo.id, "Sizes": sizes}}
        return out
    if isinstance(media, types.MessageMediaDocument) and isinstance(media.document, types.Document):
        d = media.document
        attrs = []
        for a in d.attributes:
            if isinstance(a, types.DocumentAttributeFilename):
                attrs.append({"FileName": a.file_name})
            elif isinstance(a, types.DocumentAttributeSticker):
                attrs.append({"Mask": bool(a.mask), "Alt": a.alt or "", "Stickerset": {}})
            elif isinstance(a, types.DocumentAttributeCustomEmoji):
                attrs.append({"Free": bool(a.free), "Alt": a.alt or "", "Stickerset": {}})
            elif isinstance(a, types.DocumentAttributeAnimated):
                attrs.append({})
            elif isinstance(a, types.DocumentAttributeVideo):
                attrs.append({"RoundMessage": bool(a.round_message), "SupportsStreaming": bool(a.supports_streaming),
                              "W": a.w, "H": a.h})
            elif isinstance(a, types.DocumentAttributeAudio):
                attrs.append({"Voice": bool(a.voice), "Waveform": None, "Performer": a.performer or "",
                              "Title": a.title or ""})
            elif isinstance(a, types.DocumentAttributeImageSize):
                attrs.append({"W": a.w, "H": a.h})
        out["Media"] = {"Voice": bool(media.voice), "Round": bool(media.round), "Video": bool(media.video),
                        "Document": {"ID": d.id, "MimeType": d.mime_type or "", "Size": int(d.size or 0),
                                     "DCID": d.dc_id, "Attributes": attrs}}
        return out
    return None  # link previews, polls, etc. - nothing to download (same as tdl)


async def cmd_export(args):
    client = await connect_authorized(readonly=True)
    try:
        entity = await resolve(client, args.chat)
        from telethon import utils
        chat_id = abs(int(utils.get_peer_id(entity, add_mark=False)))
        out = Path(args.output)
        n = found = 0
        t0 = time.time()
        with open(out, "w", encoding="utf-8") as f:
            f.write('{"id":%d,"messages":[' % chat_id)
            first = True
            # ~1 s between requests of 100 messages: Telegram's limit for reading history. Going faster
            # just earns a 20-30 s "slow down" every ~2,000 messages, which is slower overall.
            async for msg in client.iter_messages(entity, wait_time=HISTORY_PACE):
                n += 1
                raw = raw_of(msg) if msg.media is not None else None
                if raw is not None:
                    item = {"id": msg.id, "type": "message", "file": media_name(msg), "raw": raw}
                    f.write(("" if first else ",") + json.dumps(item, ensure_ascii=False, separators=(",", ":")))
                    first = False
                    found += 1
                if n % 2000 == 0:
                    say(f"  read {n:,} messages, {found:,} with media  ({time.time() - t0:.0f}s)")
            f.write("]}")
        say(f"Done: {n:,} messages read, {found:,} with media.")
    finally:
        await client.disconnect()


# --------------------------------------------------------------------------- #
#  dl
# --------------------------------------------------------------------------- #
_BAD = re.compile(r'[<>:"/\\|?*\x00-\x1f]')
_CHAT_MID_RE = re.compile(r"^-?\d+_(\d+)_(.+)$")
_DATE_MID_RE = re.compile(r"^\d{4}-\d{2}-\d{2}[_ -]\d{2}[-:]\d{2}[-:]\d{2}_(\d+)_(.+)$")
_OLD_DATE_RE = re.compile(r"^\d{4}-\d{2}-\d{2}[_ -]\d{2}[-:]\d{2}[-:]\d{2}_(.+)$")
_DUP_COPY_RE = re.compile(r"\s+\(\d+\)(\.[^.]+)$")
_TG_DOCID_RE = re.compile(r"(?<!\d)(\d{15,20})(?!\d)")


def file_name(chat_id: int, mid: int, name: str) -> str:
    stem = _BAD.sub("_", name or "media").strip(" .") or "media"
    return f"{chat_id}_{mid}_{stem[:150]}"


def _norm_tail(name: str, strip_copy: bool = True) -> str:
    s = _BAD.sub("_", name or "").strip(" .").lower()
    if strip_copy:
        s = _DUP_COPY_RE.sub(r"\1", s)
    return s[:150]


def _scan_existing_dir(folder: Path, extra_dirs: list[Path] | None = None) -> tuple[dict[int, set[int]], dict[int, set[int]], dict[str, set[int]], set[tuple[int, str]]]:
    """
    Indexes already-downloaded files in `folder` (and optional reference directories in `extra_dirs`)
    across both new (<chat_id>_<msg_id>_<name>) and older (<YYYY-MM-DD>_<HH-MM-SS>_...) TMSF naming schemes
    so they are never re-downloaded.
    Returns (mids_to_sizes, doc_ids_to_sizes, tails_to_sizes, date_size_exts).
    """
    mids: dict[int, set[int]] = {}
    doc_ids: dict[int, set[int]] = {}
    tails: dict[str, set[int]] = {}
    date_size_ext: set[tuple[int, str]] = set()

    def _visit(d: Path, recursive: bool):
        stack = [d]
        while stack:
            cur = stack.pop()
            try:
                with os.scandir(cur) as it:
                    for e in it:
                        n = e.name
                        if n.endswith(".tmp") or n == ".tms":
                            continue
                        try:
                            if e.is_dir(follow_symlinks=False):
                                if recursive:
                                    stack.append(Path(e.path))
                                continue
                            if not e.is_file():
                                continue
                            sz = e.stat().st_size
                        except OSError:
                            continue
                        if sz <= 0:
                            continue
                        cm = _CHAT_MID_RE.match(n)
                        if cm:
                            mids.setdefault(int(cm.group(1)), set()).add(sz)
                            for t in (_norm_tail(cm.group(2), True), _norm_tail(cm.group(2), False)):
                                if t:
                                    tails.setdefault(t, set()).add(sz)
                        dm = _DATE_MID_RE.match(n)
                        if dm:
                            mids.setdefault(int(dm.group(1)), set()).add(sz)
                            for t in (_norm_tail(dm.group(2), True), _norm_tail(dm.group(2), False)):
                                if t:
                                    tails.setdefault(t, set()).add(sz)
                        om = _OLD_DATE_RE.match(n)
                        if om:
                            for t in (_norm_tail(om.group(1), True), _norm_tail(om.group(1), False)):
                                if t:
                                    tails.setdefault(t, set()).add(sz)
                            ext = os.path.splitext(n)[1].lower()
                            if ext:
                                date_size_ext.add((sz, ext))
                        for did_s in _TG_DOCID_RE.findall(n):
                            doc_ids.setdefault(int(did_s), set()).add(sz)
            except OSError:
                pass

    _visit(folder, recursive=False)
    for rdir in (extra_dirs or []):
        if rdir and rdir.exists():
            _visit(rdir, recursive=True)
    return mids, doc_ids, tails, date_size_ext


class Stats:
    def __init__(self, total_files: int):
        self.total_files = total_files
        self.done = self.failed = self.skipped = 0
        self.bytes = 0
        self.t0 = time.time()

    def line(self) -> str:
        el = max(0.001, time.time() - self.t0)
        return (f"[{self.done + self.skipped + self.failed:,}/{self.total_files:,}]  done {self.done:,}  "
                f"skipped {self.skipped:,}  failed {self.failed:,}  -  average {self.bytes / el / 1048576:.2f} MB/s")


# Files often live on a different Telegram server than your account. The first request from each
# connection to such a server has to hand over a one-time login pass; if several connections do that at
# the same moment Telegram rejects some (AuthBytesInvalidError). So the FIRST request per connection per
# server goes one at a time; after that everything runs in parallel.
_warm: set = set()
_warm_lock: asyncio.Lock | None = None


async def _get_piece(client, media, idx, size):
    parts = []
    async for c in client.iter_download(media, offset=idx * CHUNK, limit=1, request_size=CHUNK, file_size=size):
        parts.append(c)
    return b"".join(parts)


async def fetch_chunk(clients, k, media, idx, size, refresh):
    """One 512 KB piece, with retries. Uses connection k (spreads pieces over several connections)."""
    global _warm_lock
    from telethon import errors
    if _warm_lock is None:
        _warm_lock = asyncio.Lock()
    delay = 1.0
    auth_retries = 0
    attempt = 0
    while attempt < RETRIES:
        client = clients[k % len(clients)]
        dc_id = getattr(media, "dc_id", None)
        key = (id(client), dc_id)
        try:
            # Ensure the foreign-DC sender is connected/authorized BEFORE starting the 25s piece timer,
            # so a slow initial handshake or rate-limit wait is never killed mid-way by PIECE_TIMEOUT.
            if key not in _warm:
                async with _warm_lock:
                    if key not in _warm:
                        if dc_id and client.session.dc_id != dc_id:
                            sender = await client._borrow_exported_sender(dc_id)
                            await client._return_exported_sender(sender)
                        _warm.add(key)
            async with LIMITER:
                return await asyncio.wait_for(_get_piece(client, media, idx, size), timeout=PIECE_TIMEOUT)
        except (errors.AuthBytesInvalidError, errors.AuthKeyUnregisteredError):
            auth_retries += 1  # login hand-off collided or cached DC key expired: evict & retry
            _warm.discard(key)
            if dc_id:
                _dc_key_mem.pop(dc_id, None)
                _save_dc_cache()
                old = client._borrowed_senders.pop(dc_id, None)
                if old and old[1]:
                    try:
                        await old[1].disconnect()
                    except Exception:  # noqa: BLE001
                        pass
            if auth_retries > 10:
                raise
            await asyncio.sleep(0.5 * auth_retries)
            continue
        except (errors.FileReferenceExpiredError, errors.FilerefUpgradeNeededError):
            attempt += 1
            media = await refresh()  # Telegram's link to the file went stale: get a fresh one
        except errors.FloodWaitError as e:
            LIMITER.on_flood()
            say(f"  Telegram asked us to wait {e.seconds}s ...")
            await asyncio.sleep(e.seconds + 1)
        except asyncio.CancelledError:
            raise
        except Exception as e:  # noqa: BLE001  (timeouts, Telegram-side hiccups, dropped connections)
            attempt += 1
            if attempt >= RETRIES:
                raise
            say(f"  retrying a piece ({type(e).__name__}) ...")
            k += 1  # try another connection
            await asyncio.sleep(delay)
            delay = min(delay * 2, 30)
    raise RuntimeError("piece failed")


def _fmt_eta(sec: float) -> str:
    sec = int(max(0, sec))
    h, rem = divmod(sec, 3600)
    m, s = divmod(rem, 60)
    return f"{h}h{m:02d}m{s:02d}s" if h else f"{m}m{s:02d}s" if m else f"{s}s"


async def download_document(clients, msg, tmp: Path, threads: int, refresh, label: str = ""):
    """Several pieces at once (spread over the connections), written to disk strictly in order."""
    media = msg.document
    size = int(media.size or 0)
    n = max(1, (size + CHUNK - 1) // CHUNK)
    # Big files print a progress line (same shape as tdl's) so Telegram Media Saver can colour it like a
    # loading bar: every ~5% or every ~6 seconds, whichever comes first.
    show = bool(label) and size >= 8 * 1048576
    prog = {"t0": time.time(), "last_t": 0.0, "last_pct": -1.0, "bytes": 0}
    if show:
        say(f"downloading  {label}  {size / 1048576:.1f} MB")
    window = max(threads * 6, 24)
    results: dict[int, bytes] = {}
    cond = asyncio.Condition()
    state = {"next_idx": 0, "next_write": 0, "media": media}

    async def refreshed():
        m = await refresh()
        state["media"] = m
        return m

    async def worker(wid):
        while True:
            async with cond:
                await cond.wait_for(lambda: state["next_idx"] >= n or state["next_idx"] < state["next_write"] + window)
                if state["next_idx"] >= n:
                    return
                idx = state["next_idx"]
                state["next_idx"] += 1
            data = await fetch_chunk(clients, idx, state["media"], idx, size, refreshed)  # piece i -> connection i
            async with cond:
                results[idx] = data
                cond.notify_all()

    async def writer(f):
        while state["next_write"] < n:
            async with cond:
                await cond.wait_for(lambda: state["next_write"] in results)
                data = results.pop(state["next_write"])
                state["next_write"] += 1
                cond.notify_all()
            f.write(data)
            f.flush()
            if show:
                prog["bytes"] += len(data)
                pct = prog["bytes"] * 100.0 / size
                now = time.time()
                if pct < 100 and (pct - prog["last_pct"] >= 5 or now - prog["last_t"] >= 6):
                    el = max(0.001, now - prog["t0"])
                    speed = prog["bytes"] / el
                    eta = _fmt_eta((size - prog["bytes"]) / speed) if speed > 0 else "?"
                    bar = "#" * int(pct / 5) + "." * (20 - int(pct / 5))
                    say(f"{label}... [{bar}] {pct:.1f}% [{prog['bytes'] / 1048576:.1f} MB; "
                        f"{speed / 1048576:.2f} MB/s; ~ETA: {eta}]")
                    prog["last_pct"], prog["last_t"] = pct, now

    with open(tmp, "wb") as f:
        tasks = [asyncio.create_task(worker(i)) for i in range(min(threads, n))]
        wtask = asyncio.create_task(writer(f))
        try:
            await asyncio.gather(*tasks)
            await wtask
        finally:
            for t in tasks + [wtask]:
                t.cancel()
    got = tmp.stat().st_size
    if size and got != size:
        raise RuntimeError(f"got {got:,} of {size:,} bytes")
    return got


async def cmd_dl(args):
    from telethon import utils
    from telethon.sessions import StringSession
    mode = setup_crypto()
    if mode:
        say(f"Decryption: {mode}")
    else:
        say("!" * 78)
        say("! WARNING: no fast decryption library - downloads will be slow (well under 1 MB/s).")
        say("! Fix:  py -m pip install cryptg   (then start the download again)")
        say("!" * 78)
    if args.takeout:
        say("(takeout mode isn't used by the built-in engine - ignored)")

    lists = []
    for p in args.file:
        try:
            with open(p, encoding="utf-8") as f:
                lists.append(json.load(f))
        except (OSError, ValueError) as e:
            fail(f"Can't read the download list {p}: {e}")
    out_dir = Path(args.dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    # Use flood_threshold=12 on download connections so any wait >12s raises FloodWaitError to fetch_chunk
    # (outside asyncio.wait_for) instead of sleeping inside _get_piece and getting killed by PIECE_TIMEOUT.
    main = await connect_authorized(flood_threshold=12)
    clients = [main]
    try:
        # extra connections, same login (like tdl/Telegram Desktop do), so pieces travel in parallel
        n_extra = max(0, min(MAX_CLIENTS, args.threads * args.limit) - 1) if args.threads * args.limit > 1 else 0
        if n_extra:
            s = StringSession.save(main.session)
            for _ in range(n_extra):
                c = make_client(StringSession(s), flood_threshold=12, extra_worker=True)
                _install_dc_key_cache(c, main)
                try:
                    await c.connect()
                    clients.append(c)
                except Exception as e:  # noqa: BLE001
                    say(f"  (extra connection failed: {e}) - continuing with {len(clients)}")
                    break
        say(f"Connections: {len(clients)}   pieces at once per file: {args.threads}   files at once: {args.limit}")
        LIMITER.setup(max(1, args.threads) * max(1, args.limit))

        from telethon import errors

        async def _flood_safe(fn):
            while True:
                try:
                    return await fn()
                except errors.FloodWaitError as e:
                    say(f"  Telegram asked us to wait {e.seconds}s ...")
                    await asyncio.sleep(e.seconds + 1)

        for data in lists:
            entity = await _flood_safe(lambda: resolve(main, str(data["id"])))
            chat_id = abs(int(utils.get_peer_id(entity, add_mark=False)))
            ids = [int(m["id"]) for m in data.get("messages", []) if m.get("type") == "message"]
            names = {int(m["id"]): m.get("file") or "media" for m in data.get("messages", [])}
            stats = Stats(len(ids))
            sem = asyncio.Semaphore(max(1, args.limit))
            ref_paths = [Path(p.strip()) for r in (args.ref_dir or []) for p in r.split(";") if p.strip()]
            ex_mids, ex_doc_ids, ex_tails, ex_date_sz = _scan_existing_dir(out_dir, ref_paths)
            say(f"All files will be downloaded to '{out_dir}' dir"
                + (f" (skipping files in reference folder: {', '.join(str(p) for p in ref_paths)})" if ref_paths else ""))

            def _already_on_disk(msg, final: Path, size: int, raw_name: str) -> bool:
                if final.exists() and final.stat().st_size > 0 and (not size or final.stat().st_size == size):
                    return True

                def _sz_ok(s_set: set[int]) -> bool:
                    return bool(s_set) and (not size or size in s_set or any(abs(s - size) <= 1024 for s in s_set))

                if msg.id in ex_mids and _sz_ok(ex_mids[msg.id]):
                    return True
                did = int(getattr(msg.document, "id", 0) or getattr(msg.photo, "id", 0) or 0)
                if did and did in ex_doc_ids and _sz_ok(ex_doc_ids[did]):
                    return True
                nt = _norm_tail(raw_name, True)
                if nt and nt not in ("media", "file", "video", "photo") and nt in ex_tails and _sz_ok(ex_tails[nt]):
                    return True
                if size >= 32768:
                    ext = os.path.splitext(raw_name)[1].lower()
                    if ext and (size, ext) in ex_date_sz:
                        return True
                return False

            async def one(msg):
                async with sem:
                    raw_name = names.get(msg.id) or media_name(msg)
                    final = out_dir / file_name(chat_id, msg.id, raw_name)
                    tmp = Path(str(final) + ".tmp")
                    size = int(getattr(msg.document, "size", 0) or 0) if msg.document is not None else 0
                    if _already_on_disk(msg, final, size, raw_name):
                        stats.skipped += 1
                        return
                    t0 = time.time()

                    async def refresh():
                        m = await _flood_safe(lambda: main.get_messages(entity, ids=msg.id))
                        if m is None or m.media is None:
                            raise RuntimeError("message was deleted")
                        return m.document or m.photo

                    try:
                        if msg.document is not None:
                            got = await download_document(clients, msg, tmp, max(1, args.threads), refresh, final.name)
                        else:  # photos: small, one request or two
                            async with LIMITER:
                                r = await _flood_safe(lambda: main.download_media(msg, file=str(tmp)))
                            if not r:
                                raise RuntimeError("Telegram returned no data")
                            got = tmp.stat().st_size
                        os.replace(tmp, final)
                        stats.done += 1
                        stats.bytes += got
                        el = max(0.001, time.time() - t0)
                        say(f"done!  {final.name}  {got / 1048576:.1f} MB  {got / el / 1048576:.2f} MB/s   {stats.line()}")
                    except asyncio.CancelledError:
                        raise
                    except Exception as e:  # noqa: BLE001
                        stats.failed += 1
                        try:
                            tmp.unlink()  # like tdl: a failed file leaves no .tmp behind
                        except OSError:
                            pass
                        print(f"{final.name} error: {type(e).__name__}: {e}", file=sys.stderr, flush=True)

            # fetch message details 100 at a time, keep up to 3 batches of downloads queued
            pending: set[asyncio.Task] = set()
            for i in range(0, len(ids), 100):
                batch = ids[i:i + 100]
                msgs = await _flood_safe(lambda b=batch: main.get_messages(entity, ids=b))
                for mid, m in zip(batch, msgs):
                    if m is None or m.media is None or (m.document is None and m.photo is None):
                        stats.failed += 1
                        print(f"message {mid} error: deleted or has no media any more", file=sys.stderr)
                        continue
                    pending.add(asyncio.create_task(one(m)))
                while len(pending) > max(args.limit, 1) * 150:
                    done, pending = await asyncio.wait(pending, return_when=asyncio.FIRST_COMPLETED)
                await asyncio.sleep(BATCH_PACE)  # stay under Telegram's limit for these lookups
            if pending:
                await asyncio.gather(*pending)
            say("Finished.  " + stats.line())
            if PREMIUM_LIMIT_HITS[0]:
                say(f"Telegram's free-account speed limit was hit {PREMIUM_LIMIT_HITS[0]:,} times during this run.")
    finally:
        for c in clients:
            try:
                await c.disconnect()
            except Exception:  # noqa: BLE001
                pass


# --------------------------------------------------------------------------- #
def main():
    if len(sys.argv) > 1 and sys.argv[1] in ("--version", "version"):
        say("tg_engine 1.0 (built-in engine for Telegram Media Saver)")
        return
    p = argparse.ArgumentParser(prog="tg_engine")
    sub = p.add_subparsers(dest="cmd", required=True)
    sub.add_parser("login").add_argument("-T", "--type", default="code")
    chat = sub.add_parser("chat").add_subparsers(dest="chatcmd", required=True)
    ls = chat.add_parser("ls")
    ls.add_argument("-o", "--output", default="json")
    ex = chat.add_parser("export")
    ex.add_argument("-c", "--chat", required=True)
    ex.add_argument("-o", "--output", default="tdl-export.json")
    ex.add_argument("--raw", action="store_true")
    dl = sub.add_parser("dl")
    dl.add_argument("-f", "--file", action="append", required=True)
    dl.add_argument("-d", "--dir", default="downloads")
    dl.add_argument("-r", "--ref-dir", action="append", default=[],
                    help="Reference folder(s) whose existing files should be skipped")
    dl.add_argument("-t", "--threads", type=int, default=4)
    dl.add_argument("-l", "--limit", type=int, default=2)
    dl.add_argument("--takeout", action="store_true")
    args, _unknown = p.parse_known_args()  # ignores tdl-only options like --pool / --skip-same

    try:
        import telethon  # noqa: F401
    except ImportError:
        fail("Telethon isn't installed. Open a terminal and run:  py -m pip install telethon cryptg")
    if args.cmd == "login":
        coro = cmd_login(args)
    elif args.cmd == "chat" and args.chatcmd == "ls":
        coro = cmd_chat_ls(args)
    elif args.cmd == "chat":
        coro = cmd_export(args)
    else:
        coro = cmd_dl(args)
    show_telegram_waits()
    try:
        asyncio.run(coro)
    except KeyboardInterrupt:
        fail("Stopped.", 130)


if __name__ == "__main__":
    main()
