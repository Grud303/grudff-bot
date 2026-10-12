#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Grudff Moderator — бот-модератор для Telegram-груп (один файл, без зовнішніх конфігів).

ЩО ВМІЄ
  * фільтр заборонених слів: «слово», «слово*», «*слово», «*слово*», фрази; ловить обхід
    (латиниця замість кирилиці, «лооох», «л о х», невидимі символи)
  * фільтр нікнеймів (префікс або маска *_bot, a?c*) та імен із рекламою/посиланнями
  * антиспам за балами: запрошення в групи, посилання, скорочувачі, рекламні фрази,
    крипто-гаманці, телефони, емодзі, змішані алфавіти, приховані посилання, масові згадки
  * антифлуд, дублікати, «хвилі» однакового спаму від різних акаунтів, перевірка редагувань
  * новачки: капча (арифметика кнопками), антирейд, блок сторонніх ботів, заявки на вступ
  * попередження з терміном дії → мут / бан / кік, довірені користувачі, білий список доменів
  * блокування контенту (/lock), /lockdown, скарги /report, журнал, статистика, глобальний бан
  * панель налаштувань кнопками (/settings); налаштування окремі для кожної групи (SQLite)

ВСТАНОВЛЕННЯ (Python 3.10+)
    pip install "python-telegram-bot[job-queue]>=21.0,<23.0"

ЗАПУСК
    export BOT_TOKEN="токен_від_BotFather"
    export OWNER_IDS="123456789"      # ваш Telegram ID (потрібен для /gban), можна кілька через кому
    python bot.py

ЗМІННІ СЕРЕДОВИЩА
    BOT_TOKEN  — токен бота (обов'язково)
    OWNER_IDS  — ID власників бота (мають права адміна в усіх групах)
    DATA_DIR   — папка для бази grudff_moderator.db (на Railway — шлях до Volume, напр. /data)
    LOG_LEVEL  — INFO (за замовчуванням) або DEBUG
    Railway: додайте Volume у /data, задайте DATA_DIR=/data, команда запуску: python bot.py

ПРАВА БОТА В ГРУПІ
    Адміністратор із правами: «Видаляти повідомлення» і «Блокувати користувачів» (обов'язково),
    «Запрошувати користувачів» (за бажанням, для заявок на вступ).
    Права «Додавати адмінів», «Керувати чатом», «Анонімність» НЕ потрібні.
    Після додавання виконайте /check, потім /settings.

КОМАНДИ АДМІНІВ (ціль: відповідь на повідомлення, @нік або ID)
    /warn [причина] · /unwarn · /warns · /resetwarns
    /mute [30m|2h|1d|perm] [причина] · /unmute
    /ban [тривалість] [причина] · /unban · /kick · /banned
    /trust · /untrust · /trusted
    /addword /removeword /listwords · /addnick /removenick /listnicks · /addwhite /removewhite /listwhite
    /lock /unlock /locks · /lockdown [час] /unlockdown · /raid on|off|status
    /del · /purge (відповідь на перше повідомлення діапазону)
    /settings · /set ключ значення · /setrules · /setwelcome · /setlog · /modlog · /stats · /check · /reload
    Для всіх: /rules · /mywarns · /report · /id · /help
    Власник бота: /gban · /ungban · /gbanlist

ПОРАДИ
    * Типові налаштування обережні: капча вимкнена, посилання блокуються лише новачкам, поріг спаму 6.
      Спершу спостерігайте, потім посилюйте (link_policy, капча, spam_threshold).
    * Список заборонених слів порожній — наповніть його через /addword.
    * Дані старої версії (JSON-файли) не переносяться.
"""
from __future__ import annotations

import asyncio
import functools
import hashlib
import html
import json
import logging
import os
import random
import re
import sqlite3
import threading
import time
import unicodedata
from collections import defaultdict, deque
from dataclasses import dataclass, field
from datetime import time as dtime
from fnmatch import fnmatchcase
from typing import Any, Callable, Optional

from telegram import (
    BotCommand,
    BotCommandScopeAllChatAdministrators,
    BotCommandScopeAllGroupChats,
    ChatPermissions,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    Message,
    MessageEntity,
    ReplyParameters,
    Update,
    User,
)
from telegram.constants import ChatType, ParseMode
from telegram.error import BadRequest, Forbidden, TelegramError
from telegram.ext import (
    Application,
    CallbackQueryHandler,
    ChatJoinRequestHandler,
    ChatMemberHandler,
    CommandHandler,
    ContextTypes,
    MessageHandler,
    filters,
)

# ============================================================
#  НАЛАШТУВАННЯ СЕРЕДОВИЩА
# ============================================================

TOKEN = os.getenv("BOT_TOKEN", "").strip()
OWNER_IDS = {int(x) for x in re.findall(r"\d+", os.getenv("OWNER_IDS", ""))}
DATA_DIR = os.getenv("DATA_DIR", ".")
DB_PATH = os.path.join(DATA_DIR, "grudff_moderator.db")
LOG_LEVEL = os.getenv("LOG_LEVEL", "INFO").upper()

logging.basicConfig(
    format="%(asctime)s | %(levelname)-7s | %(name)s | %(message)s",
    level=getattr(logging, LOG_LEVEL, logging.INFO),
)
logging.getLogger("httpx").setLevel(logging.WARNING)
log = logging.getLogger("grudff")

GROUP_TYPES = (ChatType.GROUP, ChatType.SUPERGROUP)

# ============================================================
#  ЗАГАЛЬНІ УТИЛІТИ
# ============================================================


def esc(value: Any) -> str:
    """Екранування тексту для HTML-розмітки Telegram."""
    return html.escape(str(value), quote=False)


def mention(user_id: int, name: str) -> str:
    return f'<a href="tg://user?id={int(user_id)}">{esc(name or user_id)}</a>'


def user_link(user: User) -> str:
    return mention(user.id, user.full_name)


def now_ts() -> int:
    return int(time.time())


def fmt_ts(ts: int) -> str:
    return time.strftime("%d.%m.%Y %H:%M", time.localtime(ts))


_DURATION_RE = re.compile(r"^(\d{1,6})\s*(s|sec|с|m|min|хв|h|hr|г|год|d|д|дн|w|т|тиж)?$", re.I)
_UNIT_SECONDS = {
    "s": 1, "sec": 1, "с": 1,
    "m": 60, "min": 60, "хв": 60,
    "h": 3600, "hr": 3600, "г": 3600, "год": 3600,
    "d": 86400, "д": 86400, "дн": 86400,
    "w": 604800, "т": 604800, "тиж": 604800,
}
_FOREVER = {"perm", "forever", "назавжди", "inf", "∞"}


def parse_duration(token: str) -> Optional[int]:
    """'30', '30m', '2h', '1d', '1w' → секунди. 'perm' → 0. Невалідне → None."""
    token = token.strip().lower()
    if token in _FOREVER:
        return 0
    m = _DURATION_RE.match(token)
    if not m:
        return None
    value = int(m.group(1))
    unit = (m.group(2) or "m").lower()
    return value * _UNIT_SECONDS.get(unit, 60)


def fmt_duration(seconds: int) -> str:
    if seconds <= 0:
        return "назавжди"
    parts = []
    for name, size in (("дн", 86400), ("год", 3600), ("хв", 60), ("с", 1)):
        if seconds >= size:
            parts.append(f"{seconds // size} {name}")
            seconds %= size
    return " ".join(parts[:2]) or "0 с"


def for_duration(seconds: int) -> str:
    """'на 2 год' або 'назавжди'."""
    return "назавжди" if seconds <= 0 else f"на {fmt_duration(seconds)}"


def split_duration(args: list[str], default: Optional[int] = None) -> tuple[Optional[int], str]:
    """Відділяє тривалість (перший аргумент) від причини. Повертає (секунди, причина)."""
    if args:
        d = parse_duration(args[0])
        if d is not None:
            return d, " ".join(args[1:]).strip()
    return default, " ".join(args).strip()


def chunked(items: list, size: int):
    for i in range(0, len(items), size):
        yield items[i:i + size]


def short(text: str, limit: int = 80) -> str:
    text = " ".join((text or "").split())
    return text if len(text) <= limit else text[: limit - 1] + "…"


# ============================================================
#  НАЛАШТУВАННЯ ЗА ЗАМОВЧУВАННЯМ (для кожної групи окремо)
# ============================================================

DEFAULTS: dict[str, Any] = {
    # --- перемикачі ---
    "bad_words_filter": True,
    "nick_filter": True,
    "name_filter": True,
    "antispam": True,
    "antiflood": True,
    "duplicate_filter": True,
    "spam_wave": True,
    "captcha": False,
    "antiraid": True,
    "welcome": True,
    "delete_service": False,
    "kick_bots": True,
    "gban_enabled": True,
    "block_channels": False,
    "forward_filter": False,
    "notify": True,
    "auto_approve": False,
    # --- режими (0/1/2...) ---
    "link_policy": 1,          # 0 — вимк., 1 — тільки новачки, 2 — усі
    "warn_action": "ban",      # ban | mute | kick
    "nick_action": "ban",      # ban | kick | delete
    # --- числа ---
    "max_warns": 3,
    "warn_expire_days": 30,
    "warn_mute_minutes": 1440,
    "flood_limit": 6,
    "flood_seconds": 8,
    "mute_minutes": 15,
    "dup_limit": 3,
    "spam_threshold": 6,
    "spam_ban_score": 12,
    "newbie_minutes": 30,
    "captcha_timeout": 120,
    "raid_joins": 8,
    "raid_seconds": 30,
    "raid_minutes": 10,
    "max_mentions": 5,
    "notify_ttl": 20,
    "welcome_ttl": 60,
    # --- тексти та службове ---
    "welcome_text": "👋 Ласкаво просимо, {mention}!\nПрочитай правила: /rules",
    "rules_text": "",
    "log_chat": 0,
    "locks": [],
    "lockdown_prev": None,
}

DEFAULT_RULES = (
    "📋 <b>Правила групи</b>\n\n"
    "1. Без заборонених слів і образ\n"
    "2. Без реклами, спаму та сторонніх посилань\n"
    "3. Не флудити\n"
    "4. Поважати учасників та адміністрацію\n"
    "5. Дотримуватися теми групи\n\n"
    "Порушення = попередження → мут / бан"
)

LOCK_TYPES = {
    "links": "посилання",
    "media": "фото/відео/гіфки",
    "stickers": "стікери",
    "voice": "голосові/аудіо",
    "documents": "файли",
    "forwards": "пересилання",
    "polls": "опитування",
    "contacts": "контакти",
    "location": "геолокація",
}

# ============================================================
#  СХОВИЩЕ (SQLite)
# ============================================================

SCHEMA = """
CREATE TABLE IF NOT EXISTS settings(chat_id INTEGER, key TEXT, value TEXT, PRIMARY KEY(chat_id, key));
CREATE TABLE IF NOT EXISTS lists(chat_id INTEGER, kind TEXT, value TEXT, PRIMARY KEY(chat_id, kind, value));
CREATE TABLE IF NOT EXISTS trusted(chat_id INTEGER, user_id INTEGER, PRIMARY KEY(chat_id, user_id));
CREATE TABLE IF NOT EXISTS warns(
    id INTEGER PRIMARY KEY AUTOINCREMENT, chat_id INTEGER, user_id INTEGER,
    admin_id INTEGER, reason TEXT, ts INTEGER);
CREATE INDEX IF NOT EXISTS ix_warns ON warns(chat_id, user_id, ts);
CREATE TABLE IF NOT EXISTS modlog(
    id INTEGER PRIMARY KEY AUTOINCREMENT, chat_id INTEGER, ts INTEGER, action TEXT,
    user_id INTEGER, user_name TEXT, admin_name TEXT, reason TEXT);
CREATE INDEX IF NOT EXISTS ix_modlog ON modlog(chat_id, ts);
CREATE TABLE IF NOT EXISTS bans(
    chat_id INTEGER, user_id INTEGER, name TEXT, reason TEXT, ts INTEGER, until INTEGER,
    PRIMARY KEY(chat_id, user_id));
CREATE TABLE IF NOT EXISTS gbans(user_id INTEGER PRIMARY KEY, name TEXT, reason TEXT, ts INTEGER);
CREATE TABLE IF NOT EXISTS captcha(
    chat_id INTEGER, user_id INTEGER, answer INTEGER, msg_id INTEGER, deadline INTEGER,
    attempts INTEGER DEFAULT 0, PRIMARY KEY(chat_id, user_id));
CREATE TABLE IF NOT EXISTS users(user_id INTEGER PRIMARY KEY, username TEXT, full_name TEXT, updated INTEGER);
CREATE INDEX IF NOT EXISTS ix_users_username ON users(username);
CREATE TABLE IF NOT EXISTS chats(chat_id INTEGER PRIMARY KEY, title TEXT, type TEXT, updated INTEGER);
CREATE TABLE IF NOT EXISTS activity(
    chat_id INTEGER, user_id INTEGER, first_seen INTEGER, joined INTEGER DEFAULT 0,
    messages INTEGER DEFAULT 0, last_seen INTEGER, PRIMARY KEY(chat_id, user_id));
CREATE TABLE IF NOT EXISTS stats(chat_id INTEGER, day TEXT, kind TEXT, n INTEGER DEFAULT 0,
    PRIMARY KEY(chat_id, day, kind));
"""


class Storage:
    """Тонка обгортка над SQLite. Усі виклики короткі, тому виконуються синхронно."""

    def __init__(self, path: str):
        if os.path.dirname(path):
            os.makedirs(os.path.dirname(path), exist_ok=True)
        self.path = path
        self._lock = threading.RLock()
        self._conn = sqlite3.connect(path, check_same_thread=False, isolation_level=None)
        self._conn.row_factory = sqlite3.Row
        with self._lock:
            self._conn.execute("PRAGMA journal_mode=WAL")
            self._conn.execute("PRAGMA synchronous=NORMAL")
            self._conn.executescript(SCHEMA)

    # ----- низький рівень -----
    def run(self, sql: str, params: tuple = (), *, one: bool = False, many: bool = False):
        with self._lock:
            cur = self._conn.execute(sql, params)
            if one:
                return cur.fetchone()
            if many:
                return cur.fetchall()
            return cur.rowcount

    # ----- налаштування -----
    def load_settings(self, chat_id: int) -> dict[str, Any]:
        rows = self.run("SELECT key, value FROM settings WHERE chat_id=?", (chat_id,), many=True)
        out = {}
        for r in rows:
            try:
                out[r["key"]] = json.loads(r["value"])
            except json.JSONDecodeError:
                continue
        return out

    def save_setting(self, chat_id: int, key: str, value: Any) -> None:
        self.run(
            "INSERT INTO settings(chat_id,key,value) VALUES(?,?,?) "
            "ON CONFLICT(chat_id,key) DO UPDATE SET value=excluded.value",
            (chat_id, key, json.dumps(value, ensure_ascii=False)),
        )

    # ----- списки (слова, ніки, домени) -----
    def list_add(self, chat_id: int, kind: str, value: str) -> bool:
        return self.run("INSERT OR IGNORE INTO lists VALUES(?,?,?)", (chat_id, kind, value)) > 0

    def list_remove(self, chat_id: int, kind: str, value: str) -> bool:
        return self.run("DELETE FROM lists WHERE chat_id=? AND kind=? AND value=?", (chat_id, kind, value)) > 0

    def list_get(self, chat_id: int, kind: str) -> list[str]:
        rows = self.run("SELECT value FROM lists WHERE chat_id=? AND kind=? ORDER BY value", (chat_id, kind), many=True)
        return [r["value"] for r in rows]

    # ----- довірені користувачі -----
    def trust_add(self, chat_id: int, user_id: int) -> bool:
        return self.run("INSERT OR IGNORE INTO trusted VALUES(?,?)", (chat_id, user_id)) > 0

    def trust_remove(self, chat_id: int, user_id: int) -> bool:
        return self.run("DELETE FROM trusted WHERE chat_id=? AND user_id=?", (chat_id, user_id)) > 0

    def is_trusted(self, chat_id: int, user_id: int) -> bool:
        return self.run("SELECT 1 FROM trusted WHERE chat_id=? AND user_id=?", (chat_id, user_id), one=True) is not None

    def trusted_list(self, chat_id: int) -> list[int]:
        return [r["user_id"] for r in self.run("SELECT user_id FROM trusted WHERE chat_id=?", (chat_id,), many=True)]

    # ----- попередження -----
    def warn_add(self, chat_id: int, user_id: int, admin_id: int, reason: str) -> None:
        self.run("INSERT INTO warns(chat_id,user_id,admin_id,reason,ts) VALUES(?,?,?,?,?)",
                 (chat_id, user_id, admin_id, reason, now_ts()))

    def warn_count(self, chat_id: int, user_id: int, expire_days: int = 0) -> int:
        since = now_ts() - expire_days * 86400 if expire_days > 0 else 0
        row = self.run("SELECT COUNT(*) AS c FROM warns WHERE chat_id=? AND user_id=? AND ts>=?",
                       (chat_id, user_id, since), one=True)
        return row["c"]

    def warn_list(self, chat_id: int, user_id: int, expire_days: int = 0):
        since = now_ts() - expire_days * 86400 if expire_days > 0 else 0
        return self.run("SELECT * FROM warns WHERE chat_id=? AND user_id=? AND ts>=? ORDER BY ts",
                        (chat_id, user_id, since), many=True)

    def warn_remove_last(self, chat_id: int, user_id: int) -> bool:
        row = self.run("SELECT id FROM warns WHERE chat_id=? AND user_id=? ORDER BY ts DESC, id DESC LIMIT 1",
                       (chat_id, user_id), one=True)
        if not row:
            return False
        self.run("DELETE FROM warns WHERE id=?", (row["id"],))
        return True

    def warn_clear(self, chat_id: int, user_id: int) -> int:
        return self.run("DELETE FROM warns WHERE chat_id=? AND user_id=?", (chat_id, user_id))

    # ----- журнал модерації -----
    def log_add(self, chat_id: int, action: str, user_id: int, user_name: str, admin_name: str, reason: str) -> None:
        self.run("INSERT INTO modlog(chat_id,ts,action,user_id,user_name,admin_name,reason) VALUES(?,?,?,?,?,?,?)",
                 (chat_id, now_ts(), action, user_id, user_name, admin_name, reason))

    def log_recent(self, chat_id: int, limit: int = 15):
        return self.run("SELECT * FROM modlog WHERE chat_id=? ORDER BY id DESC LIMIT ?", (chat_id, limit), many=True)

    # ----- бани -----
    def ban_add(self, chat_id: int, user_id: int, name: str, reason: str, until: int = 0) -> None:
        self.run("INSERT OR REPLACE INTO bans VALUES(?,?,?,?,?,?)", (chat_id, user_id, name, reason, now_ts(), until))

    def ban_remove(self, chat_id: int, user_id: int) -> None:
        self.run("DELETE FROM bans WHERE chat_id=? AND user_id=?", (chat_id, user_id))

    def ban_list(self, chat_id: int, limit: int = 30):
        return self.run("SELECT * FROM bans WHERE chat_id=? ORDER BY ts DESC LIMIT ?", (chat_id, limit), many=True)

    def ban_expired(self):
        return self.run("SELECT * FROM bans WHERE until>0 AND until<=?", (now_ts(),), many=True)

    # ----- глобальні бани -----
    def gban_add(self, user_id: int, name: str, reason: str) -> None:
        self.run("INSERT OR REPLACE INTO gbans VALUES(?,?,?,?)", (user_id, name, reason, now_ts()))

    def gban_remove(self, user_id: int) -> bool:
        return self.run("DELETE FROM gbans WHERE user_id=?", (user_id,)) > 0

    def gban_get(self, user_id: int):
        return self.run("SELECT * FROM gbans WHERE user_id=?", (user_id,), one=True)

    def gban_list(self, limit: int = 50):
        return self.run("SELECT * FROM gbans ORDER BY ts DESC LIMIT ?", (limit,), many=True)

    # ----- капча -----
    def captcha_add(self, chat_id: int, user_id: int, answer: int, msg_id: int, deadline: int) -> None:
        self.run("INSERT OR REPLACE INTO captcha VALUES(?,?,?,?,?,0)", (chat_id, user_id, answer, msg_id, deadline))

    def captcha_get(self, chat_id: int, user_id: int):
        return self.run("SELECT * FROM captcha WHERE chat_id=? AND user_id=?", (chat_id, user_id), one=True)

    def captcha_attempt(self, chat_id: int, user_id: int) -> int:
        self.run("UPDATE captcha SET attempts=attempts+1 WHERE chat_id=? AND user_id=?", (chat_id, user_id))
        row = self.captcha_get(chat_id, user_id)
        return row["attempts"] if row else 0

    def captcha_remove(self, chat_id: int, user_id: int) -> None:
        self.run("DELETE FROM captcha WHERE chat_id=? AND user_id=?", (chat_id, user_id))

    def captcha_all(self):
        return self.run("SELECT * FROM captcha", many=True)

    # ----- кеш користувачів та чатів -----
    def user_upsert(self, user: User) -> None:
        self.run(
            "INSERT INTO users VALUES(?,?,?,?) ON CONFLICT(user_id) DO UPDATE SET "
            "username=excluded.username, full_name=excluded.full_name, updated=excluded.updated",
            (user.id, (user.username or "").lower(), user.full_name, now_ts()),
        )

    def user_by_username(self, username: str):
        return self.run("SELECT * FROM users WHERE username=?", (username.lower().lstrip("@"),), one=True)

    def user_by_id(self, user_id: int):
        return self.run("SELECT * FROM users WHERE user_id=?", (user_id,), one=True)

    def chat_upsert(self, chat_id: int, title: str, ctype: str) -> None:
        self.run(
            "INSERT INTO chats VALUES(?,?,?,?) ON CONFLICT(chat_id) DO UPDATE SET "
            "title=excluded.title, type=excluded.type, updated=excluded.updated",
            (chat_id, title or "", ctype, now_ts()),
        )

    def chat_remove(self, chat_id: int) -> None:
        self.run("DELETE FROM chats WHERE chat_id=?", (chat_id,))

    def chat_list(self):
        return self.run("SELECT * FROM chats ORDER BY title", many=True)

    # ----- активність -----
    def touch_activity(self, chat_id: int, user_id: int, *, joined: bool = False, message: bool = False):
        """Оновлює запис активності. Повертає рядок (first_seen, joined, messages)."""
        ts = now_ts()
        row = self.run("SELECT * FROM activity WHERE chat_id=? AND user_id=?", (chat_id, user_id), one=True)
        if row is None:
            self.run("INSERT INTO activity VALUES(?,?,?,?,?,?)",
                     (chat_id, user_id, ts, 1 if joined else 0, 1 if message else 0, ts))
        else:
            if joined:
                self.run("UPDATE activity SET first_seen=?, joined=1, messages=0, last_seen=? WHERE chat_id=? AND user_id=?",
                         (ts, ts, chat_id, user_id))
            elif message:
                self.run("UPDATE activity SET messages=messages+1, last_seen=? WHERE chat_id=? AND user_id=?",
                         (ts, chat_id, user_id))
        return self.run("SELECT * FROM activity WHERE chat_id=? AND user_id=?", (chat_id, user_id), one=True)

    # ----- статистика -----
    def bump(self, chat_id: int, kind: str, n: int = 1) -> None:
        day = time.strftime("%Y-%m-%d")
        self.run(
            "INSERT INTO stats VALUES(?,?,?,?) ON CONFLICT(chat_id,day,kind) DO UPDATE SET n=n+excluded.n",
            (chat_id, day, kind, n),
        )

    def stats(self, chat_id: int, days: int = 7) -> dict[str, int]:
        since = time.strftime("%Y-%m-%d", time.localtime(time.time() - days * 86400))
        rows = self.run("SELECT kind, SUM(n) AS n FROM stats WHERE chat_id=? AND day>=? GROUP BY kind",
                        (chat_id, since), many=True)
        return {r["kind"]: r["n"] for r in rows}

    def cleanup(self) -> None:
        self.run("DELETE FROM modlog WHERE ts<?", (now_ts() - 90 * 86400,))
        self.run("DELETE FROM stats WHERE day<?", (time.strftime("%Y-%m-%d", time.localtime(time.time() - 120 * 86400)),))
        self.run("DELETE FROM warns WHERE ts<?", (now_ts() - 400 * 86400,))


class SettingsManager:
    """Налаштування кожної групи з кешем у пам'яті."""

    def __init__(self, db: Storage):
        self.db = db
        self._cache: dict[int, dict[str, Any]] = {}

    def _chat(self, chat_id: int) -> dict[str, Any]:
        if chat_id not in self._cache:
            self._cache[chat_id] = self.db.load_settings(chat_id)
        return self._cache[chat_id]

    def get(self, chat_id: int, key: str) -> Any:
        return self._chat(chat_id).get(key, DEFAULTS[key])

    def set(self, chat_id: int, key: str, value: Any) -> None:
        self._chat(chat_id)[key] = value
        self.db.save_setting(chat_id, key, value)

    def drop_cache(self, chat_id: Optional[int] = None) -> None:
        if chat_id is None:
            self._cache.clear()
        else:
            self._cache.pop(chat_id, None)


db = Storage(DB_PATH)
cfg = SettingsManager(db)


# ============================================================
#  НОРМАЛІЗАЦІЯ ТЕКСТУ ТА ПОШУК ЗАБОРОНЕНИХ СЛІВ
# ============================================================

# невидимі символи, якими «розбавляють» слова
_STRIP = dict.fromkeys(
    map(ord, "\u200b\u200c\u200d\u200e\u200f\u2060\u2061\u2062\u2063\ufeff\u00ad\u180e\u034f"), None
)
# схожі літери та «лір-спік»: латиниця/цифри → кирилиця
_LAT_TO_CYR = str.maketrans({
    "a": "а", "c": "с", "e": "е", "o": "о", "p": "р", "x": "х", "y": "у", "k": "к",
    "m": "м", "t": "т", "h": "н", "b": "в", "i": "і", "u": "и", "r": "г",
    "0": "о", "3": "з", "4": "а", "6": "б", "@": "а",
})
# кирилиця → латиниця (для заборонених англійських слів)
_CYR_TO_LAT = str.maketrans({
    "а": "a", "с": "c", "е": "e", "о": "o", "р": "p", "х": "x", "у": "y", "к": "k",
    "м": "m", "т": "t", "н": "h", "в": "b", "і": "i", "и": "u", "г": "r",
    "0": "o", "1": "i", "3": "e", "4": "a", "5": "s", "$": "s", "@": "a",
})
# дрібні варіанти написання, які не повинні рятувати від фільтра
_EXTRA_FOLD = str.maketrans({"ё": "е", "ґ": "г", "ї": "і", "є": "е", "ъ": "", "ь": "", "ы": "и", "э": "е", "й": "и"})

_REPEAT_RE = re.compile(r"(.)\1+")
_TOKEN_RE = re.compile(r"[^\W_]+")
_SPACED_RE = re.compile(r"(?<![^\W_])(?:[^\W\d_][ \t.\-_*,|/\\]{1,2}){2,}[^\W\d_](?![^\W_])")


def _base(text: str) -> str:
    t = unicodedata.normalize("NFKC", text or "").casefold().translate(_STRIP)
    return "".join(ch for ch in t if not unicodedata.category(ch).startswith("M"))


def squash_spaced(text: str) -> str:
    """'м а т' / 'м.а.т' → 'мат': склеює літери, рознесені роздільниками."""
    return _SPACED_RE.sub(lambda m: re.sub(r"[\W_]+", "", m.group(0)), text)


def text_forms(text: str) -> tuple[str, str]:
    """Дві «скелетні» форми тексту: у кирилиці та у латиниці. Повтори літер стискаються."""
    base = squash_spaced(_base(text)).translate(_EXTRA_FOLD)
    cyr = _REPEAT_RE.sub(r"\1", base.translate(_LAT_TO_CYR))
    lat = _REPEAT_RE.sub(r"\1", base.translate(_CYR_TO_LAT))
    return cyr, lat


class WordMatcher:
    """
    Пошук заборонених слів. Формати запису:
      слово   — точний збіг цілого слова
      слово*  — слова, що починаються на «слово»
      *слово  — слова, що закінчуються на «слово»
      *слово* — будь-яке входження
      кілька слів — збіг фрази
    """

    def __init__(self, entries: list[str]):
        self.exact: tuple[dict[str, str], dict[str, str]] = ({}, {})
        self.complex: list[tuple[str, str, str, str]] = []
        for raw in entries:
            raw = raw.strip()
            if not raw:
                continue
            starts, ends, core = raw.startswith("*"), raw.endswith("*"), raw.strip("*")
            cyr, lat = (x.strip() for x in text_forms(core))
            if len(cyr) < 2:
                continue
            mode = "contains" if starts and ends else "suffix" if starts else "prefix" if ends else "exact"
            if mode == "exact" and " " not in cyr:
                self.exact[0][cyr] = raw
                self.exact[1][lat] = raw
            else:
                self.complex.append((raw, mode, cyr, lat))

    def __bool__(self) -> bool:
        return bool(self.exact[0] or self.complex)

    def find(self, text: str) -> Optional[str]:
        """Повертає запис зі списку, що спрацював, або None."""
        if not self or not text:
            return None
        forms = text_forms(text[:4000])
        for idx, form in enumerate(forms):
            tokens = _TOKEN_RE.findall(form)
            for tok in tokens:
                hit = self.exact[idx].get(tok)
                if hit:
                    return hit
            joined = " ".join(tokens)
            padded = f" {joined} "
            for raw, mode, cyr, lat in self.complex:
                needle = cyr if idx == 0 else lat
                if " " in needle:
                    if f" {needle} " in padded:
                        return raw
                    continue
                for tok in tokens:
                    if (
                        (mode == "prefix" and tok.startswith(needle))
                        or (mode == "suffix" and tok.endswith(needle))
                        or (mode == "contains" and needle in tok)
                        or (mode == "exact" and tok == needle)
                    ):
                        return raw
        return None


class NickMatcher:
    """Заборонені нікнейми: «spam» = префікс, «*bot» / «a?c*» = маска."""

    def __init__(self, patterns: list[str]):
        self.patterns = [p.lower().strip().lstrip("@") for p in patterns if p.strip()]

    def find(self, username: Optional[str]) -> Optional[str]:
        if not username:
            return None
        u = username.lower()
        for p in self.patterns:
            if ("*" in p or "?" in p) and fnmatchcase(u, p):
                return p
            if "*" not in p and "?" not in p and u.startswith(p):
                return p
        return None


class MatcherCache:
    def __init__(self, storage: Storage):
        self.db = storage
        self._words: dict[int, WordMatcher] = {}
        self._nicks: dict[int, NickMatcher] = {}
        self._domains: dict[int, list[str]] = {}

    def words(self, chat_id: int) -> WordMatcher:
        if chat_id not in self._words:
            self._words[chat_id] = WordMatcher(self.db.list_get(chat_id, "word"))
        return self._words[chat_id]

    def nicks(self, chat_id: int) -> NickMatcher:
        if chat_id not in self._nicks:
            self._nicks[chat_id] = NickMatcher(self.db.list_get(chat_id, "nick"))
        return self._nicks[chat_id]

    def domains(self, chat_id: int) -> list[str]:
        if chat_id not in self._domains:
            self._domains[chat_id] = self.db.list_get(chat_id, "domain")
        return self._domains[chat_id]

    def invalidate(self, chat_id: int) -> None:
        self._words.pop(chat_id, None)
        self._nicks.pop(chat_id, None)
        self._domains.pop(chat_id, None)


matchers = MatcherCache(db)

# ============================================================
#  ПОСИЛАННЯ, ЗГАДКИ, ЕМОДЗІ
# ============================================================

_TLDS = (
    "com|net|org|info|ru|ua|me|io|co|xyz|top|site|online|club|vip|bet|casino|bio|link|cc|pw|tk|ml|ga|cf|gq|"
    "shop|store|app|dev|tv|su|biz|click|cfd|live|win|fun|ly|gl|gd|ink|pro|team|work|cash|money|today|world|"
    "page|space|website|tech|icu|one|best|life|cloud|blog|help|support|pics|porn|sex|xxx|adult|gold|trade"
)
# Домен шукаємо лише з початку «слова» (lookbehind) і з обмеженою кількістю міток —
# це гарантує лінійний час на довгих шкідливих рядках типу «a.a.a.a…».
URL_RE = re.compile(
    r"(?i)\b(?:https?://|www\.)[^\s<>\"']+"
    r"|(?<![\w.\-@])(?:[a-z0-9](?:[a-z0-9\-]{0,61}[a-z0-9])?\.){1,8}(?:" + _TLDS + r")\b(?:/[^\s<>\"']*)?"
)
TG_LINK_RE = re.compile(r"(?i)(?:https?://)?(?:t|telegram)\.(?:me|dog)/[^\s]+|tg://[^\s]+")
TG_INVITE_RE = re.compile(r"(?i)(?:t|telegram)\.(?:me|dog)/(?:\+|joinchat/)[\w\-]+|tg://join\?invite=[\w\-]+")
SHORTENERS = {
    "bit.ly", "tinyurl.com", "cutt.ly", "clck.ru", "goo.gl", "t.ly", "is.gd", "rb.gy", "ow.ly",
    "shorturl.at", "tiny.cc", "u.to", "vk.cc", "clc.am", "lnkd.in", "buff.ly", "rebrand.ly",
}
CRYPTO_RE = re.compile(r"\b(?:0x[a-fA-F0-9]{40}|T[1-9A-HJ-NP-Za-km-z]{33}|bc1[a-z0-9]{25,60})\b")
PHONE_RE = re.compile(r"(?<![\d.])(?:\+?\d[\s\-()]{0,2}){10,14}(?![\d.])")
INVISIBLE_RE = re.compile(r"[\u200b-\u200f\u2060-\u2064\ufeff\u202a-\u202e\u2066-\u2069]")
ZALGO_RE = re.compile(r"[\u0300-\u036f\u0483-\u0489]{3,}")
LATIN_RE = re.compile(r"[a-zA-Z]")
CYR_RE = re.compile(r"[а-яА-ЯіїєґёЁІЇЄҐ]")


def _utf16_slice(text: str, offset: int, length: int) -> str:
    raw = text.encode("utf-16-le")
    return raw[offset * 2:(offset + length) * 2].decode("utf-16-le", errors="ignore")


def extract_domain(url: str) -> str:
    u = re.sub(r"^[a-z][a-z0-9+.\-]*://", "", url.strip().lower())
    u = re.split(r"[/?#]", u, maxsplit=1)[0].rsplit("@", 1)[-1].split(":", 1)[0]
    return u.strip(". ")


def message_text(msg: Message) -> str:
    return (msg.text or msg.caption or "")[:4096]


def collect_links(msg: Message) -> tuple[list[str], int]:
    """Усі посилання повідомлення (з entities + за regex) і кількість «прихованих» text_link."""
    text = message_text(msg)
    entities = (msg.entities if msg.text else msg.caption_entities) or []
    links: list[str] = []
    hidden = 0
    for e in entities:
        if e.type == MessageEntity.URL:
            links.append(_utf16_slice(text, e.offset, e.length))
        elif e.type == MessageEntity.TEXT_LINK and e.url:
            links.append(e.url)
            visible = _utf16_slice(text, e.offset, e.length).lower()
            if extract_domain(e.url) not in visible:
                hidden += 1
    links.extend(m.group(0) for m in URL_RE.finditer(text))
    seen, unique = set(), []
    for link in links:
        key = link.lower().rstrip("/.,)")
        if key and key not in seen:
            seen.add(key)
            unique.append(link)
    return unique, hidden


def count_mentions(msg: Message) -> int:
    entities = (msg.entities if msg.text else msg.caption_entities) or []
    return sum(1 for e in entities if e.type in (MessageEntity.MENTION, MessageEntity.TEXT_MENTION))


def count_emoji(text: str) -> int:
    n = 0
    for ch in text:
        cp = ord(ch)
        if 0x1F300 <= cp <= 0x1FAFF or 0x2600 <= cp <= 0x27BF or 0x1F000 <= cp <= 0x1F2FF:
            n += 1
    return n


def domain_allowed(domain: str, whitelist: list[str]) -> bool:
    return any(domain == w or domain.endswith("." + w) for w in whitelist)


def suspicious_name_reason(full_name: str) -> Optional[str]:
    """Евристики для імені акаунта: типові ознаки спам-ботів."""
    name = full_name or ""
    if URL_RE.search(name) or TG_LINK_RE.search(name):
        return "посилання в імені"
    if re.search(r"@\w{4,}", name):
        return "реклама (@згадка) в імені"
    if len(re.findall(r"\d", name)) >= 8:
        return "номер телефону в імені"
    if len(name) > 70:
        return "задовге ім'я"
    if count_emoji(name) >= 6:
        return "забагато емодзі в імені"
    if re.search(r"[\u202a-\u202e\u2066-\u2069]", name):
        return "керівні Unicode-символи в імені"
    return None


# ============================================================
#  БАЛЬНА ОЦІНКА СПАМУ
# ============================================================

# (фраза, вага). Закінчення «*» — слова, що починаються на фразу.
_AD_PHRASES: list[tuple[str, int]] = [
    ("заробіток", 3), ("заработок", 3), ("без вкладень", 3), ("без вложений", 3),
    ("пасивний дохід", 3), ("пассивный доход", 3), ("швидкі гроші", 3), ("быстрые деньги", 3),
    ("легкі гроші", 3), ("легкие деньги", 3), ("казино", 3), ("casino", 3), ("букмекер*", 3),
    ("ставки на спорт", 3), ("airdrop", 3), ("інвестиц*", 3), ("инвестиц*", 3), ("usdt", 3),
    ("binance", 3), ("bitcoin", 3), ("крипт*", 2), ("crypto*", 2), ("порно", 3), ("porn*", 3),
    ("інтим", 3), ("интим", 3), ("знайомства", 3), ("знакомства", 3), ("18+", 2),
    ("гарантований дохід", 3), ("гарантированный доход", 3), ("в 2 рази", 2), ("в 2 раза", 2),
    ("вакансія", 2), ("вакансия", 2), ("підробіток", 2), ("подработка", 2),
    ("віддалена робота", 2), ("удаленная работа", 2), ("набираю", 2), ("шукаю людей", 2),
    ("ищу людей", 2), ("підпишись", 2), ("подпишись", 2), ("підписуйтесь", 2), ("подписывайтесь", 2),
    ("розіграш*", 2), ("розыгрыш*", 2), ("giveaway", 2), ("earn money", 3), ("free money", 3),
    ("click here", 2), ("промокод", 2), ("бонус*", 1), ("bonus*", 1), ("знижк*", 1), ("скидк*", 1),
    ("акція", 1), ("акция", 1), ("халява", 2), ("виграй*", 2), ("выиграй*", 2), ("winner", 2),
    ("в лс", 1), ("в личку", 1), ("в лічку", 1), ("пишіть мені", 1), ("пишите мне", 1),
    ("whatsapp", 1), ("вайбер", 1), ("viber", 1), ("ватсап", 1), ("dm me", 1),
]


def _compile_phrases() -> list[tuple[re.Pattern, re.Pattern, int, str]]:
    out = []
    for phrase, weight in _AD_PHRASES:
        prefix = phrase.endswith("*")
        core = phrase.rstrip("*")
        cyr, lat = text_forms(core)
        tail = "" if prefix else r"(?![^\W_])"
        mk = lambda s: re.compile(r"(?<![^\W_])" + re.escape(s.strip()) + tail)
        out.append((mk(cyr), mk(lat), weight, core))
    return out


_AD_COMPILED = _compile_phrases()


@dataclass
class SpamResult:
    score: float = 0.0
    reasons: list[str] = field(default_factory=list)

    def add(self, points: float, why: str) -> None:
        self.score += points
        self.reasons.append(f"{why} (+{points:g})")

    def summary(self) -> str:
        return f"{self.score:g} балів: " + "; ".join(self.reasons[:5])


def analyze_spam(
    text: str,
    links: list[str],
    mentions: int = 0,
    *,
    hidden_links: int = 0,
    newbie: bool = False,
    forwarded: bool = False,
    max_mentions: int = 5,
    whitelist: Optional[list[str]] = None,
) -> SpamResult:
    """Оцінює повідомлення за багатьма ознаками спаму. Чим більше балів — тим підозріліше."""
    res = SpamResult()
    text = (text or "")[:4096]
    whitelist = whitelist or []

    # --- посилання ---
    bad_links = [l for l in links if not domain_allowed(extract_domain(l), whitelist)]
    invites = [l for l in bad_links if TG_INVITE_RE.search(l)]
    tg_links = [l for l in bad_links if TG_LINK_RE.search(l) and l not in invites]
    shorteners = [l for l in bad_links if extract_domain(l) in SHORTENERS]
    other = [l for l in bad_links if l not in invites and l not in tg_links and l not in shorteners]
    if invites:
        res.add(4, "запрошення в Telegram-групу/канал")
    if tg_links:
        res.add(2, "посилання на Telegram")
    if shorteners:
        res.add(3, "скорочувач посилань")
    if other:
        res.add(min(4, 2 * len(other)), f"зовнішні посилання ×{len(other)}")
    if hidden_links:
        res.add(2, "приховане посилання в тексті")

    # --- ключові фрази реклами ---
    cyr, lat = text_forms(text)
    ad_points, ad_hits = 0, []
    for p_cyr, p_lat, weight, label in _AD_COMPILED:
        if p_cyr.search(cyr) or p_lat.search(lat):
            ad_points += weight
            ad_hits.append(label)
    if ad_points:
        res.add(min(8, ad_points), "рекламні фрази: " + ", ".join(ad_hits[:4]))

    # --- гаманці, телефони ---
    if CRYPTO_RE.search(text):
        res.add(3, "адреса крипто-гаманця")
    if PHONE_RE.search(text):
        res.add(2, "номер телефону")

    # --- форма тексту ---
    emoji = count_emoji(text)
    if emoji > 20:
        res.add(3, f"забагато емодзі ({emoji})")
    elif emoji > 10:
        res.add(2, f"багато емодзі ({emoji})")
    letters = [c for c in text if c.isalpha()]
    if len(letters) > 20 and sum(c.isupper() for c in letters) / len(letters) > 0.7:
        res.add(1, "текст великими літерами")
    mixed = [t for t in _TOKEN_RE.findall(text) if len(t) >= 4 and LATIN_RE.search(t) and CYR_RE.search(t)]
    if mixed:
        res.add(min(3, len(mixed)), "змішані алфавіти в словах (маскування)")
    if INVISIBLE_RE.search(text) or ZALGO_RE.search(text):
        res.add(2, "невидимі/службові Unicode-символи")
    if re.search(r"(.)\1{7,}", text):
        res.add(1, "довгі повтори символів")
    if len(re.findall(r"#\w+", text)) > 5:
        res.add(1, "забагато хештегів")
    if mentions > max_mentions:
        res.add(3, f"масові згадки ({mentions})")
    if forwarded and links:
        res.add(1, "пересилання з посиланням")
    if len(text) > 700 and links:
        res.add(1, "довгий рекламний текст")
    if newbie and res.score > 0:
        res.add(1, "новий учасник")
    return res


# ============================================================
#  ТРЕКЕРИ В ПАМ'ЯТІ (флуд, дублікати, рейди)
# ============================================================


class FloodTracker:
    """Ковзне вікно повідомлень користувача."""

    def __init__(self) -> None:
        self._events: dict[tuple, deque] = defaultdict(deque)

    def hit(self, key: tuple, now: float, window: float, msg_id: int) -> list[int]:
        dq = self._events[key]
        dq.append((now, msg_id))
        while dq and now - dq[0][0] > window:
            dq.popleft()
        return [m for _, m in dq]

    def clear(self, key: tuple) -> None:
        self._events.pop(key, None)

    def purge(self, now: float, max_age: float = 300) -> None:
        for key in [k for k, dq in self._events.items() if not dq or now - dq[-1][0] > max_age]:
            self._events.pop(key, None)


class DuplicateTracker:
    """Повтори одного й того ж тексту: від одного користувача та від різних акаунтів («хвиля»)."""

    def __init__(self) -> None:
        self._user: dict[tuple, deque] = defaultdict(deque)
        self._wave: dict[tuple, dict[int, tuple[float, list[int]]]] = {}

    @staticmethod
    def digest(text: str) -> str:
        cyr, _ = text_forms(text)
        return hashlib.md5(" ".join(_TOKEN_RE.findall(cyr)).encode("utf-8")).hexdigest()[:16]

    def hit_user(self, key: tuple, digest: str, now: float, window: float, msg_id: int) -> list[int]:
        dq = self._user[key]
        dq.append((now, digest, msg_id))
        while dq and now - dq[0][0] > window:
            dq.popleft()
        return [m for _, d, m in dq if d == digest]

    def hit_wave(self, chat_id: int, digest: str, user_id: int, msg_id: int, now: float, window: float) -> dict[int, list[int]]:
        users = self._wave.setdefault((chat_id, digest), {})
        for uid in [u for u, (ts, _) in users.items() if now - ts > window]:
            users.pop(uid)
        ts, ids = users.get(user_id, (now, []))
        users[user_id] = (now, ids + [msg_id])
        return {u: ids for u, (_, ids) in users.items()}

    def purge(self, now: float, max_age: float = 600) -> None:
        for key in [k for k, dq in self._user.items() if not dq or now - dq[-1][0] > max_age]:
            self._user.pop(key, None)
        for key in [k for k, users in self._wave.items() if not users or all(now - ts > max_age for ts, _ in users.values())]:
            self._wave.pop(key, None)


class RaidGuard:
    """Стежить за швидким напливом нових учасників і зберігає режим «рейд»."""

    def __init__(self) -> None:
        self._joins: dict[int, deque] = defaultdict(deque)
        self._until: dict[int, float] = {}

    def record_join(self, chat_id: int, user_id: int, now: float, window: float) -> list[int]:
        dq = self._joins[chat_id]
        dq.append((now, user_id))
        while dq and now - dq[0][0] > window:
            dq.popleft()
        return [u for _, u in dq]

    def active(self, chat_id: int, now: Optional[float] = None) -> bool:
        until = self._until.get(chat_id)
        if until is None:
            return False
        if (now or time.time()) >= until:
            self._until.pop(chat_id, None)
            return False
        return True

    def activate(self, chat_id: int, until: float) -> None:
        self._until[chat_id] = until

    def deactivate(self, chat_id: int) -> None:
        self._until.pop(chat_id, None)
        self._joins.pop(chat_id, None)

    def remaining(self, chat_id: int) -> int:
        return max(0, int(self._until.get(chat_id, 0) - time.time()))


flood = FloodTracker()
dups = DuplicateTracker()
raid = RaidGuard()

_seen_users: dict[int, tuple[str, str]] = {}
_seen_chats: set[int] = set()
_identity_cache: dict[tuple, tuple[float, Optional["Violation"]]] = {}
_rights_warned: dict[int, float] = {}
_last_report: dict[tuple, float] = {}


def remember_user(user: User) -> None:
    """Запам'ятовує @username → id, щоб команди працювали з @нік."""
    sig = (user.username or "", user.full_name)
    if _seen_users.get(user.id) != sig:
        _seen_users[user.id] = sig
        db.user_upsert(user)


def remember_chat(chat) -> None:
    if chat.id not in _seen_chats:
        _seen_chats.add(chat.id)
        db.chat_upsert(chat.id, chat.title or "", str(chat.type))


# ============================================================
#  ПРАВА АДМІНІСТРАТОРІВ
# ============================================================


class AdminCache:
    TTL = 120

    def __init__(self) -> None:
        self._data: dict[int, tuple[float, set[int]]] = {}

    async def ids(self, context: ContextTypes.DEFAULT_TYPE, chat_id: int) -> set[int]:
        item = self._data.get(chat_id)
        if item and item[0] > time.time():
            return item[1]
        try:
            admins = await context.bot.get_chat_administrators(chat_id)
            ids = {a.user.id for a in admins}
        except TelegramError as e:
            log.warning("get_chat_administrators(%s): %s", chat_id, e)
            ids = item[1] if item else set()
        self._data[chat_id] = (time.time() + self.TTL, ids)
        return ids

    def drop(self, chat_id: Optional[int] = None) -> None:
        if chat_id is None:
            self._data.clear()
        else:
            self._data.pop(chat_id, None)


admin_cache = AdminCache()


async def is_admin_id(context: ContextTypes.DEFAULT_TYPE, chat_id: int, user_id: int) -> bool:
    if user_id in OWNER_IDS:
        return True
    return user_id in await admin_cache.ids(context, chat_id)


async def is_exempt(context: ContextTypes.DEFAULT_TYPE, chat_id: int, user_id: int) -> bool:
    """Адміни, власники бота та довірені користувачі не перевіряються фільтрами."""
    return await is_admin_id(context, chat_id, user_id) or db.is_trusted(chat_id, user_id)


# ============================================================
#  ПОВІДОМЛЕННЯ ТА ВИДАЛЕННЯ
# ============================================================


async def delete_msg(bot, chat_id: int, message_id: int) -> bool:
    try:
        await bot.delete_message(chat_id, message_id)
        return True
    except TelegramError:
        return False


async def delete_many(bot, chat_id: int, ids) -> int:
    ids = sorted(set(i for i in ids if i))
    if not ids:
        return 0
    done = 0
    for part in chunked(ids, 20):
        results = await asyncio.gather(*(delete_msg(bot, chat_id, i) for i in part))
        done += sum(results)
        if len(ids) > 20:
            await asyncio.sleep(0.4)
    return done


async def _delete_job(context: ContextTypes.DEFAULT_TYPE) -> None:
    chat_id, message_id = context.job.data
    await delete_msg(context.bot, chat_id, message_id)


def delete_later(context: ContextTypes.DEFAULT_TYPE, chat_id: int, message_id: int, delay: int) -> None:
    if delay and delay > 0 and context.job_queue:
        context.job_queue.run_once(_delete_job, delay, data=(chat_id, message_id), name=f"del:{chat_id}:{message_id}")


async def say(
    context: ContextTypes.DEFAULT_TYPE,
    chat_id: int,
    text: str,
    *,
    ttl: Optional[int] = None,
    markup: Optional[InlineKeyboardMarkup] = None,
    reply_to: Optional[int] = None,
) -> Optional[Message]:
    """Надсилає повідомлення; за потреби видаляє його через ttl секунд. Помилки розмітки не фатальні."""
    kwargs = dict(reply_markup=markup)
    if reply_to:
        kwargs["reply_parameters"] = ReplyParameters(message_id=reply_to, allow_sending_without_reply=True)
    try:
        sent = await context.bot.send_message(chat_id, text, parse_mode=ParseMode.HTML, **kwargs)
    except BadRequest as e:
        if "parse" in str(e).lower():
            try:
                sent = await context.bot.send_message(chat_id, re.sub(r"<[^>]+>", "", text), **kwargs)
            except TelegramError:
                return None
        else:
            log.warning("send_message(%s): %s", chat_id, e)
            return None
    except TelegramError as e:
        log.warning("send_message(%s): %s", chat_id, e)
        return None
    if ttl is None:
        ttl = cfg.get(chat_id, "notify_ttl")
    delete_later(context, chat_id, sent.message_id, ttl)
    return sent


async def reply(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE,
    text: str,
    *,
    markup: Optional[InlineKeyboardMarkup] = None,
    ttl: int = 0,
) -> Optional[Message]:
    """Відповідь на команду. Якщо вихідне повідомлення вже видалене — просто пише в чат."""
    msg = update.effective_message
    try:
        sent = await msg.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=markup)
        delete_later(context, update.effective_chat.id, sent.message_id, ttl)
        return sent
    except TelegramError:
        return await say(context, update.effective_chat.id, text, ttl=ttl, markup=markup)


# ============================================================
#  ДОЗВОЛИ, ЖУРНАЛ, СКАРГИ НА НЕСТАЧУ ПРАВ
# ============================================================

ACTION_LABELS = {
    "ban": "🚫 Бан", "unban": "✅ Розбан", "kick": "👢 Кік", "mute": "🔇 Мут", "unmute": "🔊 Розмут",
    "warn": "⚠️ Попередження", "unwarn": "↩️ Зняття попередження", "raid": "🚨 Рейд",
    "captcha_fail": "🔐 Капча не пройдена", "gban": "🌐 Глобальний бан", "lockdown": "🔒 Lockdown",
}


def no_perms() -> ChatPermissions:
    try:
        return ChatPermissions.no_permissions()
    except AttributeError:
        return ChatPermissions(can_send_messages=False)


def all_perms() -> ChatPermissions:
    try:
        return ChatPermissions.all_permissions()
    except AttributeError:
        return ChatPermissions(
            can_send_messages=True, can_send_polls=True, can_send_other_messages=True,
            can_add_web_page_previews=True, can_invite_users=True,
        )


async def default_perms(context: ContextTypes.DEFAULT_TYPE, chat_id: int) -> ChatPermissions:
    """Стандартні дозволи групи — до них повертаємо користувача після розмуту."""
    try:
        chat = await context.bot.get_chat(chat_id)
        return chat.permissions or all_perms()
    except TelegramError:
        return all_perms()


async def log_action(
    context: ContextTypes.DEFAULT_TYPE,
    chat_id: int,
    action: str,
    user_id: int,
    user_name: str,
    admin_name: str,
    reason: str,
) -> None:
    db.log_add(chat_id, action, user_id, user_name, admin_name, reason)
    db.bump(chat_id, action)
    log_chat = cfg.get(chat_id, "log_chat")
    if log_chat:
        text = (
            f"{ACTION_LABELS.get(action, esc(action))}\n"
            f"👤 {mention(user_id, user_name)} (<code>{user_id}</code>)\n"
            f"🛠 {esc(admin_name)}\n"
            f"💬 {esc(short(reason, 300))}\n"
            f"🏷 чат <code>{chat_id}</code>"
        )
        await say(context, int(log_chat), text, ttl=0)


async def report_rights_problem(context: ContextTypes.DEFAULT_TYPE, chat_id: int, err: Exception) -> None:
    """Раз на годину просить адмінів видати боту потрібні права."""
    low = str(err).lower()
    if not any(s in low for s in ("rights", "administrator", "forbidden", "permission", "not enough")):
        log.warning("Telegram error in %s: %s", chat_id, err)
        return
    if time.time() - _rights_warned.get(chat_id, 0) < 3600:
        return
    _rights_warned[chat_id] = time.time()
    await say(
        context, chat_id,
        "⚠️ <b>Мені бракує прав.</b> Зробіть мене адміністратором із правами: "
        "<i>видаляти повідомлення</i> та <i>блокувати користувачів</i>. Перевірка: /check",
        ttl=0,
    )


# ============================================================
#  ДІЇ МОДЕРАЦІЇ
# ============================================================


async def can_punish(context: ContextTypes.DEFAULT_TYPE, chat_id: int, user_id: int) -> bool:
    if user_id == context.bot.id or user_id in OWNER_IDS:
        return False
    return not await is_admin_id(context, chat_id, user_id)


def _until(seconds: int) -> Optional[int]:
    """Telegram вважає обмеження <30 с або >366 діб безстроковим — тому тримаємо межі."""
    if not seconds or seconds <= 0:
        return None
    return now_ts() + min(max(int(seconds), 60), 366 * 86400)


async def do_ban(
    context: ContextTypes.DEFAULT_TYPE, chat_id: int, user_id: int, name: str, reason: str,
    admin: str = "Автомодерація", seconds: int = 0, revoke: bool = False,
) -> bool:
    try:
        await context.bot.ban_chat_member(chat_id, user_id, until_date=_until(seconds), revoke_messages=revoke)
    except TelegramError as e:
        await report_rights_problem(context, chat_id, e)
        return False
    until = now_ts() + seconds if seconds else 0
    db.ban_add(chat_id, user_id, name, reason, until)
    db.warn_clear(chat_id, user_id)
    await log_action(context, chat_id, "ban", user_id, name, admin, reason)
    return True


async def do_unban(context: ContextTypes.DEFAULT_TYPE, chat_id: int, user_id: int, name: str, admin: str) -> bool:
    try:
        await context.bot.unban_chat_member(chat_id, user_id, only_if_banned=True)
    except TelegramError as e:
        await report_rights_problem(context, chat_id, e)
        return False
    db.ban_remove(chat_id, user_id)
    await log_action(context, chat_id, "unban", user_id, name, admin, "розбан")
    return True


async def do_kick(
    context: ContextTypes.DEFAULT_TYPE, chat_id: int, user_id: int, name: str, reason: str, admin: str = "Автомодерація",
) -> bool:
    """Кік = бан + негайний розбан: людина може повернутись за посиланням."""
    try:
        await context.bot.ban_chat_member(chat_id, user_id)
        await context.bot.unban_chat_member(chat_id, user_id, only_if_banned=True)
    except TelegramError as e:
        await report_rights_problem(context, chat_id, e)
        return False
    await log_action(context, chat_id, "kick", user_id, name, admin, reason)
    return True


async def do_mute(
    context: ContextTypes.DEFAULT_TYPE, chat_id: int, user_id: int, name: str, seconds: int, reason: str,
    admin: str = "Автомодерація",
) -> bool:
    try:
        await context.bot.restrict_chat_member(chat_id, user_id, permissions=no_perms(), until_date=_until(seconds))
    except TelegramError as e:
        await report_rights_problem(context, chat_id, e)
        return False
    await log_action(context, chat_id, "mute", user_id, name, admin, f"{fmt_duration(seconds)}: {reason}")
    return True


async def do_unmute(context: ContextTypes.DEFAULT_TYPE, chat_id: int, user_id: int, name: str, admin: str) -> bool:
    try:
        await context.bot.restrict_chat_member(chat_id, user_id, permissions=await default_perms(context, chat_id))
    except TelegramError as e:
        await report_rights_problem(context, chat_id, e)
        return False
    await log_action(context, chat_id, "unmute", user_id, name, admin, "розмут")
    return True


async def issue_warn(
    context: ContextTypes.DEFAULT_TYPE, chat_id: int, user_id: int, name: str, reason: str,
    admin: str = "Автомодерація", admin_id: int = 0,
) -> tuple[int, int, Optional[str]]:
    """
    Видає попередження. Повертає (поточна кількість, максимум, застосована ескалація).
    Ескалація — 'ban' | 'mute' | 'kick' або None.
    """
    db.warn_add(chat_id, user_id, admin_id, reason)
    count = db.warn_count(chat_id, user_id, cfg.get(chat_id, "warn_expire_days"))
    limit = cfg.get(chat_id, "max_warns")
    await log_action(context, chat_id, "warn", user_id, name, admin, f"{count}/{limit}: {reason}")
    if count < limit:
        return count, limit, None
    action = cfg.get(chat_id, "warn_action")
    why = f"{limit} попереджень (остання: {reason})"
    ok = False
    if action == "mute":
        ok = await do_mute(context, chat_id, user_id, name, cfg.get(chat_id, "warn_mute_minutes") * 60, why)
    elif action == "kick":
        ok = await do_kick(context, chat_id, user_id, name, why)
    else:
        action = "ban"
        ok = await do_ban(context, chat_id, user_id, name, why)
    if ok:
        db.warn_clear(chat_id, user_id)
        return count, limit, action
    return count, limit, None


# ============================================================
#  ПОРУШЕННЯ ТА ПЕРЕВІРКА ПОВІДОМЛЕНЬ
# ============================================================


@dataclass
class Violation:
    kind: str                    # bad_word | link | spam | flood | duplicate | wave | lock | nick | name | gban ...
    reason: str
    action: str = "warn"         # delete | warn | mute | ban | kick
    seconds: int = 0             # для mute
    delete_ids: list[int] = field(default_factory=list)   # додаткові повідомлення для видалення
    revoke: bool = False         # при бані видалити всі повідомлення користувача
    silent: bool = False         # не писати в чат


_STRONG_NAME_REASONS = ("посилання в імені", "реклама (@згадка) в імені")


def reset_caches(chat_id: int) -> None:
    """Скидає кеші фільтрів після зміни слів/ніків/налаштувань."""
    matchers.invalidate(chat_id)
    for key in [k for k in _identity_cache if k[0] == chat_id]:
        _identity_cache.pop(key, None)


def _compute_identity(chat_id: int, user: User) -> Optional[Violation]:
    if cfg.get(chat_id, "gban_enabled"):
        g = db.gban_get(user.id)
        if g:
            return Violation("gban", f"у глобальному бані: {g['reason'] or '—'}", action="ban", revoke=True)
    if cfg.get(chat_id, "nick_filter"):
        hit = matchers.nicks(chat_id).find(user.username)
        if hit:
            return Violation("nick", f"заборонений нік @{user.username} (правило «{hit}»)",
                             action=cfg.get(chat_id, "nick_action"))
    if cfg.get(chat_id, "name_filter"):
        reason = suspicious_name_reason(user.full_name)
        if reason in _STRONG_NAME_REASONS:
            return Violation("name", reason, action="ban", revoke=True)
    if cfg.get(chat_id, "bad_words_filter"):
        hit = matchers.words(chat_id).find(user.full_name)
        if hit:
            return Violation("name", f"заборонене слово в імені («{hit}»)", action="warn")
    return None


def identity_violation(chat_id: int, user: User) -> Optional[Violation]:
    """Перевірка нікнейма, імені та глобального бану (результат кешується на 10 хвилин)."""
    key = (chat_id, user.id, user.username or "", user.full_name)
    cached = _identity_cache.get(key)
    if cached and cached[0] > time.time():
        return cached[1]
    result = _compute_identity(chat_id, user)
    _identity_cache[key] = (time.time() + 600, result)
    return result


def message_lock_types(msg: Message, has_links: bool, forwarded: bool) -> set[str]:
    kinds: set[str] = set()
    if msg.photo or msg.video or msg.video_note or msg.animation:
        kinds.add("media")
    if msg.sticker:
        kinds.add("stickers")
    if msg.voice or msg.audio:
        kinds.add("voice")
    if msg.document and not msg.animation:
        kinds.add("documents")
    if msg.poll:
        kinds.add("polls")
    if msg.contact:
        kinds.add("contacts")
    if msg.location or msg.venue:
        kinds.add("location")
    if forwarded:
        kinds.add("forwards")
    if has_links:
        kinds.add("links")
    return kinds


def is_newbie(chat_id: int, activity) -> bool:
    if not activity or not activity["joined"]:
        return False
    return now_ts() - activity["first_seen"] < cfg.get(chat_id, "newbie_minutes") * 60


async def evaluate_message(
    context: ContextTypes.DEFAULT_TYPE, msg: Message, chat, user: User, activity, is_edit: bool,
) -> Optional[Violation]:
    """Повертає перше знайдене порушення або None. Порядок: від дешевих перевірок до складних."""
    chat_id = chat.id
    s = lambda key: cfg.get(chat_id, key)
    text = message_text(msg)
    links, hidden = collect_links(msg)
    forwarded = bool(getattr(msg, "forward_origin", None) or getattr(msg, "forward_date", None))
    newbie = is_newbie(chat_id, activity)
    now = time.time()

    # 1. Нікнейм / ім'я / глобальний бан
    v = identity_violation(chat_id, user)
    if v:
        return v

    # 2. Заблоковані типи контенту
    locked = set(s("locks"))
    if locked:
        hit = message_lock_types(msg, bool(links), forwarded) & locked
        if hit:
            return Violation("lock", "заблоковано: " + ", ".join(LOCK_TYPES[k] for k in sorted(hit)), action="delete")
    if s("forward_filter") and forwarded and newbie:
        return Violation("forward", "пересилання від новачка", action="delete")

    # 3. Заборонені слова
    if s("bad_words_filter") and text:
        word = matchers.words(chat_id).find(text)
        if word:
            return Violation("bad_word", f"заборонене слово «{word}»", action="warn")

    # 4. Політика посилань
    whitelist = matchers.domains(chat_id)
    policy = s("link_policy")
    if links and policy:
        bad = [l for l in links if not domain_allowed(extract_domain(l), whitelist)]
        if bad and (policy == 2 or newbie):
            if newbie and any(TG_INVITE_RE.search(l) for l in bad):
                return Violation("link", "реклама Telegram-групи від новачка", action="ban", revoke=True)
            return Violation("link", f"посилання заборонені ({short(bad[0], 40)})", action="warn")

    # 5. Антиспам за балами
    mentions = count_mentions(msg)
    if s("antispam") and (text or links):
        res = analyze_spam(
            text, links, mentions, hidden_links=hidden, newbie=newbie, forwarded=forwarded,
            max_mentions=s("max_mentions"), whitelist=whitelist,
        )
        if res.score >= s("spam_threshold"):
            heavy = res.score >= s("spam_ban_score")
            if newbie or heavy:
                return Violation("spam", res.summary(), action="ban", revoke=True)
            return Violation("spam", res.summary(), action="warn")
    if mentions > s("max_mentions") * 2:
        return Violation("mentions", f"масові згадки ({mentions})", action="delete")

    if is_edit:            # редагування не рахуємо для флуду та дублікатів
        return None

    # 6. Дублікати та «хвилі» однакового спаму
    if len(text) >= 8 and (s("duplicate_filter") or s("spam_wave")):
        digest = dups.digest(text)
        if s("duplicate_filter"):
            same = dups.hit_user((chat_id, user.id), digest, now, 90, msg.message_id)
            if len(same) >= s("dup_limit"):
                return Violation("duplicate", f"повтор повідомлення ×{len(same)}", action="warn", delete_ids=same)
        if s("spam_wave") and len(text) >= 40:
            wave = dups.hit_wave(chat_id, digest, user.id, msg.message_id, now, 180)
            if len(wave) >= 3:
                all_ids = [i for ids in wave.values() for i in ids]
                return Violation(
                    "wave", f"однакове повідомлення від {len(wave)} акаунтів", action="ban" if newbie else "delete",
                    delete_ids=all_ids, revoke=newbie,
                )

    # 7. Флуд
    if s("antiflood"):
        ids = flood.hit((chat_id, user.id), now, s("flood_seconds"), msg.message_id)
        if len(ids) > s("flood_limit"):
            flood.clear((chat_id, user.id))
            return Violation(
                "flood", f"флуд ({len(ids)} повідомлень за {s('flood_seconds')} с)",
                action="mute", seconds=s("mute_minutes") * 60, delete_ids=ids,
            )
    return None


async def apply_violation(
    context: ContextTypes.DEFAULT_TYPE, chat, user: User, msg: Optional[Message], v: Violation,
) -> None:
    """Видаляє повідомлення та застосовує покарання; повідомляє чат (якщо ввімкнено сповіщення)."""
    chat_id = chat.id
    ids = set(v.delete_ids)
    if msg is not None:
        ids.add(msg.message_id)
    await delete_many(context.bot, chat_id, ids)
    db.bump(chat_id, f"v_{v.kind}")

    who, name, reason = user_link(user), user.full_name, v.reason
    note: Optional[str] = None
    if v.action == "delete":
        if msg is not None or v.delete_ids:
            note = f"🧹 Повідомлення від {who} видалено: {esc(reason)}"
    elif v.action == "warn":
        count, limit, escalated = await issue_warn(context, chat_id, user.id, name, reason)
        if escalated == "ban":
            note = f"🚫 {who} забанений: {limit} попереджень.\n💬 {esc(reason)}"
        elif escalated == "mute":
            note = f"🔇 {who} у муті на {fmt_duration(cfg.get(chat_id, 'warn_mute_minutes') * 60)}: {limit} попереджень."
        elif escalated == "kick":
            note = f"👢 {who} вилучений з групи: {limit} попереджень."
        else:
            note = f"⚠️ {who}, попередження <b>{count}/{limit}</b>: {esc(reason)}"
    elif v.action == "mute":
        if await do_mute(context, chat_id, user.id, name, v.seconds, reason):
            note = f"🔇 {who} у муті {for_duration(v.seconds)}: {esc(reason)}"
    elif v.action == "ban":
        if await do_ban(context, chat_id, user.id, name, reason, revoke=v.revoke):
            note = f"🚫 {who} забанений: {esc(reason)}"
    elif v.action == "kick":
        if await do_kick(context, chat_id, user.id, name, reason):
            note = f"👢 {who} вилучений: {esc(reason)}"
    if note and not v.silent and cfg.get(chat_id, "notify"):
        await say(context, chat_id, note)


# ============================================================
#  ГОЛОВНИЙ ОБРОБНИК ПОВІДОМЛЕНЬ
# ============================================================


async def handle_sender_chat(context: ContextTypes.DEFAULT_TYPE, msg: Message, chat) -> None:
    """Повідомлення від імені каналу/чату (анонімні адміни та пов'язаний канал ігноруються)."""
    sender = msg.sender_chat
    if sender.id == chat.id or getattr(msg, "is_automatic_forward", False):
        return
    if not cfg.get(chat.id, "block_channels"):
        return
    await delete_msg(context.bot, chat.id, msg.message_id)
    db.bump(chat.id, "v_channel")
    try:
        await context.bot.ban_chat_sender_chat(chat.id, sender.id)
    except TelegramError:
        pass


async def on_group_message(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    msg, chat, user = update.effective_message, update.effective_chat, update.effective_user
    if msg is None or chat is None or chat.type not in GROUP_TYPES:
        return
    is_edit = update.edited_message is not None
    remember_chat(chat)
    if msg.sender_chat:
        return await handle_sender_chat(context, msg, chat)
    if user is None or user.is_bot or getattr(msg, "is_automatic_forward", False):
        return
    remember_user(user)

    activity = db.touch_activity(chat.id, user.id, message=not is_edit)
    if await is_exempt(context, chat.id, user.id):
        return
    if db.captcha_get(chat.id, user.id):          # не пройшов капчу, але встиг щось написати
        await delete_msg(context.bot, chat.id, msg.message_id)
        return
    violation = await evaluate_message(context, msg, chat, user, activity, is_edit)
    if violation:
        await apply_violation(context, chat, user, msg, violation)
    else:
        db.bump(chat.id, "messages")


# ============================================================
#  НОВІ УЧАСНИКИ: КАПЧА, АНТИРЕЙД, ВІТАННЯ
# ============================================================


def cancel_jobs(context: ContextTypes.DEFAULT_TYPE, name: str) -> None:
    if context.job_queue:
        for job in context.job_queue.get_jobs_by_name(name):
            job.schedule_removal()


async def send_welcome(context: ContextTypes.DEFAULT_TYPE, chat, user_id: int, name: str) -> None:
    if not cfg.get(chat.id, "welcome"):
        return
    tpl = cfg.get(chat.id, "welcome_text") or DEFAULTS["welcome_text"]
    text = (
        tpl.replace("{mention}", mention(user_id, name)).replace("{name}", esc(name))
        .replace("{chat}", esc(chat.title or "")).replace("{id}", str(user_id))
    )
    await say(context, chat.id, text, ttl=cfg.get(chat.id, "welcome_ttl"))


def _schedule_captcha_job(context: ContextTypes.DEFAULT_TYPE, chat_id: int, user_id: int, delay: float) -> None:
    context.job_queue.run_once(
        captcha_timeout_job, max(delay, 5), data={"chat_id": chat_id, "user_id": user_id}, name=f"cap:{chat_id}:{user_id}",
    )


async def start_captcha(context: ContextTypes.DEFAULT_TYPE, chat, user_id: int, name: str) -> None:
    """Мутить новачка та просить розв'язати просту арифметичну задачу кнопками."""
    chat_id = chat.id
    if db.captcha_get(chat_id, user_id):
        return
    try:
        await context.bot.restrict_chat_member(chat_id, user_id, permissions=no_perms())
    except TelegramError as e:
        await report_rights_problem(context, chat_id, e)
        return
    timeout = cfg.get(chat_id, "captcha_timeout")
    a, b = random.randint(2, 9), random.randint(2, 9)
    options = {a + b}
    while len(options) < 4:
        options.add(random.randint(3, 18))
    buttons = [InlineKeyboardButton(str(o), callback_data=f"cap:{user_id}:{o}") for o in random.sample(sorted(options), 4)]
    sent = await say(
        context, chat_id,
        f"🔐 {mention(user_id, name)}, підтвердь, що ти людина: скільки буде <b>{a} + {b}</b>?\n"
        f"Є {timeout} с — інакше тебе буде видалено з групи.",
        ttl=0, markup=InlineKeyboardMarkup([buttons]),
    )
    if sent is None:
        return
    db.captcha_add(chat_id, user_id, a + b, sent.message_id, now_ts() + timeout)
    _schedule_captcha_job(context, chat_id, user_id, timeout)


async def captcha_timeout_job(context: ContextTypes.DEFAULT_TYPE) -> None:
    chat_id, user_id = context.job.data["chat_id"], context.job.data["user_id"]
    row = db.captcha_get(chat_id, user_id)
    if not row:
        return
    db.captcha_remove(chat_id, user_id)
    await delete_msg(context.bot, chat_id, row["msg_id"])
    info = db.user_by_id(user_id)
    name = info["full_name"] if info else str(user_id)
    if await do_kick(context, chat_id, user_id, name, "не пройшов капчу вчасно"):
        await log_action(context, chat_id, "captcha_fail", user_id, name, "Автомодерація", "час вичерпано")


async def cb_captcha(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    try:
        _, uid_s, val_s = query.data.split(":")
        target, value = int(uid_s), int(val_s)
    except ValueError:
        return await query.answer()
    chat = query.message.chat
    if query.from_user.id != target:
        return await query.answer("Ця кнопка не для тебе 🙂", show_alert=True)
    row = db.captcha_get(chat.id, target)
    if not row:
        return await query.answer("Капча вже неактуальна.", show_alert=True)

    if value == row["answer"]:
        db.captcha_remove(chat.id, target)
        cancel_jobs(context, f"cap:{chat.id}:{target}")
        try:
            await context.bot.restrict_chat_member(chat.id, target, permissions=await default_perms(context, chat.id))
        except TelegramError as e:
            await report_rights_problem(context, chat.id, e)
        await query.answer("✅ Готово, ласкаво просимо!")
        await delete_msg(context.bot, chat.id, row["msg_id"])
        db.bump(chat.id, "captcha_ok")
        await send_welcome(context, chat, target, query.from_user.full_name)
        return

    attempts = db.captcha_attempt(chat.id, target)
    if attempts >= 2:
        db.captcha_remove(chat.id, target)
        cancel_jobs(context, f"cap:{chat.id}:{target}")
        await query.answer("❌ Забагато помилок.", show_alert=True)
        await delete_msg(context.bot, chat.id, row["msg_id"])
        if await do_kick(context, chat.id, target, query.from_user.full_name, "помилився в капчі"):
            await log_action(context, chat.id, "captcha_fail", target, query.from_user.full_name, "Автомодерація", "помилки")
    else:
        await query.answer("❌ Неправильно, спробуй ще раз.", show_alert=True)


async def restore_captchas(application: Application) -> None:
    """Після перезапуску відновлює таймери капчі, що не завершились."""
    for row in db.captcha_all():
        application.job_queue.run_once(
            captcha_timeout_job, max(row["deadline"] - now_ts(), 5),
            data={"chat_id": row["chat_id"], "user_id": row["user_id"]}, name=f"cap:{row['chat_id']}:{row['user_id']}",
        )


# ----- антирейд -----

async def _raid_end_job(context: ContextTypes.DEFAULT_TYPE) -> None:
    chat_id = context.job.data
    raid.deactivate(chat_id)
    await say(context, chat_id, "✅ Режим захисту від рейду завершено.", ttl=60)


async def activate_raid(context: ContextTypes.DEFAULT_TYPE, chat, recent_users=(), manual: bool = False) -> None:
    minutes = cfg.get(chat.id, "raid_minutes")
    raid.activate(chat.id, time.time() + minutes * 60)
    cancel_jobs(context, f"raid:{chat.id}")
    context.job_queue.run_once(_raid_end_job, minutes * 60, data=chat.id, name=f"raid:{chat.id}")
    await log_action(context, chat.id, "raid", 0, "—", "Автомодерація",
                     "увімкнено вручну" if manual else f"{len(recent_users)} вступів за короткий час")
    await say(
        context, chat.id,
        f"🚨 <b>Режим захисту від рейду</b> на {minutes} хв: усі нові учасники проходять капчу.\n"
        "Вимкнути: <code>/raid off</code>", ttl=120,
    )
    for uid in recent_users:
        info = db.user_by_id(uid)
        await start_captcha(context, chat, uid, info["full_name"] if info else str(uid))


async def track_raid(context: ContextTypes.DEFAULT_TYPE, chat, user_id: int) -> bool:
    """True, якщо активний режим рейду (нового учасника треба перевірити капчею)."""
    if raid.active(chat.id):
        return True
    if not cfg.get(chat.id, "antiraid"):
        return False
    recent = raid.record_join(chat.id, user_id, time.time(), cfg.get(chat.id, "raid_seconds"))
    if len(recent) >= cfg.get(chat.id, "raid_joins"):
        await activate_raid(context, chat, recent)
        return True
    return False


# ----- обробка вступу -----

async def process_join(context: ContextTypes.DEFAULT_TYPE, chat, member: User, adder: Optional[User]) -> None:
    chat_id = chat.id
    if member.id == context.bot.id:
        return
    remember_user(member)
    db.touch_activity(chat_id, member.id, joined=True)
    db.bump(chat_id, "joins")
    if await is_exempt(context, chat_id, member.id):
        return

    if member.is_bot:
        added_by_admin = adder is not None and adder.id != member.id and await is_admin_id(context, chat_id, adder.id)
        if cfg.get(chat_id, "kick_bots") and not added_by_admin:
            if await do_ban(context, chat_id, member.id, member.full_name, "бот доданий не адміністратором"):
                await say(context, chat_id, f"🤖 Бота {user_link(member)} видалено: додавати ботів можуть лише адміни.")
        return

    violation = identity_violation(chat_id, member)
    if violation:
        await apply_violation(context, chat, member, None, violation)
        return

    under_raid = await track_raid(context, chat, member.id)
    if cfg.get(chat_id, "captcha") or under_raid:
        await start_captcha(context, chat, member.id, member.full_name)
    else:
        await send_welcome(context, chat, member.id, member.full_name)


async def on_new_members(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    msg, chat = update.effective_message, update.effective_chat
    if msg is None or chat is None or chat.type not in GROUP_TYPES:
        return
    remember_chat(chat)
    for member in msg.new_chat_members or []:
        await process_join(context, chat, member, msg.from_user)
    if cfg.get(chat.id, "delete_service"):
        await delete_msg(context.bot, chat.id, msg.message_id)


async def on_left_member(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    msg, chat = update.effective_message, update.effective_chat
    if msg and chat and chat.type in GROUP_TYPES and cfg.get(chat.id, "delete_service"):
        await delete_msg(context.bot, chat.id, msg.message_id)


async def on_join_request(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Заявки на вступ: відхиляємо gban та заборонені ніки; решту — за налаштуванням auto_approve."""
    req = update.chat_join_request
    chat, user = req.chat, req.from_user
    remember_chat(chat)
    remember_user(user)
    v = identity_violation(chat.id, user)
    try:
        if v:
            await context.bot.decline_chat_join_request(chat.id, user.id)
            if v.action == "ban":
                await do_ban(context, chat.id, user.id, user.full_name, f"заявку відхилено: {v.reason}")
            else:
                await log_action(context, chat.id, "kick", user.id, user.full_name, "Автомодерація",
                                 f"заявку відхилено: {v.reason}")
        elif cfg.get(chat.id, "auto_approve"):
            await context.bot.approve_chat_join_request(chat.id, user.id)
    except TelegramError as e:
        log.warning("join request %s: %s", chat.id, e)


async def on_my_chat_member(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    ev = update.my_chat_member
    chat = ev.chat
    if chat.type not in GROUP_TYPES:
        return
    new, old = ev.new_chat_member.status, ev.old_chat_member.status
    if new in ("left", "kicked"):
        db.chat_remove(chat.id)
        _seen_chats.discard(chat.id)
        return
    remember_chat(chat)
    admin_cache.drop(chat.id)
    if new == "administrator" and old != "administrator":
        await say(context, chat.id,
                  "✅ Дякую за права! Захист увімкнено. Налаштування: /settings, довідка: /help, перевірка прав: /check",
                  ttl=0)
    elif new == "member" and old in ("left", "kicked"):
        await say(context, chat.id,
                  "👋 Привіт! Щоб я міг працювати, зробіть мене <b>адміністратором</b> з правами: "
                  "видаляти повідомлення та блокувати користувачів.", ttl=0)


# ============================================================
#  ФОНОВІ ЗАДАЧІ
# ============================================================

async def maintenance_job(context: ContextTypes.DEFAULT_TYPE) -> None:
    now = time.time()
    flood.purge(now)
    dups.purge(now)
    for key in [k for k, (exp, _) in _identity_cache.items() if exp < now]:
        _identity_cache.pop(key, None)
    for key in [k for k, ts in _last_report.items() if now - ts > 3600]:
        _last_report.pop(key, None)
    for row in db.ban_expired():          # тимчасові бани Telegram знімає сам — чистимо лише записи
        db.ban_remove(row["chat_id"], row["user_id"])


async def daily_cleanup_job(context: ContextTypes.DEFAULT_TYPE) -> None:
    db.cleanup()
    log.info("Щоденне очищення бази виконано")


# ============================================================
#  ДОПОМІЖНЕ ДЛЯ КОМАНД
# ============================================================


def group_admin(func: Callable):
    """Команда лише для адмінів у групі (анонімні адміни також допускаються)."""

    @functools.wraps(func)
    async def wrapper(update: Update, context: ContextTypes.DEFAULT_TYPE):
        chat, user, msg = update.effective_chat, update.effective_user, update.effective_message
        if chat is None or msg is None:
            return
        if chat.type not in GROUP_TYPES:
            return await reply(update, context, "Ця команда працює лише в групі.")
        anonymous = msg.sender_chat is not None and msg.sender_chat.id == chat.id
        if not anonymous and not (user and await is_admin_id(context, chat.id, user.id)):
            return await reply(update, context, "⛔ Тільки адміністратори.", ttl=15)
        remember_chat(chat)
        if user:
            remember_user(user)
        return await func(update, context)

    return wrapper


def owner_only(func: Callable):
    @functools.wraps(func)
    async def wrapper(update: Update, context: ContextTypes.DEFAULT_TYPE):
        user = update.effective_user
        if user is None or user.id not in OWNER_IDS:
            return await reply(update, context, "⛔ Команда лише для власника бота (змінна OWNER_IDS).", ttl=15)
        return await func(update, context)

    return wrapper


def admin_name(update: Update) -> str:
    user = update.effective_user
    return user.full_name if user else "Адмін"


async def resolve_target(update: Update, args: list[str]) -> tuple[Optional[int], str, list[str]]:
    """Ціль команди: відповідь на повідомлення, @нік, ID або text_mention. Повертає (id, ім'я, решта аргументів)."""
    msg = update.effective_message
    rep = msg.reply_to_message
    if rep and rep.from_user:
        return rep.from_user.id, rep.from_user.full_name, list(args)
    for e in msg.entities or []:
        if e.type == MessageEntity.TEXT_MENTION and e.user:
            rest = [a for a in args if a != _utf16_slice(msg.text or "", e.offset, e.length)]
            return e.user.id, e.user.full_name, rest
    if args:
        first = args[0]
        if first.isdigit():
            row = db.user_by_id(int(first))
            return int(first), (row["full_name"] if row else f"ID {first}"), list(args[1:])
        if first.startswith("@"):
            row = db.user_by_username(first)
            if row:
                return row["user_id"], row["full_name"], list(args[1:])
    return None, "", list(args)


async def guard_target(update: Update, context: ContextTypes.DEFAULT_TYPE, user_id: int) -> bool:
    if not await can_punish(context, update.effective_chat.id, user_id):
        await reply(update, context, "🙅 Цього користувача не можна покарати (адмін, власник бота чи сам бот).", ttl=15)
        return False
    return True


TARGET_HINT = (
    "Вкажіть ціль: відповідь на повідомлення, <code>@нік</code> (якщо бот його бачив) або числовий ID."
)

# ============================================================
#  ЗАГАЛЬНІ КОМАНДИ
# ============================================================


async def cmd_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await reply(
        update, context,
        "🛡️ <b>Grudff Moderator</b>\n\n"
        "Допомагаю адмінам захищати групу від спаму, реклами, флуду, рейдів та небезпечних акаунтів.\n\n"
        "<b>Що вмію:</b>\n"
        "• фільтр слів і нікнеймів (з захистом від обходу літерами)\n"
        "• антиспам за балами, антифлуд, дублікати, «хвилі» спаму\n"
        "• капча для новачків, антирейд, блок сторонніх ботів\n"
        "• попередження → мут/бан, довірені користувачі, глобальний бан\n"
        "• блокування типів контенту, lockdown, журнал дій, скарги\n\n"
        "Додайте мене в групу адміністратором і відкрийте /settings. Усі команди: /help",
    )


async def cmd_help(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    chat, user = update.effective_chat, update.effective_user
    is_adm = chat.type in GROUP_TYPES and user and await is_admin_id(context, chat.id, user.id)
    text = (
        "📖 <b>Довідка</b>\n\n<b>Для всіх:</b>\n"
        "/rules — правила групи\n/mywarns — мої попередження\n/report — поскаржитись (відповідь на повідомлення)\n"
        "/id — показати ID\n"
    )
    if is_adm:
        text += (
            "\n<b>⚙️ Налаштування</b>\n/settings — панель кнопками\n/set <code>ключ значення</code> — число/текст\n"
            "/setrules, /setwelcome — тексти\n/setlog <code>ID|here|off</code> — чат для журналу\n/reload — скинути кеш\n"
            "\n<b>🛡 Модерація</b> (відповідь, @нік або ID)\n"
            "/warn [причина] · /unwarn · /warns · /resetwarns\n"
            "/mute [30m|2h|1d|perm] [причина] · /unmute\n"
            "/ban [тривалість] [причина] · /unban · /kick\n"
            "/banned — список банів · /trust · /untrust · /trusted\n"
            "\n<b>🔤 Фільтри</b>\n"
            "/addword · /removeword · /listwords — слова (<code>слово*</code>, <code>*слово</code>, <code>*слово*</code>)\n"
            "/addnick · /removenick · /listnicks — ніки (префікс або маска <code>*_bot</code>)\n"
            "/addwhite · /removewhite · /listwhite — дозволені домени\n"
            "/lock · /unlock · /locks — типи контенту\n"
            "\n<b>🚨 Захист</b>\n/lockdown [час] · /unlockdown — тиша в чаті\n/raid on|off|status — режим рейду\n"
            "\n<b>🧹 Очищення</b>\n/del — видалити повідомлення (відповідь)\n/purge — видалити від відповіді до кінця\n"
            "\n<b>📊 Інше</b>\n/modlog [N] · /stats · /check (права бота) · /id\n"
        )
    if user and user.id in OWNER_IDS:
        text += "\n<b>🌐 Власник бота</b>\n/gban · /ungban · /gbanlist — глобальний бан у всіх групах\n"
    await reply(update, context, text)


async def cmd_id(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    msg, chat, user = update.effective_message, update.effective_chat, update.effective_user
    lines = [f"🆔 Чат: <code>{chat.id}</code>"]
    if user:
        lines.append(f"👤 Ти: <code>{user.id}</code>")
    if msg.reply_to_message and msg.reply_to_message.from_user:
        lines.append(f"↩️ Користувач із відповіді: <code>{msg.reply_to_message.from_user.id}</code>")
    await reply(update, context, "\n".join(lines))


async def cmd_rules(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    chat = update.effective_chat
    text = (cfg.get(chat.id, "rules_text") or DEFAULT_RULES) if chat.type in GROUP_TYPES else DEFAULT_RULES
    await reply(update, context, text)


async def cmd_mystats(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    chat, user = update.effective_chat, update.effective_user
    if chat.type not in GROUP_TYPES:
        return await reply(update, context, "Команда працює в групі.")
    count = db.warn_count(chat.id, user.id, cfg.get(chat.id, "warn_expire_days"))
    await reply(update, context, f"📊 {user_link(user)}: попереджень <b>{count}</b>/{cfg.get(chat.id, 'max_warns')}")


def _command_body(update: Update) -> str:
    """Текст після команди із збереженням HTML-форматування (жирний, посилання...)."""
    raw = update.effective_message.text_html or ""
    parts = raw.split(None, 1)
    return parts[1].strip() if len(parts) > 1 else ""


@group_admin
async def cmd_setrules(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    body = _command_body(update)
    if not body:
        return await reply(update, context, "Використання: <code>/setrules текст правил</code> (підтримується форматування). "
                                            "Скинути: <code>/setrules default</code>")
    cfg.set(update.effective_chat.id, "rules_text", "" if body.lower() == "default" else body)
    await reply(update, context, "✅ Правила оновлено. Перегляд: /rules")


@group_admin
async def cmd_setwelcome(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    body = _command_body(update)
    if not body:
        return await reply(update, context, "Використання: <code>/setwelcome текст</code>\n"
                                            "Змінні: <code>{mention}</code> <code>{name}</code> <code>{chat}</code> <code>{id}</code>")
    cfg.set(update.effective_chat.id, "welcome_text", body)
    await reply(update, context, "✅ Вітання збережено.")


# ============================================================
#  МОДЕРАЦІЯ: WARN / MUTE / BAN / KICK
# ============================================================


@group_admin
async def cmd_warn(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    chat, admin = update.effective_chat, update.effective_user
    uid, name, rest = await resolve_target(update, context.args or [])
    if uid is None:
        return await reply(update, context, "Використання: <code>/warn [причина]</code>\n" + TARGET_HINT)
    if not await guard_target(update, context, uid):
        return
    reason = " ".join(rest) or "Порушення правил"
    count, limit, escalated = await issue_warn(context, chat.id, uid, name, reason, admin_name(update), admin.id if admin else 0)
    who = mention(uid, name)
    if escalated:
        text = f"⚠️ {who}: {limit}/{limit} попереджень → <b>{escalated}</b>."
        markup = None
    else:
        text = f"⚠️ {who} отримав попередження <b>{count}/{limit}</b>.\n💬 {esc(reason)}"
        markup = InlineKeyboardMarkup([[InlineKeyboardButton("↩️ Зняти попередження", callback_data=f"unwarn:{uid}")]])
    await reply(update, context, text, markup=markup)


@group_admin
async def cmd_unwarn(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    uid, name, _ = await resolve_target(update, context.args or [])
    if uid is None:
        return await reply(update, context, TARGET_HINT)
    chat = update.effective_chat
    if db.warn_remove_last(chat.id, uid):
        await log_action(context, chat.id, "unwarn", uid, name, admin_name(update), "знято останнє попередження")
        left = db.warn_count(chat.id, uid, cfg.get(chat.id, "warn_expire_days"))
        await reply(update, context, f"↩️ З {mention(uid, name)} знято попередження. Залишилось: <b>{left}</b>.")
    else:
        await reply(update, context, "У користувача немає попереджень.")


@group_admin
async def cmd_resetwarns(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    uid, name, _ = await resolve_target(update, context.args or [])
    if uid is None:
        return await reply(update, context, TARGET_HINT)
    db.warn_clear(update.effective_chat.id, uid)
    await reply(update, context, f"✅ Попередження {mention(uid, name)} скинуто.")


@group_admin
async def cmd_warns(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    chat = update.effective_chat
    uid, name, _ = await resolve_target(update, context.args or [])
    if uid is None:
        return await reply(update, context, TARGET_HINT)
    rows = db.warn_list(chat.id, uid, cfg.get(chat.id, "warn_expire_days"))
    if not rows:
        return await reply(update, context, f"У {mention(uid, name)} немає активних попереджень.")
    lines = [f"{i}. {fmt_ts(r['ts'])} — {esc(short(r['reason'], 100))}" for i, r in enumerate(rows, 1)]
    await reply(update, context, f"📊 {mention(uid, name)}: <b>{len(rows)}</b>/{cfg.get(chat.id, 'max_warns')}\n" + "\n".join(lines))


@group_admin
async def cmd_mute(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    chat = update.effective_chat
    uid, name, rest = await resolve_target(update, context.args or [])
    if uid is None:
        return await reply(update, context, "Використання: <code>/mute [30m|2h|1d|perm] [причина]</code>\n" + TARGET_HINT)
    if not await guard_target(update, context, uid):
        return
    seconds, reason = split_duration(rest, 1800)
    reason = reason or "Рішення адміністратора"
    if await do_mute(context, chat.id, uid, name, seconds, reason, admin_name(update)):
        await reply(update, context, f"🔇 {mention(uid, name)} у муті {for_duration(seconds)}.\n💬 {esc(reason)}")
    else:
        await reply(update, context, "❌ Не вдалося замутити (перевірте права бота: /check).")


@group_admin
async def cmd_unmute(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    uid, name, _ = await resolve_target(update, context.args or [])
    if uid is None:
        return await reply(update, context, TARGET_HINT)
    if await do_unmute(context, update.effective_chat.id, uid, name, admin_name(update)):
        await reply(update, context, f"🔊 {mention(uid, name)} знову може писати.")
    else:
        await reply(update, context, "❌ Не вдалося зняти мут.")


@group_admin
async def cmd_ban(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    chat, msg = update.effective_chat, update.effective_message
    uid, name, rest = await resolve_target(update, context.args or [])
    if uid is None:
        return await reply(update, context, "Використання: <code>/ban [тривалість] [причина]</code>\n" + TARGET_HINT)
    if not await guard_target(update, context, uid):
        return
    seconds, reason = split_duration(rest, 0)
    reason = reason or "Рішення адміністратора"
    if await do_ban(context, chat.id, uid, name, reason, admin_name(update), seconds or 0):
        if msg.reply_to_message:
            await delete_msg(context.bot, chat.id, msg.reply_to_message.message_id)
        await reply(update, context, f"🚫 {mention(uid, name)} забанений {for_duration(seconds or 0)}.\n💬 {esc(reason)}")
    else:
        await reply(update, context, "❌ Не вдалося забанити (перевірте права бота: /check).")


@group_admin
async def cmd_kick(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    uid, name, rest = await resolve_target(update, context.args or [])
    if uid is None:
        return await reply(update, context, TARGET_HINT)
    if not await guard_target(update, context, uid):
        return
    reason = " ".join(rest) or "Рішення адміністратора"
    if await do_kick(context, update.effective_chat.id, uid, name, reason, admin_name(update)):
        await reply(update, context, f"👢 {mention(uid, name)} вилучений з групи (може повернутись).")
    else:
        await reply(update, context, "❌ Не вдалося вилучити.")


@group_admin
async def cmd_unban(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    uid, name, _ = await resolve_target(update, context.args or [])
    if uid is None:
        return await reply(update, context, "Використання: відповідь, <code>/unban ID</code> або <code>/unban @нік</code>")
    if await do_unban(context, update.effective_chat.id, uid, name, admin_name(update)):
        await reply(update, context, f"✅ {mention(uid, name)} розбанений.")
    else:
        await reply(update, context, "❌ Не вдалося розбанити.")


@group_admin
async def cmd_banned(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    rows = db.ban_list(update.effective_chat.id)
    if not rows:
        return await reply(update, context, "Список банів порожній.")
    lines = []
    for r in rows:
        until = f" до {fmt_ts(r['until'])}" if r["until"] else ""
        lines.append(f"• <b>{esc(r['name'])}</b>{until}\n  <code>{r['user_id']}</code> — {esc(short(r['reason'], 60))}\n"
                     f"  /unban <code>{r['user_id']}</code>")
    await reply(update, context, "🚫 <b>Останні бани:</b>\n\n" + "\n".join(lines))


# ----- довірені користувачі -----

@group_admin
async def cmd_trust(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    uid, name, _ = await resolve_target(update, context.args or [])
    if uid is None:
        return await reply(update, context, TARGET_HINT)
    added = db.trust_add(update.effective_chat.id, uid)
    await reply(update, context, f"🤝 {mention(uid, name)} {'тепер довірений — фільтри його не чіпають' if added else 'вже довірений'}.")


@group_admin
async def cmd_untrust(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    uid, name, _ = await resolve_target(update, context.args or [])
    if uid is None:
        return await reply(update, context, TARGET_HINT)
    removed = db.trust_remove(update.effective_chat.id, uid)
    await reply(update, context, f"{mention(uid, name)}: {'довіру знято' if removed else 'не був у списку довірених'}.")


@group_admin
async def cmd_trusted(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    ids = db.trusted_list(update.effective_chat.id)
    if not ids:
        return await reply(update, context, "Довірених користувачів немає.")
    lines = []
    for uid in ids:
        row = db.user_by_id(uid)
        lines.append(f"• {mention(uid, row['full_name'] if row else str(uid))} <code>{uid}</code>")
    await reply(update, context, "🤝 <b>Довірені:</b>\n" + "\n".join(lines))


# ----- очищення -----

@group_admin
async def cmd_del(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    msg = update.effective_message
    if not msg.reply_to_message:
        return await reply(update, context, "Відповідайте на повідомлення, яке треба видалити.", ttl=10)
    await delete_msg(context.bot, update.effective_chat.id, msg.reply_to_message.message_id)
    await delete_msg(context.bot, update.effective_chat.id, msg.message_id)


@group_admin
async def cmd_purge(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    msg, chat = update.effective_message, update.effective_chat
    if not msg.reply_to_message:
        return await reply(update, context, "Відповідайте на повідомлення, з якого починати видалення: "
                                            "видаляться всі повідомлення від нього до команди (до 200).", ttl=15)
    start, end = msg.reply_to_message.message_id, msg.message_id
    done = await delete_many(context.bot, chat.id, range(start, min(end, start + 200) + 1))
    await say(context, chat.id, f"🧹 Видалено повідомлень: <b>{done}</b>", ttl=8)


# ----- скарги -----


async def cmd_report(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    msg, chat, user = update.effective_message, update.effective_chat, update.effective_user
    if chat.type not in GROUP_TYPES:
        return await reply(update, context, "Команда працює в групі.")
    target = msg.reply_to_message
    if not target or not target.from_user:
        return await reply(update, context, "Відповідайте командою /report на повідомлення порушника.", ttl=10)
    key = (chat.id, user.id)
    if time.time() - _last_report.get(key, 0) < 60:
        return await reply(update, context, "Скаргу можна надсилати не частіше ніж раз на хвилину.", ttl=10)
    _last_report[key] = time.time()
    try:
        admins = [a.user for a in await context.bot.get_chat_administrators(chat.id) if not a.user.is_bot][:5]
    except TelegramError:
        admins = []
    pings = "".join(f'<a href="tg://user?id={a.id}">\u2063</a>' for a in admins)
    kb = InlineKeyboardMarkup([[
        InlineKeyboardButton("🚫 Бан", callback_data=f"rep:ban:{target.from_user.id}:{target.message_id}"),
        InlineKeyboardButton("🗑 Видалити", callback_data=f"rep:del:{target.from_user.id}:{target.message_id}"),
        InlineKeyboardButton("✅ Закрити", callback_data="rep:ok:0:0"),
    ]])
    await delete_msg(context.bot, chat.id, msg.message_id)
    await say(
        context, chat.id,
        f"🚨 <b>Скарга</b> від {user_link(user)} на {user_link(target.from_user)}\n"
        f"📝 «{esc(short(message_text(target) or '[медіа]', 120))}»{pings}",
        ttl=0, markup=kb, reply_to=target.message_id,
    )
    db.bump(chat.id, "reports")


async def cb_report(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    chat = query.message.chat
    if not await is_admin_id(context, chat.id, query.from_user.id):
        return await query.answer("Тільки для адмінів.", show_alert=True)
    try:
        _, action, uid_s, mid_s = query.data.split(":")
        uid, mid = int(uid_s), int(mid_s)
    except ValueError:
        return await query.answer()
    result = "закрито"
    if action == "ban":
        if not await can_punish(context, chat.id, uid):
            return await query.answer("Цього користувача не можна покарати.", show_alert=True)
        info = db.user_by_id(uid)
        ok = await do_ban(context, chat.id, uid, info["full_name"] if info else str(uid), "за скаргою",
                          query.from_user.full_name, revoke=True)
        result = "користувача забанено" if ok else "не вдалося забанити"
    elif action == "del":
        await delete_msg(context.bot, chat.id, mid)
        result = "повідомлення видалено"
    await query.answer("Готово")
    try:
        await query.message.edit_text(f"✅ Скаргу опрацьовано ({esc(query.from_user.full_name)}): {result}.", parse_mode=ParseMode.HTML)
    except TelegramError:
        pass
    delete_later(context, chat.id, query.message.message_id, 30)


async def cb_unwarn(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    chat = query.message.chat
    if not await is_admin_id(context, chat.id, query.from_user.id):
        return await query.answer("Тільки для адмінів.", show_alert=True)
    uid = int(query.data.split(":")[1])
    if db.warn_remove_last(chat.id, uid):
        info = db.user_by_id(uid)
        await log_action(context, chat.id, "unwarn", uid, info["full_name"] if info else str(uid),
                         query.from_user.full_name, "знято кнопкою")
        await query.answer("Попередження знято")
        try:
            await query.message.edit_text("↩️ Попередження знято.", parse_mode=ParseMode.HTML)
        except TelegramError:
            pass
    else:
        await query.answer("Попереджень немає.", show_alert=True)


# ============================================================
#  СПИСКИ: СЛОВА, НІКИ, ДОМЕНИ
# ============================================================

LIST_META = {
    "word": ("слово", "Заборонені слова", "/addword слово"),
    "nick": ("префікс або маску нікнейма", "Заборонені нікнейми", "/addnick spam  або  /addnick *_bot"),
    "domain": ("домен", "Дозволені домени (посилання на них не блокуються)", "/addwhite youtube.com"),
}


def _list_value(kind: str, args: list[str]) -> str:
    if kind == "word":
        return " ".join(args).lower().strip()
    if kind == "nick":
        return args[0].lower().strip().lstrip("@")
    return extract_domain(args[0])


def make_list_commands(kind: str):
    noun, title, example = LIST_META[kind]

    @group_admin
    async def add(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
        if not context.args:
            return await reply(update, context, f"Використання: <code>{esc(example)}</code>")
        value = _list_value(kind, context.args)
        if len(value) < 2:
            return await reply(update, context, "Занадто коротке значення.")
        chat_id = update.effective_chat.id
        if db.list_add(chat_id, kind, value):
            reset_caches(chat_id)
            await reply(update, context, f"✅ Додано: <code>{esc(value)}</code>")
        else:
            await reply(update, context, f"«{esc(value)}» вже є у списку.")

    @group_admin
    async def remove(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
        if not context.args:
            return await reply(update, context, f"Вкажіть {noun}, який треба видалити.")
        value = _list_value(kind, context.args)
        chat_id = update.effective_chat.id
        if db.list_remove(chat_id, kind, value):
            reset_caches(chat_id)
            await reply(update, context, f"✅ Видалено: <code>{esc(value)}</code>")
        else:
            await reply(update, context, f"«{esc(value)}» немає у списку.")

    @group_admin
    async def show(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
        items = db.list_get(update.effective_chat.id, kind)
        if not items:
            return await reply(update, context, f"{title}: список порожній.\nДодати: <code>{esc(example)}</code>")
        body, shown = "", 0
        for item in items:
            line = f"• <code>{esc(item)}</code>\n"
            if len(body) + len(line) > 3500:
                break
            body += line
            shown += 1
        tail = f"\n…і ще {len(items) - shown}" if shown < len(items) else ""
        await reply(update, context, f"📋 <b>{title}</b> ({len(items)}):\n\n{body}{tail}")

    return add, remove, show


cmd_addword, cmd_removeword, cmd_listwords = make_list_commands("word")
cmd_addnick, cmd_removenick, cmd_listnicks = make_list_commands("nick")
cmd_addwhite, cmd_removewhite, cmd_listwhite = make_list_commands("domain")

# ============================================================
#  БЛОКУВАННЯ КОНТЕНТУ, LOCKDOWN, РЕЖИМ РЕЙДУ
# ============================================================


def _locks_text(chat_id: int) -> str:
    locked = set(cfg.get(chat_id, "locks"))
    lines = [f"{'🔒' if k in locked else '🔓'} <code>{k}</code> — {v}" for k, v in LOCK_TYPES.items()]
    return "\n".join(lines)


@group_admin
async def cmd_lock(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    chat_id = update.effective_chat.id
    args = [a.lower() for a in (context.args or [])]
    if not args:
        return await reply(update, context, "Використання: <code>/lock тип [тип…]</code> або <code>/lock all</code>\n\n" + _locks_text(chat_id))
    wanted = set(LOCK_TYPES) if "all" in args else {a for a in args if a in LOCK_TYPES}
    if not wanted:
        return await reply(update, context, "Невідомий тип.\n\n" + _locks_text(chat_id))
    cfg.set(chat_id, "locks", sorted(set(cfg.get(chat_id, "locks")) | wanted))
    await reply(update, context, "🔒 Заблоковано: " + ", ".join(sorted(wanted)) + "\n\n" + _locks_text(chat_id))


@group_admin
async def cmd_unlock(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    chat_id = update.effective_chat.id
    args = [a.lower() for a in (context.args or [])]
    if not args:
        return await reply(update, context, "Використання: <code>/unlock тип [тип…]</code> або <code>/unlock all</code>\n\n" + _locks_text(chat_id))
    wanted = set(LOCK_TYPES) if "all" in args else {a for a in args if a in LOCK_TYPES}
    cfg.set(chat_id, "locks", sorted(set(cfg.get(chat_id, "locks")) - wanted))
    await reply(update, context, "🔓 Розблоковано.\n\n" + _locks_text(chat_id))


@group_admin
async def cmd_locks(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await reply(update, context, "🔐 <b>Блокування контенту</b>\n\n" + _locks_text(update.effective_chat.id))


async def _lockdown_end_job(context: ContextTypes.DEFAULT_TYPE) -> None:
    chat_id = context.job.data
    await end_lockdown(context, chat_id)
    await say(context, chat_id, "🔓 Lockdown завершено, чат знову відкритий.", ttl=60)


async def end_lockdown(context: ContextTypes.DEFAULT_TYPE, chat_id: int) -> bool:
    prev = cfg.get(chat_id, "lockdown_prev")
    if prev is None:
        return False
    try:
        perms = ChatPermissions(**prev) if prev else all_perms()
    except Exception:
        perms = all_perms()
    try:
        await context.bot.set_chat_permissions(chat_id, perms)
    except TelegramError as e:
        await report_rights_problem(context, chat_id, e)
        return False
    cfg.set(chat_id, "lockdown_prev", None)
    cancel_jobs(context, f"lock:{chat_id}")
    return True


@group_admin
async def cmd_lockdown(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    chat = update.effective_chat
    if cfg.get(chat.id, "lockdown_prev") is not None:
        return await reply(update, context, "Lockdown уже активний. Вимкнути: /unlockdown")
    seconds, _ = split_duration(context.args or [], 0)
    try:
        info = await context.bot.get_chat(chat.id)
        prev = info.permissions.to_dict() if info.permissions else {}
        await context.bot.set_chat_permissions(chat.id, no_perms())
    except TelegramError as e:
        await report_rights_problem(context, chat.id, e)
        return await reply(update, context, "❌ Не вдалося увімкнути lockdown (потрібне право «Блокувати користувачів»).")
    cfg.set(chat.id, "lockdown_prev", prev)
    await log_action(context, chat.id, "lockdown", 0, "—", admin_name(update), fmt_duration(seconds or 0))
    if seconds:
        context.job_queue.run_once(_lockdown_end_job, seconds, data=chat.id, name=f"lock:{chat.id}")
    await reply(update, context, f"🔒 <b>Lockdown</b>: писати можуть лише адміни ({fmt_duration(seconds or 0)}). Зняти: /unlockdown")


@group_admin
async def cmd_unlockdown(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if await end_lockdown(context, update.effective_chat.id):
        await reply(update, context, "🔓 Lockdown знято, чат відкритий.")
    else:
        await reply(update, context, "Lockdown не був активний.")


@group_admin
async def cmd_raid(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    chat = update.effective_chat
    arg = (context.args[0].lower() if context.args else "status")
    if arg == "on":
        await activate_raid(context, chat, manual=True)
    elif arg == "off":
        raid.deactivate(chat.id)
        cancel_jobs(context, f"raid:{chat.id}")
        await reply(update, context, "✅ Режим рейду вимкнено.")
    else:
        left = raid.remaining(chat.id)
        await reply(update, context, f"🚨 Режим рейду активний, залишилось {fmt_duration(left)}." if left
                    else "Режим рейду не активний. Увімкнути вручну: <code>/raid on</code>")


# ============================================================
#  ЖУРНАЛ, СТАТИСТИКА, ПЕРЕВІРКА ПРАВ, ГЛОБАЛЬНИЙ БАН
# ============================================================


@group_admin
async def cmd_setlog(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    chat = update.effective_chat
    arg = (context.args[0].lower() if context.args else "")
    if arg == "off":
        cfg.set(chat.id, "log_chat", 0)
        return await reply(update, context, "✅ Журнал у зовнішній чат вимкнено (історія лишається в /modlog).")
    if arg == "here":
        target = chat.id
    elif arg.lstrip("-").isdigit():
        target = int(arg)
    else:
        return await reply(update, context, "Використання: <code>/setlog ID_чату</code>, <code>/setlog here</code> або <code>/setlog off</code>.\n"
                                            "Бот має бути учасником чату для журналу.")
    probe = await say(context, target, f"✅ Журнал модерації групи «{esc(chat.title)}» підключено.", ttl=0)
    if probe is None:
        return await reply(update, context, "❌ Не вдалося написати в цей чат. Додайте бота та дайте право писати.")
    cfg.set(chat.id, "log_chat", target)
    await reply(update, context, "✅ Журнал підключено.")


@group_admin
async def cmd_modlog(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    limit = 15
    if context.args and context.args[0].isdigit():
        limit = max(1, min(int(context.args[0]), 40))
    rows = db.log_recent(update.effective_chat.id, limit)
    if not rows:
        return await reply(update, context, "Журнал порожній.")
    lines = [
        f"{fmt_ts(r['ts'])} · {ACTION_LABELS.get(r['action'], esc(r['action']))} · <b>{esc(short(r['user_name'], 25))}</b> "
        f"— {esc(short(r['reason'], 60))}"
        for r in rows
    ]
    await reply(update, context, "📝 <b>Журнал модерації</b>\n\n" + "\n".join(lines))


STAT_LABELS = [
    ("messages", "💬 Повідомлень (чистих)"), ("joins", "👋 Вступів"), ("warn", "⚠️ Попереджень"),
    ("mute", "🔇 Мутів"), ("ban", "🚫 Банів"), ("kick", "👢 Кіків"),
    ("v_bad_word", "🔤 Заборонені слова"), ("v_link", "🔗 Посилання"), ("v_spam", "🧠 Спам (за балами)"),
    ("v_flood", "🌊 Флуд"), ("v_duplicate", "♻️ Дублікати"), ("v_wave", "🌪 Хвилі спаму"),
    ("v_lock", "🔒 Заблокований контент"), ("v_nick", "👤 Ніки"), ("v_name", "🪪 Імена"), ("v_gban", "🌐 Глобальні бани"),
    ("captcha_ok", "🔐 Капча пройдена"), ("captcha_fail", "🔐 Капча не пройдена"), ("raid", "🚨 Рейдів"), ("reports", "📣 Скарг"),
]


@group_admin
async def cmd_chatstats(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    chat = update.effective_chat
    data = db.stats(chat.id, 7)
    lines = [f"{label}: <b>{data[k]}</b>" for k, label in STAT_LABELS if data.get(k)]
    if not lines:
        return await reply(update, context, "Статистики за 7 днів поки немає.")
    removed = sum(v for k, v in data.items() if k.startswith("v_"))
    await reply(update, context, f"📊 <b>Статистика за 7 днів</b>\n\n" + "\n".join(lines) + f"\n\n🧹 Усього спрацювань фільтрів: <b>{removed}</b>")


async def cmd_stats(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Для адмінів — статистика групи, для інших — їхні власні попередження."""
    chat, user = update.effective_chat, update.effective_user
    if chat.type in GROUP_TYPES and user and await is_admin_id(context, chat.id, user.id):
        return await cmd_chatstats(update, context)
    return await cmd_mystats(update, context)


@group_admin
async def cmd_check(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    chat = update.effective_chat
    try:
        me = await context.bot.get_chat_member(chat.id, context.bot.id)
    except TelegramError as e:
        return await reply(update, context, f"❌ Не вдалося отримати мої права: {esc(e)}")
    if me.status not in ("administrator", "creator"):
        return await reply(update, context, "❌ Я не адміністратор. Зробіть мене адміном із правами видаляти повідомлення та блокувати користувачів.")
    checks = [
        ("can_delete_messages", "Видаляти повідомлення", True),
        ("can_restrict_members", "Блокувати та обмежувати користувачів", True),
        ("can_invite_users", "Запрошувати користувачів", False),
        ("can_pin_messages", "Закріплювати повідомлення", False),
    ]
    lines, critical = [], False
    for attr, label, needed in checks:
        ok = bool(getattr(me, attr, False)) or me.status == "creator"
        lines.append(f"{'✅' if ok else ('❌' if needed else '➖')} {label}")
        critical |= needed and not ok
    lines.append("")
    lines.append("⚠️ Критичних прав бракує — бот не зможе карати." if critical else "✅ Усе, що потрібно для роботи, є.")
    lines.append(f"🧩 Капча/антирейд: {'ввімкнено' if cfg.get(chat.id, 'captcha') else 'капча вимкнена'}, "
                 f"{'антирейд on' if cfg.get(chat.id, 'antiraid') else 'антирейд off'}")
    await reply(update, context, "🔎 <b>Перевірка прав бота</b>\n\n" + "\n".join(lines))


@group_admin
async def cmd_reload(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    chat_id = update.effective_chat.id
    admin_cache.drop(chat_id)
    cfg.drop_cache(chat_id)
    reset_caches(chat_id)
    await reply(update, context, "♻️ Кеш адмінів, налаштувань та фільтрів оновлено.")


@owner_only
async def cmd_gban(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    uid, name, rest = await resolve_target(update, context.args or [])
    if uid is None:
        return await reply(update, context, "Використання: <code>/gban ID [причина]</code> або відповіддю на повідомлення.")
    if uid in OWNER_IDS or uid == context.bot.id:
        return await reply(update, context, "🙅 Цього користувача не можна заблокувати глобально.")
    reason = " ".join(rest) or "спам"
    db.gban_add(uid, name, reason)
    banned = 0
    chats = db.chat_list()
    for row in chats:
        try:
            await context.bot.ban_chat_member(row["chat_id"], uid)
            banned += 1
        except TelegramError:
            pass
        await asyncio.sleep(0.05)
    _identity_cache.clear()
    await reply(update, context, f"🌐 {mention(uid, name)} у глобальному бані. Забанено в чатах: <b>{banned}</b> із {len(chats)}.\n"
                                 f"Нові спроби вступу блокуватимуться автоматично.")


@owner_only
async def cmd_ungban(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    uid, name, _ = await resolve_target(update, context.args or [])
    if uid is None:
        return await reply(update, context, "Використання: <code>/ungban ID</code>")
    if not db.gban_remove(uid):
        return await reply(update, context, "Цього користувача немає в глобальному бані.")
    for row in db.chat_list():
        try:
            await context.bot.unban_chat_member(row["chat_id"], uid, only_if_banned=True)
        except TelegramError:
            pass
        await asyncio.sleep(0.05)
    _identity_cache.clear()
    await reply(update, context, f"✅ {mention(uid, name)} знято з глобального бану.")


@owner_only
async def cmd_gbanlist(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    rows = db.gban_list()
    if not rows:
        return await reply(update, context, "Глобальний список порожній.")
    lines = [f"• <b>{esc(short(r['name'], 30))}</b> <code>{r['user_id']}</code> — {esc(short(r['reason'], 40))}" for r in rows]
    await reply(update, context, f"🌐 <b>Глобальні бани ({len(rows)}):</b>\n\n" + "\n".join(lines))


# ============================================================
#  ПАНЕЛЬ НАЛАШТУВАНЬ (/settings)
# ============================================================

TOGGLES = [
    ("bad_words_filter", "🔤 Фільтр слів"), ("nick_filter", "👤 Фільтр ніків"),
    ("name_filter", "🪪 Фільтр імен"), ("antispam", "🧠 Антиспам"),
    ("antiflood", "🌊 Антифлуд"), ("duplicate_filter", "♻️ Дублікати"),
    ("spam_wave", "🌪 Хвиля спаму"), ("captcha", "🔐 Капча"),
    ("antiraid", "🛡 Антирейд"), ("welcome", "👋 Вітання"),
    ("delete_service", "🧹 Служб. повід."), ("kick_bots", "🤖 Блок ботів"),
    ("gban_enabled", "🌐 Глобал. бан"), ("block_channels", "📢 Пости каналів"),
    ("forward_filter", "↪️ Пересил. новач."), ("notify", "🔔 Сповіщення"),
    ("auto_approve", "✅ Автоприйом заявок"),
]
CYCLES = {
    "link_policy": ("🔗 Посилання", [0, 1, 2], {0: "дозволено", 1: "блок новачкам", 2: "блок усім"}),
    "warn_action": ("⚖️ Після ліміту", ["ban", "mute", "kick"], {"ban": "бан", "mute": "мут", "kick": "кік"}),
    "nick_action": ("👤 Заборонений нік", ["ban", "kick", "delete"], {"ban": "бан", "kick": "кік", "delete": "лише видалити"}),
}
# ключ: (назва, мін, макс, крок)
NUMS = {
    "max_warns": ("⚠️ Макс. попереджень", 1, 10, 1),
    "warn_expire_days": ("⏳ Термін попереджень (дн, 0=∞)", 0, 365, 5),
    "flood_limit": ("🌊 Флуд: повідомлень", 3, 20, 1),
    "flood_seconds": ("🌊 Флуд: секунд", 3, 30, 1),
    "mute_minutes": ("🔇 Мут за флуд (хв)", 1, 1440, 5),
    "dup_limit": ("♻️ Ліміт повторів", 2, 8, 1),
    "spam_threshold": ("🧠 Поріг спаму (бали)", 3, 20, 1),
    "spam_ban_score": ("🧠 Бал для бану", 6, 30, 1),
    "newbie_minutes": ("🆕 «Новачок» (хв)", 1, 1440, 10),
    "captcha_timeout": ("🔐 Час капчі (с)", 30, 600, 30),
    "raid_joins": ("🚨 Рейд: вступів", 3, 40, 1),
    "raid_seconds": ("🚨 Рейд: за секунд", 10, 120, 5),
    "raid_minutes": ("🚨 Рейд: тривалість (хв)", 1, 120, 5),
    "max_mentions": ("📣 Макс. згадок", 1, 20, 1),
    "notify_ttl": ("🔔 Автовидалення сповіщень (с)", 0, 300, 5),
    "warn_mute_minutes": ("🔇 Мут після ліміту (хв)", 5, 10080, 60),
}


def panel_text(chat_id: int, page: str) -> str:
    if page == "num":
        return "🔢 <b>Числові параметри</b>\nНатискайте ➖ / ➕. Точні значення: <code>/set ключ число</code>"
    locks = cfg.get(chat_id, "locks")
    lines = [
        "⚙️ <b>Налаштування групи</b>",
        "",
        f"🔐 Блокування: {', '.join(locks) if locks else 'немає'}",
        f"🚨 Рейд: {'активний' if raid.active(chat_id) else 'ні'} · 🔒 Lockdown: "
        f"{'так' if cfg.get(chat_id, 'lockdown_prev') is not None else 'ні'}",
        f"📝 Журнал: {'ID ' + str(cfg.get(chat_id, 'log_chat')) if cfg.get(chat_id, 'log_chat') else 'не підключено (/setlog)'}",
        "",
        "Натисніть кнопку, щоб змінити параметр.",
    ]
    return "\n".join(lines)


def panel_markup(chat_id: int, page: str) -> InlineKeyboardMarkup:
    rows: list[list[InlineKeyboardButton]] = []
    if page == "num":
        for key, (label, lo, hi, step) in NUMS.items():
            rows.append([
                InlineKeyboardButton("➖", callback_data=f"cfg:n:{key}:-1"),
                InlineKeyboardButton(f"{label}: {cfg.get(chat_id, key)}", callback_data="cfg:i"),
                InlineKeyboardButton("➕", callback_data=f"cfg:n:{key}:1"),
            ])
        rows.append([InlineKeyboardButton("◀ Назад", callback_data="cfg:p:main")])
    else:
        for pair in chunked(TOGGLES, 2):
            rows.append([
                InlineKeyboardButton(f"{'✅' if cfg.get(chat_id, k) else '❌'} {label}", callback_data=f"cfg:t:{k}")
                for k, label in pair
            ])
        for key, (label, _, names) in CYCLES.items():
            rows.append([InlineKeyboardButton(f"{label}: {names[cfg.get(chat_id, key)]}", callback_data=f"cfg:c:{key}")])
        rows.append([
            InlineKeyboardButton("🔢 Числа ▶", callback_data="cfg:p:num"),
            InlineKeyboardButton("✖ Закрити", callback_data="cfg:x"),
        ])
    return InlineKeyboardMarkup(rows)


@group_admin
async def cmd_settings(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    chat_id = update.effective_chat.id
    await reply(update, context, panel_text(chat_id, "main"), markup=panel_markup(chat_id, "main"))


async def cb_settings(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    chat = query.message.chat
    if not await is_admin_id(context, chat.id, query.from_user.id):
        return await query.answer("Тільки для адмінів.", show_alert=True)
    parts = query.data.split(":")
    op, page = parts[1], "main"
    if op == "x":
        await query.answer()
        await delete_msg(context.bot, chat.id, query.message.message_id)
        return
    if op == "i":
        return await query.answer()
    if op == "t" and parts[2] in dict(TOGGLES):
        cfg.set(chat.id, parts[2], not cfg.get(chat.id, parts[2]))
    elif op == "c" and parts[2] in CYCLES:
        options = CYCLES[parts[2]][1]
        cur = cfg.get(chat.id, parts[2])
        cfg.set(chat.id, parts[2], options[(options.index(cur) + 1) % len(options)] if cur in options else options[0])
    elif op == "n" and parts[2] in NUMS:
        _, lo, hi, step = NUMS[parts[2]]
        value = cfg.get(chat.id, parts[2]) + step * int(parts[3])
        cfg.set(chat.id, parts[2], max(lo, min(hi, value)))
        page = "num"
    elif op == "p":
        page = parts[2] if parts[2] in ("main", "num") else "main"
    reset_caches(chat.id)
    await query.answer()
    try:
        await query.message.edit_text(panel_text(chat.id, page), parse_mode=ParseMode.HTML, reply_markup=panel_markup(chat.id, page))
    except BadRequest as e:
        if "not modified" not in str(e).lower():
            log.warning("settings panel: %s", e)


@group_admin
async def cmd_set(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    chat_id = update.effective_chat.id
    args = context.args or []
    if len(args) < 2:
        keys = ", ".join(f"<code>{k}</code>" for k in list(NUMS) + list(CYCLES) + [k for k, _ in TOGGLES])
        return await reply(update, context, "Використання: <code>/set ключ значення</code>\n(для перемикачів: on/off)\n\n" + keys)
    key, raw = args[0].lower(), args[1].lower()
    if key in NUMS:
        _, lo, hi, _ = NUMS[key]
        if not raw.lstrip("-").isdigit() or not lo <= int(raw) <= hi:
            return await reply(update, context, f"Значення для <code>{key}</code>: число від {lo} до {hi}.")
        cfg.set(chat_id, key, int(raw))
    elif key in CYCLES:
        options = CYCLES[key][1]
        value = next((o for o in options if str(o) == raw), None)
        if value is None:
            return await reply(update, context, f"Допустимі значення: {', '.join(map(str, options))}")
        cfg.set(chat_id, key, value)
    elif key in dict(TOGGLES):
        if raw not in ("on", "off", "1", "0", "true", "false"):
            return await reply(update, context, "Використовуйте on або off.")
        cfg.set(chat_id, key, raw in ("on", "1", "true"))
    else:
        return await reply(update, context, "Невідомий ключ. Список: /set")
    reset_caches(chat_id)
    await reply(update, context, f"✅ <code>{key}</code> = <b>{esc(cfg.get(chat_id, key))}</b>")


@group_admin
async def cmd_toggle(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Сумісність зі старою командою /toggle назва."""
    chat_id = update.effective_chat.id
    key = (context.args[0].lower() if context.args else "")
    if key not in dict(TOGGLES):
        return await reply(update, context, "Використання: <code>/toggle назва</code>\n" + ", ".join(f"<code>{k}</code>" for k, _ in TOGGLES))
    cfg.set(chat_id, key, not cfg.get(chat_id, key))
    reset_caches(chat_id)
    await reply(update, context, f"<b>{key}</b>: {'увімкнено ✅' if cfg.get(chat_id, key) else 'вимкнено ❌'}")


# ============================================================
#  ЗАПУСК
# ============================================================

COMMANDS: dict[str, Callable] = {
    "start": cmd_start, "help": cmd_help, "id": cmd_id, "rules": cmd_rules,
    "stats": cmd_stats, "mywarns": cmd_mystats, "report": cmd_report,
    "settings": cmd_settings, "set": cmd_set, "toggle": cmd_toggle, "setrules": cmd_setrules, "setwelcome": cmd_setwelcome,
    "warn": cmd_warn, "unwarn": cmd_unwarn, "warns": cmd_warns, "userstats": cmd_warns,
    "resetwarns": cmd_resetwarns, "resetstrikes": cmd_resetwarns,
    "mute": cmd_mute, "unmute": cmd_unmute, "ban": cmd_ban, "unban": cmd_unban, "kick": cmd_kick, "banned": cmd_banned,
    "trust": cmd_trust, "untrust": cmd_untrust, "trusted": cmd_trusted,
    "addword": cmd_addword, "removeword": cmd_removeword, "listwords": cmd_listwords,
    "addnick": cmd_addnick, "removenick": cmd_removenick, "listnicks": cmd_listnicks,
    "addwhite": cmd_addwhite, "removewhite": cmd_removewhite, "listwhite": cmd_listwhite,
    "lock": cmd_lock, "unlock": cmd_unlock, "locks": cmd_locks,
    "lockdown": cmd_lockdown, "unlockdown": cmd_unlockdown, "raid": cmd_raid,
    "del": cmd_del, "purge": cmd_purge,
    "setlog": cmd_setlog, "modlog": cmd_modlog, "check": cmd_check, "reload": cmd_reload,
    "gban": cmd_gban, "ungban": cmd_ungban, "gbanlist": cmd_gbanlist,
}


async def on_error(update: object, context: ContextTypes.DEFAULT_TYPE) -> None:
    err = context.error
    if isinstance(err, (Forbidden, BadRequest)):
        log.warning("Telegram API: %s", err)
    else:
        log.error("Необроблена помилка: %s", err, exc_info=err)


async def post_init(application: Application) -> None:
    await restore_captchas(application)
    try:
        everyone = [
            BotCommand("rules", "Правила групи"), BotCommand("report", "Поскаржитись (відповідь)"),
            BotCommand("mywarns", "Мої попередження"), BotCommand("id", "Показати ID"), BotCommand("help", "Довідка"),
        ]
        admins = everyone + [
            BotCommand("settings", "Налаштування групи"), BotCommand("warn", "Попередження"), BotCommand("mute", "Мут"),
            BotCommand("ban", "Бан"), BotCommand("unban", "Розбан"), BotCommand("kick", "Вилучити"),
            BotCommand("purge", "Видалити пачку повідомлень"), BotCommand("lockdown", "Тиша в чаті"),
            BotCommand("modlog", "Журнал дій"), BotCommand("stats", "Статистика"), BotCommand("check", "Перевірка прав бота"),
        ]
        await application.bot.set_my_commands(everyone, scope=BotCommandScopeAllGroupChats())
        await application.bot.set_my_commands(admins, scope=BotCommandScopeAllChatAdministrators())
        await application.bot.set_my_commands(everyone[-1:] + [BotCommand("start", "Про бота")])
    except TelegramError as e:
        log.warning("Не вдалося встановити меню команд: %s", e)
    me = await application.bot.get_me()
    log.info("Бот запущено: @%s (id %s)", me.username, me.id)


def build_application() -> Application:
    app = Application.builder().token(TOKEN).post_init(post_init).build()
    if app.job_queue is None:
        raise SystemExit("Потрібен JobQueue: pip install \"python-telegram-bot[job-queue]\"")

    for name, handler in COMMANDS.items():
        app.add_handler(CommandHandler(name, handler))

    app.add_handler(CallbackQueryHandler(cb_captcha, pattern=r"^cap:"))
    app.add_handler(CallbackQueryHandler(cb_settings, pattern=r"^cfg:"))
    app.add_handler(CallbackQueryHandler(cb_report, pattern=r"^rep:"))
    app.add_handler(CallbackQueryHandler(cb_unwarn, pattern=r"^unwarn:"))

    app.add_handler(MessageHandler(filters.StatusUpdate.NEW_CHAT_MEMBERS, on_new_members))
    app.add_handler(MessageHandler(filters.StatusUpdate.LEFT_CHAT_MEMBER, on_left_member))
    app.add_handler(ChatJoinRequestHandler(on_join_request))
    app.add_handler(ChatMemberHandler(on_my_chat_member, ChatMemberHandler.MY_CHAT_MEMBER))
    # фільтри — в окремій групі, щоб працювали і для повідомлень-команд, і для редагувань
    app.add_handler(MessageHandler(filters.ChatType.GROUPS & ~filters.StatusUpdate.ALL, on_group_message), group=1)
    app.add_error_handler(on_error)

    app.job_queue.run_repeating(maintenance_job, interval=300, first=60)
    app.job_queue.run_daily(daily_cleanup_job, time=dtime(hour=4, minute=0))
    return app


def main() -> None:
    if not TOKEN:
        raise SystemExit("Не задано змінну середовища BOT_TOKEN")
    app = build_application()
    log.info("Запуск polling… (БД: %s)", DB_PATH)
    app.run_polling(allowed_updates=Update.ALL_TYPES, drop_pending_updates=True)


if __name__ == "__main__":
    main()
