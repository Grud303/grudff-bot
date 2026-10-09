import os
import json
import logging
from datetime import datetime, timedelta
from collections import defaultdict

from telegram import Update, ChatPermissions
from telegram.ext import (
    Application,
    CommandHandler,
    MessageHandler,
    ContextTypes,
    filters,
)
from telegram.error import TelegramError

# ================== НАЛАШТУВАННЯ ==================
logging.basicConfig(
    format="%(asctime)s - %(levelname)s - %(message)s",
    level=logging.INFO
)
logger = logging.getLogger(__name__)

TOKEN = os.getenv("BOT_TOKEN")

# Файли даних
FILES = {
    "settings": "settings.json",
    "words": "bad_words.json",
    "nicks": "banned_nicks.json",
    "banned": "banned.json",
    "strikes": "strikes.json",
}

DEFAULT_SETTINGS = {
    "bad_words_filter": True,
    "username_filter": True,
    "antiflood": True,
    "welcome": True,
    "max_strikes": 3,
    "flood_limit": 6,
    "flood_seconds": 8,
    "mute_on_flood_minutes": 15,
}

GROUP_RULES = """
📋 <b>Правила групи</b>

1. Без заборонених слів
2. Без заборонених нікнеймів
3. Не флудити і не спамити
4. Поважати учасників та адміністрацію
5. Дотримуватися теми групи

Порушення = попередження → мут / бан
"""

# ================== РОБОТА З ДАНИМИ ==================

def load(filename, default):
    try:
        with open(filename, "r", encoding="utf-8") as f:
            return json.load(f)
    except (FileNotFoundError, json.JSONDecodeError):
        return default


def save(filename, data):
    with open(filename, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=2)


settings = load(FILES["settings"], DEFAULT_SETTINGS.copy())
BAD_WORDS = set(load(FILES["words"], []))
BANNED_NICKS = set(load(FILES["nicks"], []))          # порожній список
banned_users = load(FILES["banned"], {})
strikes = load(FILES["strikes"], {})

flood_data = defaultdict(lambda: defaultdict(list))

# ================== ДОПОМІЖНІ ФУНКЦІЇ ==================

def get_set(key):
    return settings.get(key, DEFAULT_SETTINGS.get(key))


def set_set(key, value):
    settings[key] = value
    save(FILES["settings"], settings)


def get_strikes(chat_id, user_id):
    return strikes.get(str(chat_id), {}).get(str(user_id), 0)


def set_strikes(chat_id, user_id, value):
    cid = str(chat_id)
    if cid not in strikes:
        strikes[cid] = {}
    strikes[cid][str(user_id)] = value
    save(FILES["strikes"], strikes)


def add_strike(chat_id, user_id):
    val = get_strikes(chat_id, user_id) + 1
    set_strikes(chat_id, user_id, val)
    return val


def add_to_banned(user_id, name, reason):
    banned_users[str(user_id)] = {
        "name": name,
        "reason": reason,
        "date": datetime.now().strftime("%d.%m.%Y %H:%M")
    }
    save(FILES["banned"], banned_users)


def remove_from_banned(user_id):
    if str(user_id) in banned_users:
        del banned_users[str(user_id)]
        save(FILES["banned"], banned_users)


def is_bad_nick(username: str | None) -> bool:
    if not username:
        return False
    u = username.lower()
    return any(u.startswith(p.lower()) for p in BANNED_NICKS)


async def is_admin(update: Update, context: ContextTypes.DEFAULT_TYPE) -> bool:
    try:
        member = await context.bot.get_chat_member(
            update.effective_chat.id,
            update.effective_user.id
        )
        return member.status in ("administrator", "creator")
    except TelegramError:
        return False


async def safe_delete(msg) -> bool:
    try:
        await msg.delete()
        return True
    except TelegramError:
        return False


async def do_ban(context, chat_id, user_id, name, reason) -> bool:
    try:
        await context.bot.ban_chat_member(chat_id, user_id)
        add_to_banned(user_id, name, reason)
        set_strikes(chat_id, user_id, 0)
        return True
    except TelegramError as e:
        logger.error(f"Ban failed: {e}")
        return False


async def do_unban(context, chat_id, user_id) -> bool:
    try:
        await context.bot.unban_chat_member(chat_id, user_id, only_if_banned=True)
        remove_from_banned(user_id)
        return True
    except TelegramError as e:
        logger.error(f"Unban failed: {e}")
        return False


async def do_mute(context, chat_id, user_id, minutes) -> bool:
    until = datetime.utcnow() + timedelta(minutes=minutes)
    perms = ChatPermissions(can_send_messages=False)
    try:
        await context.bot.restrict_chat_member(
            chat_id, user_id, permissions=perms, until_date=until
        )
        return True
    except TelegramError:
        return False


# ================== КОМАНДИ ==================

async def cmd_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    text = (
        "🛡️ <b>Grudff Moderator</b>\n\n"
        "Розумний бот для захисту групи від спаму, мату та небезпечних акаунтів.\n\n"
        "<b>Можливості:</b>\n"
        "• Фільтр заборонених слів\n"
        "• Бан за нікнейми\n"
        "• Антифлуд\n"
        "• Система попереджень\n"
        "• Мут / Бан / Розбан\n"
        "• Гнучкі налаштування\n\n"
        "📌 /help — всі команди\n"
        "📌 /settings — налаштування"
    )
    await update.message.reply_text(text, parse_mode="HTML")


async def cmd_help(update: Update, context: ContextTypes.DEFAULT_TYPE):
    adm = await is_admin(update, context)

    text = (
        "📖 <b>ДОВІДКА</b>\n\n"
        "<b>Для всіх:</b>\n"
        "/start — про бота\n"
        "/help — ця довідка\n"
        "/rules — правила групи\n"
        "/stats — твої попередження\n\n"
    )

    if adm:
        text += (
            "<b>⚙️ Налаштування</b>\n"
            "/settings — поточні налаштування\n"
            "/toggle <code>назва</code> — увімкнути/вимкнути функцію\n"
            "Доступні: <code>bad_words_filter</code>, <code>username_filter</code>, "
            "<code>antiflood</code>, <code>welcome</code>\n\n"

            "<b>🔤 Слова</b>\n"
            "/addword слово — додати заборонене слово\n"
            "/removeword слово — видалити\n"
            "/listwords — список слів\n\n"

            "<b>👤 Нікнейми</b>\n"
            "/addnick префікс — заборонити ніки, що починаються на ...\n"
            "/removenick префікс — прибрати\n"
            "/listnicks — список заборонених ніків\n"
            "Приклад: <code>/addnick spam</code> → банить @spam, @spam123...\n\n"

            "<b>🛡️ Модерація</b>\n"
            "/warn — попередження (відповідь)\n"
            "/mute 30 — мут на 30 хв (відповідь)\n"
            "/ban — бан (відповідь)\n"
            "/unban — розбан (відповідь або /unban ID)\n"
            "/banned — список забанених\n"
            "/resetstrikes — скинути попередження\n"
            "/userstats — статистика користувача\n\n"

            "<b>🧹 Очищення</b>\n"
            "/del — видалити повідомлення (відповідь)\n"
            "/purge 10 — видалити 10 повідомлень\n\n"

            "<b>ℹ️ Інше</b>\n"
            "/id — показати ID\n"
        )

    await update.message.reply_text(text, parse_mode="HTML")


async def cmd_rules(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(GROUP_RULES, parse_mode="HTML")


async def cmd_stats(update: Update, context: ContextTypes.DEFAULT_TYPE):
    u = update.effective_user
    c = update.effective_chat
    count = get_strikes(c.id, u.id)
    await update.message.reply_text(
        f"📊 <b>Твоя статистика</b>\n\n"
        f"Ім'я: {u.full_name}\n"
        f"Попереджень: <b>{count}</b>/{get_set('max_strikes')}",
        parse_mode="HTML"
    )


# ----- Налаштування -----

async def cmd_settings(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await is_admin(update, context):
        return await update.message.reply_text("⛔ Тільки адміністратори.")

    def st(k):
        return "✅ Увімкнено" if get_set(k) else "❌ Вимкнено"

    text = (
        "⚙️ <b>Налаштування</b>\n\n"
        f"🔤 Фільтр слів: <b>{st('bad_words_filter')}</b>\n"
        f"👤 Фільтр ніків: <b>{st('username_filter')}</b>\n"
        f"🌊 Антифлуд: <b>{st('antiflood')}</b>\n"
        f"👋 Вітання: <b>{st('welcome')}</b>\n\n"
        f"⚠️ Макс. попереджень: <b>{get_set('max_strikes')}</b>\n"
        f"🌊 Флуд: <b>{get_set('flood_limit')}</b> пов. / "
        f"<b>{get_set('flood_seconds')}</b> сек.\n\n"
        "Змінити функцію: <code>/toggle назва</code>"
    )
    await update.message.reply_text(text, parse_mode="HTML")


async def cmd_toggle(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await is_admin(update, context):
        return await update.message.reply_text("⛔ Тільки адміністратори.")

    if not context.args:
        return await update.message.reply_text(
            "Використання: <code>/toggle назва</code>\n\n"
            "Доступні:\n"
            "• bad_words_filter\n"
            "• username_filter\n"
            "• antiflood\n"
            "• welcome",
            parse_mode="HTML"
        )

    key = context.args[0].lower()
    if key not in ("bad_words_filter", "username_filter", "antiflood", "welcome"):
        return await update.message.reply_text("❌ Невідома функція.")

    new_val = not get_set(key)
    set_set(key, new_val)
    status = "увімкнено ✅" if new_val else "вимкнено ❌"
    await update.message.reply_text(f"Функція <b>{key}</b> тепер {status}", parse_mode="HTML")


# ----- Слова -----

async def cmd_addword(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await is_admin(update, context):
        return await update.message.reply_text("⛔ Тільки адміністратори.")
    if not context.args:
        return await update.message.reply_text("Використання: /addword слово")

    word = " ".join(context.args).lower().strip()
    if word in BAD_WORDS:
        return await update.message.reply_text(f"«{word}» вже є.")
    BAD_WORDS.add(word)
    save(FILES["words"], list(BAD_WORDS))
    await update.message.reply_text(f"✅ Слово «{word}» додано.")


async def cmd_removeword(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await is_admin(update, context):
        return await update.message.reply_text("⛔ Тільки адміністратори.")
    if not context.args:
        return await update.message.reply_text("Використання: /removeword слово")

    word = " ".join(context.args).lower().strip()
    if word not in BAD_WORDS:
        return await update.message.reply_text(f"«{word}» немає.")
    BAD_WORDS.discard(word)
    save(FILES["words"], list(BAD_WORDS))
    await update.message.reply_text(f"✅ Слово «{word}» видалено.")


async def cmd_listwords(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await is_admin(update, context):
        return await update.message.reply_text("⛔ Тільки адміністратори.")
    if not BAD_WORDS:
        return await update.message.reply_text("Список слів порожній.")
    words = "\n".join(f"• <code>{w}</code>" for w in sorted(BAD_WORDS))
    await update.message.reply_text(f"📋 <b>Заборонені слова:</b>\n\n{words}", parse_mode="HTML")


# ----- Нікнейми -----

async def cmd_addnick(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await is_admin(update, context):
        return await update.message.reply_text("⛔ Тільки адміністратори.")
    if not context.args:
        return await update.message.reply_text(
            "Використання: /addnick префікс\n"
            "Приклад: /addnick spam\n"
            "Банитиме @spam, @spam123, @Spam_bot..."
        )

    prefix = context.args[0].lower().strip().lstrip("@")
    if prefix in BANNED_NICKS:
        return await update.message.reply_text(f"«{prefix}» вже є.")
    BANNED_NICKS.add(prefix)
    save(FILES["nicks"], list(BANNED_NICKS))
    await update.message.reply_text(
        f"✅ Ніки, що починаються на <b>{prefix}</b>, тепер заборонені.",
        parse_mode="HTML"
    )


async def cmd_removenick(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await is_admin(update, context):
        return await update.message.reply_text("⛔ Тільки адміністратори.")
    if not context.args:
        return await update.message.reply_text("Використання: /removenick префікс")

    prefix = context.args[0].lower().strip().lstrip("@")
    if prefix not in BANNED_NICKS:
        return await update.message.reply_text(f"«{prefix}» немає.")
    BANNED_NICKS.discard(prefix)
    save(FILES["nicks"], list(BANNED_NICKS))
    await update.message.reply_text(f"✅ Префікс «{prefix}» видалено.")


async def cmd_listnicks(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await is_admin(update, context):
        return await update.message.reply_text("⛔ Тільки адміністратори.")
    if not BANNED_NICKS:
        return await update.message.reply_text("Список ніків порожній.\nДодай через /addnick")
    nicks = "\n".join(f"• <code>{n}</code>" for n in sorted(BANNED_NICKS))
    await update.message.reply_text(
        f"👤 <b>Заборонені нікнейми:</b>\n\n{nicks}",
        parse_mode="HTML"
    )


# ----- Модерація -----

async def cmd_warn(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await is_admin(update, context):
        return await update.message.reply_text("⛔ Тільки адміністратори.")
    if not update.message.reply_to_message:
        return await update.message.reply_text("Відповідай на повідомлення.")

    t = update.message.reply_to_message.from_user
    chat_id = update.effective_chat.id
    count = add_strike(chat_id, t.id)
    max_s = get_set("max_strikes")

    await update.message.reply_text(
        f"⚠️ {t.mention_html()} отримав попередження.\n"
        f"Зараз: <b>{count}</b>/{max_s}",
        parse_mode="HTML"
    )

    if count >= max_s:
        if await do_ban(context, chat_id, t.id, t.full_name, f"{max_s} попередження"):
            await update.message.reply_text(
                f"🚫 {t.mention_html()} забанений.",
                parse_mode="HTML"
            )


async def cmd_mute(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await is_admin(update, context):
        return await update.message.reply_text("⛔ Тільки адміністратори.")
    if not update.message.reply_to_message:
        return await update.message.reply_text("Відповідай на повідомлення.")

    minutes = 30
    if context.args and context.args[0].isdigit():
        minutes = int(context.args[0])

    t = update.message.reply_to_message.from_user
    if await do_mute(context, update.effective_chat.id, t.id, minutes):
        await update.message.reply_text(
            f"🔇 {t.mention_html()} замучений на {minutes} хв.",
            parse_mode="HTML"
        )
    else:
        await update.message.reply_text("❌ Не вдалося замутити.")


async def cmd_ban(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await is_admin(update, context):
        return await update.message.reply_text("⛔ Тільки адміністратори.")
    if not update.message.reply_to_message:
        return await update.message.reply_text("Відповідай на повідомлення.")

    t = update.message.reply_to_message.from_user
    reason = " ".join(context.args) if context.args else "Рішення адміна"

    if await do_ban(context, update.effective_chat.id, t.id, t.full_name, reason):
        await update.message.reply_text(
            f"🚫 {t.mention_html()} забанений.\nПричина: {reason}",
            parse_mode="HTML"
        )
    else:
        await update.message.reply_text("❌ Не вдалося забанити.")


async def cmd_unban(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await is_admin(update, context):
        return await update.message.reply_text("⛔ Тільки адміністратори.")

    chat_id = update.effective_chat.id
    uid = name = None

    if update.message.reply_to_message:
        t = update.message.reply_to_message.from_user
        uid, name = t.id, t.full_name
    elif context.args and context.args[0].isdigit():
        uid = int(context.args[0])
        name = banned_users.get(str(uid), {}).get("name", f"ID {uid}")
    else:
        return await update.message.reply_text("Відповідь + /unban  або  /unban ID")

    if await do_unban(context, chat_id, uid):
        await update.message.reply_text(f"✅ {name} розбанений.")
    else:
        await update.message.reply_text("❌ Не вдалося розбанити.")


async def cmd_banned(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await is_admin(update, context):
        return await update.message.reply_text("⛔ Тільки адміністратори.")
    if not banned_users:
        return await update.message.reply_text("Список забанених порожній.")

    text = "🚫 <b>Забанені:</b>\n\n"
    for uid, info in banned_users.items():
        text += (
            f"• <b>{info.get('name', '?')}</b>\n"
            f"  ID: <code>{uid}</code>\n"
            f"  Причина: {info.get('reason', '—')}\n"
            f"  Дата: {info.get('date', '—')}\n"
            f"  <code>/unban {uid}</code>\n\n"
        )
    await update.message.reply_text(text, parse_mode="HTML")


async def cmd_resetstrikes(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await is_admin(update, context):
        return await update.message.reply_text("⛔ Тільки адміністратори.")
    if not update.message.reply_to_message:
        return await update.message.reply_text("Відповідай на повідомлення.")

    t = update.message.reply_to_message.from_user
    set_strikes(update.effective_chat.id, t.id, 0)
    await update.message.reply_text(
        f"✅ Попередження {t.mention_html()} скинуто.",
        parse_mode="HTML"
    )


async def cmd_userstats(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await is_admin(update, context):
        return await update.message.reply_text("⛔ Тільки адміністратори.")
    if not update.message.reply_to_message:
        return await update.message.reply_text("Відповідай на повідомлення.")

    t = update.message.reply_to_message.from_user
    count = get_strikes(update.effective_chat.id, t.id)
    await update.message.reply_text(
        f"📊 {t.mention_html()}\nПопереджень: <b>{count}</b>/{get_set('max_strikes')}",
        parse_mode="HTML"
    )


# ----- Очищення -----

async def cmd_del(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await is_admin(update, context):
        return await update.message.reply_text("⛔ Тільки адміністратори.")
    if not update.message.reply_to_message:
        return await update.message.reply_text("Відповідай на повідомлення.")
    await safe_delete(update.message.reply_to_message)
    await safe_delete(update.message)


async def cmd_purge(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await is_admin(update, context):
        return await update.message.reply_text("⛔ Тільки адміністратори.")
    if not update.message.reply_to_message:
        return await update.message.reply_text("Відповідай на повідомлення: /purge 10")

    count = 5
    if context.args and context.args[0].isdigit():
        count = min(int(context.args[0]), 50)

    chat_id = update.effective_chat.id
    start_id = update.message.reply_to_message.message_id
    deleted = 0

    for i in range(count):
        try:
            await context.bot.delete_message(chat_id, start_id - i)
            deleted += 1
        except TelegramError:
            pass

    msg = await update.message.reply_text(f"🧹 Видалено ~{deleted} повідомлень")
    await safe_delete(update.message)
    try:
        await msg.delete()
    except:
        pass


async def cmd_id(update: Update, context: ContextTypes.DEFAULT_TYPE):
    u = update.effective_user
    c = update.effective_chat
    text = f"🆔 Твій ID: <code>{u.id}</code>\nЧат ID: <code>{c.id}</code>"
    if update.message.reply_to_message:
        t = update.message.reply_to_message.from_user
        text += f"\nID співрозмовника: <code>{t.id}</code>"
    await update.message.reply_text(text, parse_mode="HTML")


# ================== АВТОМОДЕРАЦІЯ ==================

async def on_message(update: Update, context: ContextTypes.DEFAULT_TYPE):
    msg = update.effective_message
    user = update.effective_user
    chat = update.effective_chat

    if not msg or not user or not chat:
        return
    if await is_admin(update, context):
        return

    chat_id, user_id = chat.id, user.id

    # 1. Фільтр нікнеймів
    if get_set("username_filter") and is_bad_nick(user.username):
        await safe_delete(msg)
        if await do_ban(context, chat_id, user_id, user.full_name, f"нік @{user.username}"):
            await context.bot.send_message(
                chat_id,
                f"🚫 {user.mention_html()} забанений (заборонений нік <b>@{user.username}</b>)",
                parse_mode="HTML"
            )
        return

    # 2. Антифлуд
    if get_set("antiflood"):
        now = datetime.now().timestamp()
        limit = get_set("flood_limit")
        sec = get_set("flood_seconds")

        times = [t for t in flood_data[chat_id][user_id] if now - t < sec]
        times.append(now)
        flood_data[chat_id][user_id] = times

        if len(times) > limit:
            await safe_delete(msg)
            minutes = get_set("mute_on_flood_minutes")
            await do_mute(context, chat_id, user_id, minutes)
            await context.bot.send_message(
                chat_id,
                f"🌊 {user.mention_html()} флудить → мут на {minutes} хв.",
                parse_mode="HTML"
            )
            flood_data[chat_id][user_id] = []
            return

    # 3. Фільтр слів
    if get_set("bad_words_filter") and BAD_WORDS:
        text = (msg.text or msg.caption or "").lower()
        if text and any(w in text for w in BAD_WORDS):
            await safe_delete(msg)
            count = add_strike(chat_id, user_id)
            max_s = get_set("max_strikes")

            if count >= max_s:
                if await do_ban(context, chat_id, user_id, user.full_name, "заборонене слово"):
                    await context.bot.send_message(
                        chat_id,
                        f"🚫 {user.mention_html()} забанений (заборонене слово)",
                        parse_mode="HTML"
                    )
            else:
                await context.bot.send_message(
                    chat_id,
                    f"⚠️ {user.mention_html()}, заборонене слово.\n"
                    f"Попередження: <b>{count}</b>/{max_s}",
                    parse_mode="HTML"
                )


async def on_new_member(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not get_set("welcome"):
        return

    chat = update.effective_chat

    for user in update.message.new_chat_members:
        if user.is_bot:
            continue

        if get_set("username_filter") and is_bad_nick(user.username):
            if await do_ban(context, chat.id, user.id, user.full_name, f"нік @{user.username}"):
                await context.bot.send_message(
                    chat.id,
                    f"🚫 {user.mention_html()} одразу забанений (нік)",
                    parse_mode="HTML"
                )
            continue

        await chat.send_message(
            f"👋 Вітаємо, {user.mention_html()}!\nПравила: /rules",
            parse_mode="HTML"
        )


# ================== ЗАПУСК ==================

def main():
    if not TOKEN:
        raise RuntimeError("Встанови BOT_TOKEN")

    app = Application.builder().token(TOKEN).build()

    # Команди
    commands = [
        ("start", cmd_start),
        ("help", cmd_help),
        ("rules", cmd_rules),
        ("stats", cmd_stats),
        ("settings", cmd_settings),
        ("toggle", cmd_toggle),
        ("addword", cmd_addword),
        ("removeword", cmd_removeword),
        ("listwords", cmd_listwords),
        ("addnick", cmd_addnick),
        ("removenick", cmd_removenick),
        ("listnicks", cmd_listnicks),
        ("warn", cmd_warn),
        ("mute", cmd_mute),
        ("ban", cmd_ban),
        ("unban", cmd_unban),
        ("banned", cmd_banned),
        ("resetstrikes", cmd_resetstrikes),
        ("userstats", cmd_userstats),
        ("del", cmd_del),
        ("purge", cmd_purge),
        ("id", cmd_id),
    ]

    for name, handler in commands:
        app.add_handler(CommandHandler(name, handler))

    app.add_handler(MessageHandler(filters.StatusUpdate.NEW_CHAT_MEMBERS, on_new_member))
    app.add_handler(MessageHandler(
        (filters.TEXT | filters.CAPTION) & ~filters.COMMAND,
        on_message
    ))

    print("✅ Grudff Moderator запущений!")
    app.run_polling(allowed_updates=Update.ALL_TYPES)


if __name__ == "__main__":
    main()