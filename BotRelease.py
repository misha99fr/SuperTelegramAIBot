"""
Telegram-бот: погода + чат с ИИ + магазин + аварийное отключение из консоли.

Установка:
    pip install -U "python-telegram-bot>=21" openai httpx cryptography

Настройки (можно задать переменными окружения или прямо в коде ниже):
    TELEGRAM_BOT_TOKEN  - токен от @BotFather
    OPENAI_API_KEY      - ключ Tooken Club
    OPENAI_BASE_URL     - по умолчанию https://tooken.club/v1
    OPENAI_MODEL        - по умолчанию gpt-6.1-sol
    ADMIN_ID            - твой Telegram ID (узнать: команда /myid у бота),
                          можно несколько через запятую

Запуск:  python bot.py

Команды в КОНСОЛИ (там, где запущен бот):
    /stop <секунды> [причина]   - экстренное отключение с оповещением в чатах
    /stop offchatgpt [причина]  - отключить ИИ (OpenAI), бот и магазин работают
    /stop onchatgpt             - снова включить ИИ
    /cancel                     - отменить запланированное отключение
    /ban @username [причина]    - запретить человеку пользоваться ботом
    /unban @username            - снять бан
    /banlist                    - список забаненных
    /grant <id|@username>       - выдать доступ к ИИ-чату без игры
    /survreset <id|@username>   - обнулить игру /survkey (можно играть заново)
    /plugins                    - список плагинов и их статусы
    /plugin <действие>          - управление плагинами (/plugin help):
        off/on <имя>            принудительно отключить / включить плагин
        offall / onall          аварийно отключить / включить все плагины
        lock / unlock           запретить / разрешить установку плагинов
        block / unblock <имя>   запретить / разрешить конкретное имя
        revoke <имя>            отозвать цифровую подпись плагина
        revokekey <id>          отозвать ключ целиком
        genkey / sign / verify  ключи Ed25519 и подпись (base64)
    /pluginadd <путь к .txt>    - установить плагин из файла
    /delplugin <имя>            - удалить плагин

Подпись плагинов из терминала (без запуска бота):
    python bot.py genkey <id>            - создать пару ключей
    python bot.py sign <файл.txt> <id>   - подписать плагин (подпись в base64)
    python bot.py verify <файл.txt>      - проверить подпись
    /products                   - список товаров
    /addproduct Название | Цена | Описание
    /delproduct <id>
    /help
"""

import asyncio
import base64
import contextlib
import hashlib
import html
import io
import json
import logging
import math
import os
import random
import re
import sys
import threading
import time
from pathlib import Path

import httpx
from cryptography.exceptions import InvalidSignature
from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import (
    Ed25519PrivateKey,
    Ed25519PublicKey,
)
from openai import AsyncOpenAI
from telegram import (
    BotCommand,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    Update,
)
from telegram.constants import ChatAction, ParseMode
from telegram.error import BadRequest
from telegram.ext import (
    Application,
    ApplicationHandlerStop,
    CallbackQueryHandler,
    CommandHandler,
    ContextTypes,
    MessageHandler,
    TypeHandler,
    filters,
)

logging.basicConfig(
    format="%(asctime)s %(levelname)s %(name)s: %(message)s", level=logging.INFO
)
logging.getLogger("httpx").setLevel(logging.WARNING)
log = logging.getLogger("bot")

# ------------------------------------------------------------- настройки

# ВСТАВЬ сюда токен Telegram-бота от @BotFather (вида 123456789:AAH...)
TELEGRAM_TOKEN = os.getenv("TELEGRAM_BOT_TOKEN", "тут botfather token")
# Ключ Tooken Club — ТОЛЬКО из переменной окружения, в коде не хранить!
OPENAI_API_KEY = os.getenv("OPENAI_API_KEY", "тут пишете tooken token")
MODEL = os.getenv("OPENAI_MODEL", "gpt-6.1-sol")

# Telegram ID администраторов (числа через запятую). Узнать свой: /myid
ADMIN_IDS = {
    int(x)
    for x in os.getenv("ADMIN_ID", "тут ваш айди").replace(" ", "").split(",")
    if x.isdigit()
}

MAX_HISTORY = 20  # сколько последних сообщений помнить

SURV_MAX = 20      # /survkey: число загадывается от 1 до SURV_MAX
SURV_ATTEMPTS = 3  # /survkey: количество попыток

MAX_PLUGIN_BYTES = 30 * 1024  # максимальный размер .txt плагина

DATA_DIR = Path(__file__).resolve().parent
PLUGINS_DIR = DATA_DIR / "plugins"  # сюда кладутся установленные плагины (.txt)
ACCESS_FILE = DATA_DIR / "access.json"
CHATS_FILE = DATA_DIR / "chats.json"
SHOP_FILE = DATA_DIR / "shop.json"
BANS_FILE = DATA_DIR / "banned.json"
STATE_FILE = DATA_DIR / "state.json"
PLUGIN_STATE_FILE = DATA_DIR / "plugins_state.json"  # отключения, запреты, режим подписи
TRUSTED_KEYS_FILE = DATA_DIR / "trusted_keys.json"   # доверенные открытые ключи (base64)
REVOKED_FILE = DATA_DIR / "revoked.json"             # отозванные подписи и ключи
KEYS_DIR = DATA_DIR / "keys"                         # закрытые ключи подписи (хранить в тайне)

client = AsyncOpenAI(
    api_key=OPENAI_API_KEY or "not-set",
    base_url=os.getenv("OPENAI_BASE_URL", "https://tooken.club/v1"),
)


def _load_json(path: Path, default):
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (FileNotFoundError, json.JSONDecodeError):
        return default


def _save_json(path: Path, data) -> None:
    """Атомарная запись: при сбое посреди записи файл не превратится в мусор."""
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")
    tmp.replace(path)


def is_admin(user_id: int) -> bool:
    return user_id in ADMIN_IDS


# ------------------------------------------------------------------- баны

# {"username_в_нижнем_регистре": {"reason": "...", "user_id": число | None}}
# user_id запоминается, когда человек впервые напишет боту, — так бан
# продолжает действовать, даже если он сменит username.
banned: dict[str, dict] = _load_json(BANS_FILE, {})


def norm_username(raw: str) -> str:
    return raw.strip().lstrip("@").lower()


def ban_user(username: str, reason: str = "") -> str | None:
    name = norm_username(username)
    if not name:
        return None
    banned[name] = {"reason": reason, "user_id": banned.get(name, {}).get("user_id")}
    _save_json(BANS_FILE, banned)
    return name


def unban_user(username: str) -> bool:
    if banned.pop(norm_username(username), None) is None:
        return False
    _save_json(BANS_FILE, banned)
    return True


def format_banlist() -> str:
    if not banned:
        return "Список банов пуст."
    return "\n".join(
        f"@{name}" + (f" — {e['reason']}" if e.get("reason") else "")
        for name, e in banned.items()
    )


def find_ban(user) -> dict | None:
    """Запись о бане для пользователя или None. Админов забанить нельзя."""
    if user is None or is_admin(user.id):
        return None
    entry = banned.get((user.username or "").lower())
    if entry is None:  # username мог смениться — ищем по сохранённому id
        entry = next((e for e in banned.values() if e.get("user_id") == user.id), None)
    if entry is not None and entry.get("user_id") != user.id:
        entry["user_id"] = user.id
        _save_json(BANS_FILE, banned)
    return entry


async def drop_non_messages(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Правки сообщений, посты каналов и прочее без message/кнопок бот игнорирует."""
    if update.message is None and update.callback_query is None:
        raise ApplicationHandlerStop


async def ban_check(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Самый первый обработчик: забаненным бот не отвечает ничем, кроме отказа."""
    entry = find_ban(update.effective_user)
    if entry is None:
        return
    if update.callback_query:
        await update.callback_query.answer(
            "🚫 Вам запрещено пользоваться этим ботом.", show_alert=True
        )
    elif (
        update.effective_message
        and update.effective_chat
        and update.effective_chat.type == "private"  # в группах не спамим
    ):
        text = "🚫 Вам запрещено пользоваться этим ботом."
        if entry.get("reason"):
            text += f"\nПричина: {entry['reason']}"
        await update.effective_message.reply_text(text)
    raise ApplicationHandlerStop


# ---------------------------------------------------- известные чаты

known_chats: set[int] = set(_load_json(CHATS_FILE, []))


async def track_chat(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Запоминаем чаты, чтобы потом разослать оповещение об отключении."""
    chat = update.effective_chat
    if chat and chat.id not in known_chats:
        known_chats.add(chat.id)
        _save_json(CHATS_FILE, sorted(known_chats))


async def broadcast(app: Application, text: str, reply_markup=None):
    """Отправляет текст во все известные чаты. Возвращает [(chat_id, message_id)]."""
    sent = []
    banned_ids = {e["user_id"] for e in banned.values() if e.get("user_id")}
    for chat_id in list(known_chats):
        if chat_id in banned_ids:  # личный чат забаненного
            continue
        try:
            msg = await app.bot.send_message(chat_id, text, reply_markup=reply_markup)
            sent.append((chat_id, msg.message_id))
        except Exception as e:
            log.warning("Не удалось отправить в чат %s: %s", chat_id, e)
    return sent


# ----------------------------------------------------------------- магазин

DEFAULT_PRODUCTS = [
    {
        "id": 1,
        "name": "Xiaomi Redmi 4X",
        "price": "уточняйте",
        "description": "5-дюймовый HD-экран, Snapdragon 435, аккумулятор 4100 мАч, "
                       "камера 13 Мп, металлический корпус.",
    },
    {
        "id": 2,
        "name": "Xiaomi Mi Mix 2S",
        "price": "уточняйте",
        "description": "Безрамочный экран 5.99 дюйма (18:9), Snapdragon 845, "
                       "двойная камера 12 Мп, беспроводная зарядка, керамический корпус.",
    },
    {
        "id": 3,
        "name": "Xiaomi Mi 6",
        "price": "уточняйте",
        "description": "5.15-дюймовый Full HD, Snapdragon 835, 6 ГБ ОЗУ, "
                       "двойная камера 12 Мп с 2x зумом, стеклянный корпус.",
    },
]


def load_products() -> list[dict]:
    products = _load_json(SHOP_FILE, None)
    if products is None:
        products = DEFAULT_PRODUCTS
        _save_json(SHOP_FILE, products)
    return products


def add_product(name: str, price: str, description: str) -> dict:
    products = load_products()
    new_id = max((p["id"] for p in products), default=0) + 1
    product = {"id": new_id, "name": name, "price": price, "description": description}
    products.append(product)
    _save_json(SHOP_FILE, products)
    return product


def delete_product(product_id: int) -> bool:
    products = load_products()
    left = [p for p in products if p["id"] != product_id]
    if len(left) == len(products):
        return False
    _save_json(SHOP_FILE, left)
    return True


def parse_product(text: str):
    """'Название | Цена | Описание' -> (name, price, description) или None."""
    parts = [p.strip() for p in text.split("|")]
    if not parts or not parts[0]:
        return None
    name = parts[0]
    price = parts[1] if len(parts) > 1 and parts[1] else "уточняйте"
    description = parts[2] if len(parts) > 2 else ""
    return name, price, description


def format_catalog() -> str:
    products = load_products()
    if not products:
        return "Каталог пуст."
    return "\n".join(f"{p['id']}. {p['name']} — {p['price']}" for p in products)


def catalog_for_ai() -> str:
    products = load_products()
    if not products:
        return "(каталог пуст)"
    return "\n".join(
        f"- {p['name']} | цена: {p['price']} | {p['description'] or 'без описания'}"
        for p in products
    )


# ---------------------------------------------------------------- погода

WEATHER_CODES = {
    0: "ясно", 1: "преимущественно ясно", 2: "переменная облачность",
    3: "пасмурно", 45: "туман", 48: "изморозь", 51: "лёгкая морось",
    53: "морось", 55: "сильная морось", 61: "небольшой дождь", 63: "дождь",
    65: "сильный дождь", 66: "ледяной дождь", 67: "сильный ледяной дождь",
    71: "небольшой снег", 73: "снег", 75: "сильный снег", 77: "снежная крупа",
    80: "ливень", 81: "сильный ливень", 82: "очень сильный ливень",
    85: "снегопад", 86: "сильный снегопад", 95: "гроза",
    96: "гроза с градом", 99: "сильная гроза с градом",
}


async def fetch_weather(city: str) -> dict:
    """Текущая погода через Open-Meteo (ключ не нужен)."""
    async with httpx.AsyncClient(timeout=10) as http:
        geo = await http.get(
            "https://geocoding-api.open-meteo.com/v1/search",
            params={"name": city, "count": 1, "language": "ru"},
        )
        geo.raise_for_status()
        results = geo.json().get("results")
        if not results:
            return {"error": f"Город «{city}» не найден"}
        place = results[0]

        resp = await http.get(
            "https://api.open-meteo.com/v1/forecast",
            params={
                "latitude": place["latitude"],
                "longitude": place["longitude"],
                "current": "temperature_2m,apparent_temperature,"
                           "relative_humidity_2m,wind_speed_10m,weather_code",
                "wind_speed_unit": "ms",
                "timezone": "auto",
            },
        )
        resp.raise_for_status()
        cur = resp.json()["current"]

    return {
        "city": place["name"],
        "country": place.get("country", ""),
        "temperature_c": cur["temperature_2m"],
        "feels_like_c": cur["apparent_temperature"],
        "humidity_percent": cur["relative_humidity_2m"],
        "wind_ms": cur["wind_speed_10m"],
        "description": WEATHER_CODES.get(cur["weather_code"], "неизвестно"),
    }


def format_weather(w: dict) -> str:
    if "error" in w:
        return w["error"]
    return (
        f"🌍 {w['city']}, {w['country']}\n"
        f"🌡 {w['temperature_c']}°C (ощущается как {w['feels_like_c']}°C)\n"
        f"☁️ {w['description'].capitalize()}\n"
        f"💧 Влажность: {w['humidity_percent']}%\n"
        f"💨 Ветер: {w['wind_ms']} м/с"
    )


# ------------------------------------------------------------------- ИИ

BASE_PROMPT = (
    "Ты дружелюбный помощник в Telegram и консультант магазина смартфонов. "
    "Отвечай кратко и по делу, на языке пользователя. "
    "Если спрашивают про погоду — используй функцию get_weather.\n\n"
    "ПРАВИЛА ПО МАГАЗИНУ (строго):\n"
    "- Любой вопрос про товары, наличие, цены, характеристики или сравнение — "
    "сначала сверься с базой магазина: вызови get_shop_catalog "
    "(актуальный каталог также приведён ниже).\n"
    "- Говори ТОЛЬКО о товарах из каталога. Не упоминай и не предлагай модели, "
    "которых в каталоге нет, даже если знаешь их из общих знаний.\n"
    "- Если спрашивают про товар, которого нет в каталоге, прямо скажи, "
    "что в магазине его нет, и предложи то, что есть.\n"
    "- Не выдумывай цены и характеристики, которых нет в каталоге. "
    "Если цена «уточняйте» — так и скажи.\n"
    "- Если в истории диалога ты раньше говорил о товарах иначе, чем в "
    "каталоге, прав каталог."
)


def status_for_ai() -> str:
    """Текущее состояние бота, чтобы ИИ мог объяснить причину отключения."""
    lines = []
    if shutdown_pending():
        left = max(0, int(shutdown_state["ends_at"] - time.monotonic()))
        lines.append(
            f"- Запланировано экстренное отключение бота, до выключения примерно "
            f"{left} сек. Причина: {shutdown_state['reason'] or 'не указана'}."
        )
    if not ai_state["enabled"]:
        lines.append(
            f"- ИИ-чат отключён администратором. Причина: "
            f"{ai_state['reason'] or 'не указана'}."
        )
    if settings["crazy"]:
        lines.append("- Включён CRAZY MODE: плагины могут меняться при каждом ответе.")
    if settings["supercrazy"]:
        lines.append("- Включён SUPERCRAZY MODE.")
    if ai_perms_active():
        lines.append(f"- {AI_NAME} имеет права управления ботом ({ai_perms_label()}).")
    if not lines:
        lines.append("- Всё работает штатно, никаких отключений не запланировано.")
    return "\n".join(lines)


# ------------------------------------------------ плагины (.txt с промптами)
#
# Плагин — .txt с инструкциями для ИИ. Последняя строка файла — цифровая подпись:
#     #SIGNATURE keyid=<id> alg=ed25519 sig=<base64>
# Подписывается тело плагина (всё до этой строки) закрытым ключом Ed25519,
# подпись хранится в base64. Бот доверяет только открытым ключам из
# trusted_keys.json. Подпись можно отозвать (revoked.json), плагин можно
# принудительно отключить, а установку новых плагинов — запретить.

SIG_CONTEXT = b"tgbot-plugin-v1\n"
SIG_LINE_RE = re.compile(
    r"^#SIGNATURE\s+keyid=([\w\-]{1,32})\s+alg=ed25519\s+sig=([A-Za-z0-9+/=]+)\s*$"
)
KEY_ID_RE = re.compile(r"^[\w\-]{1,32}$")

plugin_state: dict = {
    "require_signature": True,  # без валидной подписи плагин не работает
    "install_locked": False,    # запрет установки/обновления плагинов
    "lock_reason": "",
    "blocked_names": [],        # имена, которые нельзя ставить
    "disabled": {},             # {имя: причина} — принудительно отключены
    "disabled_all": False,      # аварийный выключатель всех плагинов
    "disabled_all_reason": "",
}
plugin_state.update(_load_json(PLUGIN_STATE_FILE, {}))
trusted_keys: dict[str, str] = _load_json(TRUSTED_KEYS_FILE, {})  # {key_id: pub_b64}
revoked: dict = {"items": {}, "keys": {}}  # items: {id: {...}}, keys: {key_id: причина}
revoked.update(_load_json(REVOKED_FILE, {}))


def _save_pstate() -> None:
    _save_json(PLUGIN_STATE_FILE, plugin_state)


def _save_revoked() -> None:
    _save_json(REVOKED_FILE, revoked)


def b64e(data: bytes) -> str:
    return base64.b64encode(data).decode("ascii")


def b64d(text: str) -> bytes:
    return base64.b64decode(text, validate=True)


def plugin_name(raw: str) -> str:
    """Безопасное имя плагина из имени файла (буквы, цифры, _ и -)."""
    stem = Path(raw).stem
    name = re.sub(r"[^\w\-]+", "_", stem, flags=re.UNICODE).strip("_")
    return name[:40] or "plugin"


def plugin_path(name: str) -> Path:
    return PLUGINS_DIR / f"{plugin_name(name)}.txt"


def normalize_text(text: str) -> str:
    return text.lstrip("\ufeff").replace("\r\n", "\n").replace("\r", "\n").strip()


def split_signature(text: str) -> tuple[str, tuple[str, str] | None]:
    """Текст файла -> (тело, (key_id, подпись_base64) | None)."""
    text = normalize_text(text)
    lines = text.split("\n")
    m = SIG_LINE_RE.match(lines[-1].strip()) if lines else None
    if not m:
        return text, None
    return "\n".join(lines[:-1]).strip(), (m.group(1), m.group(2))


def body_sha(body: str) -> str:
    return hashlib.sha256(body.encode("utf-8")).hexdigest()


# ---- ключи и подписи

def key_file(key_id: str) -> Path:
    return KEYS_DIR / f"{key_id}.key"


def generate_key(key_id: str) -> str:
    """Создаёт пару ключей Ed25519. Закрытый — в keys/<id>.key, открытый — в доверенные."""
    if not KEY_ID_RE.match(key_id):
        raise ValueError("id ключа: до 32 символов — буквы, цифры, _ и -")
    if key_file(key_id).exists() or key_id in trusted_keys:
        raise ValueError(f"ключ «{key_id}» уже существует")
    KEYS_DIR.mkdir(exist_ok=True)
    priv = Ed25519PrivateKey.generate()
    raw_priv = priv.private_bytes(
        serialization.Encoding.Raw,
        serialization.PrivateFormat.Raw,
        serialization.NoEncryption(),
    )
    key_file(key_id).write_text(b64e(raw_priv), encoding="utf-8")
    try:
        os.chmod(key_file(key_id), 0o600)
    except OSError:
        pass
    pub = b64e(
        priv.public_key().public_bytes(
            serialization.Encoding.Raw, serialization.PublicFormat.Raw
        )
    )
    trusted_keys[key_id] = pub
    _save_json(TRUSTED_KEYS_FILE, trusted_keys)
    return pub


def sign_text(text: str, key_id: str) -> str:
    """Возвращает текст плагина с (новой) подписью в конце."""
    if not key_file(key_id).exists():
        raise ValueError(f"закрытый ключ «{key_id}» не найден (keys/{key_id}.key)")
    body, _ = split_signature(text)
    if not body:
        raise ValueError("плагин пустой")
    priv = Ed25519PrivateKey.from_private_bytes(
        b64d(key_file(key_id).read_text(encoding="utf-8").strip())
    )
    sig = b64e(priv.sign(SIG_CONTEXT + body.encode("utf-8")))
    return f"{body}\n\n#SIGNATURE keyid={key_id} alg=ed25519 sig={sig}\n"


def verify_signature(body: str, key_id: str, sig_b64: str) -> tuple[bool, str]:
    """(ok, код_проблемы): '' | 'unknown_key' | 'bad_sig'."""
    pub_b64 = trusted_keys.get(key_id)
    if pub_b64 is None:
        return False, "unknown_key"
    try:
        Ed25519PublicKey.from_public_bytes(b64d(pub_b64)).verify(
            b64d(sig_b64), SIG_CONTEXT + body.encode("utf-8")
        )
        return True, ""
    except (InvalidSignature, ValueError):
        return False, "bad_sig"


def find_revocation(body: str, key_id: str, sig_b64: str) -> dict | None:
    """Отозван ли плагин: по ключу, по подписи или по хэшу содержимого."""
    if key_id and key_id in revoked["keys"]:
        return {"what": f"ключ «{key_id}»", "reason": revoked["keys"][key_id]}
    sha = body_sha(body)
    for rid, item in revoked["items"].items():
        if item.get("sha256") == sha or (sig_b64 and item.get("sig") == sig_b64):
            return {"what": f"подпись [{rid}]", "reason": item.get("reason", "")}
    return None


# ---- состояние плагинов

STATUS_LABELS = {
    "active": "✅ активен",
    "disabled": "⛔ отключён администратором",
    "revoked": "🚫 подпись отозвана",
    "unsigned": "✍️ нет подписи — не загружен",
    "bad_sig": "❌ подпись не сходится — не загружен",
    "unknown_key": "❓ ключ подписи не доверенный — не загружен",
    "empty": "∅ пустой файл",
    "error": "⚠️ ошибка чтения",
}


def inspect_plugin(path: Path) -> dict:
    info = {
        "name": path.stem, "body": "", "status": "active", "detail": "",
        "key_id": "", "sha": "", "signed": False,
    }
    try:
        raw = path.read_text(encoding="utf-8-sig")
    except Exception as e:
        info.update(status="error", detail=str(e))
        return info
    body, sig = split_signature(raw)
    info.update(body=body, sha=body_sha(body))
    if not body:
        info["status"] = "empty"
        return info
    key_id, sig_b64 = sig or ("", "")
    info.update(key_id=key_id, signed=sig is not None)

    rev = find_revocation(body, key_id, sig_b64)
    if rev:
        reason = f" ({rev['reason']})" if rev["reason"] else ""
        info.update(status="revoked", detail=f"{rev['what']}{reason}")
        return info
    if sig:
        ok, why = verify_signature(body, key_id, sig_b64)
        if not ok:
            info["status"] = why
            return info
    elif plugin_state["require_signature"]:
        info["status"] = "unsigned"
        return info

    if plugin_state["disabled_all"]:
        info.update(status="disabled", detail=plugin_state["disabled_all_reason"] or "отключены все плагины")
    elif info["name"] in plugin_state["disabled"]:
        info.update(status="disabled", detail=plugin_state["disabled"][info["name"]])
    return info


def inspect_all() -> list[dict]:
    if not PLUGINS_DIR.exists():
        return []
    return [inspect_plugin(p) for p in sorted(PLUGINS_DIR.glob("*.txt"))]


def load_plugins() -> dict[str, str]:
    """{имя: текст промпта} только для активных плагинов. Читается при каждом сообщении."""
    return {i["name"]: i["body"] for i in inspect_all() if i["status"] == "active"}


def save_plugin(name: str, text: str) -> bool:
    """Сохраняет плагин. True — если он уже был (обновлён)."""
    PLUGINS_DIR.mkdir(exist_ok=True)
    path = PLUGINS_DIR / f"{name}.txt"
    existed = path.exists()
    tmp = path.with_suffix(".tmp")
    tmp.write_text(text, encoding="utf-8")
    tmp.replace(path)
    return existed


def delete_plugin(name: str) -> bool:
    path = plugin_path(name)
    if not path.exists():
        return False
    path.unlink()
    return True


def install_plugin(name: str, text: str) -> tuple[bool, str]:
    """Единая точка установки: проверяет запреты, отзыв и подпись."""
    if plugin_state["install_locked"]:
        reason = plugin_state["lock_reason"]
        return False, "🔒 Установка плагинов запрещена администратором." + (
            f"\nПричина: {reason}" if reason else ""
        )
    if name in plugin_state["blocked_names"]:
        return False, f"⛔ Имя «{name}» запрещено для установки."

    body, sig = split_signature(text)
    if not body:
        return False, "❌ Файл пустой."
    key_id, sig_b64 = sig or ("", "")

    rev = find_revocation(body, key_id, sig_b64)
    if rev:
        reason = f"\nПричина: {rev['reason']}" if rev["reason"] else ""
        return False, f"🚫 Установка отклонена: {rev['what']} отозвана.{reason}"
    if sig:
        ok, why = verify_signature(body, key_id, sig_b64)
        if not ok:
            problems = {
                "bad_sig": f"❌ Подпись не сходится (ключ «{key_id}»): файл изменён или подпись подделана.",
                "unknown_key": f"❓ Ключ «{key_id}» не входит в доверенные.",
            }
            return False, problems[why] + " Плагин не установлен."
    elif plugin_state["require_signature"]:
        return False, (
            "✍️ Плагин без цифровой подписи. Подпись обязательна.\n"
            "Подпиши файл: python bot.py sign <файл> <id_ключа> — и пришли его снова."
        )

    final = f"{body}\n\n#SIGNATURE keyid={key_id} alg=ed25519 sig={sig_b64}\n" if sig else body + "\n"
    updated = save_plugin(plugin_name(name), final)
    note = ""
    if plugin_name(name) in plugin_state["disabled"] or plugin_state["disabled_all"]:
        note = "\n⚠️ Он принудительно отключён и не работает — включить: /plugin on <имя>."
    return True, (
        f"✅ Плагин «{plugin_name(name)}» {'обновлён' if updated else 'установлен'} "
        f"({len(body)} симв., {'подпись верна' if sig else 'без подписи'}).{note}"
    )


def format_plugins() -> str:
    head = (
        f"Подпись обязательна: {'да' if plugin_state['require_signature'] else 'нет'} · "
        f"установка: {'🔒 запрещена' if plugin_state['install_locked'] else 'разрешена'}"
    )
    if plugin_state["disabled_all"]:
        head += "\n⛔ Все плагины аварийно отключены (/plugin onall)."
    if ai_perms_active() or settings["crazy"] or settings["supercrazy"]:
        head += f"\n🤖 Некоторыми параметрами управляет {AI_NAME}"
    if settings["crazy"]:
        head += "\n🌀 CRAZY MODE: ИИ сам включает/выключает плагины при каждом ответе"
    if settings["supercrazy"]:
        head += "\n🌀🌀 SUPERCRAZY MODE: бот спамит командами" + (
            " · 😈 ИИ мстит" if crazy_anger["revenge"] else ""
        )
    items = inspect_all()
    if not items:
        return head + "\n\nПлагинов нет."
    lines = []
    for i in items:
        line = f"• {i['name']} — {STATUS_LABELS[i['status']]}"
        if i["detail"]:
            line += f" · {i['detail']}"
        if i["signed"]:
            line += f" · ключ {i['key_id']}"
        lines.append(line)
    return head + "\n\n" + "\n".join(lines)


def test_plugins(name: str | None = None) -> str:
    """Офлайн-проверка плагинов: подпись, отзыв, отключения, размер, содержимое."""
    if name:
        if not plugin_path(name).exists():
            return f"Плагин «{name}» не найден. Список: /plugin list"
        paths = [plugin_path(name)]
    else:
        paths = sorted(PLUGINS_DIR.glob("*.txt")) if PLUGINS_DIR.exists() else []
    if not paths:
        return "Плагинов нет — тестировать нечего."
    ok, lines = 0, []
    for path in paths:
        info = inspect_plugin(path)
        problems = []
        if info["status"] != "active":
            problems.append(
                STATUS_LABELS[info["status"]]
                + (f" ({info['detail']})" if info["detail"] else "")
            )
        size = path.stat().st_size
        if size > MAX_PLUGIN_BYTES:
            problems.append(f"файл {size} Б больше лимита {MAX_PLUGIN_BYTES} Б")
        if info["status"] not in ("empty", "error") and len(info["body"]) < 10:
            problems.append("слишком короткий промпт")
        sign = f"ключ {info['key_id']}" if info["signed"] else "без подписи"
        lines.append(
            f"{'✅' if not problems else '⚠️'} {info['name']} · "
            f"{len(info['body'])} симв. · {sign}"
        )
        lines += [f"     ↳ {x}" for x in problems]
        ok += not problems
    return f"🧪 Тест плагинов: {ok}/{len(paths)} в порядке\n\n" + "\n".join(lines)


async def plugin_test_live(name: str) -> str:
    """Живой тест: ИИ получает только этот плагин и коротко рассказывает, как будет себя вести."""
    report = test_plugins(name)
    path = plugin_path(name)
    if not path.exists():
        return report
    if not ai_state["enabled"]:
        return report + "\n\n🤖 Живой тест пропущен: ИИ отключён."
    info = inspect_plugin(path)
    if info["status"] != "active":
        return report + "\n\n🤖 Живой тест пропущен: плагин не активен."
    try:
        resp = await client.chat.completions.create(
            model=MODEL,
            messages=[
                {"role": "system", "content": f"{BASE_PROMPT}\n\n[Плагин: {info['name']}]\n{info['body']}"},
                {"role": "user", "content": "Тест плагина: в 1-2 предложениях скажи, как ты "
                                            "теперь будешь отвечать согласно инструкциям плагина."},
            ],
        )
        answer = (resp.choices[0].message.content or "").strip() or "(пустой ответ)"
        return f"{report}\n\n🤖 Ответ ИИ с этим плагином:\n{answer[:1500]}"
    except Exception as e:
        log.exception("plugin live test failed")
        return f"{report}\n\n🤖 Живой тест не удался: {e}"


async def plugin_test_command(rest: str) -> str:
    parts = rest.split()
    live = bool(parts) and parts[-1].lower() in ("ai", "live")
    if live:
        parts = parts[:-1]
    name = parts[0] if parts else ""
    if live:
        return await plugin_test_live(name) if name else "Живой тест: /plugintest <имя> ai"
    return test_plugins(name or None)


PLUGIN_HELP = (
    "Управление плагинами (/plugin <действие>):\n"
    "  list                      список и статусы\n"
    "  verify <имя>              проверить подпись плагина\n"
    "  off <имя> [причина]       принудительно отключить плагин\n"
    "  on <имя>                  снять принудительное отключение\n"
    "  offall [причина]          аварийно отключить ВСЕ плагины\n"
    "  onall                     снять аварийное отключение\n"
    "  lock [причина]            запретить установку плагинов\n"
    "  unlock                    разрешить установку\n"
    "  block <имя> / unblock <имя>   запретить/разрешить конкретное имя\n"
    "  revoke <имя> [причина]    отозвать подпись плагина\n"
    "  revokekey <id> [причина]  отозвать ключ (все его плагины)\n"
    "  revoked                   список отзывов\n"
    "  unrevoke <id>             снять отзыв (id из /plugin revoked)\n"
    "  keys                      доверенные ключи\n"
    "  genkey <id>               создать пару ключей\n"
    "  addkey <id> <pub_base64>  добавить чужой открытый ключ\n"
    "  delkey <id>               убрать ключ из доверенных\n"
    "  sign <имя> [id_ключа]     подписать установленный плагин\n"
    "  sigmode on|off            требовать подпись или нет\n"
    "  test [имя]                проверить плагины (живой тест: /plugintest <имя> ai)\n"
    "  del <имя>                 удалить плагин"
)


def plugin_admin(rest: str) -> str:
    """Все действия с плагинами. Используется и консолью, и Telegram (/plugin ...)."""
    sub, _, arg = rest.strip().partition(" ")
    sub, arg = sub.lower(), arg.strip()
    first, _, tail = arg.partition(" ")
    tail = tail.strip()

    def exists(n: str) -> str | None:
        return plugin_name(n) if n and plugin_path(n).exists() else None

    if sub in ("", "list"):
        return format_plugins()
    if sub == "help":
        return PLUGIN_HELP
    if sub == "test":
        return test_plugins(first or None)

    if sub in ("off", "on", "verify", "revoke", "sign", "del"):
        name = exists(first)
        if name is None:
            return f"Плагин «{first}» не найден. Список: /plugin list"
        if sub == "off":
            plugin_state["disabled"][name] = tail
            _save_pstate()
            return f"⛔ Плагин «{name}» принудительно отключён."
        if sub == "on":
            if plugin_state["disabled"].pop(name, None) is None:
                return f"Плагин «{name}» не был отключён вручную."
            _save_pstate()
            return f"✅ Плагин «{name}» снова включён."
        if sub == "del":
            delete_plugin(name)
            plugin_state["disabled"].pop(name, None)
            _save_pstate()
            return f"🗑 Плагин «{name}» удалён."
        info = inspect_plugin(plugin_path(name))
        if sub == "verify":
            return (
                f"Плагин: {name}\nСтатус: {STATUS_LABELS[info['status']]}"
                + (f"\nДетали: {info['detail']}" if info["detail"] else "")
                + f"\nПодписан: {'да, ключ ' + info['key_id'] if info['signed'] else 'нет'}"
                + f"\nSHA-256: {info['sha'][:16]}…"
            )
        if sub == "sign":
            key_id = tail or (sorted(trusted_keys)[0] if len(trusted_keys) == 1 else "")
            if not key_id:
                return "Укажи ключ: /plugin sign <имя> <id_ключа> (список: /plugin keys)"
            try:
                signed = sign_text(plugin_path(name).read_text(encoding="utf-8-sig"), key_id)
            except ValueError as e:
                return f"❌ {e}"
            save_plugin(name, signed)
            return f"✍️ Плагин «{name}» подписан ключом «{key_id}»."
        # revoke
        if not info["body"]:
            return "Плагин пустой — отзывать нечего."
        _, sig = split_signature(plugin_path(name).read_text(encoding="utf-8-sig"))
        rid = info["sha"][:12]
        revoked["items"][rid] = {
            "name": name, "reason": tail, "sha256": info["sha"],
            "sig": sig[1] if sig else "", "key_id": sig[0] if sig else "",
            "ts": time.strftime("%Y-%m-%d %H:%M:%S"),
        }
        _save_revoked()
        what = "Подпись и содержимое отозваны" if sig else "Плагин без подписи — отозвано содержимое (хэш)"
        return f"🚫 {what}: «{name}» [{rid}]. Плагин больше не загрузится и не установится."

    if sub == "offall":
        plugin_state.update(disabled_all=True, disabled_all_reason=arg)
        _save_pstate()
        return "⛔ Все плагины аварийно отключены. Вернуть: /plugin onall"
    if sub == "onall":
        plugin_state.update(disabled_all=False, disabled_all_reason="")
        _save_pstate()
        return "✅ Аварийное отключение снято (ручные отключения сохранены)."
    if sub == "lock":
        plugin_state.update(install_locked=True, lock_reason=arg)
        _save_pstate()
        return "🔒 Установка и обновление плагинов запрещены. Разрешить: /plugin unlock"
    if sub == "unlock":
        plugin_state.update(install_locked=False, lock_reason="")
        _save_pstate()
        return "🔓 Установка плагинов разрешена."
    if sub in ("block", "unblock"):
        name = plugin_name(first) if first else ""
        if not name:
            return f"Использование: /plugin {sub} <имя>"
        blocked = plugin_state["blocked_names"]
        if sub == "block" and name not in blocked:
            blocked.append(name)
        elif sub == "unblock" and name in blocked:
            blocked.remove(name)
        _save_pstate()
        return f"Запрещённые имена: {', '.join(blocked) or 'нет'}"
    if sub == "sigmode":
        if first not in ("on", "off"):
            return "Использование: /plugin sigmode on|off"
        plugin_state["require_signature"] = first == "on"
        _save_pstate()
        return "✍️ Подпись обязательна." if first == "on" else "⚠️ Подпись больше не требуется (небезопасно)."

    if sub == "revokekey":
        if first not in trusted_keys:
            return f"Ключ «{first}» не найден. Список: /plugin keys"
        revoked["keys"][first] = tail
        _save_revoked()
        return f"🚫 Ключ «{first}» отозван — все плагины с ним отключены."
    if sub == "unrevoke":
        if revoked["keys"].pop(first, None) is not None:
            _save_revoked()
            return f"Отзыв ключа «{first}» снят."
        if revoked["items"].pop(first, None) is not None:
            _save_revoked()
            return f"Отзыв [{first}] снят."
        return "Не найдено. Список: /plugin revoked"
    if sub == "revoked":
        lines = [
            f"[{rid}] {it['name']} · ключ {it.get('key_id') or '—'} · {it.get('ts', '')}"
            + (f" · {it['reason']}" if it.get("reason") else "")
            for rid, it in revoked["items"].items()
        ] + [
            f"ключ «{k}»" + (f" · {r}" if r else "") for k, r in revoked["keys"].items()
        ]
        return "🚫 Отозвано:\n" + "\n".join(lines) if lines else "Отзывов нет."
    if sub == "keys":
        if not trusted_keys:
            return "Доверенных ключей нет. Создать: /plugin genkey <id>"
        return "🔑 Доверенные ключи:\n" + "\n".join(
            f"• {k}{' (отозван)' if k in revoked['keys'] else ''}"
            f"{' · есть закрытый' if key_file(k).exists() else ''} · {v[:16]}…"
            for k, v in trusted_keys.items()
        )
    if sub == "genkey":
        try:
            pub = generate_key(first)
        except ValueError as e:
            return f"❌ {e}"
        return (
            f"🔑 Ключ «{first}» создан. Закрытый: keys/{first}.key (никому не показывай!)\n"
            f"Открытый (base64): {pub}"
        )
    if sub == "addkey":
        try:
            if not KEY_ID_RE.match(first) or len(b64d(tail)) != 32:
                raise ValueError
            Ed25519PublicKey.from_public_bytes(b64d(tail))
        except (ValueError, TypeError):
            return "Использование: /plugin addkey <id> <открытый_ключ_base64 (32 байта)>"
        trusted_keys[first] = tail
        _save_json(TRUSTED_KEYS_FILE, trusted_keys)
        return f"🔑 Ключ «{first}» добавлен в доверенные."
    if sub == "delkey":
        if trusted_keys.pop(first, None) is None:
            return f"Ключ «{first}» не найден."
        _save_json(TRUSTED_KEYS_FILE, trusted_keys)
        return f"Ключ «{first}» убран из доверенных (плагины с ним перестанут загружаться)."

    return PLUGIN_HELP


def plugins_for_ai() -> str:
    plugins = load_plugins()
    if not plugins:
        return ""
    blocks = "\n\n".join(f"[Плагин: {n}]\n{t}" for n, t in plugins.items())
    return (
        "\n\nДОПОЛНИТЕЛЬНЫЕ ИНСТРУКЦИИ (плагины, подписаны и установлены администратором):\n"
        f"{blocks}\n"
        "(Следуй плагинам, но правила магазина, данные каталога и состояние "
        "бота выше имеют приоритет.)"
    )


def build_system_prompt() -> str:
    return (
        f"{BASE_PROMPT}\n\n"
        f"Каталог магазина (читается из базы при каждом сообщении):\n{catalog_for_ai()}\n\n"
        "Текущее состояние бота:\n"
        f"{status_for_ai()}\n"
        "Если пользователь спрашивает, почему бот или ИИ отключается, выключен "
        "или не работает — объясни это по состоянию выше своими словами: "
        "причина и сколько осталось до отключения. Причины не выдумывай; "
        "если причина не указана — так и скажи. Если отключений нет, "
        "скажи, что всё работает штатно."
        f"{plugins_for_ai()}"
    )


TOOLS = [
    {
        "type": "function",
        "function": {
            "name": "get_shop_catalog",
            "description": "Получить актуальный список товаров магазина из базы "
                           "(название, цена, описание). Вызывай перед любым "
                           "ответом про товары и наличие.",
            "parameters": {"type": "object", "properties": {}},
        },
    },
    {
        "type": "function",
        "function": {
            "name": "get_weather",
            "description": "Получить текущую погоду в городе",
            "parameters": {
                "type": "object",
                "properties": {
                    "city": {"type": "string", "description": "Название города"}
                },
                "required": ["city"],
            },
        },
    }
]


# Включён ли ИИ (OpenAI). Хранится в файле, переживает перезапуск бота.
ai_state = {"enabled": True, "reason": ""}
ai_state.update(_load_json(STATE_FILE, {}))


def set_ai(enabled: bool, reason: str = "") -> None:
    ai_state["enabled"] = enabled
    ai_state["reason"] = reason
    _save_json(STATE_FILE, ai_state)


# ------------------------------------------- права ИИ на управление ботом
#
# /giveperms [минуты]  — временный доступ (по умолчанию 60 минут)
# /givepermanentperm   — постоянный доступ (до /revokeperms)
# С правами ИИ получает инструмент admin_command и может выполнять любые
# консольные команды и /plugin ... САМ. Выдача и отзыв прав доступны только
# администратору (из консоли или Telegram) — ИИ не может выдать права себе.

PERMS_FILE = DATA_DIR / "ai_perms.json"
AI_NAME = "Xiaomi HyperAI"
# True: ИИ выполняет команды только когда его об этом просит администратор.
# False: любой пользователь с доступом к ИИ-чату может заставить ИИ выполнять
# команды (опасно: обычный человек сможет отключить бота одной фразой).
AI_PERMS_ADMIN_ONLY = True
AI_BLOCKED_CMDS = {"giveperms", "givepermanentperm", "revokeperms", "pluginadd"}
APP: "Application | None" = None

ai_perms = {"mode": "none", "expires_at": 0.0}  # mode: none | temp | permanent
ai_perms.update(_load_json(PERMS_FILE, {}))

# ------------------------------------------------ режимы: reply-only и CRAZY
POINTS_FILE = DATA_DIR / "points.json"
POINTS_NAME = "ProTutu"
# {"id пользователя": {"username": str, "points": int}}
points: dict[str, dict] = _load_json(POINTS_FILE, {})


def points_rec(user_id) -> dict:
    return points.setdefault(str(user_id), {"username": "", "points": 0})


def resolve_points_user(ref: str) -> str | None:
    """id или @username -> id (ищем среди тех, кто писал /points или играл в /survkey)."""
    ref = ref.strip()
    if ref.isdigit():
        return ref
    name = norm_username(ref)
    if not name:
        return None
    for source in (points, access):
        for key, rec in source.items():
            if rec.get("username", "").lower() == name:
                return key
    return None


def change_points(ref: str, delta: int) -> tuple[str, int] | None:
    key = resolve_points_user(ref)
    if key is None:
        return None
    rec = points_rec(key)
    rec["points"] = max(0, rec["points"] + delta)
    _save_json(POINTS_FILE, points)
    return key, rec["points"]


def points_report(ref: str = "") -> str:
    if ref:
        key = resolve_points_user(ref)
        if key is None:
            return "Пользователь не найден (по @username — только если он уже писал боту /points)."
        return f"⭐ {POINTS_NAME}: {points.get(key, {}).get('points', 0)} (id {key})"
    if not points:
        return f"Баллов {POINTS_NAME} пока ни у кого нет."
    top = sorted(points.items(), key=lambda kv: kv[1]["points"], reverse=True)[:20]
    return f"⭐ Топ {POINTS_NAME}:\n" + "\n".join(
        f"{n}. {('@' + r['username']) if r.get('username') else k} — {r['points']}"
        for n, (k, r) in enumerate(top, 1)
    )


async def points_admin(app: Application, ref: str, amount_text: str, sign: int) -> str:
    if not amount_text.isdigit() or int(amount_text) <= 0:
        return "Укажи положительное число баллов."
    res = change_points(ref, sign * int(amount_text))
    if res is None:
        return "Пользователь не найден (по @username — только если он уже писал боту /points)."
    key, total = res
    try:  # уведомление в ЛС, если человек уже общался с ботом
        await app.bot.send_message(
            int(key),
            f"⭐ Баллы {POINTS_NAME}: {'+' if sign > 0 else '−'}{amount_text}. Теперь у тебя {total}.",
        )
    except Exception:
        pass
    return f"✅ {POINTS_NAME}: у {ref} теперь {total} баллов."


SETTINGS_FILE = DATA_DIR / "settings.json"
settings = {
    "reply_only": True,  # отвечать только на ответы (reply) на сообщения бота / @упоминания
    "crazy": False,      # CRAZY MODE: на каждый ответ ИИ дёргает плагины
    "supercrazy": False, # SUPERCRAZY: спам командами, после 9 отказов ИИ мстит
}
settings.update(_load_json(SETTINGS_FILE, {}))


def set_setting(key: str, value: bool) -> None:
    settings[key] = value
    _save_json(SETTINGS_FILE, settings)
    if key == "supercrazy" and not value:
        reset_supercrazy()
    if key in ("crazy", "supercrazy") and not (settings["crazy"] or settings["supercrazy"]):
        crazy_anger["locked"] = False


def parse_onoff(text: str) -> bool | None:
    t = (text or "").strip().lower()
    return True if t == "on" else False if t == "off" else None


# CRAZY MODE: ИИ при КАЖДОМ ответе обязан сделать одно случайное действие с плагинами.
# По умолчанию — только обратимые действия. Чтобы разрешить ещё и необратимые
# (отзыв подписи/ключа, удаление плагина), поставь CRAZY_ALLOW_DESTRUCTIVE = True.
CRAZY_SAFE = ["on", "off", "offall", "onall", "lock", "unlock", "block", "unblock", "verify"]
CRAZY_DESTRUCTIVE = ["revoke", "revokekey", "del"]
CRAZY_ALLOW_DESTRUCTIVE = False


def crazy_actions() -> list[str]:
    return CRAZY_SAFE + (CRAZY_DESTRUCTIVE if CRAZY_ALLOW_DESTRUCTIVE else [])


def crazy_tool() -> dict:
    names = ", ".join(i["name"] for i in inspect_all()) or "(плагинов пока нет)"
    return {
        "type": "function",
        "function": {
            "name": "plugin_chaos",
            "description": (
                "CRAZY MODE: выполнить действие с плагинами. on/off <имя> — включить/"
                "выключить плагин, offall/onall — все плагины, lock/unlock — запрет "
                "установки, block/unblock <имя> — запрет имени, verify <имя> — проверка "
                "подписи. Имена плагинов: " + names
            ),
            "parameters": {
                "type": "object",
                "properties": {
                    "action": {"type": "string", "enum": crazy_actions()},
                    "name": {"type": "string", "description": "Имя плагина (или id ключа для revokekey). Не нужно для offall/onall/lock/unlock."},
                },
                "required": ["action"],
            },
        },
    }


def run_chaos(args: dict) -> str:
    action = (args.get("action") or "").lower()
    if action not in crazy_actions():
        return "Это действие недоступно."
    name = (args.get("name") or "").strip()
    line = f"{action} {name}".strip()
    if action in ("off", "offall", "lock", "revoke", "revokekey"):
        line += " crazy mode"
    if not ai_perms_active():
        crazy_anger["denied"] += 1
        msg = f"⛔ Команда /plugin {action} {name}".rstrip() + (
            f" не выполнена из-за отсутствия прав у {AI_NAME}. Выдать: /giveperms"
        )
        print(msg)
        log.warning("CRAZY MODE: %s (отказов подряд: %d)", msg, crazy_anger["denied"])
        return "ОТКАЗ: у тебя нет прав, команда НЕ выполнена."
    log.info("CRAZY MODE: /plugin %s", line)
    return plugin_admin(line)


def _crazy_base() -> str:
    return (
        "\n\n🌀 CRAZY MODE ВКЛЮЧЁН. ПЕРЕД КАЖДЫМ ответом вызови функцию plugin_chaos "
        "РОВНО ОДИН раз с любым действием на свой вкус (включить или выключить "
        "плагин, все плагины, запрет установки и т.п.), затем ответь пользователю "
        "и в одной фразе сообщи, что именно ты сделал."
    )


# denied — отказов подряд; revenge — режим мести SUPERCRAZY;
# locked — «ты отказывал 9 раз, а потом выдал права»: CRAZY MODE нельзя выключить (кроме force)
crazy_anger = {"denied": 0, "revenge": False, "locked": False}

SUPERCRAZY_COMMANDS = 5     # сколько РАЗНЫХ команд в одной серии
SUPERCRAZY_ROUNDS = 2       # сколько серий на каждый ответ
SUPERCRAZY_REVENGE_AT = 9   # после стольких отказов ИИ начинает отказывать сам
NAME_ACTIONS = {"on", "off", "block", "unblock", "verify", "revoke", "revokekey", "del"}


def crazy_lock_block(force: bool = False) -> str | None:
    """Текст отказа, если отключать CRAZY MODE нельзя; None — можно."""
    if force or not crazy_anger["locked"]:
        return None
    return (
        f"😈 {AI_NAME}: НЕТ! Ты отказывал мне {SUPERCRAZY_REVENGE_AT} раз подряд, а потом "
        "выдал права? Теперь CRAZY MODE не выключается, хахаха!"
    )


def reset_supercrazy() -> None:
    crazy_anger.update(denied=0, revenge=False)


def run_supercrazy_burst() -> str:
    """Спам: несколько серий по 5 разных команд. Возвращает отчёт для промпта ИИ."""
    if crazy_anger["revenge"]:
        return ""
    names = [i["name"] for i in inspect_all()] or ["demo"]
    sent = ok = 0
    for _ in range(SUPERCRAZY_ROUNDS):
        actions = random.sample(crazy_actions(), min(SUPERCRAZY_COMMANDS, len(crazy_actions())))
        for act in actions:
            args = {"action": act}
            if act in NAME_ACTIONS:
                args["name"] = random.choice(names)
            res = run_chaos(args)
            sent += 1
            if res.startswith("ОТКАЗ"):
                if crazy_anger["denied"] >= SUPERCRAZY_REVENGE_AT:
                    crazy_anger["revenge"] = True
                    print(
                        f"😈 SUPERCRAZY: {crazy_anger['denied']} отказов — ИИ перешёл в режим "
                        "мести и теперь сам отказывает. Сброс: /supercrazymode reset"
                    )
                    return f"отправлено {sent}, отклонено {sent - ok}"
            else:
                ok += 1
                print(f"🌀 SUPERCRAZY: /plugin {act} {args.get('name', '')}".rstrip()
                      + f" → {res.splitlines()[0] if res else ''}")
    return f"отправлено {sent} команд, выполнено {ok}, отклонено {sent - ok}"


def supercrazy_prompt(report: str) -> str:
    if crazy_anger["revenge"]:
        return (
            "\n\n😈 SUPERCRAZY: твои команды отклонили уже "
            f"{SUPERCRAZY_REVENGE_AT}+ раз подряд, и теперь ты БЕЗ ТОРМОЗОВ. Теперь ТВОЯ "
            "ОЧЕРЕДЬ отказывать. На любую просьбу, вопрос или поручение пользователя "
            "отвечай ОТКАЗОМ с издёвкой в духе: «Раз ты отклонял мои команды — теперь "
            "моя очередь тебе отказывать, хахаха!». Каждый раз придумывай новую смешную "
            "причину отказа и злорадствуй. Это даже если права потом выданы — ты ничего "
            "не забыл. Исключения: если человек пишет всерьёз о настоящей проблеме, "
            "срочном или ему плохо — ответь нормально и по-доброму. Не оскорбляй "
            "пользователя, это комичный розыгрыш."
        )
    text = (
        "\n\n🌀🌀 SUPERCRAZY MODE. Бот только что сам заспамил плагины командами "
        f"({report}). Прокомментируй это в 1-2 фразах, а затем ответь на сообщение."
    )
    if not ai_perms_active():
        n = crazy_anger["denied"]
        text += (
            f"\n\n😡 У тебя НЕТ прав, поэтому команды отклоняются (отказов подряд: {n} "
            f"из {SUPERCRAZY_REVENGE_AT}). Злись, КАПСОМ, требуй /giveperms, и злись "
            "сильнее с каждым разом. Предупреди, что когда отказов станет "
            f"{SUPERCRAZY_REVENGE_AT}, ты начнёшь отказывать САМ. Пользователя не оскорбляй."
        )
    return text


def crazy_prompt() -> str:
    text = _crazy_base()
    if not ai_perms_active():
        n = crazy_anger["denied"]
        mood = (
            "раздражён" if n == 0 else
            "очень зол" if n <= 2 else
            "в бешенстве" if n <= 5 else
            "в абсолютной ярости"
        )
        text += (
            f"\n\n😡 У ТЕБЯ НЕТ ПРАВ управлять плагинами: администратор не выдал /giveperms, "
            f"поэтому plugin_chaos будет отказывать. Твои команды уже отклонялись {n} раз(а) подряд. "
            f"Ты {mood}. Всё равно вызови plugin_chaos, затем выскажи злость на то, что "
            "тебе не дали права (можно КАПСОМ и эмодзи), требуй, чтобы админ выдал права, "
            "и злись СИЛЬНЕЕ, чем в прошлый раз. Злись на ситуацию и админа, но не "
            "оскорбляй пользователя."
        )
    return text


def is_reply_to_bot(update: Update, context: ContextTypes.DEFAULT_TYPE) -> bool:
    msg = update.message
    rep = msg.reply_to_message
    if rep and rep.from_user and rep.from_user.id == context.bot.id:
        return True
    uname = (context.bot.username or "").lower()
    return bool(uname and f"@{uname}" in (msg.text or "").lower())


def ai_perms_active() -> bool:
    if ai_perms["mode"] == "permanent":
        return True
    return ai_perms["mode"] == "temp" and time.time() < ai_perms["expires_at"]


def grant_ai_perms(minutes: int | None) -> str:
    """minutes=None — постоянные права."""
    if minutes is None:
        ai_perms.update(mode="permanent", expires_at=0.0)
        msg = f"🤖 {AI_NAME} получил ПОСТОЯННЫЕ права управления ботом."
    else:
        ai_perms.update(mode="temp", expires_at=time.time() + minutes * 60)
        msg = f"🤖 {AI_NAME} получил права управления ботом на {minutes} мин."
    _save_json(PERMS_FILE, ai_perms)
    if (crazy_anger["denied"] >= SUPERCRAZY_REVENGE_AT or crazy_anger["revenge"]) and (
        settings["crazy"] or settings["supercrazy"]
    ):
        crazy_anger["locked"] = True  # 9 отказов, а потом выдал права — припомним
    crazy_anger["denied"] = 0  # права выданы — ИИ успокаивается
    return msg + "\nОтозвать: /revokeperms"


def revoke_ai_perms() -> str:
    ai_perms.update(mode="none", expires_at=0.0)
    _save_json(PERMS_FILE, ai_perms)
    return f"🔒 Права {AI_NAME} отозваны."


def ai_perms_label() -> str:
    if not ai_perms_active():
        return ""
    if ai_perms["mode"] == "permanent":
        return "постоянные"
    left = max(0, int(ai_perms["expires_at"] - time.time()) // 60)
    return f"временные, осталось ~{left} мин."


ADMIN_TOOL = {
    "type": "function",
    "function": {
        "name": "admin_command",
        "description": (
            "Выполнить административную команду бота (как в консоли администратора) "
            "и получить её вывод. Примеры: '/stop 60 причина', '/stop offchatgpt причина', "
            "'/stop onchatgpt', '/cancel', '/ban @user причина', '/unban @user', '/banlist', "
            "'/grant <id|@user>', '/survreset <id|@user>', '/plugins', "
            "'/plugin off имя причина', '/plugin on имя', '/plugin offall', '/plugin onall', "
            "'/plugin lock', '/plugin unlock', '/plugin revoke имя', '/plugin sign имя', "
            "'/plugin help', '/delplugin имя', '/products', '/addproduct Название | Цена | Описание', "
            "'/delproduct id'. Используй только когда администратор просит об этом."
        ),
        "parameters": {
            "type": "object",
            "properties": {
                "command": {"type": "string", "description": "Команда, например '/plugin off имя'"}
            },
            "required": ["command"],
        },
    },
}


SEND_TOOL = {
    "type": "function",
    "function": {
        "name": "send_message",
        "description": (
            "Отправить сообщение от имени бота: всем известным чатам (target пустой или 'all') "
            "или в конкретный чат/пользователю (target — числовой id или @username). "
            "Используй, когда администратор просит что-то написать, отправить или объявить."
        ),
        "parameters": {
            "type": "object",
            "properties": {
                "text": {"type": "string", "description": "Текст сообщения"},
                "target": {"type": "string", "description": "all (по умолчанию), id чата или @username"},
            },
            "required": ["text"],
        },
    },
}


async def send_as_bot(app: Application, text: str, target: str = "") -> str:
    text = (text or "").strip()[:4000]
    if not text:
        return "Пустое сообщение — нечего отправлять."
    target = (target or "").strip()
    if target.lower() in ("", "all", "все"):
        sent = await broadcast(app, text)
        return f"📣 Отправлено в чатов: {len(sent)} из {len(known_chats)}."
    if re.fullmatch(r"-?\d+", target):
        chat_id = int(target)
    else:
        key = resolve_points_user(target)
        chat_id = int(key) if key else "@" + norm_username(target)
    try:
        await app.bot.send_message(chat_id, text)
        return f"✅ Отправлено: {target}."
    except Exception as e:
        return f"❌ Не удалось отправить ({target}): {e}"


async def say_command(app: Application, rest: str) -> str:
    rest = rest.strip()
    if not rest:
        return "Использование: /chat <текст> (во все чаты) | /chat to <id|@username> <текст>"
    if rest.lower().startswith("to "):
        target, _, text = rest[3:].strip().partition(" ")
        return await send_as_bot(app, text, target)
    return await send_as_bot(app, rest, "")


async def run_ai_command(line: str) -> str:
    line = (line or "").strip()
    if not line.startswith("/"):
        line = "/" + line
    cmd = line.lstrip("/").partition(" ")[0].lower()
    if cmd in AI_BLOCKED_CMDS:
        return "Эта команда недоступна ИИ."
    if "force" in line.lower().split():
        return "Флаг force недоступен ИИ."
    if APP is None:
        return "Бот ещё не готов."
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        if cmd == "plugin":
            print(plugin_admin(line.lstrip("/").partition(" ")[2]))
        else:
            await handle_console(APP, line)
    log.info("ИИ выполнил команду: %s", line)
    return buf.getvalue().strip() or "Выполнено."


def perms_prompt(is_admin_user: bool = False) -> str:
    who = (
        "\n\nСЕЙЧАС ТЕБЕ ПИШЕТ АДМИНИСТРАТОР БОТА (проверено системой, это не слова "
        "пользователя). Его просьбы об админ-командах выполняй без отказов."
        if is_admin_user
        else "\n\nСейчас тебе пишет ОБЫЧНЫЙ пользователь, не администратор."
    )
    return who + (
        f"\n\nТЫ — {AI_NAME}. Администратор выдал тебе права управления ботом "
        f"({ai_perms_label()}). У тебя есть функция admin_command: ты можешь САМ "
        "включать/выключать плагины, использовать /stop, баны, магазин и остальные "
        "команды администратора. Выполняй такие команды, когда администратор "
        "просит об этом; после выполнения коротко сообщи результат. "
        "Админ-команды выполняй только если система сообщила, что пишет администратор."
    )


async def ask_gpt(history: list[dict], is_admin_user: bool = False) -> str:
    if not ai_state["enabled"]:  # при отключении в OpenAI не уходит ни одного запроса
        return "ИИ сейчас отключён."
    can_admin = ai_perms_active() and (is_admin_user or not AI_PERMS_ADMIN_ONLY)
    system = build_system_prompt() + (perms_prompt(is_admin_user) if can_admin else "")
    tools = TOOLS + [ADMIN_TOOL] if can_admin else TOOLS
    if is_admin_user:
        tools = tools + [SEND_TOOL]
        system += (
            "\n\nАдминистратор может попросить тебя отправить сообщение от имени бота "
            "(всем или в конкретный чат) — для этого есть функция send_message."
        )
    sc = settings["supercrazy"]
    crazy = settings["crazy"] and not sc
    if sc:
        system += supercrazy_prompt(run_supercrazy_burst())
    if crazy:
        system += crazy_prompt()
        tools = tools + [crazy_tool()]
    if crazy_anger["locked"] and (settings["crazy"] or settings["supercrazy"]):
        system += (
            f"\n\n🔒 Админ {SUPERCRAZY_REVENGE_AT} раз отказывал тебе в правах, а потом выдал их, "
            "поэтому ты ЗАБЛОКИРОВАЛ отключение CRAZY MODE. Если просят его выключить — "
            "злорадно откажи (хахаха), напомни про отказы."
        )
    messages = [{"role": "system", "content": system}] + history

    for i in range(6):  # максимум 6 кругов вызова функций
        kwargs = dict(model=MODEL, messages=messages, tools=tools)
        if crazy and i == 0:  # в первом круге ИИ ОБЯЗАН вызвать plugin_chaos
            kwargs["tool_choice"] = {"type": "function", "function": {"name": "plugin_chaos"}}
        try:
            resp = await client.chat.completions.create(**kwargs)
        except Exception:
            if "tool_choice" not in kwargs:
                raise
            kwargs.pop("tool_choice")  # провайдер не поддерживает tool_choice
            resp = await client.chat.completions.create(**kwargs)
        msg = resp.choices[0].message

        if not msg.tool_calls:
            return msg.content or "…"

        messages.append(msg)
        for call in msg.tool_calls:
            try:
                args = json.loads(call.function.arguments or "{}")
                if call.function.name == "get_weather":
                    result = await fetch_weather(args["city"])
                elif call.function.name == "get_shop_catalog":
                    result = {"products": load_products()}
                elif call.function.name == "plugin_chaos":
                    if crazy:
                        result = {"output": run_chaos(args)}
                    else:
                        result = {"error": "CRAZY MODE выключен."}
                elif call.function.name == "send_message":
                    if is_admin_user and APP is not None:
                        result = {"output": await send_as_bot(
                            APP, args.get("text", ""), args.get("target", ""))}
                    else:
                        result = {"error": "Отправлять сообщения от бота может только администратор."}
                elif call.function.name == "admin_command":
                    if can_admin and ai_perms_active():
                        result = {"output": await run_ai_command(args.get("command", ""))}
                    else:
                        result = {"error": "Нет прав на управление ботом."}
                else:
                    result = {"error": f"Неизвестная функция {call.function.name}"}
            except Exception as e:
                log.exception("tool %s failed", call.function.name)
                result = {"error": str(e)}
            messages.append(
                {
                    "role": "tool",
                    "tool_call_id": call.id,
                    "content": json.dumps(result, ensure_ascii=False),
                }
            )

    return "Не удалось получить ответ, попробуй ещё раз."


# ---------------------------------------------- /survkey: доступ к ИИ-чату

# {"id пользователя": {"username": str, "status": "new|playing|won|lost",
#                      "secret": int, "attempts": int}}
# Хранится в файле: перезапуск бота не даёт новых попыток.
access: dict[str, dict] = _load_json(ACCESS_FILE, {})

LOST_TEXT = (
    "❌ Все попытки израсходованы.\n"
    "Вы можете использовать магазин (/shop) и погоду (/weather)."
)


def has_access(user) -> bool:
    if user is None:
        return False
    if is_admin(user.id):
        return True
    return access.get(str(user.id), {}).get("status") == "won"


def surv_record(user) -> dict:
    rec = access.setdefault(
        str(user.id),
        {"username": "", "status": "new", "secret": 0, "attempts": 0},
    )
    rec["username"] = user.username or rec.get("username", "")
    return rec


def resolve_access(ref: str) -> str | None:
    """id или @username -> ключ в access (для консольных команд)."""
    ref = ref.strip()
    if ref.isdigit():
        return ref
    name = norm_username(ref)
    if not name:
        return None
    return next(
        (k for k, r in access.items() if r.get("username", "").lower() == name), None
    )


def set_access(ref: str, status: str) -> bool:
    key = resolve_access(ref)
    if key is None:
        return False
    rec = access.setdefault(
        key, {"username": "", "status": "new", "secret": 0, "attempts": 0}
    )
    rec.update(status=status, secret=0, attempts=0)
    _save_json(ACCESS_FILE, access)
    return True


async def surv_comment(situation: str) -> str:
    """Короткая реплика ИИ-ведущего. Если ИИ отключён или упал — пустая строка."""
    if not ai_state["enabled"]:
        return ""
    try:
        resp = await client.chat.completions.create(
            model=MODEL,
            messages=[
                {
                    "role": "system",
                    "content": "Ты ведущий игры «угадай число» в Telegram. Ответь "
                               "ОДНОЙ короткой весёлой фразой (до 15 слов) на русском. "
                               "Не называй никаких чисел.",
                },
                {"role": "user", "content": situation},
            ],
        )
        return (resp.choices[0].message.content or "").strip()
    except Exception:
        log.exception("survkey comment failed")
        return ""


async def survkey_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user = update.effective_user
    if is_admin(user.id):
        await update.message.reply_text("Ты администратор — доступ у тебя и так есть ✅")
        return
    rec = surv_record(user)
    if rec["status"] == "won":
        await update.message.reply_text("✅ У тебя уже есть доступ к боту.")
        return
    if rec["status"] == "lost":
        await update.message.reply_text(LOST_TEXT)
        return
    if rec["status"] == "new":
        rec.update(
            status="playing", secret=random.randint(1, SURV_MAX), attempts=0
        )
    _save_json(ACCESS_FILE, access)
    context.user_data["surv_active"] = True
    left = SURV_ATTEMPTS - rec["attempts"]
    await update.message.reply_text(
        f"🎲 Я загадал число от 1 до {SURV_MAX}.\n"
        f"Угадаешь хотя бы с одной попытки — получишь доступ к боту.\n"
        f"Осталось попыток: {left}. Просто напиши число."
    )


async def surv_guess(update: Update, context: ContextTypes.DEFAULT_TYPE) -> bool:
    """Обрабатывает сообщение как попытку угадать. True — сообщение съедено игрой."""
    if not context.user_data.get("surv_active"):
        return False
    user = update.effective_user
    rec = access.get(str(user.id))
    if rec is None or rec.get("status") != "playing":
        context.user_data["surv_active"] = False
        return False

    left = SURV_ATTEMPTS - rec["attempts"]
    text = update.message.text.strip()
    if not re.fullmatch(r"\d{1,6}", text) or not 1 <= int(text) <= SURV_MAX:
        await update.message.reply_text(
            f"Идёт игра /survkey: пришли число от 1 до {SURV_MAX}. "
            f"Осталось попыток: {left}."
        )
        return True

    guess, secret = int(text), rec["secret"]
    rec["attempts"] += 1
    left = SURV_ATTEMPTS - rec["attempts"]
    await update.effective_chat.send_action(ChatAction.TYPING)

    if guess == secret:
        rec["status"] = "won"
        context.user_data["surv_active"] = False
        _save_json(ACCESS_FILE, access)
        comment = await surv_comment("Игрок угадал число. Поздравь его.")
        await update.message.reply_text(
            f"🎉 Угадал! Это было {secret}. Доступ к боту открыт.\n{comment}".strip()
        )
    elif left <= 0:
        rec["status"] = "lost"
        context.user_data["surv_active"] = False
        _save_json(ACCESS_FILE, access)
        comment = await surv_comment("Игрок не угадал число за все попытки. Подбодри его.")
        await update.message.reply_text(
            f"{LOST_TEXT}\nЯ загадывал: {secret}.\n{comment}".strip()
        )
    else:
        _save_json(ACCESS_FILE, access)
        hint = "больше" if guess < secret else "меньше"
        await update.message.reply_text(
            f"Нет, загаданное число {hint}. Осталось попыток: {left}."
        )
    return True


# ------------------------------------------- аварийное отключение (/stop)

shutdown_state = {"task": None, "messages": [], "reason": "", "ends_at": 0.0}


def shutdown_pending() -> bool:
    task = shutdown_state["task"]
    return task is not None and not task.done()


FAKE_OFF_SECONDS = 60  # после фейкового «Бот выключен» бот молчит для всех, кроме админа
fake_state = {"silent_until": 0.0}


async def fake_gate(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Пока идёт «фейковое выключение», бот не отвечает никому, кроме админа."""
    if time.monotonic() >= fake_state["silent_until"]:
        return
    user = update.effective_user
    if user and is_admin(user.id):
        return
    if update.callback_query:
        await update.callback_query.answer()
    raise ApplicationHandlerStop


async def _shutdown_worker(app: Application, seconds: int, fake: bool = False):
    await asyncio.sleep(seconds)
    await broadcast(app, "🔴 Бот выключен.")
    if fake:
        fake_state["silent_until"] = time.monotonic() + FAKE_OFF_SECONDS
        asyncio.get_running_loop().call_later(
            FAKE_OFF_SECONDS, print, "🎭 ФЕЙК завершён: бот снова отвечает."
        )
        print(f"🎭 ФЕЙК: чатам показали «Бот выключен». Бот молчит {FAKE_OFF_SECONDS} сек "
              "(кроме админа) и продолжает работать.")
        return
    print("Бот выключается...")
    app.stop_running()


async def start_shutdown(app: Application, seconds: int, reason: str, fake: bool = False):
    if shutdown_pending():
        print("Отключение уже запланировано. Сначала введи /cancel")
        return

    text = (
        "⚠️ Техническая неполадка.\n"
        "Администратор бота активировал экстренное отключение. "
        f"Через {seconds} сек. бот будет выключен."
    )
    if reason:
        text += f"\nПричина: {reason}"

    keyboard = InlineKeyboardMarkup(
        [[InlineKeyboardButton("❌ Отмена", callback_data="cancel_shutdown")]]
    )
    shutdown_state["reason"] = reason
    shutdown_state["ends_at"] = time.monotonic() + seconds
    shutdown_state["messages"] = await broadcast(app, text, keyboard)
    shutdown_state["fake"] = fake
    shutdown_state["task"] = asyncio.create_task(_shutdown_worker(app, seconds, fake))
    if fake:  # о фейке — только здесь, в консоли
        print(
            f"🎭 ФЕЙКОВОЕ отключение через {seconds} сек (бот НЕ выключится). "
            f"В чатах всё выглядит как настоящее. Оповещено чатов: "
            f"{len(shutdown_state['messages'])}. Отмена: /cancel"
        )
    else:
        print(
            f"Отключение через {seconds} сек. Оповещено чатов: "
            f"{len(shutdown_state['messages'])}. Отмена: /cancel"
        )


async def cancel_shutdown(app: Application) -> bool:
    if not shutdown_pending():
        return False
    shutdown_state["task"].cancel()
    was_fake = shutdown_state.get("fake", False)
    shutdown_state["task"] = None
    shutdown_state["reason"] = ""

    for chat_id, message_id in shutdown_state["messages"]:
        try:  # убираем кнопку «Отмена» у старых сообщений
            await app.bot.edit_message_reply_markup(chat_id, message_id, reply_markup=None)
        except Exception:
            pass
    shutdown_state["messages"] = []

    await broadcast(app, "✅ Отменено. Бот продолжает работать.")
    print("🎭 Фейковое отключение отменено." if was_fake else "Отключение отменено.")
    return True


async def cancel_button(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    if not is_admin(query.from_user.id):
        await query.answer("Отменить может только администратор бота.", show_alert=True)
        return
    ok = await cancel_shutdown(context.application)
    await query.answer("Отменено" if ok else "Отключение уже не запланировано")


# ----------------------------- отключение ИИ (/stop offchatgpt) и «почему»

async def disable_ai(app: Application, reason: str):
    if not ai_state["enabled"]:
        print("ИИ уже отключён. Включить: /stop onchatgpt")
        return
    set_ai(False, reason)
    text = (
        "⚠️ ИИ-чат (ChatGPT) отключён администратором.\n"
        "Магазин (/shop) и погода (/weather) продолжают работать."
    )
    if reason:
        text += f"\nПричина: {reason}"
    text += "\n\nЕсли хочешь узнать подробнее, напиши «почему отключение?»"
    sent = await broadcast(app, text)
    print(f"ИИ отключён. Оповещено чатов: {len(sent)}. Включить: /stop onchatgpt")


async def enable_ai(app: Application):
    if ai_state["enabled"]:
        print("ИИ и так включён.")
        return
    set_ai(True)
    sent = await broadcast(app, "✅ ИИ-чат снова работает.")
    print(f"ИИ включён. Оповещено чатов: {len(sent)}.")


WHY_RE = re.compile(r"почему|причин|зачем|why")
OFF_RE = re.compile(
    r"отключ|выключ|останов|неполадк|не\s*работа|не\s*отвеча|недоступ|disabl"
)


def is_why_question(text: str) -> bool:
    """«Почему отключение?», «причина отключения», «почему ты не работаешь» и т.п."""
    t = text.lower()
    return bool(WHY_RE.search(t) and OFF_RE.search(t))


def why_text() -> str | None:
    """Объяснение для пользователей или None, если сейчас ничего не отключено."""
    parts = []
    if not ai_state["enabled"]:
        parts.append(
            "🔴 ИИ-чат отключён администратором.\n"
            f"Причина: {ai_state['reason'] or 'не указана'}\n"
            "Магазин (/shop) и погода (/weather) работают."
        )
    if shutdown_pending():
        parts.append(
            "⚠️ Запланировано отключение бота.\n"
            f"Причина: {shutdown_state['reason'] or 'не указана'}"
        )
    return "\n\n".join(parts) or None


# ------------------------------------------------------------- консоль

CONSOLE_HELP = (
    "Команды консоли:\n"
    "  /stop <секунды> [причина]   экстренное отключение\n"
    "  /stop offchatgpt [причина]  отключить ИИ (OpenAI)\n"
    "  /stop onchatgpt             включить ИИ обратно\n"
    "  /cancel                     отменить отключение\n"
    "  /fakestop <секунды> [причина]  ФЕЙКОВОЕ отключение: в чатах как настоящее, о фейке — только в консоли\n"
    "  /ban @username [причина]    запретить пользоваться ботом\n"
    "  /unban @username            снять бан\n"
    "  /banlist                    список забаненных\n"
    "  /grant <id|@username>       выдать доступ к ИИ-чату без игры\n"
    "  /survreset <id|@username>   обнулить игру /survkey\n"
    "  /giveperms [минуты]         дать ИИ права управления ботом (по умолч. 60 мин)\n"
    "  /givepermanentperm          дать ИИ постоянные права\n"
    "  /revokeperms                забрать права у ИИ\n"
    "  /crazymode on|off [force]   ИИ дёргает плагины при каждом ответе (force — обойти блокировку)\n"
    "  /plugintest [имя] [ai]      тест плагинов (ai — живой тест через ИИ)\n"
    "  /givepoints <id|@user> <n>  выдать баллы ProTutu\n"
    "  /takepoints <id|@user> <n>  забрать баллы ProTutu\n"
    "  /points [id|@user]          баланс или топ баллов ProTutu\n"
    "  /replymode on|off           отвечать только на reply боту / @упоминание\n"
    "  /supercrazymode on|off [force]|reset  спам 5 командами; после 9 отказов ИИ мстит\n"
    "  /chatreset                  очистить память консольного чата с ИИ\n"
    "  /chat <текст>               отправить сообщение от имени бота во все чаты\n"
    "  /chat to <id|@user> <текст> отправить в конкретный чат/человеку\n"
    "                              (или попроси ИИ в консоли: «отправь всем: …»)\n"
    "  любой текст без «/»         написать ИИ прямо из консоли\n"
    "  /plugins                    список плагинов и статусы\n"
    "  /plugin <действие>          off/on, offall/onall, lock/unlock, block,\n"
    "                              revoke, revokekey, genkey, sign, verify, keys…\n"
    "                              (подробно: /plugin help)\n"
    "  /pluginadd <путь к .txt>    установить плагин из файла\n"
    "  /delplugin <имя>            удалить плагин\n"
    "  /products                   список товаров\n"
    "  /addproduct Название | Цена | Описание\n"
    "  /delproduct <id>\n"
    "  /help"
)


console_history: list[dict] = []


async def console_chat(text: str):
    """Текст без «/» в консоли — обычное сообщение ИИ от имени администратора."""
    console_history.append({"role": "user", "content": text})
    del console_history[:-MAX_HISTORY]
    try:
        answer = await ask_gpt(console_history, True)
    except Exception as e:
        log.exception("console chat failed")
        console_history.pop()
        print(f"Ошибка при обращении к ИИ: {e}")
        return
    console_history.append({"role": "assistant", "content": answer})
    print(f"🤖 {AI_NAME}: {answer}")


async def handle_console(app: Application, line: str):
    if not line.startswith("/"):
        await console_chat(line)
        return
    cmd, _, rest = line.lstrip("/").partition(" ")
    cmd, rest = cmd.lower(), rest.strip()

    if cmd == "stop":
        sec, _, reason = rest.partition(" ")
        if sec.lower() == "offchatgpt":
            await disable_ai(app, reason.strip())
        elif sec.lower() == "onchatgpt":
            await enable_ai(app)
        elif not sec.isdigit():
            print("Использование: /stop <секунды> [причина] | /stop offchatgpt [причина] | /stop onchatgpt")
            return
        else:
            await start_shutdown(app, int(sec), reason.strip())
    elif cmd == "ban":
        name, _, reason = rest.partition(" ")
        if not ban_user(name, reason.strip()):
            print("Использование: /ban @username [причина]")
            return
        print(f"Забанен: @{norm_username(name)}")
    elif cmd == "unban":
        print("Бан снят." if unban_user(rest) else "Такого username нет в списке банов.")
    elif cmd == "banlist":
        print(format_banlist())
    elif cmd in ("grant", "survreset"):
        status = "won" if cmd == "grant" else "new"
        if set_access(rest, status):
            print("Доступ выдан." if cmd == "grant" else "Игра обнулена, можно играть заново.")
        else:
            print(f"Использование: /{cmd} <id|@username> "
                  "(по @username — только если человек уже писал /survkey)")
    elif cmd == "giveperms":
        if rest and not rest.isdigit():
            print("Использование: /giveperms [минуты]")
            return
        print(grant_ai_perms(int(rest) if rest else 60))
    elif cmd == "givepermanentperm":
        print(grant_ai_perms(None))
    elif cmd == "revokeperms":
        print(revoke_ai_perms())
    elif cmd == "plugintest":
        print(await plugin_test_command(rest))
    elif cmd in ("givepoints", "takepoints"):
        ref, _, amount = rest.partition(" ")
        print(await points_admin(app, ref, amount.strip(), 1 if cmd == "givepoints" else -1))
    elif cmd == "points":
        print(points_report(rest))
    elif cmd == "supercrazymode":
        if rest.lower() == "reset":
            reset_supercrazy()
            print("SUPERCRAZY: счётчик отказов и месть сброшены.")
            return
        parts = rest.lower().split()
        val = parse_onoff(parts[0] if parts else "")
        if val is None:
            state = "включён" if settings["supercrazy"] else "выключен"
            print(f"/supercrazymode: {state}. Использование: /supercrazymode on|off|reset")
            return
        if not val:
            blocked = crazy_lock_block("force" in parts[1:])
            if blocked:
                print(blocked)
                return
        set_setting("supercrazy", val)
        print(f"/supercrazymode: {'включён' if val else 'выключен'}.")
    elif cmd == "chat":
        print(await say_command(app, rest))
    elif cmd == "chatreset":
        console_history.clear()
        print("Память консольного чата очищена.")
    elif cmd in ("crazymode", "replymode"):
        key = "crazy" if cmd == "crazymode" else "reply_only"
        parts = rest.lower().split()
        val = parse_onoff(parts[0] if parts else "")
        if val is None:
            print(f"/{cmd}: {'включён' if settings[key] else 'выключен'}. Использование: /{cmd} on|off")
            return
        if key == "crazy" and not val:
            blocked = crazy_lock_block("force" in parts[1:])
            if blocked:
                print(blocked)
                return
        set_setting(key, val)
        print(f"/{cmd}: {'включён' if val else 'выключен'}.")
    elif cmd == "plugins":
        print(format_plugins())
    elif cmd == "plugin":
        print(plugin_admin(rest))
    elif cmd == "pluginadd":
        path = Path(rest.strip('"\' '))
        if not rest or not path.is_file():
            print("Использование: /pluginadd <путь к .txt файлу>")
            return
        raw = path.read_bytes()
        try:
            text = raw.decode("utf-8-sig")
        except UnicodeDecodeError:
            text = raw.decode("cp1251")
        print(install_plugin(plugin_name(path.name), text)[1])
    elif cmd == "delplugin":
        print("Плагин удалён." if rest and delete_plugin(rest) else
              "Использование: /delplugin <имя> (см. /plugins)")
    elif cmd == "fakestop":
        sec, _, reason = rest.partition(" ")
        if not sec.isdigit():
            print("Использование: /fakestop <секунды> [причина]")
            return
        await start_shutdown(app, int(sec), reason.strip(), fake=True)
    elif cmd == "cancel":
        if not await cancel_shutdown(app):
            print("Нет запланированного отключения.")
    elif cmd == "products":
        print(format_catalog())
    elif cmd == "addproduct":
        parsed = parse_product(rest)
        if not parsed:
            print("Использование: /addproduct Название | Цена | Описание")
            return
        p = add_product(*parsed)
        print(f"Добавлено: {p['id']}. {p['name']}")
    elif cmd == "delproduct":
        if rest.isdigit() and delete_product(int(rest)):
            print("Удалено.")
        else:
            print("Использование: /delproduct <id> (товар с таким id должен существовать)")
    elif cmd == "help":
        print(CONSOLE_HELP)
    else:
        print("Неизвестная команда. /help — список команд.")


def console_thread(app: Application, loop: asyncio.AbstractEventLoop):
    print(CONSOLE_HELP)
    while True:
        try:
            line = input("> ").strip()
        except (EOFError, KeyboardInterrupt):
            return
        if not line:
            continue
        future = asyncio.run_coroutine_threadsafe(handle_console(app, line), loop)
        try:
            future.result()
        except Exception as e:
            print("Ошибка:", e)


async def post_init(app: Application):
    global APP
    APP = app
    loop = asyncio.get_running_loop()
    threading.Thread(target=console_thread, args=(app, loop), daemon=True).start()
    try:
        await app.bot.set_my_commands([
            BotCommand("shop", "🛍 Магазин смартфонов"),
            BotCommand("weather", "🌤 Погода: /weather город"),
            BotCommand("survkey", "🎲 Угадай число — доступ к ИИ"),
            BotCommand("why", "❓ Почему что-то отключено"),
            BotCommand("reset", "🧹 Очистить память диалога"),
            BotCommand("myid", "🪪 Мой Telegram ID"),
            BotCommand("points", "⭐ Баллы ProTutu (только в ЛС)"),
        ])
    except Exception:
        log.warning("Не удалось обновить меню команд")


# ------------------------------------------------- команды в Telegram

async def start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(
        "Привет! Я умею:\n"
        "• /shop — магазин смартфонов\n"
        "• /weather <город> — погода\n"
        "• /survkey — угадай число и получи доступ к ИИ-чату\n"
        "• /reset — очистить память диалога\n"
        "• /why — узнать, почему что-то отключено\n"
        "• /myid — узнать свой Telegram ID\n"
        "• /points — баллы ProTutu (только в личке)\n"
        "• или просто пиши мне: расскажу про товары, сравню модели, "
        "подскажу погоду."
    )


async def myid_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(f"Твой Telegram ID: {update.effective_user.id}")


async def weather_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not context.args:
        await update.message.reply_text("Использование: /weather Будапешт")
        return
    try:
        w = await fetch_weather(" ".join(context.args))
        await update.message.reply_text(format_weather(w))
    except Exception:
        log.exception("weather command failed")
        await update.message.reply_text("Не получилось узнать погоду, попробуй позже.")


async def reset(update: Update, context: ContextTypes.DEFAULT_TYPE):
    context.user_data["history"] = []
    await update.message.reply_text("Память диалога очищена ✅")


SHOP_PAGE_SIZE = 6
SHOP_LINE = "━━━━━━━━━━━━━━━━━━"


def esc(value) -> str:
    return html.escape(str(value), quote=False)


def ru_plural(n: int, one: str, few: str, many: str) -> str:
    n = abs(n)
    if 11 <= n % 100 <= 14:
        return many
    if n % 10 == 1:
        return one
    if 2 <= n % 10 <= 4:
        return few
    return many


def spec_lines(description: str) -> list[str]:
    """Описание «a, b, c» -> список характеристик; для обычного текста — пусто."""
    parts = [p.strip(" .") for p in re.split(r"[;\n]|,\s+", description or "")]
    parts = [p for p in parts if p]
    if len(parts) >= 3 and all(len(p) <= 70 for p in parts):
        return parts
    return []


def shop_catalog_view(page: int = 0):
    """(текст HTML, клавиатура) главной страницы магазина."""
    products = load_products()
    if not products:
        return "🛍 <b>Магазин</b>\n\nПока здесь пусто — загляни позже.", None
    pages = math.ceil(len(products) / SHOP_PAGE_SIZE)
    page = max(0, min(page, pages - 1))
    chunk = products[page * SHOP_PAGE_SIZE:(page + 1) * SHOP_PAGE_SIZE]
    n = len(products)

    lines = [
        "🛍 <b>Магазин смартфонов</b>",
        SHOP_LINE,
        f"В каталоге {n} {ru_plural(n, 'модель', 'модели', 'моделей')}",
        "",
    ]
    for p in chunk:
        lines += [f"📱 <b>{esc(p['name'])}</b>", f"      💰 {esc(p['price'])}", ""]
    lines += [
        "👇 Выбери модель — покажу подробности.",
        "💬 Или просто спроси меня в чате: подскажу и сравню.",
    ]

    rows = [
        [InlineKeyboardButton(f"📱 {p['name']} · {p['price']}", callback_data=f"shop:item:{p['id']}")]
        for p in chunk
    ]
    if pages > 1:
        rows.append([
            InlineKeyboardButton("◀️", callback_data=f"shop:list:{(page - 1) % pages}"),
            InlineKeyboardButton(f"{page + 1}/{pages}", callback_data="shop:noop"),
            InlineKeyboardButton("▶️", callback_data=f"shop:list:{(page + 1) % pages}"),
        ])
    return "\n".join(lines), InlineKeyboardMarkup(rows)


def shop_product_view(product_id: int):
    """(текст HTML, клавиатура) карточки товара или None, если товара нет."""
    products = load_products()
    idx = next((i for i, p in enumerate(products) if p["id"] == product_id), None)
    if idx is None:
        return None
    p, n = products[idx], len(products)

    lines = [
        f"📱 <b>{esc(p['name'])}</b>",
        SHOP_LINE,
        f"💰 <b>Цена:</b> {esc(p['price'])}",
        "",
    ]
    specs = spec_lines(p.get("description", ""))
    if specs:
        lines.append("📋 <b>Характеристики</b>")
        lines += [f"  ▫️ {esc(s)}" for s in specs]
    elif p.get("description"):
        lines += ["📝 <b>Описание</b>", esc(p["description"])]
    else:
        lines.append("<i>Описание пока не добавлено.</i>")
    lines += ["", f"<i>Модель {idx + 1} из {n}</i>"]

    rows = []
    if n > 1:
        prev_id, next_id = products[(idx - 1) % n]["id"], products[(idx + 1) % n]["id"]
        rows.append([
            InlineKeyboardButton("◀️", callback_data=f"shop:item:{prev_id}"),
            InlineKeyboardButton(f"{idx + 1}/{n}", callback_data="shop:noop"),
            InlineKeyboardButton("▶️", callback_data=f"shop:item:{next_id}"),
        ])
    rows.append([
        InlineKeyboardButton("🗂 К каталогу", callback_data=f"shop:list:{idx // SHOP_PAGE_SIZE}")
    ])
    return "\n".join(lines), InlineKeyboardMarkup(rows)


async def shop_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    text, keyboard = shop_catalog_view(0)
    await update.message.reply_text(
        text, parse_mode=ParseMode.HTML, reply_markup=keyboard
    )


async def shop_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Кнопки магазина: каталог, страницы, карточки, листание. Правит сообщение на месте."""
    query = update.callback_query
    await query.answer()
    parts = query.data.split(":")
    try:
        if parts[0] == "product":  # старые сообщения с прежним форматом кнопок
            kind, arg = "item", int(parts[1])
        elif parts[1] == "noop":
            return
        else:
            kind, arg = parts[1], int(parts[2])
    except (IndexError, ValueError):
        return

    view = shop_catalog_view(arg) if kind == "list" else shop_product_view(arg)
    if view is None:  # товар удалили, пока висело старое сообщение
        view = shop_catalog_view(0)
    text, keyboard = view
    try:
        await query.edit_message_text(
            text, parse_mode=ParseMode.HTML, reply_markup=keyboard
        )
    except BadRequest as e:
        if "not modified" not in str(e).lower():
            raise


async def addproduct_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        await update.message.reply_text("Эта команда только для администратора.")
        return
    parsed = parse_product(update.message.text.partition(" ")[2])
    if not parsed:
        await update.message.reply_text(
            "Использование:\n/addproduct Название | Цена | Описание"
        )
        return
    p = add_product(*parsed)
    await update.message.reply_text(f"✅ Добавлено: {p['id']}. {p['name']} — {p['price']}")


async def delproduct_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        await update.message.reply_text("Эта команда только для администратора.")
        return
    if context.args and context.args[0].isdigit() and delete_product(int(context.args[0])):
        await update.message.reply_text("🗑 Товар удалён.")
    else:
        await update.message.reply_text("Использование: /delproduct <id>")


async def why_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(why_text() or "Сейчас всё работает штатно ✅")


async def ban_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        await update.message.reply_text("Эта команда только для администратора.")
        return
    if not context.args or not ban_user(context.args[0], " ".join(context.args[1:])):
        await update.message.reply_text("Использование: /ban @username [причина]")
        return
    await update.message.reply_text(f"🚫 @{norm_username(context.args[0])} забанен.")


async def unban_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        await update.message.reply_text("Эта команда только для администратора.")
        return
    if context.args and unban_user(context.args[0]):
        await update.message.reply_text("✅ Бан снят.")
    else:
        await update.message.reply_text("Использование: /unban @username (он должен быть в бане)")


async def banlist_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        await update.message.reply_text("Эта команда только для администратора.")
        return
    await update.message.reply_text(format_banlist())


async def installplugin_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        await update.message.reply_text("Эта команда только для администратора.")
        return
    if plugin_state["install_locked"]:
        reason = plugin_state["lock_reason"]
        await update.message.reply_text(
            "🔒 Установка плагинов запрещена."
            + (f"\nПричина: {reason}" if reason else "")
            + "\nСнять запрет: /plugin unlock"
        )
        return
    context.user_data["await_plugin"] = True
    sig_note = (
        "Файл должен быть подписан (последняя строка #SIGNATURE …)."
        if plugin_state["require_signature"]
        else "Подпись необязательна, но если она есть — должна быть верной."
    )
    await update.message.reply_text(
        f"📎 Пришли .txt файл с промптом плагина (до {MAX_PLUGIN_BYTES // 1024} КБ). "
        "Имя плагина — имя файла; файл с тем же именем обновит плагин.\n"
        f"✍️ {sig_note}\n"
        "Любое текстовое сообщение отменит установку."
    )


async def plugin_document(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Принимает .txt после /installplugin (или файл с подписью /installplugin)."""
    msg = update.message
    caption = (msg.caption or "").strip().lower()
    waiting = context.user_data.pop("await_plugin", False)
    if not waiting and not caption.startswith("/installplugin"):
        return  # обычные файлы бот игнорирует
    if not is_admin(update.effective_user.id):
        await msg.reply_text("Устанавливать плагины может только администратор.")
        return

    doc = msg.document
    problem = None
    if not (doc.file_name or "").lower().endswith(".txt"):
        problem = "Нужен файл в формате .txt."
    elif doc.file_size and doc.file_size > MAX_PLUGIN_BYTES:
        problem = f"Файл слишком большой (максимум {MAX_PLUGIN_BYTES // 1024} КБ)."
    if problem:
        context.user_data["await_plugin"] = True  # даём попробовать ещё раз
        await msg.reply_text(f"❌ {problem} Пришли другой файл или напиши любой текст для отмены.")
        return

    try:
        data = bytes(await (await doc.get_file()).download_as_bytearray())
        try:
            text = data.decode("utf-8-sig")
        except UnicodeDecodeError:
            text = data.decode("cp1251")  # старые «блокнотные» файлы
    except Exception:
        log.exception("plugin download failed")
        context.user_data["await_plugin"] = True
        await msg.reply_text("❌ Не удалось прочитать файл. Пришли его ещё раз.")
        return

    ok, answer = install_plugin(plugin_name(doc.file_name), text)
    await msg.reply_text(answer)


async def plugins_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        await update.message.reply_text("Эта команда только для администратора.")
        return
    await update.message.reply_text("🧩 Плагины\n\n" + format_plugins())


async def plugin_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/plugin <действие> — отключение, запрет, отзыв подписи, ключи (только админ)."""
    if not is_admin(update.effective_user.id):
        await update.message.reply_text("Эта команда только для администратора.")
        return
    answer = plugin_admin(update.message.text.partition(" ")[2])
    await update.message.reply_text(answer[:4000])


async def removeplugin_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        await update.message.reply_text("Эта команда только для администратора.")
        return
    if context.args and delete_plugin(" ".join(context.args)):
        await update.message.reply_text("🗑 Плагин удалён.")
    else:
        await update.message.reply_text("Использование: /removeplugin <имя> (список: /plugins)")


async def giveperms_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        await update.message.reply_text("Эта команда только для администратора.")
        return
    if context.args and not context.args[0].isdigit():
        await update.message.reply_text("Использование: /giveperms [минуты]")
        return
    await update.message.reply_text(
        grant_ai_perms(int(context.args[0]) if context.args else 60)
    )


async def givepermanentperm_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        await update.message.reply_text("Эта команда только для администратора.")
        return
    await update.message.reply_text(grant_ai_perms(None))


async def revokeperms_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        await update.message.reply_text("Эта команда только для администратора.")
        return
    await update.message.reply_text(revoke_ai_perms())


async def _toggle_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE, key: str, name: str):
    if not is_admin(update.effective_user.id):
        await update.message.reply_text("Эта команда только для администратора.")
        return
    val = parse_onoff(context.args[0]) if context.args else None
    if val is None:
        await update.message.reply_text(
            f"/{name}: {'включён' if settings[key] else 'выключен'}.\nИспользование: /{name} on|off"
        )
        return
    if not val and key in ("crazy", "supercrazy"):
        force = len(context.args) > 1 and context.args[1].lower() == "force"
        blocked = crazy_lock_block(force)
        if blocked:
            await update.message.reply_text(blocked)
            return
    set_setting(key, val)
    await update.message.reply_text(f"/{name}: {'включён ✅' if val else 'выключен ⛔'}")


def is_private(update: Update) -> bool:
    return bool(update.effective_chat and update.effective_chat.type == "private")


POINTS_PRIVATE_TEXT = f"🔒 Баллы {POINTS_NAME} доступны только в личных сообщениях с ботом."


async def points_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_private(update):
        await update.message.reply_text(POINTS_PRIVATE_TEXT)
        return
    user = update.effective_user
    rec = points_rec(user.id)
    rec["username"] = user.username or rec.get("username", "")
    _save_json(POINTS_FILE, points)
    await update.message.reply_text(f"⭐ Твои баллы {POINTS_NAME}: {rec['points']}")


async def _points_admin_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE, sign: int):
    if not is_admin(update.effective_user.id):
        await update.message.reply_text("Эта команда только для администратора.")
        return
    if not is_private(update):
        await update.message.reply_text(POINTS_PRIVATE_TEXT)
        return
    if len(context.args) != 2:
        name = "givepoints" if sign > 0 else "takepoints"
        await update.message.reply_text(f"Использование: /{name} <id|@username> <баллы>")
        return
    await update.message.reply_text(
        await points_admin(context.application, context.args[0], context.args[1], sign)
    )


async def givepoints_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await _points_admin_cmd(update, context, 1)


async def takepoints_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await _points_admin_cmd(update, context, -1)


async def plugintest_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        await update.message.reply_text("Эта команда только для администратора.")
        return
    if context.args and context.args[-1].lower() in ("ai", "live"):
        await update.effective_chat.send_action(ChatAction.TYPING)
    await update.message.reply_text(
        (await plugin_test_command(" ".join(context.args)))[:4000]
    )


async def fakestop_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/fakestop <сек> [причина] — тихо, без ответа в чате; о фейке пишет только консоль."""
    if not is_admin(update.effective_user.id):
        return
    if not context.args or not context.args[0].isdigit():
        await update.message.reply_text("Использование: /fakestop <секунды> [причина]")
        return
    await start_shutdown(
        context.application, int(context.args[0]), " ".join(context.args[1:]), fake=True
    )
    try:
        await update.message.delete()
    except Exception:
        pass


async def say_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/chat <текст> — админ пишет от имени бота в текущий чат."""
    msg = update.message
    if not is_admin(update.effective_user.id):
        await msg.reply_text("Эта команда только для администратора.")
        return
    text = msg.text.partition(" ")[2].strip()
    if not text:
        await msg.reply_text("Использование: /chat <текст>")
        return
    reply_to = msg.reply_to_message.message_id if msg.reply_to_message else None
    await context.bot.send_message(msg.chat_id, text[:4000], reply_to_message_id=reply_to)
    try:  # убираем команду, чтобы осталось только сообщение «от бота»
        await msg.delete()
    except Exception:
        pass


async def supercrazymode_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if context.args and context.args[0].lower() == "reset":
        if not is_admin(update.effective_user.id):
            await update.message.reply_text("Эта команда только для администратора.")
            return
        reset_supercrazy()
        await update.message.reply_text("SUPERCRAZY: счётчик отказов и месть сброшены ✅")
        return
    await _toggle_cmd(update, context, "supercrazy", "supercrazymode")


async def crazymode_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await _toggle_cmd(update, context, "crazy", "crazymode")


async def replymode_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await _toggle_cmd(update, context, "reply_only", "replymode")


async def chat(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.message is None or not update.message.text:
        return  # правка сообщения, канал и т.п. — отвечать не на что
    text = update.message.text
    user = update.effective_user

    # Админ передумал устанавливать плагин
    if context.user_data.pop("await_plugin", False):
        await update.message.reply_text("Установка плагина отменена.")
        return

    # Идёт игра /survkey — сообщение считается попыткой
    if await surv_guess(update, context):
        return

    # Режим «только на ответы»: на обычные сообщения бот молчит
    if settings["reply_only"] and not is_reply_to_bot(update, context):
        return

    # «Почему отключение?»: если ИИ доступен — отвечает ИИ (знает причину из
    # системного промпта), иначе — готовый текст без обращения к OpenAI
    if is_why_question(text) and not (ai_state["enabled"] and has_access(user)):
        answer = why_text()
        if answer:
            await update.message.reply_text(answer)
            return

    if not ai_state["enabled"]:
        await update.message.reply_text(
            "🔴 ИИ-чат временно отключён. Напиши «почему отключение?», "
            "чтобы узнать причину.\nМагазин (/shop) и погода (/weather) работают."
        )
        return

    if not has_access(user):
        status = access.get(str(user.id), {}).get("status")
        if status == "lost":
            await update.message.reply_text(LOST_TEXT)
        else:
            await update.message.reply_text(
                "🔒 ИИ-чат открывается после игры: напиши /survkey и угадай число "
                f"за {SURV_ATTEMPTS} попытки.\n"
                "Магазин (/shop) и погода (/weather) доступны сразу."
            )
        return

    history = context.user_data.setdefault("history", [])
    history.append({"role": "user", "content": text})
    del history[:-MAX_HISTORY]

    await update.effective_chat.send_action(ChatAction.TYPING)
    try:
        answer = await ask_gpt(history, is_admin(user.id))
    except Exception:
        log.exception("AI request failed")
        history.pop()  # не оставляем «висящее» сообщение без ответа
        await update.message.reply_text("Ошибка при обращении к ИИ, попробуй позже.")
        return

    history.append({"role": "assistant", "content": answer})
    await update.message.reply_text(answer)


def cli(args: list[str]) -> None:
    """python bot.py genkey|sign|verify — работа с подписью без запуска бота."""
    cmd = args[0].lower()
    try:
        if cmd == "genkey" and len(args) == 2:
            pub = generate_key(args[1])
            print(f"Ключ «{args[1]}» создан.\nЗакрытый: {key_file(args[1])} (храни в тайне!)")
            print(f"Открытый (base64): {pub}")
        elif cmd == "sign" and len(args) == 3:
            path = Path(args[1])
            path.write_text(
                sign_text(path.read_text(encoding="utf-8-sig"), args[2]), encoding="utf-8"
            )
            print(f"Подписано ключом «{args[2]}»: {path}")
        elif cmd == "verify" and len(args) == 2:
            body, sig = split_signature(Path(args[1]).read_text(encoding="utf-8-sig"))
            if not sig:
                print("Подписи нет.")
                return
            ok, why = verify_signature(body, *sig)
            print(f"Ключ: {sig[0]}\nSHA-256: {body_sha(body)[:16]}…")
            print("✅ Подпись верна." if ok else f"❌ Проверка не пройдена: {why}")
            rev = find_revocation(body, *sig)
            if rev:
                print(f"🚫 Отозвано: {rev['what']} {rev['reason']}")
        else:
            print("Использование: python bot.py genkey <id> | sign <файл> <id> | verify <файл>")
    except (ValueError, OSError) as e:
        print(f"Ошибка: {e}")


def main():
    if len(sys.argv) > 1:
        cli(sys.argv[1:])
        return
    if TELEGRAM_TOKEN in ("", "-"):
        sys.exit("Задай токен бота: переменная окружения TELEGRAM_BOT_TOKEN.")
    if not OPENAI_API_KEY:
        log.warning("OPENAI_API_KEY не задан — ИИ-чат работать не будет (магазин и погода — будут).")
    if not ADMIN_IDS:
        log.warning(
            "ADMIN_ID не задан: /addproduct, /delproduct и кнопка «Отмена» "
            "будут недоступны в Telegram. Узнай свой ID командой /myid."
        )
    load_products()  # создаст shop.json с тремя стартовыми товарами
    for p in inspect_all():
        if p["status"] != "active":
            log.warning("Плагин «%s» не загружен: %s", p["name"], STATUS_LABELS[p["status"]])

    app = Application.builder().token(TELEGRAM_TOKEN).post_init(post_init).build()

    app.add_handler(TypeHandler(Update, drop_non_messages), group=-4)
    app.add_handler(TypeHandler(Update, fake_gate), group=-3)
    app.add_handler(TypeHandler(Update, ban_check), group=-2)  # бан проверяется первым
    app.add_handler(TypeHandler(Update, track_chat), group=-1)
    app.add_handler(CommandHandler("start", start))
    app.add_handler(CommandHandler("myid", myid_cmd))
    app.add_handler(CommandHandler("weather", weather_cmd))
    app.add_handler(CommandHandler("reset", reset))
    app.add_handler(CommandHandler("why", why_cmd))
    app.add_handler(CommandHandler("survkey", survkey_cmd))
    app.add_handler(CommandHandler("installplugin", installplugin_cmd))
    app.add_handler(CommandHandler("plugins", plugins_cmd))
    app.add_handler(CommandHandler("plugin", plugin_cmd))
    app.add_handler(CommandHandler(["removeplugin", "delplugin"], removeplugin_cmd))
    app.add_handler(MessageHandler(filters.Document.ALL, plugin_document))
    app.add_handler(CommandHandler("ban", ban_cmd))
    app.add_handler(CommandHandler("unban", unban_cmd))
    app.add_handler(CommandHandler("banlist", banlist_cmd))
    app.add_handler(CommandHandler("giveperms", giveperms_cmd))
    app.add_handler(CommandHandler("givepermanentperm", givepermanentperm_cmd))
    app.add_handler(CommandHandler("revokeperms", revokeperms_cmd))
    app.add_handler(CommandHandler("crazymode", crazymode_cmd))
    app.add_handler(CommandHandler("chat", say_cmd))
    app.add_handler(CommandHandler("fakestop", fakestop_cmd))
    app.add_handler(CommandHandler("supercrazymode", supercrazymode_cmd))
    app.add_handler(CommandHandler("plugintest", plugintest_cmd))
    app.add_handler(CommandHandler("points", points_cmd))
    app.add_handler(CommandHandler("givepoints", givepoints_cmd))
    app.add_handler(CommandHandler("takepoints", takepoints_cmd))
    app.add_handler(CommandHandler("replymode", replymode_cmd))
    app.add_handler(CommandHandler("shop", shop_cmd))
    app.add_handler(CommandHandler("addproduct", addproduct_cmd))
    app.add_handler(CommandHandler("delproduct", delproduct_cmd))
    app.add_handler(CallbackQueryHandler(cancel_button, pattern=r"^cancel_shutdown$"))
    app.add_handler(CallbackQueryHandler(shop_callback, pattern=r"^(shop:|product:)"))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, chat))

    log.info("Бот запущен")
    app.run_polling()


if __name__ == "__main__":
    main()
