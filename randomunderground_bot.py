
import os
import asyncio
import html
import re
import sqlite3
import time
import logging
import hashlib
from functools import wraps

from telegram import (
    Update,
    ChatPermissions,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    MessageEntity,
)
from telegram.constants import ChatMemberStatus
from telegram.error import BadRequest
from telegram.ext import (
    Application,
    ChatMemberHandler,
    CommandHandler,
    CallbackQueryHandler,
    MessageHandler,
    ContextTypes,
    filters,
)

from randomunderground_creative_v17 import register_creative_handlers

# ============================================================
# RANDOM UNDERGROUND BOT - clean rebuild v15
# Menfess anonim + comments + anonymous replies + event system
# V16: weighted comment points; preserves all existing Event scores
# ============================================================

def _load_env_files(*paths):
    """Load KEY=VALUE lines from local env files into os.environ without
    overriding variables already set. Dependency-free; secrets stay out of source."""
    for path in paths:
        try:
            with open(path, encoding="utf-8") as fh:
                for line in fh:
                    line = line.strip()
                    if not line or line.startswith("#") or "=" not in line:
                        continue
                    key, _, value = line.partition("=")
                    key = key.strip()
                    value = value.strip().strip('"').strip("'")
                    if key and key not in os.environ:
                        os.environ[key] = value
        except FileNotFoundError:
            continue
        except OSError:
            continue


_load_env_files(".envo", ".env")

BOT_TOKEN = os.getenv("RANDOMUNDERGROUND_BOT_TOKEN", "").strip()
CHANNEL_USERNAME = "@randomunderground"
DISCUSSION_GROUP_USERNAME = "@randomundergrounds"

# OWNER RANDOM UNDERGROUND
OWNER_USER_IDS = {
    5480598942,
    7005302744,
}

# Compatibility alias untuk kode lama.
OWNER_USER_ID = 5480598942

# Semua owner disembunyikan dari leaderboard publik.
HIDDEN_LEADERBOARD_USER_IDS = set(OWNER_USER_IDS)

# Kuota menfess user biasa
MAX_SENDS = 20
WINDOW_SECONDS = 24 * 60 * 60

# Event:
# skor = (menfess valid x 2) + (komentar/reply valid x 1)
POINT_PER_MENFESS = 2
POINT_PER_COMMENT = 1

# Leaderboards
WEEKLY_LEADERBOARD_SIZE = 20
MONTHLY_LEADERBOARD_SIZE = 20
ALL_TIME_LEADERBOARD_SIZE = 20

# Leaderboards continue from the existing V15 reset point.
# V16 adds a separate comment-points epoch so existing scores are never rebuilt.


DATA_DIR = os.getenv("RANDOMUNDERGROUND_DATA_DIR", ".")
os.makedirs(DATA_DIR, exist_ok=True)
DB_FILE = os.path.join(DATA_DIR, "randomunderground.db")

VALID_HASHTAGS = {
    "#mutual": "cari mutual / teman baru",
    "#curhat": "cerita atau keluh kesah",
    "#random": "bebas, apa aja",
    "#gabut": "ajak ngobrol / cari teman",
    "#confess": "sesuatu yang ingin disampaikan",
    "#ask": "tanya atau minta pendapat",
    "#salty": "lagi pengen ngeluarin kekesalan",
    "#want": "sedang mencari sesuatu / seseorang",
}

# Filter dasar. Ini sengaja tidak memblokir kata biasa yang bisa punya konteks
# netral. Daftar ini bisa diperluas oleh owner.
BAD_WORDS = {
    "anjing", "anjg", "anj", "bangsat", "bngsat", "bajingan",
    "brengsek", "kampret", "kontol", "kntl", "memek", "mmk",
    "perek", "lonte", "tolol", "goblok", "idiot", "bego",
    "jembut", "pepek", "ngentot", "ngewe", "asu",
}

MAX_COMMENT_WARNINGS = 3

# ------------------------------------------------------------
# MODERASI / LOG CHANNEL
# ------------------------------------------------------------
# Channel atau grup privat tempat bot mencatat setiap menfess beserta
# identitas pengirimnya. Isi dengan chat id numerik (channel privat
# biasanya -100xxxxxxxxxx). Kalau dibiarkan kosong, log dikirim ke DM
# owner pertama supaya fitur tetap jalan tanpa setup tambahan.
def _parse_log_chat_id(raw):
    raw = (raw or "").strip()
    if not raw:
        return None
    try:
        return int(raw)
    except ValueError:
        # Boleh juga @username kalau channel log publik.
        return raw if raw.startswith("@") else None


LOG_CHAT_ID = _parse_log_chat_id(os.getenv("RANDOMUNDERGROUND_LOG_CHAT_ID"))

# Komentar jumlahnya jauh lebih banyak dari menfess. Secara default hanya
# komentar bermasalah (kena filter / dihapus / dari user yang dibatasi) yang
# dicatat, supaya log channel tidak banjir. Set ke 1 untuk mencatat semuanya.
LOG_ALL_COMMENTS = os.getenv("RANDOMUNDERGROUND_LOG_ALL_COMMENTS", "0").strip() in ("1", "true", "yes")

# Mode pembatasan user:
#   ban    -> tidak bisa kirim apa pun, dikasih tahu alasannya
#   mute   -> sama seperti ban tapi ada masa berlaku
#   shadow -> pesan terlihat "terkirim" oleh user, tapi tidak pernah tayang
BAN_MODES = ("ban", "mute", "shadow")
BAN_MODE_LABEL = {
    "ban": "BANNED",
    "mute": "MUTED",
    "shadow": "SHADOWBANNED",
}

EMOJI = {
    "post": "◈",
    "ok": "✓",
    "warn": "⚠️",
    "event": "⚡",
    "reply": "↳",
}

CHANNEL_CHAT_ID = None
DISCUSSION_CHAT_ID = None
BOT_USER_ID = None


# ============================================================
# RELAY YANG MEMPERTAHANKAN FORMATTING
# Telegram mengirim formatting (bold, spoiler, link, emoji premium)
# sebagai daftar "entity" yang terpisah dari teks polos. Meneruskan
# message.text saja membuang semuanya, dan emoji premium jatuh ke
# emoji biasa. Helper di bawah ikut meneruskan entity aslinya.
#
# Batasan custom emoji (emoji premium) dari Bot API:
#   - bot yang punya username Fragment: boleh di semua chat
#   - bot biasa: hanya di chat privat/grup/supergrup, dan hanya kalau
#     owner bot punya Telegram Premium (Bot API 9.4)
#   - channel tidak termasuk, jadi post menfess di channel tetap
#     memakai emoji fallback kecuali bot punya username Fragment
# Kalau Telegram menolak entity custom emoji, pesan dikirim ulang
# tanpa entity itu supaya menfess tetap masuk.
# ============================================================

def utf16_len(text):
    """Panjang teks dalam satuan UTF-16, satuan yang dipakai offset entity."""
    return len(text.encode("utf-16-le")) // 2


def shift_entities(entities, offset):
    """Salin entity dengan offset digeser, dipakai saat teks diberi prefix."""
    return [
        MessageEntity(
            type=entity.type,
            offset=entity.offset + offset,
            length=entity.length,
            url=entity.url,
            user=entity.user,
            language=entity.language,
            custom_emoji_id=entity.custom_emoji_id,
        )
        for entity in (entities or [])
    ]


def has_custom_emoji(entities):
    return any(e.type == MessageEntity.CUSTOM_EMOJI for e in (entities or []))


def without_custom_emoji(entities):
    return [e for e in (entities or []) if e.type != MessageEntity.CUSTOM_EMOJI]


async def send_text_keep_format(bot, chat_id, text, entities=None, **kwargs):
    """send_message yang mempertahankan formatting asli pengirim."""
    try:
        return await bot.send_message(chat_id, text, entities=entities, **kwargs)
    except BadRequest:
        if not has_custom_emoji(entities):
            raise
        logging.info("Emoji premium ditolak Telegram, kirim ulang tanpa custom emoji.")
        return await bot.send_message(
            chat_id, text, entities=without_custom_emoji(entities), **kwargs
        )


async def send_photo_keep_format(
    bot, chat_id, photo, caption=None, caption_entities=None, **kwargs
):
    """send_photo yang mempertahankan formatting caption asli pengirim."""
    try:
        return await bot.send_photo(
            chat_id, photo, caption=caption,
            caption_entities=caption_entities, **kwargs
        )
    except BadRequest:
        if not has_custom_emoji(caption_entities):
            raise
        logging.info("Emoji premium ditolak Telegram, kirim ulang tanpa custom emoji.")
        return await bot.send_photo(
            chat_id, photo, caption=caption,
            caption_entities=without_custom_emoji(caption_entities), **kwargs
        )


# ============================================================
# DATABASE
# ============================================================

def db():
    # timeout + WAL + busy_timeout: kurangi error "database is locked" saat
    # handler async dan background watcher mengakses DB bersamaan.
    conn = sqlite3.connect(DB_FILE, timeout=30)
    conn.row_factory = sqlite3.Row
    try:
        conn.execute("PRAGMA journal_mode=WAL")
        conn.execute("PRAGMA busy_timeout=5000")
    except sqlite3.Error:
        pass
    return conn


def init_db():
    conn = db()

    conn.execute("""
        CREATE TABLE IF NOT EXISTS users (
            user_id INTEGER PRIMARY KEY,
            username TEXT DEFAULT '',
            first_name TEXT DEFAULT '',
            created_at INTEGER NOT NULL
        )
    """)

    conn.execute("""
        CREATE TABLE IF NOT EXISTS menfess (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            sender_id INTEGER NOT NULL,
            channel_message_id INTEGER NOT NULL,
            created_at INTEGER NOT NULL
        )
    """)

    conn.execute("""
        CREATE TABLE IF NOT EXISTS send_log (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            created_at INTEGER NOT NULL
        )
    """)

    conn.execute("""
        CREATE TABLE IF NOT EXISTS discussion_messages (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            menfess_id INTEGER NOT NULL,
            discussion_chat_id INTEGER NOT NULL,
            message_id INTEGER NOT NULL,
            parent_message_id INTEGER,
            author_user_id INTEGER NOT NULL,
            created_at INTEGER NOT NULL,
            UNIQUE(discussion_chat_id, message_id)
        )
    """)

    conn.execute("""
        CREATE TABLE IF NOT EXISTS comment_warnings (
            user_id INTEGER PRIMARY KEY,
            warnings INTEGER NOT NULL DEFAULT 0,
            updated_at INTEGER NOT NULL
        )
    """)

    conn.execute("""
        CREATE TABLE IF NOT EXISTS bot_settings (
            key TEXT PRIMARY KEY,
            value TEXT NOT NULL
        )
    """)

    conn.execute("""
        CREATE TABLE IF NOT EXISTS bans (
            user_id INTEGER PRIMARY KEY,
            mode TEXT NOT NULL DEFAULT 'ban',
            banned_until INTEGER NOT NULL DEFAULT 0,
            reason TEXT NOT NULL DEFAULT '',
            actor_id INTEGER NOT NULL DEFAULT 0,
            created_at INTEGER NOT NULL
        )
    """)

    conn.execute("""
        CREATE TABLE IF NOT EXISTS mod_actions (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            actor_id INTEGER NOT NULL,
            target_id INTEGER NOT NULL,
            action TEXT NOT NULL,
            detail TEXT NOT NULL DEFAULT '',
            created_at INTEGER NOT NULL
        )
    """)
    conn.execute(
        "CREATE INDEX IF NOT EXISTS idx_mod_actions_target "
        "ON mod_actions(target_id, created_at)"
    )

    conn.execute("""
        CREATE TABLE IF NOT EXISTS events (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            started_at INTEGER NOT NULL,
            ends_at INTEGER,
            stopped_at INTEGER,
            active INTEGER NOT NULL DEFAULT 1
        )
    """)

    # Event settings added after the first version of the bot.
    event_cols = {
        row["name"]
        for row in conn.execute("PRAGMA table_info(events)").fetchall()
    }
    if "event_name" not in event_cols:
        conn.execute("ALTER TABLE events ADD COLUMN event_name TEXT")
    if "winner_count" not in event_cols:
        conn.execute("ALTER TABLE events ADD COLUMN winner_count INTEGER NOT NULL DEFAULT 3")

    conn.execute("""
        CREATE TABLE IF NOT EXISTS event_points (
            event_id INTEGER NOT NULL,
            user_id INTEGER NOT NULL,
            menfess_count INTEGER NOT NULL DEFAULT 0,
            comment_count INTEGER NOT NULL DEFAULT 0,
            PRIMARY KEY(event_id, user_id)
        )
    """)

    conn.execute("""
        CREATE TABLE IF NOT EXISTS activity_log (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            activity_type TEXT NOT NULL,
            created_at INTEGER NOT NULL
        )
    """)

    # Community engagement data. Existing databases are migrated safely.
    for table, column in (("menfess", "content"), ("discussion_messages", "content")):
        cols = {r["name"] for r in conn.execute(f"PRAGMA table_info({table})").fetchall()}
        if column not in cols:
            conn.execute(f"ALTER TABLE {table} ADD COLUMN {column} TEXT DEFAULT ''")

    conn.execute("""
        CREATE TABLE IF NOT EXISTS daily_missions (
            day_key TEXT PRIMARY KEY,
            mission1 TEXT NOT NULL, mission2 TEXT NOT NULL, mission3 TEXT NOT NULL
        )
    """)
    conn.execute("""
        CREATE TABLE IF NOT EXISTS mission_claims (
            day_key TEXT NOT NULL, user_id INTEGER NOT NULL, mission_key TEXT NOT NULL,
            claimed_at INTEGER NOT NULL, PRIMARY KEY(day_key,user_id,mission_key)
        )
    """)
    conn.execute("""
        CREATE TABLE IF NOT EXISTS mystery_claims (
            day_key TEXT NOT NULL, user_id INTEGER NOT NULL, reward TEXT NOT NULL, claimed_at INTEGER NOT NULL,
            PRIMARY KEY(day_key, user_id)
        )
    """)
    conn.execute("""
        CREATE TABLE IF NOT EXISTS community_meta (
            key TEXT PRIMARY KEY, value TEXT NOT NULL
        )
    """)

    # V15 statistics state. One reset epoch is shared by:
    # - ALL-TIME / WEEKLY / MONTHLY leaderboards
    # - profile points, menfess, comments, weekly/monthly activity
    # - profile event wins
    # Existing source rows are preserved; rows before reset are simply ignored.
    conn.execute("""
        CREATE TABLE IF NOT EXISTS leaderboard_meta (
            key TEXT PRIMARY KEY, value TEXT NOT NULL
        )
    """)

    initialized = conn.execute(
        "SELECT value FROM leaderboard_meta WHERE key='v15_initialized'"
    ).fetchone()
    if not initialized:
        reset_at = int(time.time())
        conn.execute(
            "INSERT OR REPLACE INTO leaderboard_meta(key,value) VALUES ('v15_reset_at',?)",
            (str(reset_at),),
        )
        conn.execute(
            "INSERT OR REPLACE INTO leaderboard_meta(key,value) VALUES ('v15_initialized','1')"
        )
    # V16 comment scoring epoch. IMPORTANT: never delete or reset event_points.
    v16_initialized = conn.execute(
        "SELECT value FROM leaderboard_meta WHERE key='v16_initialized'"
    ).fetchone()
    if not v16_initialized:
        v16_at = int(time.time())
        conn.execute(
            "INSERT OR REPLACE INTO leaderboard_meta(key,value) VALUES ('v16_comment_points_at',?)",
            (str(v16_at),),
        )
        conn.execute(
            "INSERT OR REPLACE INTO leaderboard_meta(key,value) VALUES ('v16_initialized','1')"
        )

    # Preserve old Event #3 scores exactly by storing their legacy comment
    # points separately from the new weighted comment score.
    ep_cols = {r["name"] for r in conn.execute("PRAGMA table_info(event_points)").fetchall()}
    if "comment_score" not in ep_cols:
        conn.execute("ALTER TABLE event_points ADD COLUMN comment_score REAL NOT NULL DEFAULT 0")
        conn.execute("UPDATE event_points SET comment_score = comment_count")
    if "menfess_score" not in ep_cols:
        conn.execute("ALTER TABLE event_points ADD COLUMN menfess_score REAL NOT NULL DEFAULT 0")
        conn.execute("UPDATE event_points SET menfess_score = menfess_count * ?", (POINT_PER_MENFESS,))

    # V16 SAFE was briefly deployed with a legacy event updater. Preserve the
    # exact score users currently see before switching to weighted comments.
    legacy_sync = conn.execute(
        "SELECT value FROM leaderboard_meta WHERE key='v16_legacy_event_score_synced'"
    ).fetchone()
    if not legacy_sync:
        conn.execute("""
            UPDATE event_points
            SET comment_score = comment_count,
                menfess_score = menfess_count * ?
        """, (POINT_PER_MENFESS,))
        conn.execute(
            "INSERT OR REPLACE INTO leaderboard_meta(key,value) VALUES ('v16_legacy_event_score_synced','1')"
        )

    conn.commit()
    conn.close()


def save_user(user):
    conn = db()
    conn.execute("""
        INSERT INTO users(user_id, username, first_name, created_at)
        VALUES (?, ?, ?, ?)
        ON CONFLICT(user_id) DO UPDATE SET
            username=excluded.username,
            first_name=excluded.first_name
    """, (
        user.id,
        user.username or "",
        user.first_name or "",
        int(time.time()),
    ))
    conn.commit()
    conn.close()


def add_send_log(user_id):
    conn = db()
    conn.execute(
        "INSERT INTO send_log(user_id, created_at) VALUES (?, ?)",
        (user_id, int(time.time())),
    )
    conn.commit()
    conn.close()


def get_used_count(user_id):
    cutoff = int(time.time()) - WINDOW_SECONDS
    conn = db()
    conn.execute("DELETE FROM send_log WHERE created_at < ?", (cutoff,))
    row = conn.execute(
        "SELECT COUNT(*) AS total FROM send_log WHERE user_id=?",
        (user_id,),
    ).fetchone()
    conn.commit()
    conn.close()
    return int(row["total"])


def create_menfess(sender_id, channel_message_id, content=""):
    conn = db()
    cur = conn.execute("""
        INSERT INTO menfess(sender_id, channel_message_id, created_at, content)
        VALUES (?, ?, ?, ?)
    """, (sender_id, channel_message_id, int(time.time()), content[:4000]))
    menfess_id = cur.lastrowid
    conn.commit()
    conn.close()
    return menfess_id


def get_menfess(menfess_id):
    conn = db()
    row = conn.execute(
        "SELECT * FROM menfess WHERE id=?",
        (menfess_id,),
    ).fetchone()
    conn.close()
    return row


def get_menfess_by_channel_message(channel_message_id):
    conn = db()
    row = conn.execute(
        "SELECT * FROM menfess WHERE channel_message_id=?",
        (channel_message_id,),
    ).fetchone()
    conn.close()
    return row


def create_discussion_message(
    menfess_id,
    discussion_chat_id,
    message_id,
    parent_message_id,
    author_user_id,
    content="",
):
    conn = db()
    conn.execute("""
        INSERT OR IGNORE INTO discussion_messages(
            menfess_id, discussion_chat_id, message_id,
            parent_message_id, author_user_id, created_at, content
        )
        VALUES (?, ?, ?, ?, ?, ?, ?)
    """, (
        menfess_id,
        discussion_chat_id,
        message_id,
        parent_message_id,
        author_user_id,
        int(time.time()),
        (content or "")[:4000],
    ))
    conn.commit()
    conn.close()


def find_discussion_message(chat_id, message_id):
    conn = db()
    row = conn.execute("""
        SELECT * FROM discussion_messages
        WHERE discussion_chat_id=? AND message_id=?
    """, (chat_id, message_id)).fetchone()
    conn.close()
    return row


def get_discussion_message_by_db_id(db_id):
    conn = db()
    row = conn.execute(
        "SELECT * FROM discussion_messages WHERE id=?",
        (db_id,),
    ).fetchone()
    conn.close()
    return row


# ============================================================
# COMMUNITY FEATURES
# ============================================================

QOTD = [
    "Kalau besok libur total, kamu paling pengen ngapain?",
    "Makanan yang nggak pernah kamu tolak apa?",
    "Tim begadang atau tim bangun pagi?",
    "Hal receh apa yang akhir-akhir ini bikin kamu ketawa?",
    "Kalau bisa langsung jago satu skill, pilih apa?",
    "Lagu apa yang lagi paling sering kamu putar?",
    "Mending WiFi gratis seumur hidup atau makanan gratis seumur hidup?",
]

MISSION_POOL = [
    ("comment3", "Komentar 3 kali di base"),
    ("comment5", "Komentar 5 kali di base"),
    ("menfess1", "Kirim 1 menfess"),
    ("comment10", "Komentar 10 kali di base"),
]

TITLE_RULES = [
    ("◆ UNDERGROUND LEGEND", 500),
    ("◆ UNDERGROUND ADDICT", 250),
    ("◆ TALKATIVE", 100),
    ("◈ ACTIVE MEMBER", 50),
    ("◉ NEW ARRIVAL", 0),
]


def day_key(ts=None):
    return time.strftime("%Y-%m-%d", time.localtime(ts or time.time()))


def get_user_title(user_id):
    rows = get_period_leaderboard("all_time", 1000)
    points = next((int(r["points"]) for r in rows if r["user_id"] == user_id), 0)
    for title, threshold in TITLE_RULES:
        if points >= threshold:
            return title
    return "◉ NEW ARRIVAL"


def ensure_daily_missions():
    key = day_key()
    conn = db()
    row = conn.execute("SELECT * FROM daily_missions WHERE day_key=?", (key,)).fetchone()
    if row:
        conn.close(); return row
    # Rotate deterministically each day so everyone sees the same missions.
    offset = int(time.strftime("%j")) % len(MISSION_POOL)
    picks = [MISSION_POOL[(offset+i) % len(MISSION_POOL)] for i in range(3)]
    conn.execute("INSERT INTO daily_missions VALUES (?,?,?,?)", (key,picks[0][0],picks[1][0],picks[2][0]))
    conn.commit()
    row = conn.execute("SELECT * FROM daily_missions WHERE day_key=?", (key,)).fetchone()
    conn.close(); return row


def activity_counts_today(user_id):
    """Count today's real source activities; never depend on the legacy activity_log."""
    start = int(time.time()) - (int(time.strftime("%H"))*3600 + int(time.strftime("%M"))*60 + int(time.strftime("%S")))
    conn = db()
    m = conn.execute(
        "SELECT COUNT(*) n FROM menfess WHERE sender_id=? AND created_at>=?",
        (user_id, start),
    ).fetchone()["n"]
    c = conn.execute(
        "SELECT COUNT(*) n FROM discussion_messages WHERE author_user_id=? AND parent_message_id IS NOT NULL AND created_at>=?",
        (user_id, start),
    ).fetchone()["n"]
    conn.close()
    return int(m), int(c)


def mission_progress(user_id, mission_key):
    m,c = activity_counts_today(user_id)
    return {"menfess1": (m,1), "comment3":(c,3), "comment5":(c,5), "comment10":(c,10)}[mission_key]


def claim_daily_mission(user_id, mission_key):
    key=day_key(); progress,target=mission_progress(user_id,mission_key)
    if progress < target: return False, f"Masih {progress}/{target}."
    conn=db()
    try:
        conn.execute("INSERT INTO mission_claims VALUES (?,?,?,?)",(key,user_id,mission_key,int(time.time())))
        conn.commit(); ok=True
    except sqlite3.IntegrityError: ok=False
    conn.close()
    return ok, ("Misi selesai. +10 Mission Points." if ok else "Misi ini sudah kamu klaim hari ini.")


def daily_mission_text(user_id):
    row=ensure_daily_missions(); conn=db()
    claimed={r["mission_key"] for r in conn.execute("SELECT mission_key FROM mission_claims WHERE day_key=? AND user_id=?",(day_key(),user_id)).fetchall()}; conn.close()
    labels={k:v for k,v in MISSION_POOL}
    lines=["◆ DAILY MISSION","", "Selesaikan misi hari ini!"]
    for k in (row["mission1"],row["mission2"],row["mission3"]):
        p,target=mission_progress(user_id,k); mark="✓" if k in claimed else f"{p}/{target}"
        lines.append(f"{mark} {labels[k]}")
    return "\n".join(lines)


def mission_menu(user_id):
    row=ensure_daily_missions()
    labels={k:v for k,v in MISSION_POOL}
    return InlineKeyboardMarkup([
        [InlineKeyboardButton(f"✓ {labels[row['mission1']]}",callback_data=f"mission:{row['mission1']}" )],
        [InlineKeyboardButton(f"✓ {labels[row['mission2']]}",callback_data=f"mission:{row['mission2']}" )],
        [InlineKeyboardButton(f"✓ {labels[row['mission3']]}",callback_data=f"mission:{row['mission3']}" )],
        [InlineKeyboardButton("← COMMUNITY",callback_data="community")],
    ])



BADGE_RULES = [
    ("◉ NEW ARRIVAL", "Aktif dan mulai meramaikan RANDOM UNDERGROUND."),
    ("◈ ACTIVE MEMBER", "Mencapai 50 poin All-Time."),
    ("◆ TALKATIVE", "Mencapai 100 poin All-Time."),
    ("◆ UNDERGROUND ADDICT", "Mencapai 250 poin All-Time."),
    ("◆ UNDERGROUND LEGEND", "Mencapai 500 poin All-Time."),
    ("✦ MENFESS ADDICT", "Mengirim sedikitnya 25 menfess."),
    ("✦ CHATTERBOX", "Mengirim sedikitnya 100 komentar."),
    ("⚡ EVENT WINNER", "Pernah masuk daftar pemenang event."),
]


def get_profile_stats(user_id):
    """Profile statistics use the exact same V15 reset epoch as leaderboards."""
    conn = db()
    reset_row = conn.execute(
        "SELECT value FROM leaderboard_meta WHERE key='v15_reset_at'"
    ).fetchone()
    reset_at = int(reset_row["value"]) if reset_row else int(time.time())

    row = conn.execute("""
        SELECT
            (SELECT COUNT(*) FROM menfess
             WHERE sender_id=? AND created_at>=?) AS menfess_count,
            (SELECT COUNT(*) FROM discussion_messages
             WHERE author_user_id=? AND parent_message_id IS NOT NULL
             AND created_at>=?) AS comment_count
    """, (user_id, reset_at, user_id, reset_at)).fetchone()

    now = int(time.time())
    week_start = max(reset_at, now - 7 * 86400)
    month_start = max(reset_at, now - 30 * 86400)

    week = conn.execute("""
        SELECT
            (SELECT COUNT(*) FROM menfess
             WHERE sender_id=? AND created_at>=?) +
            (SELECT COUNT(*) FROM discussion_messages
             WHERE author_user_id=? AND parent_message_id IS NOT NULL
             AND created_at>=?) AS n
    """, (user_id, week_start, user_id, week_start)).fetchone()["n"]

    month = conn.execute("""
        SELECT
            (SELECT COUNT(*) FROM menfess
             WHERE sender_id=? AND created_at>=?) +
            (SELECT COUNT(*) FROM discussion_messages
             WHERE author_user_id=? AND parent_message_id IS NOT NULL
             AND created_at>=?) AS n
    """, (user_id, month_start, user_id, month_start)).fetchone()["n"]

    # Only events created after the V15 reset can contribute an Event Win.
    winners = conn.execute("""
        SELECT COUNT(*) AS n
        FROM events e
        JOIN event_points ep ON ep.event_id=e.id
        WHERE ep.user_id=?
          AND e.started_at>=?
          AND e.active=0
          AND (
              SELECT COUNT(*) FROM event_points ep2
              WHERE ep2.event_id=e.id
                AND (ep2.menfess_count * ?) + (ep2.comment_count * ?) >
                    (ep.menfess_count * ?) + (ep.comment_count * ?)
          ) < COALESCE(e.winner_count, 3)
    """, (
        user_id,
        reset_at,
        POINT_PER_MENFESS, POINT_PER_COMMENT,
        POINT_PER_MENFESS, POINT_PER_COMMENT,
    )).fetchone()["n"]

    conn.close()

    menfess = int(row["menfess_count"] or 0)
    comments = int(row["comment_count"] or 0)
    points = menfess * POINT_PER_MENFESS + comments * POINT_PER_COMMENT

    return {
        "points": points,
        "menfess": menfess,
        "comments": comments,
        "week_activity": int(week or 0),
        "month_activity": int(month or 0),
        "event_wins": int(winners or 0),
    }


def get_public_rank(user_id):
    if user_id in HIDDEN_LEADERBOARD_USER_IDS:
        return None
    rows = get_period_leaderboard("all_time", 100000)
    for i, r in enumerate(rows, 1):
        if r["user_id"] == user_id:
            return i
    return None


def get_profile_badges(stats):
    badges = []
    points = stats["points"]
    if points >= 500:
        badges.append(BADGE_RULES[4])
    elif points >= 250:
        badges.append(BADGE_RULES[3])
    elif points >= 100:
        badges.append(BADGE_RULES[2])
    elif points >= 50:
        badges.append(BADGE_RULES[1])
    else:
        badges.append(BADGE_RULES[0])

    if stats["menfess"] >= 25:
        badges.append(BADGE_RULES[5])
    if stats["comments"] >= 100:
        badges.append(BADGE_RULES[6])
    if stats["event_wins"] > 0:
        badges.append(BADGE_RULES[7])
    return badges


def profile_text(target_user):
    stats = get_profile_stats(target_user.id)
    hidden = target_user.id in HIDDEN_LEADERBOARD_USER_IDS
    rank = None if hidden else get_public_rank(target_user.id)
    title = get_user_title(target_user.id)
    display = f"@{target_user.username}" if target_user.username else (target_user.first_name or f"User {target_user.id}")

    lines = [
        "◈ RANDOM UNDERGROUND // PROFILE",
        "",
        f"◈ {display}",
        f"◆ Rank Title: {title}",
        f"◆ All-Time Points: {stats['points']}",
    ]
    if hidden:
        lines.append("▪ Rank: disembunyikan")
    else:
        lines.append(f"◆ All-Time Rank: #{rank}" if rank else "▪ Rank All-Time: belum masuk leaderboard")

    lines += [
        f"◆ Weekly Activity: {stats['week_activity']}",
        f"◆ Monthly Activity: {stats['month_activity']}",
        f"◆ Anonymous Posts: {stats['menfess']}",
        f"◆ Comments: {stats['comments']}",
        f"◆ Event Wins: {stats['event_wins']}",
        "",
        "◆ BADGES",
    ]
    badges = get_profile_badges(stats)
    lines.extend(f"• {name}" for name, _ in badges)
    return "\n".join(lines)


def profile_menu(user_id):
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("◆ SEMUA BADGE", callback_data=f"profile:badges:{user_id}")],
        [InlineKeyboardButton("← MENU", callback_data="back_menu")],
    ])


def profile_badges_text(user_id):
    stats = get_profile_stats(user_id)
    earned = {name for name, _ in get_profile_badges(stats)}
    lines = ["◆ PROFILE BADGES", ""]
    for name, description in BADGE_RULES:
        mark = "✓" if name in earned else "·"
        lines.append(f"{mark} {name}\n   {description}")
    return "\n".join(lines)


async def profile_command(update, context):
    if not update.effective_user or not update.message:
        return
    target = update.effective_user

    # /profile as a reply shows the replied user's public profile.
    if update.message.reply_to_message and update.message.reply_to_message.from_user:
        target = update.message.reply_to_message.from_user
    elif context.args:
        wanted = context.args[0].lstrip("@").lower()
        conn = db()
        row = conn.execute(
            "SELECT * FROM users WHERE lower(username)=?",
            (wanted,),
        ).fetchone()
        conn.close()
        if not row:
            await update.message.reply_text("✕ Username itu belum ditemukan di database RANDOM UNDERGROUND.")
            return
        # Build a lightweight Telegram-like target from saved DB data.
        class SavedUser:
            pass
        target = SavedUser()
        target.id = row["user_id"]
        target.username = row["username"]
        target.first_name = row["first_name"]

    save_user(update.effective_user)
    await update.message.reply_text(
        profile_text(target),
        reply_markup=profile_menu(target.id),
    )


def community_menu():
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("◆ DAILY MISSION",callback_data="community:mission")],
        [InlineKeyboardButton("◆ QUESTION OF THE DAY",callback_data="community:qotd")],
        [InlineKeyboardButton("◆ TITLE & BADGE",callback_data="community:title")],
        [InlineKeyboardButton("◆ WEEKLY MVP",callback_data="community:mvp")],
        [InlineKeyboardButton("◆ COMMENT SPOTLIGHT",callback_data="community:comment")],
        [InlineKeyboardButton("◆ MYSTERY DROP",callback_data="community:box")],
        [InlineKeyboardButton("◆ TRENDING",callback_data="community:trending")],
        [InlineKeyboardButton("← MENU",callback_data="back_menu")],
    ])


def community_text():
    return "◇ RANDOM UNDERGROUND // COMMUNITY\n\nSelect a module:"


def weekly_mvp_text():
    rows=get_period_leaderboard("weekly",20)
    visible=[r for r in rows if r["user_id"] not in HIDDEN_LEADERBOARD_USER_IDS]
    if not visible: return "WEEKLY MVP\n\nBelum ada MVP minggu ini."
    r=visible[0]; name=f"@{r['username']}" if r["username"] else (r["first_name"] or "Member")
    return f"WEEKLY MVP\n\n▪ {name}\n▪ {r['points']} poin minggu ini\n\nSiapa yang bakal ngerebut posisi MVP minggu depan?"


def comment_spotlight_text():
    conn=db()
    row=conn.execute('''SELECT d.*, COUNT(r.id) replies FROM discussion_messages d LEFT JOIN discussion_messages r ON r.parent_message_id=d.message_id WHERE d.parent_message_id IS NOT NULL GROUP BY d.id ORDER BY replies DESC,d.created_at DESC LIMIT 1''').fetchone()
    conn.close()
    if not row: return "COMMENT SPOTLIGHT\n\nBelum ada komentar yang bisa ditampilkan."
    text=row["content"] or "(komentar tanpa teks)"; text=text[:300]
    return f"COMMENT SPOTLIGHT\n\n✨ {text}\n\nKomentar ini paling banyak mendapat balasan!"


def trending_text():
    conn=db()
    rows=conn.execute("SELECT content, created_at FROM menfess WHERE created_at>=?",(int(time.time())-7*86400,)).fetchall()
    conn.close()
    counts={}
    for r in rows:
        for h in re.findall(r"#[A-Za-z0-9_]+", r["content"] or ""):
            h=h.lower(); counts[h]=counts.get(h,0)+1
    if not counts: return "TRENDING\n\nBelum cukup data minggu ini."
    top=sorted(counts.items(), key=lambda x:(-x[1],x[0]))[:5]
    return "TRENDING 7 HARI\n\n"+"\n".join(f"{i}. {h} — {n} post" for i,(h,n) in enumerate(top,1))


def mystery_box_text(user_id):
    key=day_key(); conn=db(); row=conn.execute("SELECT reward FROM mystery_claims WHERE day_key=? AND user_id=?",(key,user_id)).fetchone(); conn.close()
    if row: return f"MYSTERY BOX\n\nHari ini hadiahnya: {row['reward']}\n\nBesok coba lagi!"
    # Non-monetary reward; deterministic by user/day.
    rewards=["Badge Lucky Member","◈ Badge Night Walker","Badge Active","Title Mini MVP"]
    reward=rewards[(user_id+int(time.strftime('%j')))%len(rewards)]
    conn=db(); conn.execute("INSERT INTO mystery_claims VALUES (?,?,?,?)",(key,user_id,reward,int(time.time()))); conn.commit(); conn.close()
    return f"MYSTERY BOX\n\nKamu mendapatkan:\n\n{reward}\n\nBalik lagi besok!"

# ============================================================
# EVENT SYSTEM
# ============================================================

def get_active_event():
    now = int(time.time())
    conn = db()
    row = conn.execute("""
        SELECT * FROM events
        WHERE active=1
        ORDER BY id DESC
        LIMIT 1
    """).fetchone()

    if row and row["ends_at"] and now >= row["ends_at"]:
        conn.execute(
            "UPDATE events SET active=0, stopped_at=? WHERE id=?",
            (now, row["id"]),
        )
        conn.commit()
        row = None

    conn.close()
    return row


def _normalized_comment(text: str) -> str:
    return re.sub(r"\s+", " ", (text or "").strip()).lower()


def _word_tokens(text: str):
    # Words/numbers only; punctuation and emoji do not count as words.
    return re.findall(r"[a-zA-Z0-9]+", text or "")


def event_activity_is_valid(text: str, activity_type: str) -> bool:
    """Only meaningful text activity earns points; one-word/emoji-only comments do not."""
    if activity_type == "comment":
        text = _normalized_comment(text)
        tokens = _word_tokens(text)
        if len(tokens) <= 1:
            return False
        # Obvious repeated-token spam, e.g. "wkwk wkwk wkwk".
        if len(tokens) >= 3 and len(set(tokens)) == 1:
            return False
        return True

    text = _normalized_comment(text)
    if not text:
        return False
    return True


def get_v16_comment_points_at():
    conn = db()
    row = conn.execute(
        "SELECT value FROM leaderboard_meta WHERE key='v16_comment_points_at'"
    ).fetchone()
    conn.close()
    return int(row["value"]) if row else int(time.time())


def get_new_comment_weight(user_id: int, menfess_id: int) -> float:
    """Weight for this user's next valid comment in the same post after V16."""
    cutoff = get_v16_comment_points_at()
    conn = db()
    rows = conn.execute("""
        SELECT content FROM discussion_messages
        WHERE author_user_id=? AND menfess_id=? AND parent_message_id IS NOT NULL
          AND created_at>=?
        ORDER BY created_at ASC, id ASC
    """, (user_id, menfess_id, cutoff)).fetchall()
    conn.close()
    valid_count = sum(1 for r in rows if event_activity_is_valid(r["content"] or "", "comment"))
    return (1.0, 1.0, 0.5, 0.5)[valid_count] if valid_count < 4 else 0.1


def _add_event_score(user_id, menfess=0, comment_score=0.0, comment_count=0):
    event = get_active_event()
    if not event:
        return
    conn = db()
    conn.execute("""
        INSERT INTO event_points(
            event_id, user_id, menfess_count, comment_count, menfess_score, comment_score
        ) VALUES (?, ?, ?, ?, ?, ?)
        ON CONFLICT(event_id, user_id) DO UPDATE SET
            menfess_count=menfess_count + excluded.menfess_count,
            comment_count=comment_count + excluded.comment_count,
            menfess_score=menfess_score + excluded.menfess_score,
            comment_score=comment_score + excluded.comment_score
    """, (event["id"], user_id, menfess, comment_count, menfess * POINT_PER_MENFESS, comment_score))
    conn.commit()
    conn.close()


def add_event_points(user_id, menfess=0, comment=0, menfess_id=None):
    """Add new activity points without changing any pre-V16 Event score."""
    if menfess:
        _add_event_score(user_id, menfess=menfess)
    if comment and menfess_id is not None:
        _add_event_score(user_id, comment_score=get_new_comment_weight(user_id, menfess_id), comment_count=1)


def get_event_leaderboard(event_id, limit=10):
    conn = db()
    rows = conn.execute("""
        SELECT ep.user_id, ep.menfess_count, ep.comment_count,
               (ep.menfess_score + ep.comment_score) AS points,
               COALESCE(u.username, '') AS username,
               COALESCE(u.first_name, '') AS first_name
        FROM event_points ep
        LEFT JOIN users u ON u.user_id = ep.user_id
        WHERE ep.event_id=?
        ORDER BY points DESC, ep.comment_score DESC, ep.menfess_score DESC
        LIMIT ?
    """, (event_id, limit)).fetchall()
    conn.close()
    return rows

def _insert_activity(conn, user_id, activity_type, created_at, source_id=None):
    """Insert an activity while adapting to the existing activity_log schema."""
    cols = {
        row["name"]
        for row in conn.execute("PRAGMA table_info(activity_log)").fetchall()
    }

    values = {
        "user_id": user_id,
        "activity_type": activity_type,
        "created_at": created_at,
    }

    if "content_hash" in cols:
        import hashlib
        raw = f"{user_id}:{activity_type}:{created_at}:{source_id or ''}"
        values["content_hash"] = hashlib.sha256(raw.encode()).hexdigest()

    insert_cols = [c for c in ("user_id", "activity_type", "created_at", "content_hash")
                   if c in cols]
    placeholders = ",".join("?" for _ in insert_cols)
    conn.execute(
        f"INSERT INTO activity_log({','.join(insert_cols)}) VALUES ({placeholders})",
        [values[c] for c in insert_cols],
    )


def record_activity(user_id, activity_type, source_id=None):
    if is_owner(user_id):
        return
    conn = db()
    _insert_activity(conn, user_id, activity_type, int(time.time()), source_id)
    conn.commit()
    conn.close()


def get_period_leaderboard(period, limit=20):
    """Live leaderboard from real source tables after the V15 reset point.

    This intentionally does NOT read activity_log. The leaderboard is rebuilt
    from menfess and real discussion comments every time it is opened, so new
    activity is reflected immediately without a restart or backfill.
    """
    now = int(time.time())

    if period == "weekly":
        start = now - 7 * 86400
    elif period == "monthly":
        t = time.localtime(now)
        start_struct = time.struct_time((t.tm_year, t.tm_mon, 1, 0, 0, 0, 0, 0, -1))
        start = int(time.mktime(start_struct))
    else:
        start = 0

    conn = db()
    reset_row = conn.execute(
        "SELECT value FROM leaderboard_meta WHERE key='v15_reset_at'"
    ).fetchone()
    reset_at = int(reset_row["value"]) if reset_row else 0
    start = max(start, reset_at)
    cutoff_v16 = get_v16_comment_points_at()
    rows = conn.execute("""
        WITH menfess_acts AS (
            SELECT sender_id AS user_id, COUNT(*) AS menfess_count, COUNT(*) * ? AS menfess_points
            FROM menfess
            WHERE created_at >= ? AND sender_id IS NOT NULL
            GROUP BY sender_id
        ),
        comment_rows AS (
            SELECT author_user_id AS user_id, menfess_id, created_at, id, content,
                   CASE WHEN created_at < ? THEN 1.0
                        ELSE ROW_NUMBER() OVER (PARTITION BY author_user_id, menfess_id ORDER BY created_at, id) END AS seq
            FROM discussion_messages
            WHERE created_at >= ? AND author_user_id IS NOT NULL AND parent_message_id IS NOT NULL
        ),
        comment_acts AS (
            SELECT user_id, COUNT(*) AS comment_count,
                   SUM(CASE WHEN seq=1 OR seq=2 THEN 1.0 WHEN seq=3 OR seq=4 THEN 0.5 ELSE 0.1 END) AS comment_points
            FROM comment_rows
            WHERE content IS NOT NULL AND length(trim(content)) > 0
              AND (created_at < ? OR length(trim(content)) - length(replace(trim(content),' ','')) + 1 > 1)
            GROUP BY user_id
        ),
        combined AS (
            SELECT COALESCE(m.user_id,c.user_id) AS user_id,
                   COALESCE(m.menfess_count,0) AS menfess_count,
                   COALESCE(c.comment_count,0) AS comment_count,
                   COALESCE(m.menfess_points,0) + COALESCE(c.comment_points,0) AS points
            FROM menfess_acts m LEFT JOIN comment_acts c ON c.user_id=m.user_id
            UNION ALL
            SELECT c.user_id,0,c.comment_count,c.comment_points
            FROM comment_acts c LEFT JOIN menfess_acts m ON m.user_id=c.user_id
            WHERE m.user_id IS NULL
        )
        SELECT x.user_id, x.menfess_count, x.comment_count, x.points,
               (x.menfess_count + x.comment_count) AS activity_count,
               COALESCE(u.username,'') AS username, COALESCE(u.first_name,'') AS first_name
        FROM combined x LEFT JOIN users u ON u.user_id=x.user_id
        WHERE x.user_id NOT IN (?, ?)
        ORDER BY points DESC, activity_count DESC, x.user_id ASC
        LIMIT ?
    """, (POINT_PER_MENFESS, start, cutoff_v16, start, cutoff_v16,
          5480598942, 7005302744, limit)).fetchall()
    conn.close()
    return rows


def leaderboard_menu():
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("◆ ALL-TIME", callback_data="lb:all_time"),
         InlineKeyboardButton("◆ WEEKLY", callback_data="lb:weekly")],
        [InlineKeyboardButton("◆ MONTHLY", callback_data="lb:monthly"),
         InlineKeyboardButton("◆ EVENT", callback_data="lb:event")],
        [InlineKeyboardButton("← MENU", callback_data="back_menu")],
    ])


def format_period_leaderboard(period):
    titles = {
        "all_time": "ALL-TIME TOP 20",
        "weekly": "WEEKLY TOP 20",
        "monthly": "MONTHLY TOP 20",
    }
    rows = get_period_leaderboard(period, 20)
    if not rows:
        return f"{titles[period]}\n\nBelum ada peserta."
    medals = ["01", "02", "03"]
    lines = [titles[period], ""]
    for i, row in enumerate(rows, 1):
        name = f"@{row['username']}" if row['username'] else (row['first_name'] or f"User {row['user_id']}")
        prefix = medals[i-1] if i <= 3 else f"{i}."
        lines.append(f"{prefix} {name} — {row['points']:g} poin")
    return "\n".join(lines)


def format_public_event_leaderboard():
    event = get_active_event()
    if not event:
        conn = db()
        event = conn.execute("SELECT * FROM events ORDER BY id DESC LIMIT 1").fetchone()
        conn.close()
    if not event:
        return "EVENT\n\nBelum ada event."
    rows = [r for r in get_event_leaderboard(event["id"], 30) if r["user_id"] not in HIDDEN_LEADERBOARD_USER_IDS][:20]
    if not rows:
        return f"EVENT #{event['id']}\n\nBelum ada peserta."
    medals = ["01", "02", "03"]
    lines = [f"EVENT #{event['id']} — TOP 20", ""]
    for i, row in enumerate(rows, 1):
        name = f"@{row['username']}" if row['username'] else (row['first_name'] or f"User {row['user_id']}")
        prefix = medals[i-1] if i <= 3 else f"{i}."
        lines.append(f"{prefix} {name} — {row['points']:g} poin")
    return "\n".join(lines)


def leaderboard_periods():
    """Leaderboard model used by RANDOM UNDERGROUND.

    all_time: permanent, never reset.
    weekly: activity from the current 7-day period.
    monthly: activity from the current calendar month.
    event: activity only inside the active event.
    """
    return ("all_time", "weekly", "monthly", "event")


def start_event(event_name, duration_days, winner_count):
    conn = db()
    now = int(time.time())
    conn.execute(
        "UPDATE events SET active=0, stopped_at=? WHERE active=1",
        (now,),
    )
    ends_at = now + (duration_days * 86400)
    cur = conn.execute("""
        INSERT INTO events(
            event_name, started_at, ends_at, active, winner_count
        )
        VALUES (?, ?, ?, 1, ?)
    """, (event_name, now, ends_at, winner_count))
    event_id = cur.lastrowid
    conn.commit()
    event = conn.execute("SELECT * FROM events WHERE id=?", (event_id,)).fetchone()
    conn.close()
    return event


def stop_event():
    conn = db()
    now = int(time.time())
    event = conn.execute(
        "SELECT * FROM events WHERE active=1 ORDER BY id DESC LIMIT 1"
    ).fetchone()
    if not event:
        conn.close()
        return None
    conn.execute(
        "UPDATE events SET active=0, stopped_at=? WHERE id=?",
        (now, event["id"]),
    )
    conn.commit()
    event = conn.execute("SELECT * FROM events WHERE id=?", (event["id"],)).fetchone()
    conn.close()
    return event



def format_event_end(event):
    if not event["ends_at"]:
        return "manual — gunakan /event_stop"
    remaining = max(0, event["ends_at"] - int(time.time()))
    days = remaining // 86400
    hours = (remaining % 86400) // 3600
    return f"{days} hari {hours} jam lagi"


# ============================================================
# TEXT / MODERATION
# ============================================================

def is_owner(user_id):
    return int(user_id) in OWNER_USER_IDS


def quota_text(user_id):
    if is_owner(user_id):
        return "∞/∞"
    return f"{max(0, MAX_SENDS - get_used_count(user_id))}/{MAX_SENDS}"


def normalize_for_filter(text):
    text = (text or "").lower()
    text = re.sub(r"[\W_]+", " ", text, flags=re.UNICODE)
    return f" {text} "


def contains_bad_word(text):
    normalized = normalize_for_filter(text)
    for word in BAD_WORDS:
        if f" {word} " in normalized:
            return True
    return False


def get_warning_count(user_id):
    conn = db()
    row = conn.execute(
        "SELECT warnings FROM comment_warnings WHERE user_id=?",
        (user_id,),
    ).fetchone()
    conn.close()
    return int(row["warnings"]) if row else 0


def add_warning(user_id):
    now = int(time.time())
    conn = db()
    conn.execute("""
        INSERT INTO comment_warnings(user_id, warnings, updated_at)
        VALUES (?, 1, ?)
        ON CONFLICT(user_id) DO UPDATE SET
            warnings=warnings+1,
            updated_at=excluded.updated_at
    """, (user_id, now))
    row = conn.execute(
        "SELECT warnings FROM comment_warnings WHERE user_id=?",
        (user_id,),
    ).fetchone()
    conn.commit()
    conn.close()
    return int(row["warnings"])


# ============================================================
# MODERASI: IDENTITAS PENGIRIM, BAN/MUTE, LOG CHANNEL
# ============================================================

def reset_warnings(user_id):
    conn = db()
    conn.execute("DELETE FROM comment_warnings WHERE user_id=?", (int(user_id),))
    conn.commit()
    conn.close()


def get_user_row(user_id):
    conn = db()
    row = conn.execute(
        "SELECT * FROM users WHERE user_id=?", (int(user_id),)
    ).fetchone()
    conn.close()
    return row


def find_user_by_username(username):
    uname = (username or "").lstrip("@").strip().lower()
    if not uname:
        return None
    conn = db()
    row = conn.execute(
        "SELECT * FROM users WHERE LOWER(username)=? ORDER BY created_at LIMIT 1",
        (uname,),
    ).fetchone()
    conn.close()
    return row


def fmt_ts(ts):
    if not ts:
        return "-"
    return time.strftime("%d %b %Y %H:%M", time.localtime(int(ts)))


def fmt_duration(seconds):
    seconds = int(seconds)
    if seconds <= 0:
        return "0 menit"
    if seconds < 3600:
        return f"{max(1, seconds // 60)} menit"
    if seconds < 86400:
        hours, rest = divmod(seconds, 3600)
        minutes = rest // 60
        return f"{hours} jam" + (f" {minutes} menit" if minutes else "")
    days, rest = divmod(seconds, 86400)
    hours = rest // 3600
    return f"{days} hari" + (f" {hours} jam" if hours else "")


# ------------------------------------------------------------
# BAN / MUTE / SHADOWBAN
# ------------------------------------------------------------

def get_ban(user_id):
    """Kembalikan baris ban yang masih berlaku, atau None.

    Mute yang sudah kedaluwarsa dibersihkan di sini supaya tidak perlu
    background job terpisah.
    """
    user_id = int(user_id)
    now = int(time.time())
    conn = db()
    row = conn.execute("SELECT * FROM bans WHERE user_id=?", (user_id,)).fetchone()
    if row and row["banned_until"] and int(row["banned_until"]) <= now:
        conn.execute("DELETE FROM bans WHERE user_id=?", (user_id,))
        conn.commit()
        row = None
    conn.close()
    return row


def set_ban(user_id, mode, duration_seconds, reason, actor_id):
    """Pasang atau perbarui pembatasan user. duration_seconds 0 = permanen."""
    if mode not in BAN_MODES:
        raise ValueError(f"mode ban tidak dikenal: {mode}")
    user_id = int(user_id)
    now = int(time.time())
    until = now + int(duration_seconds) if duration_seconds else 0
    conn = db()
    conn.execute("""
        INSERT INTO bans(user_id, mode, banned_until, reason, actor_id, created_at)
        VALUES (?, ?, ?, ?, ?, ?)
        ON CONFLICT(user_id) DO UPDATE SET
            mode=excluded.mode,
            banned_until=excluded.banned_until,
            reason=excluded.reason,
            actor_id=excluded.actor_id,
            created_at=excluded.created_at
    """, (user_id, mode, until, (reason or "")[:500], int(actor_id), now))
    conn.commit()
    conn.close()
    return until


def remove_ban(user_id):
    conn = db()
    cur = conn.execute("DELETE FROM bans WHERE user_id=?", (int(user_id),))
    conn.commit()
    removed = cur.rowcount > 0
    conn.close()
    return removed


def list_bans(limit=50):
    now = int(time.time())
    conn = db()
    conn.execute("DELETE FROM bans WHERE banned_until>0 AND banned_until<=?", (now,))
    conn.commit()
    rows = conn.execute("""
        SELECT b.*, u.username, u.first_name
        FROM bans b LEFT JOIN users u ON u.user_id=b.user_id
        ORDER BY b.created_at DESC LIMIT ?
    """, (int(limit),)).fetchall()
    conn.close()
    return rows


def log_mod_action(actor_id, target_id, action, detail=""):
    conn = db()
    conn.execute("""
        INSERT INTO mod_actions(actor_id, target_id, action, detail, created_at)
        VALUES (?, ?, ?, ?, ?)
    """, (int(actor_id), int(target_id), action, (detail or "")[:500], int(time.time())))
    conn.commit()
    conn.close()


def get_mod_actions(limit=15, target_id=None):
    conn = db()
    if target_id is None:
        rows = conn.execute(
            "SELECT * FROM mod_actions ORDER BY created_at DESC LIMIT ?",
            (int(limit),),
        ).fetchall()
    else:
        rows = conn.execute("""
            SELECT * FROM mod_actions WHERE target_id=?
            ORDER BY created_at DESC LIMIT ?
        """, (int(target_id), int(limit))).fetchall()
    conn.close()
    return rows


def ban_status_line(user_id):
    ban = get_ban(user_id)
    if not ban:
        return "Tidak ada pembatasan aktif"
    label = BAN_MODE_LABEL.get(ban["mode"], ban["mode"].upper())
    if ban["banned_until"]:
        remaining = fmt_duration(int(ban["banned_until"]) - int(time.time()))
        label += f" (sisa {remaining})"
    else:
        label += " (permanen)"
    if ban["reason"]:
        label += f" — {ban['reason']}"
    return label


# ------------------------------------------------------------
# IDENTITAS PENGIRIM
# ------------------------------------------------------------

def moderation_stats(user_id):
    """Angka mentah untuk moderasi: semua-waktu, tidak terpengaruh reset leaderboard."""
    user_id = int(user_id)
    conn = db()
    row = conn.execute("""
        SELECT
            (SELECT COUNT(*) FROM menfess WHERE sender_id=?) AS menfess_total,
            (SELECT COUNT(*) FROM discussion_messages
             WHERE author_user_id=? AND parent_message_id IS NOT NULL) AS comment_total,
            (SELECT COUNT(*) FROM menfess
             WHERE sender_id=? AND created_at>=?) AS menfess_24h,
            (SELECT warnings FROM comment_warnings WHERE user_id=?) AS warnings
    """, (user_id, user_id, user_id, int(time.time()) - 86400, user_id)).fetchone()
    conn.close()
    return {
        "menfess_total": int(row["menfess_total"] or 0),
        "comment_total": int(row["comment_total"] or 0),
        "menfess_24h": int(row["menfess_24h"] or 0),
        "warnings": int(row["warnings"] or 0),
    }


def user_label(user_id, user_row=None):
    """Nama + @username untuk ditampilkan di log. Aman untuk HTML."""
    row = user_row if user_row is not None else get_user_row(user_id)
    name = (row["first_name"] if row else "") or "Tanpa nama"
    uname = (row["username"] if row else "") or ""
    label = html.escape(name)
    if uname:
        label += f" (@{html.escape(uname)})"
    return label


def identity_block(user_id, user_row=None):
    """Blok identitas standar yang dipakai /whois dan log channel."""
    user_id = int(user_id)
    row = user_row if user_row is not None else get_user_row(user_id)
    stats = moderation_stats(user_id)
    joined = fmt_ts(row["created_at"]) if row else "-"

    lines = [
        f"👤 {user_label(user_id, row)}",
        f"🆔 <code>{user_id}</code>",
        f"🔗 <a href=\"tg://user?id={user_id}\">Buka profil</a>",
        f"📅 Terdaftar di bot: {joined}",
        f"📊 {stats['menfess_total']} menfess · {stats['comment_total']} komentar"
        f" · {stats['menfess_24h']} menfess/24 jam",
        f"⚠️ Warning: {stats['warnings']}/{MAX_COMMENT_WARNINGS}",
        f"🚫 Status: {html.escape(ban_status_line(user_id))}",
    ]
    if row is None:
        lines.append("ℹ️ User ini belum pernah /start di bot.")
    return "\n".join(lines)


def channel_post_url(channel_message_id):
    return (
        f"https://t.me/{CHANNEL_USERNAME.lstrip('@')}/{channel_message_id}"
    )


# ------------------------------------------------------------
# LOG CHANNEL
# ------------------------------------------------------------

def get_setting(key, default=None):
    conn = db()
    row = conn.execute(
        "SELECT value FROM bot_settings WHERE key=?", (key,)
    ).fetchone()
    conn.close()
    return row["value"] if row else default


def set_setting(key, value):
    conn = db()
    conn.execute(
        "INSERT INTO bot_settings(key, value) VALUES (?, ?) "
        "ON CONFLICT(key) DO UPDATE SET value=excluded.value",
        (key, str(value)),
    )
    conn.commit()
    conn.close()


def delete_setting(key):
    conn = db()
    conn.execute("DELETE FROM bot_settings WHERE key=?", (key,))
    conn.commit()
    conn.close()


def log_target():
    """Chat tujuan log, urut prioritas:

      1. pengaturan runtime di DB (dipasang lewat tombol / /setlog)
      2. env RANDOMUNDERGROUND_LOG_CHAT_ID
      3. DM owner pertama

    Nomor 1 ada supaya log channel bisa dipasang dari dalam Telegram tanpa
    perlu mengedit .envo dan restart container.
    """
    stored = get_setting("log_chat_id")
    if stored:
        try:
            return int(stored)
        except ValueError:
            if stored.startswith("@"):
                return stored
    if LOG_CHAT_ID is not None:
        return LOG_CHAT_ID
    return OWNER_USER_ID


def log_target_source():
    if get_setting("log_chat_id"):
        return "diatur dari dalam bot"
    if LOG_CHAT_ID is not None:
        return "dari env RANDOMUNDERGROUND_LOG_CHAT_ID"
    return "belum diatur, jatuh ke DM owner"


async def send_log(bot, text, reply_markup=None):
    """Kirim satu entri ke log channel. Kegagalan tidak boleh mengganggu bot."""
    try:
        return await bot.send_message(
            chat_id=log_target(),
            text=text,
            parse_mode="HTML",
            reply_markup=reply_markup,
            disable_web_page_preview=True,
        )
    except Exception:
        logging.exception(
            "Gagal mengirim log ke %s (%s). Pastikan bot admin di log channel "
            "dengan izin Post Messages, lalu pasang ulang dengan /setlog.",
            log_target(), log_target_source(),
        )
        return None


def mod_action_menu(user_id, menfess_id=None, comment_db_id=None):
    """Tombol aksi cepat di bawah setiap entri log."""
    rows = [
        [
            InlineKeyboardButton("🚫 BAN", callback_data=f"mod:ban:{user_id}"),
            InlineKeyboardButton("🔇 MUTE 24J", callback_data=f"mod:mute:{user_id}"),
        ],
        [
            InlineKeyboardButton("👻 SHADOWBAN", callback_data=f"mod:shadow:{user_id}"),
            InlineKeyboardButton("⚠️ WARNING", callback_data=f"mod:warn:{user_id}"),
        ],
    ]
    last = [InlineKeyboardButton("🔎 RIWAYAT", callback_data=f"mod:who:{user_id}")]
    if menfess_id is not None:
        last.append(
            InlineKeyboardButton("🗑 HAPUS POST", callback_data=f"mod:delpost:{menfess_id}")
        )
    elif comment_db_id is not None:
        last.append(
            InlineKeyboardButton("🗑 HAPUS KOMEN", callback_data=f"mod:delcom:{comment_db_id}")
        )
    rows.append(last)
    rows.append([InlineKeyboardButton("✓ BEBASKAN", callback_data=f"mod:unban:{user_id}")])
    return InlineKeyboardMarkup(rows)


def never_fails(func):
    """Pembungkus untuk fungsi log: kegagalan dicatat, tidak pernah dilempar.

    Penting karena log_menfess dipanggil di dalam blok try process_new_menfess.
    Tanpa ini, error saat menyusun log akan membuat bot salah memberi tahu
    user bahwa menfess-nya gagal terkirim padahal sudah tayang.
    """
    @wraps(func)
    async def wrapper(*args, **kwargs):
        try:
            return await func(*args, **kwargs)
        except Exception:
            logging.exception("Gagal menyusun entri log moderasi (%s)", func.__name__)
            return None
    return wrapper


def preview_for_log(text, limit=600):
    text = (text or "").strip()
    if not text:
        return "<i>(tanpa teks)</i>"
    if len(text) > limit:
        text = text[:limit] + "…"
    return html.escape(text)


@never_fails
async def log_menfess(bot, menfess_id, user, content, channel_message_id, shadowed=False):
    header = "◈ MENFESS BARU" if not shadowed else "👻 MENFESS DITAHAN (SHADOWBAN)"
    ref = f"#RU{menfess_id}" if menfess_id else "tidak tayang"
    lines = [
        f"<b>{header}</b>  <code>{ref}</code>",
        "",
        identity_block(user.id),
        "",
        f"💬 {preview_for_log(content)}",
    ]
    if not shadowed and channel_message_id:
        lines.append("")
        lines.append(f"🔗 <a href=\"{channel_post_url(channel_message_id)}\">Lihat postingan</a>")
    await send_log(
        bot,
        "\n".join(lines),
        reply_markup=mod_action_menu(
            user.id, menfess_id=None if shadowed else menfess_id
        ),
    )


@never_fails
async def log_comment(bot, user, content, menfess, comment_db_id, note=None):
    lines = [
        "<b>💭 KOMENTAR</b>" if not note else f"<b>💭 KOMENTAR — {html.escape(note)}</b>",
        "",
        identity_block(user.id),
        "",
        f"💬 {preview_for_log(content)}",
    ]
    if menfess:
        lines.append("")
        lines.append(
            f"🔗 <a href=\"{channel_post_url(menfess['channel_message_id'])}\">"
            f"Postingan #RU{menfess['id']}</a>"
        )
    await send_log(
        bot,
        "\n".join(lines),
        reply_markup=mod_action_menu(user.id, comment_db_id=comment_db_id),
    )


@never_fails
async def log_event(bot, title, user_id, detail="", actor_id=None):
    lines = [f"<b>{html.escape(title)}</b>", "", identity_block(user_id)]
    if detail:
        lines += ["", html.escape(detail)]
    if actor_id:
        lines += ["", f"Oleh: {user_label(actor_id)} (<code>{actor_id}</code>)"]
    await send_log(bot, "\n".join(lines), reply_markup=mod_action_menu(user_id))


# ------------------------------------------------------------
# DETEKSI OTOMATIS CALON LOG CHANNEL
# ------------------------------------------------------------
# Telegram tidak punya API "daftar chat tempat bot ini berada", jadi satu-satunya
# cara mengetahui id sebuah channel privat adalah dengan menunggu satu peristiwa
# dari channel itu. Dua pemicu di bawah menangkapnya, lalu owner cukup menekan
# satu tombol. Tidak ada id yang perlu disalin tangan.

def _known_chat_ids():
    known = {CHANNEL_CHAT_ID, DISCUSSION_CHAT_ID, BOT_USER_ID}
    known.update(OWNER_USER_IDS)
    target = log_target()
    if isinstance(target, int):
        known.add(target)
    return {c for c in known if c is not None}


def setlog_offer_menu(chat_id):
    return InlineKeyboardMarkup([
        [InlineKeyboardButton(
            "✓ JADIKAN LOG CHANNEL",
            callback_data=f"mod:setlog:{chat_id}",
        )],
        [InlineKeyboardButton("✕ ABAIKAN", callback_data=f"mod:skiplog:{chat_id}")],
    ])


async def offer_as_log_channel(bot, chat, reason):
    """Tawarkan chat yang baru terdeteksi ke owner, sekali saja per chat."""
    if chat is None or chat.id in _known_chat_ids():
        return
    seen_key = f"offered_log:{chat.id}"
    if get_setting(seen_key):
        return
    set_setting(seen_key, "1")

    title = chat.title or getattr(chat, "full_name", None) or "(tanpa nama)"
    logging.info(
        "CHAT TERDETEKSI id=%s type=%s title=%r via=%s",
        chat.id, chat.type, title, reason,
    )
    for owner_id in OWNER_USER_IDS:
        try:
            await bot.send_message(
                owner_id,
                f"🔎 Bot terdeteksi di chat baru\n\n"
                f"Nama : {title}\n"
                f"Tipe : {chat.type}\n"
                f"Id   : {chat.id}\n"
                f"Cara : {reason}\n\n"
                "Jadikan ini log channel moderasi? Semua menfess beserta "
                "identitas pengirimnya akan dikirim ke sini.",
                reply_markup=setlog_offer_menu(chat.id),
            )
        except Exception:
            logging.info("Tidak bisa menawarkan log channel ke owner %s", owner_id)


async def my_chat_member_watcher(update, context):
    """Dipicu saat status bot berubah di sebuah chat (ditambahkan / dijadikan admin)."""
    member = update.my_chat_member
    if not member:
        return
    status = member.new_chat_member.status
    if status in (ChatMemberStatus.LEFT, ChatMemberStatus.BANNED):
        return
    await offer_as_log_channel(
        context.bot, member.chat, f"bot ditambahkan (status: {status})"
    )


async def channel_post_watcher(update, context):
    """Dipicu oleh postingan di channel mana pun tempat bot jadi admin.

    Jaring pengaman kalau update my_chat_member terlewat, misalnya karena bot
    sudah lebih dulu ditambahkan sebelum fitur ini ada.
    """
    post = update.channel_post or update.edited_channel_post
    if not post:
        return
    await offer_as_log_channel(context.bot, post.chat, "postingan terbaca di channel")


# ------------------------------------------------------------
# PENERAPAN BAN
# ------------------------------------------------------------

async def enforce_group_restriction(bot, user_id, mode, until_ts):
    """Terapkan ban/mute di grup diskusi kalau bot punya izin. Best effort."""
    if not DISCUSSION_CHAT_ID:
        return
    try:
        if mode == "ban":
            await bot.ban_chat_member(DISCUSSION_CHAT_ID, user_id)
        elif mode == "mute":
            await bot.restrict_chat_member(
                DISCUSSION_CHAT_ID,
                user_id,
                permissions=ChatPermissions(can_send_messages=False),
                until_date=until_ts or None,
            )
    except Exception:
        logging.info(
            "Tidak bisa menerapkan %s di grup diskusi untuk user %s "
            "(bot perlu izin Restrict Members).",
            mode, user_id,
        )


async def lift_group_restriction(bot, user_id):
    if not DISCUSSION_CHAT_ID:
        return
    try:
        await bot.unban_chat_member(
            DISCUSSION_CHAT_ID, user_id, only_if_banned=True
        )
    except Exception:
        pass
    try:
        await bot.restrict_chat_member(
            DISCUSSION_CHAT_ID,
            user_id,
            permissions=ChatPermissions(
                can_send_messages=True,
                can_send_other_messages=True,
                can_send_polls=True,
                can_add_web_page_previews=True,
                can_invite_users=True,
            ),
        )
    except Exception:
        pass


def ban_notice_text(ban):
    label = BAN_MODE_LABEL.get(ban["mode"], "DIBATASI")
    if ban["banned_until"]:
        sisa = fmt_duration(int(ban["banned_until"]) - int(time.time()))
        head = f"✕ Akun kamu sedang dibatasi ({label}).\n\nSisa waktu: {sisa}."
    else:
        head = f"✕ Akun kamu dibatasi permanen ({label})."
    if ban["reason"]:
        head += f"\nAlasan: {ban['reason']}"
    return head + "\n\nKalau merasa ini keliru, hubungi admin RANDOM UNDERGROUND."


async def block_if_banned(update, context, user):
    """True kalau user tidak boleh melanjutkan.

    Owner selalu lolos. Mode shadow tidak diblokir di sini: user sengaja
    dibiarkan mengira pesannya terkirim, penahanan terjadi saat posting.
    """
    if is_owner(user.id):
        return False
    ban = get_ban(user.id)
    if not ban or ban["mode"] == "shadow":
        return False
    message = update.message if update.message else None
    try:
        if message:
            await message.reply_text(ban_notice_text(ban))
        elif update.callback_query:
            await update.callback_query.message.reply_text(ban_notice_text(ban))
    except Exception:
        pass
    return True


def is_shadowbanned(user_id):
    if is_owner(user_id):
        return False
    ban = get_ban(user_id)
    return bool(ban and ban["mode"] == "shadow")



async def moderate_message(message, context):
    text = message.text or message.caption or ""
    if not text:
        return False

    if not contains_bad_word(text):
        return False

    warning_no = add_warning(message.from_user.id)

    try:
        await message.delete()
    except Exception:
        pass

    # Catat ke log channel supaya owner tetap punya jejak isi pesan dan
    # identitas pengirimnya walaupun pesannya sudah dihapus dari grup.
    log_mod_action(
        BOT_USER_ID or 0,
        message.from_user.id,
        "auto_delete",
        f"filter kata terlarang (warning {warning_no})",
    )
    await log_comment(
        context.bot,
        message.from_user,
        text,
        None,
        None,
        note=f"DIHAPUS OTOMATIS · warning {warning_no}/{MAX_COMMENT_WARNINGS}",
    )

    if warning_no >= MAX_COMMENT_WARNINGS:
        warning_text = (
            f"✕ Pesan kamu dihapus karena mengandung kata yang tidak diperbolehkan.\n\n"
            f"⚠️ Warning {warning_no}/{MAX_COMMENT_WARNINGS}.\n"
            f"Kalau terus diulang, akun bisa dibatasi dari komentar."
        )
    else:
        warning_text = (
            f"✕ Komentar kamu dihapus karena mengandung kata yang tidak diperbolehkan.\n\n"
            f"⚠️ Warning {warning_no}/{MAX_COMMENT_WARNINGS}.\n"
            f"Yuk jaga kolom komentar RANDOM UNDERGROUND tetap nyaman."
        )

    try:
        notice = await context.bot.send_message(
            chat_id=message.chat.id,
            text=warning_text,
        )
    except Exception:
        pass

    return True


async def delete_message_job(context):
    data = context.job.data
    try:
        await context.bot.delete_message(
            chat_id=data["chat_id"],
            message_id=data["message_id"],
        )
    except Exception:
        pass


# ============================================================
# TELEGRAM SETUP / MEMBERSHIP
# ============================================================

async def load_chat_ids(application):
    global CHANNEL_CHAT_ID, DISCUSSION_CHAT_ID, BOT_USER_ID

    me = await application.bot.get_me()
    BOT_USER_ID = me.id

    channel = await application.bot.get_chat(CHANNEL_USERNAME)
    CHANNEL_CHAT_ID = channel.id
    DISCUSSION_CHAT_ID = getattr(channel, "linked_chat_id", None)

    logging.info("BOT_USER_ID=%s", BOT_USER_ID)
    logging.info("CHANNEL_CHAT_ID=%s", CHANNEL_CHAT_ID)
    logging.info("DISCUSSION_CHAT_ID=%s", DISCUSSION_CHAT_ID)

    if DISCUSSION_CHAT_ID:
        try:
            member = await application.bot.get_chat_member(
                DISCUSSION_CHAT_ID, BOT_USER_ID
            )
            logging.info("DISCUSSION BOT STATUS=%s", member.status)
        except Exception:
            logging.exception("Bot tidak bisa cek status di discussion group.")


async def is_subscribed(user_id, context):
    try:
        member = await context.bot.get_chat_member(
            CHANNEL_USERNAME, user_id
        )
        allowed = member.status in (
            ChatMemberStatus.MEMBER,
            ChatMemberStatus.ADMINISTRATOR,
            ChatMemberStatus.OWNER,
        )
        if not allowed:
            logging.info(
                "is_subscribed: user=%s status=%r -> ditolak", user_id, member.status
            )
        return allowed
    except Exception:
        # Jangan telan diam-diam: tanpa log, kegagalan API tidak bisa dibedakan
        # dari user yang memang belum subscribe.
        logging.exception("is_subscribed gagal untuk user=%s", user_id)
        return False


async def is_discussion_member(user_id, context):
    if not DISCUSSION_CHAT_ID:
        return False
    try:
        member = await context.bot.get_chat_member(
            DISCUSSION_CHAT_ID, user_id
        )
        return member.status in (
            ChatMemberStatus.MEMBER,
            ChatMemberStatus.ADMINISTRATOR,
            ChatMemberStatus.OWNER,
        )
    except Exception:
        return False


# ============================================================
# KEYBOARDS / TEXT
# ============================================================

def main_menu(user_id=None):
    rows = [
        [InlineKeyboardButton("◈ PROFILE", callback_data="profile:self")],
        [InlineKeyboardButton("✦ ANONYMOUS POST", callback_data="send_menfess")],
        [InlineKeyboardButton("◆ RANKING", callback_data="leaderboard")],
        [InlineKeyboardButton("◇ COMMUNITY", callback_data="community")],
        [InlineKeyboardButton("⚠ RULES", callback_data="rules")],
    ]
    if user_id is not None and is_owner(user_id):
        rows.insert(0, [InlineKeyboardButton("⚙ OWNER CONTROL", callback_data="owner_panel")])
    return InlineKeyboardMarkup(rows)


def subscribe_menu():
    return InlineKeyboardMarkup([
        [InlineKeyboardButton(
            "◆ JOIN CHANNEL",
            url=f"https://t.me/{CHANNEL_USERNAME.lstrip('@')}",
        )],
        [InlineKeyboardButton("✓ CHECK ACCESS", callback_data="check_sub")],
    ])


def discussion_join_menu():
    return InlineKeyboardMarkup([
        [
            InlineKeyboardButton(
                "◆ JOIN DISCUSSION",
                url=f"https://t.me/{DISCUSSION_GROUP_USERNAME.lstrip('@')}",
            ),
            InlineKeyboardButton(
                "✓ CHECK AGAIN",
                callback_data="check_discussion_join",
            ),
        ]
    ])


def rules_menu():
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("← MENU", callback_data="back_menu")]
    ])


def view_menfess_button(menfess):
    url = (
        f"https://t.me/{CHANNEL_USERNAME.lstrip('@')}/"
        f"{menfess['channel_message_id']}"
    )
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("◆ OPEN POST", url=url)],
        [InlineKeyboardButton("← MENU", callback_data="back_menu")],
    ])


WELCOME_TEXT = (
    "RANDOM UNDERGROUND // ACCESS GRANTED\n\n"
    "Anonymous social space for people who prefer\n"
    "to speak without putting their identity forward.\n\n"
    "POST. TALK. CONNECT. STAY ANONYMOUS.\n\n"
    "Select a module below."
)

RULES_TEXT = (
    "RANDOM UNDERGROUND // RULES\n\n"
    "\u25aa Satu hashtag di awal pesan.\n"
    "\u25aa Jangan spam. Jangan ulang-ulang.\n"
    "\u25aa Data pribadi orang lain: jangan.\n"
    "\u25aa Kata kasar dan serangan pribadi: jangan.\n"
    "\u25aa Hormati penghuni lain.\n"
    "\u25aa Komentar terbuka, tapi dimoderasi.\n\n"
    "AVAILABLE TAGS\n"
    "#mutual  #curhat  #random  #gabut\n"
    "#confess  #ask  #salty  #want"
)

SEND_HELP_TEXT = (
    "ANONYMOUS POST\n\n"
    "Send your message here.\n"
    "Text or photo + caption are supported.\n\n"
    "Jangan lupa pakai satu hashtag di awal:\n\n"
    "#mutual — cari mutual / teman baru\n"
    "#curhat — cerita atau keluh kesah\n"
    "#random — bebas, apa aja\n"
    "#gabut — ajak ngobrol / cari teman\n"
    "#confess — sesuatu yang ingin disampaikan\n"
    "#ask — tanya atau minta pendapat\n"
    "#salty — lagi pengen ngeluarin kekesalan\n"
    "#want — sedang mencari sesuatu / seseorang\n\n"
    "Example: #random hari ini ngantuk banget."
)


# ============================================================
# START
# ============================================================

async def start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not update.message or not update.effective_user:
        return

    user = update.effective_user
    save_user(user)
    context.user_data["waiting_message"] = False
    context.user_data["waiting_comment_reply"] = None

    if not await is_subscribed(user.id, context):
        await update.message.reply_text(
            "⟡ RANDOM UNDERGROUND\n\n"
            "Subscribe channel RANDOM UNDERGROUND dulu sebelum kirim pesan.\n\n"
            "Kalau sudah subscribe, tekan CEK SUBSCRIBE.",
            reply_markup=subscribe_menu(),
        )
        return

    await update.message.reply_text(
        f"{WELCOME_TEXT}\n\n"
        f"▪ Sisa kuota: {quota_text(user.id)}",
        reply_markup=main_menu(user.id),
    )



def event_cancel_menu():
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("✕ BATAL BUAT EVENT", callback_data="owner:event_cancel")]
    ])


def owner_event_menu():
    event = get_active_event()
    if event:
        name = event["event_name"] or f"Event #{event['id']}"
        return InlineKeyboardMarkup([
            [InlineKeyboardButton("◆ LIHAT RANKING", callback_data="owner:event_rank")],
            [InlineKeyboardButton("◆ INFO EVENT", callback_data="owner:event_info")],
            [InlineKeyboardButton("◆ STOP EVENT", callback_data="owner:event_stop")],
            [InlineKeyboardButton("← OWNER PANEL", callback_data="owner_panel")],
        ])
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("◆ BUAT EVENT", callback_data="owner:event_create")],
        [InlineKeyboardButton("◆ EVENT TERAKHIR", callback_data="owner:event_last")],
        [InlineKeyboardButton("← OWNER PANEL", callback_data="owner_panel")],
    ])


def owner_panel_menu():
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("◆ EVENT", callback_data="owner_event")],
        [InlineKeyboardButton("⚡ FLASH EVENT", callback_data="owner:flash")],
        [InlineKeyboardButton("🛡 MODERASI", callback_data="owner_mod")],
        [InlineKeyboardButton("← MENU", callback_data="back_menu")],
    ])


def owner_mod_menu():
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("🚫 DAFTAR BAN", callback_data="owner:banlist")],
        [InlineKeyboardButton("🛡 RIWAYAT MODERASI", callback_data="owner:modlog")],
        [InlineKeyboardButton("🔎 CARA LACAK PENGIRIM", callback_data="owner:whoishelp")],
        [InlineKeyboardButton("✓ TEST LOG CHANNEL", callback_data="owner:logtest")],
        [InlineKeyboardButton("⚙ PASANG LOG CHANNEL", callback_data="owner:setloghelp")],
        [InlineKeyboardButton("← OWNER PANEL", callback_data="owner_panel")],
    ])


def format_event_settings(event):
    name = event["event_name"] or f"Event #{event['id']}"
    winners = event["winner_count"] or 3
    return (
        f"{name}\n\n"
        f"▪ Pemenang: {winners} orang\n"
        f"⏰ {format_event_end(event)}\n\n"
        "Skor event dimulai dari 0 dan terpisah dari leaderboard biasa."
    )


def format_event_result(event):
    rows = [
        r for r in get_event_leaderboard(event["id"], 30)
        if r["user_id"] not in HIDDEN_LEADERBOARD_USER_IDS
    ][:20]
    winners = max(1, int(event["winner_count"] or 3))
    name = event["event_name"] or f"Event #{event['id']}"

    if not rows:
        return (
            f"{name} // SELESAI\n\n"
            "Belum ada peserta yang mendapatkan poin."
        )

    medals = ["01", "02", "03"]
    winner_lines = []
    for i, row in enumerate(rows[:winners], 1):
        uname = f"@{row['username']}" if row["username"] else (row["first_name"] or f"User {row['user_id']}")
        winner_lines.append(f"{medals[i-1] if i <= 3 else f'{i}.'} {uname} — {row['points']} poin")

    lines = [
        f"{name} // SELESAI",
        "",
        "SELAMAT KEPADA PEMENANG",
        "",
        *winner_lines,
        "",
        "HASIL RANKING",
    ]
    for i, row in enumerate(rows, 1):
        uname = f"@{row['username']}" if row["username"] else (row["first_name"] or f"User {row['user_id']}")
        prefix = medals[i-1] if i <= 3 else f"{i}."
        lines.append(f"{prefix} {uname} — {row['points']} poin")
    return "\n".join(lines)


async def announce_event_start(bot, event):
    name = event["event_name"] or f"Event #{event['id']}"
    winners = int(event["winner_count"] or 3)
    duration = "tanpa batas waktu" if not event["ends_at"] else format_event_end(event)
    text = (
        "EVENT RANDOM UNDERGROUND DIMULAI\n\n"
        f"{name}\n"
        f"⏰ Durasi: {duration}\n"
        f"▪ Pemenang: {winners} orang\n\n"
        "Skor event dimulai dari 0 untuk semua peserta.\n\n"
        f"▪ Menfess valid = +{POINT_PER_MENFESS} poin\n"
        f"▪ Komentar valid = +{POINT_PER_COMMENT} poin\n\n"
        "Ranking event bisa dilihat kapan saja lewat menu LEADERBOARD."
    )
    await bot.send_message(CHANNEL_USERNAME, text)


async def announce_event_end(bot, event):
    await bot.send_message(CHANNEL_USERNAME, format_event_result(event))


# ============================================================
# CALLBACKS
# ============================================================

async def callback_handler(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    if not query:
        return

    await query.answer()
    user = query.from_user
    save_user(user)
    data = query.data or ""

    # Tombol moderasi khusus owner; diproses sebelum pengecekan ban.
    if data.startswith("mod:"):
        await handle_mod_callback(update, context, data)
        return

    if await block_if_banned(update, context, user):
        return

    if data == "back_menu":
        await query.message.reply_text(
            f"{WELCOME_TEXT}\n\n▪ Sisa kuota: {quota_text(user.id)}",
            reply_markup=main_menu(user.id),
        )
        return

    if data == "check_sub":
        if await is_subscribed(user.id, context):
            await query.message.reply_text(
                f"Akses terverifikasi.\n\n"
                f"▪ Sisa kuota: {quota_text(user.id)}",
                reply_markup=main_menu(user.id),
            )
        else:
            await query.message.reply_text(
                "✕ Kamu belum subscribe channel RANDOM UNDERGROUND.\n\n"
                "Subscribe dulu, lalu tekan CEK SUBSCRIBE.",
                reply_markup=subscribe_menu(),
            )
        return

    if data == "check_discussion_join":
        if await is_discussion_member(user.id, context):
            await query.message.reply_text(
                "Kamu sudah join grup diskusi RANDOM UNDERGROUND.\n\n"
                "Sekarang kamu sudah bisa ikut berkomentar.",
                reply_markup=main_menu(user.id),
            )
        else:
            await query.message.reply_text(
                "✕ Kamu belum join grup diskusi RANDOM UNDERGROUND.\n\n"
                "Join dulu, lalu tekan CEK LAGI.",
                reply_markup=discussion_join_menu(),
            )
        return

    if data == "profile:self":
        await query.message.reply_text(
            profile_text(user),
            reply_markup=profile_menu(user.id),
        )
        return

    if data.startswith("profile:badges:"):
        try:
            target_id = int(data.rsplit(":", 1)[1])
        except ValueError:
            target_id = user.id
        await query.message.reply_text(
            profile_badges_text(target_id),
            reply_markup=InlineKeyboardMarkup([
                [InlineKeyboardButton("← PROFILE", callback_data=f"profile:self" if target_id == user.id else "back_menu")]
            ]),
        )
        return

    if data == "owner_panel":
        if not is_owner(user.id):
            return
        await query.message.reply_text(
            "⚙ OWNER PANEL\n\nPilih pengaturan:",
            reply_markup=owner_panel_menu(),
        )
        return

    if data == "owner_mod":
        if not is_owner(user.id):
            return
        aktif = len(list_bans())
        status = (
            f"Log channel: <code>{log_target()}</code>\n"
            f"Sumber: {log_target_source()}"
        )
        await query.message.reply_text(
            "<b>🛡 MODERASI</b>\n\n"
            f"{status}\n"
            f"User dibatasi: {aktif}\n"
            f"Catat semua komentar: {'ya' if LOG_ALL_COMMENTS else 'hanya yang bermasalah'}\n\n"
            "Perintah lengkap: /modhelp",
            parse_mode="HTML",
            reply_markup=owner_mod_menu(),
        )
        return

    if data == "owner:banlist":
        if not is_owner(user.id):
            return
        await query.message.reply_text(
            banlist_text(), parse_mode="HTML", reply_markup=owner_mod_menu()
        )
        return

    if data == "owner:modlog":
        if not is_owner(user.id):
            return
        await query.message.reply_text(
            modlog_text(), parse_mode="HTML",
            reply_markup=owner_mod_menu(), disable_web_page_preview=True,
        )
        return

    if data == "owner:setloghelp":
        if not is_owner(user.id):
            return
        await query.message.reply_text(
            "PASANG LOG CHANNEL\n\n"
            f"Sekarang: {log_target()} ({log_target_source()})\n\n"
            "Cara termudah: tambahkan bot sebagai ADMIN di channel privatmu. "
            "Bot akan otomatis mengirimkan tombol JADIKAN LOG CHANNEL ke sini.\n\n"
            "Cara manual:\n"
            "• /setlog -1002345678901\n"
            "• forward satu postingan dari channel itu ke sini, lalu reply "
            "forward-nya dengan /setlog\n"
            "• /setlog langsung di dalam grup tujuan\n\n"
            "Kembalikan ke DM owner: /unsetlog",
            reply_markup=owner_mod_menu(),
        )
        return

    if data == "owner:whoishelp":
        if not is_owner(user.id):
            return
        await query.message.reply_text(WHOIS_HELP, reply_markup=owner_mod_menu())
        return

    if data == "owner:logtest":
        if not is_owner(user.id):
            return
        sent = await send_log(
            context.bot,
            "<b>✓ LOG CHANNEL AKTIF</b>\n\n"
            "Semua menfess baru beserta identitas pengirimnya akan masuk ke sini.",
        )
        await query.message.reply_text(
            f"✓ Log terkirim ke {log_target()} ({log_target_source()})."
            if sent else
            f"✕ Gagal mengirim log ke {log_target()}.\n\n"
            "Pastikan bot admin di sana dengan izin Post Messages, "
            "lalu pasang ulang dengan /setlog.",
            reply_markup=owner_mod_menu(),
        )
        return

    if data == "owner_event":
        if not is_owner(user.id):
            return
        event = get_active_event()
        if event:
            await query.message.reply_text(
                f"EVENT AKTIF\n\n{format_event_settings(event)}",
                reply_markup=owner_event_menu(),
            )
        else:
            await query.message.reply_text(
                "EVENT MANAGER\n\nBelum ada event aktif.",
                reply_markup=owner_event_menu(),
            )
        return

    if data == "owner:event_create":
        if not is_owner(user.id):
            return
        context.user_data["event_create_step"] = "name"
        context.user_data.pop("event_name", None)
        context.user_data.pop("event_duration", None)
        await query.message.reply_text(
            "BUAT EVENT\n\nKirim nama event-nya dulu.",
            reply_markup=event_cancel_menu(),
        )
        return

    if data == "owner:event_cancel":
        if not is_owner(user.id):
            return
        context.user_data.pop("event_create_step", None)
        context.user_data.pop("event_name", None)
        context.user_data.pop("event_duration", None)
        await query.message.reply_text(
            "✕ Pembuatan event dibatalkan.\n\nTidak ada event baru yang dibuat.",
            reply_markup=owner_event_menu(),
        )
        return

    if data == "owner:event_stop":
        if not is_owner(user.id):
            return
        event = stop_event()
        if not event:
            await query.message.reply_text("✕ Tidak ada event yang sedang aktif.")
            return
        await announce_event_end(context.bot, event)
        await query.message.reply_text(
            "Event selesai. Hasil akhirnya sudah diumumkan di base.",
            reply_markup=owner_event_menu(),
        )
        return

    if data == "owner:event_rank":
        if not is_owner(user.id):
            return
        await query.message.reply_text(
            format_public_event_leaderboard(),
            reply_markup=owner_event_menu(),
        )
        return

    if data == "owner:event_info":
        if not is_owner(user.id):
            return
        event = get_active_event()
        if not event:
            await query.message.reply_text("✕ Tidak ada event aktif.", reply_markup=owner_event_menu())
            return
        await query.message.reply_text(
            format_event_settings(event),
            reply_markup=owner_event_menu(),
        )
        return

    if data == "owner:event_last":
        if not is_owner(user.id):
            return
        conn = db()
        event = conn.execute("SELECT * FROM events ORDER BY id DESC LIMIT 1").fetchone()
        conn.close()
        if not event:
            await query.message.reply_text("✕ Belum ada event.", reply_markup=owner_event_menu())
        else:
            await query.message.reply_text(
                format_event_result(event),
                reply_markup=owner_event_menu(),
            )
        return

    if data == "community":
        await query.message.reply_text(community_text(), reply_markup=community_menu())
        return
    if data == "community:mission":
        await query.message.reply_text(daily_mission_text(user.id), reply_markup=mission_menu(user.id))
        return
    if data == "community:qotd":
        q=QOTD[int(time.strftime("%j")) % len(QOTD)]
        await query.message.reply_text("QUESTION OF THE DAY\n\n"+q+"\n\n▸ Jawab di komentar base.", reply_markup=community_menu())
        return
    if data == "community:title":
        await query.message.reply_text(f"TITLE KAMU\n\n{get_user_title(user.id)}", reply_markup=community_menu())
        return
    if data == "community:mvp":
        await query.message.reply_text(weekly_mvp_text(), reply_markup=community_menu())
        return
    if data == "community:comment":
        await query.message.reply_text(comment_spotlight_text(), reply_markup=community_menu())
        return
    if data == "community:trending":
        await query.message.reply_text(trending_text(), reply_markup=community_menu())
        return
    if data == "community:box":
        await query.message.reply_text(mystery_box_text(user.id), reply_markup=community_menu())
        return
    if data.startswith("mission:"):
        ok,msg=claim_daily_mission(user.id,data.split(":",1)[1])
        await query.message.reply_text(msg, reply_markup=community_menu())
        return
    if data == "owner:flash":
        if not is_owner(user.id): return
        active=get_active_event()
        if active:
            await query.message.reply_text("✕ Hentikan event aktif dulu sebelum membuat Flash Event.", reply_markup=owner_panel_menu())
            return
        event=start_event("⚡ FLASH EVENT",2/24,3)
        await announce_event_start(context.bot,event)
        await query.message.reply_text("⚡ Flash Event 2 jam dimulai!", reply_markup=owner_panel_menu())
        return

    if data == "leaderboard":
        await query.message.reply_text(
            "◆ RANDOM UNDERGROUND // RANKING\n\nSelect ranking mode:",
            reply_markup=leaderboard_menu(),
        )
        return

    if data == "lb:all_time":
        await query.message.reply_text(format_period_leaderboard("all_time"), reply_markup=leaderboard_menu())
        return

    if data == "lb:weekly":
        await query.message.reply_text(format_period_leaderboard("weekly"), reply_markup=leaderboard_menu())
        return

    if data == "lb:monthly":
        await query.message.reply_text(format_period_leaderboard("monthly"), reply_markup=leaderboard_menu())
        return

    if data == "lb:event":
        await query.message.reply_text(format_public_event_leaderboard(), reply_markup=leaderboard_menu())
        return

    if data == "rules":
        await query.message.reply_text(RULES_TEXT, reply_markup=rules_menu())
        return

    if data == "send_menfess":
        if not await is_subscribed(user.id, context):
            await query.message.reply_text(
                "✕ Kamu belum subscribe channel RANDOM UNDERGROUND.\n\n"
                "Subscribe dulu sebelum kirim pesan.",
                reply_markup=subscribe_menu(),
            )
            return

        if not is_owner(user.id) and get_used_count(user.id) >= MAX_SENDS:
            await query.message.reply_text(
                "✕ Kuota pesan kamu sudah habis.\n\n"
                f"Maksimal {MAX_SENDS} pesan dalam 24 jam."
            )
            return

        context.user_data["waiting_message"] = True
        context.user_data["waiting_comment_reply"] = None

        await query.message.reply_text(SEND_HELP_TEXT)
        return

    if data.startswith("reply_comment:"):
        await start_comment_reply(update, context, user, data)
        return


async def start_comment_reply(update, context, user, data):
    query = update.callback_query

    # Semua orang boleh membalas komentar; tidak wajib menjadi member grup.
    try:
        db_id = int(data.split(":", 1)[1])
    except (ValueError, IndexError):
        await query.message.reply_text("✕ Komentar tidak ditemukan.")
        return

    comment = get_discussion_message_by_db_id(db_id)
    if not comment:
        await query.message.reply_text("✕ Komentar tidak ditemukan.")
        return

    menfess = get_menfess(comment["menfess_id"])
    if not menfess:
        await query.message.reply_text("✕ Postingan tidak ditemukan.")
        return

    allowed = (
        menfess["sender_id"] == user.id
        or comment["author_user_id"] == user.id
    )

    if not allowed:
        await query.message.reply_text(
            "✕ Balasan ini bukan untuk akun kamu."
        )
        return

    context.user_data["waiting_comment_reply"] = db_id
    context.user_data["waiting_message"] = False

    await query.message.reply_text(
        "Balas komentar.\n\n"
        "Kirim balasan kamu sekarang.\n"
        "Balasan akan dikirim anonim lewat bot."
    )


# ============================================================
# PRIVATE MESSAGE HANDLER
# ============================================================

async def message_handler(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not update.message or not update.effective_user:
        return

    if update.effective_chat.type != "private":
        return

    user = update.effective_user
    save_user(user)

    # User yang di-ban/mute tidak bisa memakai bot sama sekali.
    if await block_if_banned(update, context, user):
        context.user_data["waiting_message"] = False
        context.user_data["waiting_comment_reply"] = None
        return

    # Owner event creation wizard.
    if is_owner(user.id) and context.user_data.get("event_create_step"):
        raw = (update.message.text or "").strip()
        step = context.user_data["event_create_step"]

        if step == "name":
            if not raw or len(raw) > 80:
                await update.message.reply_text(
                    "✕ Nama event 1–80 karakter.",
                    reply_markup=event_cancel_menu(),
                )
                return
            context.user_data["event_name"] = raw
            context.user_data["event_create_step"] = "duration"
            await update.message.reply_text(
                "⏰ Durasi event berapa hari? Kirim angka 1–365.",
                reply_markup=event_cancel_menu(),
            )
            return

        if step == "duration":
            try:
                duration = int(raw)
                if duration < 1 or duration > 365:
                    raise ValueError
            except ValueError:
                await update.message.reply_text(
                    "✕ Kirim angka 1–365.",
                    reply_markup=event_cancel_menu(),
                )
                return
            context.user_data["event_duration"] = duration
            context.user_data["event_create_step"] = "winners"
            await update.message.reply_text(
                "Berapa orang yang jadi pemenang?\n\n"
                "Kirim angka 1–20.",
                reply_markup=event_cancel_menu(),
            )
            return

        if step == "winners":
            try:
                winners = int(raw)
                if winners < 1 or winners > 20:
                    raise ValueError
            except ValueError:
                await update.message.reply_text(
                    "✕ Jumlah pemenang harus 1–20.",
                    reply_markup=event_cancel_menu(),
                )
                return

            event = start_event(
                context.user_data.pop("event_name"),
                context.user_data.pop("event_duration"),
                winners,
            )
            context.user_data.pop("event_create_step", None)
            await announce_event_start(context.bot, event)
            await update.message.reply_text(
                "Event dimulai. Pengumuman sudah dikirim ke base.",
                reply_markup=owner_event_menu(),
            )
            return

    # Owner can answer the legacy /event_start duration prompt.
    if is_owner(user.id) and context.user_data.get("waiting_event_duration"):
        raw = (update.message.text or "").strip()
        try:
            duration = int(raw)
            if duration <= 0 or duration > 365:
                raise ValueError
        except ValueError:
            await update.message.reply_text(
                "✕ Kirim angka 1–365 saja. Contoh: 14"
            )
            return

        context.user_data["waiting_event_duration"] = False
        await actually_start_event(update, duration)
        return

    if not await is_subscribed(user.id, context):
        context.user_data["waiting_message"] = False
        context.user_data["waiting_comment_reply"] = None
        await update.message.reply_text(
            "✕ Kamu belum subscribe channel RANDOM UNDERGROUND.\n\n"
            "Subscribe dulu sebelum mengirim pesan.",
            reply_markup=subscribe_menu(),
        )
        return

    waiting_reply = context.user_data.get("waiting_comment_reply")
    if waiting_reply:
        context.user_data["waiting_comment_reply"] = None
        await process_private_comment_reply(update, context, waiting_reply)
        return

    if context.user_data.get("waiting_message", False):
        if not is_owner(user.id) and get_used_count(user.id) >= MAX_SENDS:
            context.user_data["waiting_message"] = False
            await update.message.reply_text(
                "✕ Kuota pesan kamu sudah habis.\n\n"
                f"Maksimal {MAX_SENDS} pesan dalam 24 jam."
            )
            return

        context.user_data["waiting_message"] = False
        await process_new_menfess(update, context)
        return

    await update.message.reply_text(
        "⟡ Tekan KIRIM PESAN dulu.",
        reply_markup=main_menu(user.id),
    )


async def process_private_comment_reply(update, context, db_id):
    user = update.effective_user
    comment = get_discussion_message_by_db_id(db_id)

    if not comment:
        await update.message.reply_text("✕ Komentar sudah tidak ditemukan.")
        return

    menfess = get_menfess(comment["menfess_id"])
    if not menfess:
        await update.message.reply_text("✕ Postingan sudah tidak ditemukan.")
        return

    allowed = (
        menfess["sender_id"] == user.id
        or comment["author_user_id"] == user.id
    )
    if not allowed:
        await update.message.reply_text("✕ Kamu tidak bisa membalas komentar ini.")
        return

    text = update.message.text or update.message.caption or ""
    if contains_bad_word(text):
        await update.message.reply_text(
            "✕ Balasan tidak dikirim karena mengandung kata yang tidak diperbolehkan."
        )
        return

    if is_shadowbanned(user.id):
        log_mod_action(BOT_USER_ID or 0, user.id, "shadow_hold", text[:200])
        await log_comment(
            context.bot, user, text, menfess, db_id,
            note="BALASAN DITAHAN (SHADOWBAN)",
        )
        await update.message.reply_text(
            "Balasan kamu sudah dikirim secara anonim."
        )
        return

    discussion_chat_id = comment["discussion_chat_id"]
    target_message_id = comment["message_id"]

    try:
        prefix = f"{EMOJI['reply']} "
        shift = utf16_len(prefix)
        if update.message.text:
            sent = await send_text_keep_format(
                context.bot,
                discussion_chat_id,
                prefix + update.message.text,
                entities=shift_entities(update.message.entities, shift),
                reply_to_message_id=target_message_id,
                allow_sending_without_reply=False,
            )
        elif update.message.photo:
            sent = await send_photo_keep_format(
                context.bot,
                discussion_chat_id,
                update.message.photo[-1].file_id,
                caption=prefix + (update.message.caption or ""),
                caption_entities=shift_entities(
                    update.message.caption_entities, shift
                ),
                reply_to_message_id=target_message_id,
                allow_sending_without_reply=False,
            )
        else:
            await update.message.reply_text(
                "Balasan untuk sekarang berupa teks atau foto + caption."
            )
            return

        create_discussion_message(
            menfess_id=menfess["id"],
            discussion_chat_id=discussion_chat_id,
            message_id=sent.message_id,
            parent_message_id=target_message_id,
            author_user_id=user.id,
            content=text,
        )
        record_activity(user.id, "comment", source_id=db_id)
        if event_activity_is_valid(update.message.text or update.message.caption or "", "comment"):
            add_event_points(user.id, comment=1, menfess_id=db_id)

        await update.message.reply_text(
            "Balasan kamu sudah dikirim secara anonim."
        )
    except Exception:
        logging.exception("Gagal mengirim balasan anonim")
        await update.message.reply_text(
            "✕ Balasannya belum bisa dikirim.\n\n"
            "Pastikan bot admin di channel dan grup komentar."
        )


# ============================================================
# NEW MENFESS
# ============================================================

async def process_new_menfess(update, context):
    message = update.message
    user = message.from_user

    content = message.text if message.text is not None else (message.caption or "")

    if contains_bad_word(content):
        await message.reply_text(
            "✕ Pesan belum dikirim.\n\n"
            "Pesan mengandung kata yang tidak diperbolehkan. "
            "Coba ubah kata-katanya lalu kirim lagi."
        )
        return

    match = re.match(r"^\s*(#[A-Za-z0-9_]+)(?:\s|$)", content)
    if not match:
        await message.reply_text(
            "✕ Pesan tidak dikirim.\n\n"
            "Wajib memakai satu hashtag di awal pesan.\n"
            "Contoh: #random hari ini gabut banget."
        )
        return

    hashtags = re.findall(r"(?<!\\w)#[A-Za-z0-9_]+", content)
    if len(hashtags) != 1:
        await message.reply_text(
            "✕ Pesan tidak dikirim.\n\n"
            "Gunakan tepat satu hashtag yang sesuai dengan isi pesan."
        )
        return

    hashtag = match.group(1).lower()
    if hashtag not in VALID_HASHTAGS:
        await message.reply_text(
            "✕ Hashtag tidak tersedia.\n\n"
            "Pakai salah satu:\n" + "  ".join(VALID_HASHTAGS.keys())
        )
        return

    # Shadowban: user melihat konfirmasi seperti biasa, tapi pesannya tidak
    # pernah tayang. Tujuannya supaya spammer tidak sadar lalu bikin akun baru.
    if is_shadowbanned(user.id):
        add_send_log(user.id)
        log_mod_action(BOT_USER_ID or 0, user.id, "shadow_hold", content[:200])
        await log_menfess(
            context.bot, None, user, content, None, shadowed=True
        )
        await message.reply_text(
            "✓ Menfess kamu terkirim!\n\n"
            "Postingan akan tayang di channel sebentar lagi."
        )
        return

    try:
        if message.text:
            sent = await send_text_keep_format(
                context.bot,
                CHANNEL_USERNAME,
                message.text,
                entities=message.entities,
            )
        elif message.photo:
            sent = await send_photo_keep_format(
                context.bot,
                CHANNEL_USERNAME,
                message.photo[-1].file_id,
                caption=message.caption or "",
                caption_entities=message.caption_entities,
            )
        else:
            await message.reply_text(
                "Boleh kirim teks atau foto + caption."
            )
            return

        menfess_id = create_menfess(user.id, sent.message_id, content)
        add_send_log(user.id)
        record_activity(user.id, "menfess")
        if event_activity_is_valid(message.text or message.caption or "", "menfess"):
            add_event_points(user.id, menfess=1)

        menfess = get_menfess(menfess_id)

        await message.reply_text(
            "✓ Menfess kamu terkirim!\n\n"
            "Kalau mau lihat postingannya, tekan tombol di bawah.",
            reply_markup=view_menfess_button(menfess),
        )

        logging.info(
            "MENFESS id=%s user=%s channel_msg=%s",
            menfess_id,
            user.id,
            sent.message_id,
        )

        # Jejak permanen ke log channel: isi pesan + identitas pengirim.
        await log_menfess(
            context.bot, menfess_id, user, content, sent.message_id
        )

    except Exception:
        logging.exception("Gagal mengirim menfess")
        await message.reply_text(
            "✕ Pesan belum berhasil dikirim.\n\n"
            "Pastikan bot sudah menjadi admin di channel RANDOM UNDERGROUND."
        )


# ============================================================
# DISCUSSION GROUP
# ============================================================

def get_channel_post_id_from_discussion_root(message):
    origin = getattr(message, "forward_origin", None)
    if origin is not None:
        origin_message_id = getattr(origin, "message_id", None)
        origin_chat = getattr(origin, "chat", None)
        if origin_message_id is not None:
            if CHANNEL_CHAT_ID is None or origin_chat is None:
                return origin_message_id
            if origin_chat.id == CHANNEL_CHAT_ID:
                return origin_message_id

    return None


async def discussion_comment_handler(update, context):
    message = update.message
    if not message or not message.from_user:
        return

    if DISCUSSION_CHAT_ID is None or message.chat.id != DISCUSSION_CHAT_ID:
        return

    if message.from_user.id == BOT_USER_ID:
        return

    # Root automatic-forward dari channel bukan komentar user.
    is_root_forward = bool(getattr(message, "is_automatic_forward", False))
    parent = message.reply_to_message

    if is_root_forward and parent is None:
        channel_post_id = get_channel_post_id_from_discussion_root(message)
        if channel_post_id is not None:
            menfess = get_menfess_by_channel_message(channel_post_id)
            if menfess:
                create_discussion_message(
                    menfess["id"],
                    message.chat.id,
                    message.message_id,
                    None,
                    menfess["sender_id"],
                )
        return

    # User yang dibatasi (termasuk shadowban): komentarnya dihapus tanpa
    # pemberitahuan apa pun di grup, tapi tetap tercatat di log channel.
    ban = None if is_owner(message.from_user.id) else get_ban(message.from_user.id)
    if ban:
        try:
            await message.delete()
        except Exception:
            pass
        log_mod_action(
            BOT_USER_ID or 0,
            message.from_user.id,
            "auto_delete",
            f"komentar dari user {ban['mode']}",
        )
        await log_comment(
            context.bot,
            message.from_user,
            message.text or message.caption or "",
            None,
            None,
            note=f"DIHAPUS · user {BAN_MODE_LABEL.get(ban['mode'], ban['mode'])}",
        )
        return

    # Semua orang boleh komentar. Tidak ada syarat wajib join grup.
    # Moderasi sebelum menyimpan / menghitung poin.
    if await moderate_message(message, context):
        return

    if parent is None:
        return

    menfess = None
    parent_record = find_discussion_message(
        message.chat.id, parent.message_id
    )

    if parent_record:
        menfess = get_menfess(parent_record["menfess_id"])

    if not menfess:
        channel_post_id = get_channel_post_id_from_discussion_root(parent)
        if channel_post_id is not None:
            menfess = get_menfess_by_channel_message(channel_post_id)

    if not menfess:
        return

    create_discussion_message(
        menfess_id=menfess["id"],
        discussion_chat_id=message.chat.id,
        message_id=message.message_id,
        parent_message_id=parent.message_id,
        author_user_id=message.from_user.id,
        content=(message.text or message.caption or ""),
    )
    record_activity(message.from_user.id, "comment", source_id=message.message_id)
    if event_activity_is_valid(message.text or message.caption or "", "comment"):
        add_event_points(message.from_user.id, comment=1, menfess_id=menfess["id"])

    if LOG_ALL_COMMENTS:
        logged = find_discussion_message(message.chat.id, message.message_id)
        await log_comment(
            context.bot,
            message.from_user,
            message.text or message.caption or "",
            menfess,
            logged["id"] if logged else None,
        )

    # Notifikasi hanya untuk pihak yang relevan.
    target_user_id = (
        parent_record["author_user_id"]
        if parent_record
        else menfess["sender_id"]
    )

    if target_user_id == message.from_user.id:
        return

    preview = (
        message.text
        or message.caption
        or ("Foto" if message.photo else "Pesan baru")
    )
    preview = preview.strip()
    if len(preview) > 250:
        preview = preview[:250] + "…"

    try:
        comment_db = find_discussion_message(
            message.chat.id, message.message_id
        )
        if not comment_db:
            return

        await context.bot.send_message(
            target_user_id,
            f"✓ Ada balasan baru!\n\n"
            f"{preview}\n\n"
            "Identitas pengirim tetap anonim.",
            reply_markup=reply_comment_button(comment_db["id"]),
        )
    except Exception:
        logging.info(
            "Tidak bisa mengirim notif komentar ke user %s",
            target_user_id,
        )


def reply_comment_button(comment_db_id):
    comment = get_discussion_message_by_db_id(comment_db_id)
    if not comment:
        return InlineKeyboardMarkup([])

    menfess = get_menfess(comment["menfess_id"])
    if not menfess:
        return InlineKeyboardMarkup([])

    post_url = (
        f"https://t.me/{CHANNEL_USERNAME.lstrip('@')}/"
        f"{menfess['channel_message_id']}"
    )
    comment_url = f"{post_url}?comment={comment['message_id']}"

    return InlineKeyboardMarkup([
        [
            InlineKeyboardButton("✦ LIHAT KOMENTAR", url=comment_url),
            InlineKeyboardButton(
                "✦ BALAS",
                callback_data=f"reply_comment:{comment_db_id}",
            ),
        ],
        [InlineKeyboardButton("⟡ LIHAT POSTINGAN", url=post_url)],
    ])


# ============================================================
# ============================================================
# EVENT ADMIN / OWNER PANEL
# ============================================================

def owner_only(func):
    @wraps(func)
    async def wrapper(update, context):
        user = update.effective_user
        if not user or not is_owner(user.id):
            if update.message:
                await update.message.reply_text("✕ Bagian ini khusus owner.")
            return
        return await func(update, context)
    return wrapper


# ============================================================
# PERINTAH MODERASI OWNER
# ============================================================

WHOIS_HELP = (
    "🔎 CARA PAKAI /whois\n\n"
    "1. Postingan channel:\n"
    "   forward postingannya ke chat ini, lalu reply forward itu dengan /whois\n\n"
    "2. Komentar di grup diskusi:\n"
    "   reply komentarnya dengan /whois\n\n"
    "3. Lewat pencarian langsung:\n"
    "   /whois 123456789      (user id)\n"
    "   /whois @username\n"
    "   /whois #RU1482        (kode menfess di log channel)\n"
    "   /whois https://t.me/randomunderground/3391"
)

MOD_HELP = (
    "🛡 PERINTAH MODERASI\n\n"
    "/whois — lihat identitas pengirim\n"
    "/ban [alasan] — ban permanen\n"
    "/mute <jam> [alasan] — bisukan sementara\n"
    "/shadowban [alasan] — pesan tidak tayang, user tidak diberi tahu\n"
    "/unban — cabut semua pembatasan\n"
    "/warn [alasan] — tambah warning\n"
    "/resetwarn — nolkan warning\n"
    "/banlist — daftar user yang dibatasi\n"
    "/modlog [jumlah] — riwayat tindakan moderasi\n"
    "/setlog — pasang log channel (tanpa restart)\n"
    "/unsetlog — kembalikan log ke DM owner\n"
    "/logtest — cek log channel sudah jalan\n"
    "/id — tampilkan chat id\n\n"
    "Semua perintah di atas bisa dipakai dengan cara reply ke pesan target,\n"
    "atau dengan menulis target di depan alasan. Contoh:\n"
    "/ban 123456789 promosi jualan\n"
    "/mute @username 12 spam komentar"
)


def _menfess_ref_to_id(token):
    """Referensi menfess harus berawalan: #RU123, RU123, atau #123.

    Angka polos sengaja tidak diterima di sini supaya tidak bentrok dengan
    user id, yang juga berupa angka polos.
    """
    m = re.fullmatch(r"(?:#RU|#ru|RU|ru|#)(\d+)", (token or "").strip())
    return int(m.group(1)) if m else None


def _channel_message_id_from_link(token):
    m = re.search(r"t\.me/(?:c/\d+|[A-Za-z0-9_]+)/(\d+)", token or "")
    return int(m.group(1)) if m else None


def resolve_mod_target(update, args):
    """Cari user yang jadi target perintah moderasi.

    Mengembalikan (user_id, keterangan_sumber, sisa_argumen).
    Kalau gagal, user_id None dan keterangan berisi pesan error.
    """
    args = list(args or [])
    message = update.effective_message
    reply = message.reply_to_message if message else None

    if reply is not None:
        # Owner mem-forward postingan channel ke DM bot.
        channel_msg_id = get_channel_post_id_from_discussion_root(reply)
        if channel_msg_id is not None:
            menfess = get_menfess_by_channel_message(channel_msg_id)
            if menfess:
                return (
                    int(menfess["sender_id"]),
                    f"pengirim menfess #RU{menfess['id']}",
                    args,
                )
            return (
                None,
                f"✕ Postingan channel #{channel_msg_id} tidak ada di database bot.",
                args,
            )

        # Reply ke komentar di grup diskusi (termasuk balasan anonim via bot).
        record = find_discussion_message(reply.chat.id, reply.message_id)
        if record:
            return (
                int(record["author_user_id"]),
                f"penulis komentar di menfess #RU{record['menfess_id']}",
                args,
            )

        # Pesan biasa dari user asli.
        if reply.from_user and reply.from_user.id != BOT_USER_ID:
            return int(reply.from_user.id), "pengirim pesan yang direply", args

        return (
            None,
            "✕ Pesan itu tidak ada di database bot, jadi pengirimnya tidak bisa "
            "dilacak. Coba /whois dengan user id atau link postingannya.",
            args,
        )

    if not args:
        return None, None, args

    token = args[0]
    rest = args[1:]

    if token.startswith("@"):
        row = find_user_by_username(token)
        if not row:
            return (
                None,
                f"✕ {token} belum pernah tercatat di bot. Pakai user id-nya.",
                rest,
            )
        return int(row["user_id"]), f"pencarian {token}", rest

    link_msg_id = _channel_message_id_from_link(token)
    if link_msg_id is not None:
        menfess = get_menfess_by_channel_message(link_msg_id)
        if not menfess:
            return None, f"✕ Postingan #{link_msg_id} tidak ada di database.", rest
        return (
            int(menfess["sender_id"]),
            f"pengirim menfess #RU{menfess['id']}",
            rest,
        )

    menfess_id = _menfess_ref_to_id(token)
    if menfess_id is not None:
        menfess = get_menfess(menfess_id)
        if not menfess:
            return None, f"✕ Menfess #RU{menfess_id} tidak ditemukan.", rest
        return (
            int(menfess["sender_id"]),
            f"pengirim menfess #RU{menfess_id}",
            rest,
        )

    # Angka polos selalu dibaca sebagai user id.
    if token.isdigit():
        return int(token), "user id langsung", rest

    return None, f"✕ Target '{token}' tidak dikenali.", rest


def recent_activity_text(user_id, limit=5):
    """Beberapa jejak terakhir user, untuk menilai pola pelanggaran."""
    user_id = int(user_id)
    conn = db()
    menfess_rows = conn.execute("""
        SELECT id, channel_message_id, created_at, content
        FROM menfess WHERE sender_id=? ORDER BY created_at DESC LIMIT ?
    """, (user_id, limit)).fetchall()
    comment_rows = conn.execute("""
        SELECT menfess_id, message_id, created_at, content
        FROM discussion_messages
        WHERE author_user_id=? AND parent_message_id IS NOT NULL
        ORDER BY created_at DESC LIMIT ?
    """, (user_id, limit)).fetchall()
    conn.close()

    parts = []
    if menfess_rows:
        parts.append("<b>Menfess terakhir</b>")
        for row in menfess_rows:
            snippet = preview_for_log(row["content"], 90)
            parts.append(
                f"• <a href=\"{channel_post_url(row['channel_message_id'])}\">"
                f"#RU{row['id']}</a> · {fmt_ts(row['created_at'])}\n  {snippet}"
            )
    if comment_rows:
        parts.append("")
        parts.append("<b>Komentar terakhir</b>")
        for row in comment_rows:
            snippet = preview_for_log(row["content"], 90)
            parts.append(f"• {fmt_ts(row['created_at'])} · {snippet}")

    actions = get_mod_actions(limit=5, target_id=user_id)
    if actions:
        parts.append("")
        parts.append("<b>Riwayat moderasi</b>")
        for row in actions:
            detail = f" — {html.escape(row['detail'])}" if row["detail"] else ""
            parts.append(f"• {fmt_ts(row['created_at'])} · {row['action']}{detail}")

    if not parts:
        return "<i>Belum ada aktivitas tercatat.</i>"
    return "\n".join(parts)


async def reply_html(update, text, reply_markup=None):
    message = update.effective_message
    if not message:
        return
    await message.reply_text(
        text,
        parse_mode="HTML",
        reply_markup=reply_markup,
        disable_web_page_preview=True,
    )


# ------------------------------------------------------------
# AKSI
# ------------------------------------------------------------

async def apply_ban(context, actor_id, target_id, mode, duration_seconds, reason):
    """Pasang pembatasan + catat + beri tahu pihak terkait. Kembalikan ringkasan."""
    target_id = int(target_id)
    if is_owner(target_id):
        return "✕ Owner tidak bisa dibatasi."
    if target_id == BOT_USER_ID:
        return "✕ Itu akun bot ini sendiri."

    until = set_ban(target_id, mode, duration_seconds, reason, actor_id)
    log_mod_action(
        actor_id, target_id, mode,
        reason or ("permanen" if not until else fmt_duration(duration_seconds)),
    )
    await enforce_group_restriction(context.bot, target_id, mode, until)

    # Shadowban sengaja tidak diberitahukan ke user.
    if mode != "shadow":
        ban = get_ban(target_id)
        if ban:
            try:
                await context.bot.send_message(target_id, ban_notice_text(ban))
            except Exception:
                logging.info("Tidak bisa memberi tahu user %s soal ban", target_id)

    await log_event(
        context.bot,
        f"🚫 {BAN_MODE_LABEL[mode]}",
        target_id,
        reason or "tanpa alasan tertulis",
        actor_id,
    )

    durasi = "permanen" if not until else f"{fmt_duration(duration_seconds)} (sampai {fmt_ts(until)})"
    return (
        f"✓ {BAN_MODE_LABEL[mode]}: {user_label(target_id)}\n"
        f"ID: {target_id}\n"
        f"Durasi: {durasi}\n"
        f"Alasan: {html.escape(reason) if reason else '-'}"
    )


async def apply_unban(context, actor_id, target_id):
    target_id = int(target_id)
    removed = remove_ban(target_id)
    await lift_group_restriction(context.bot, target_id)
    log_mod_action(actor_id, target_id, "unban", "")
    if removed:
        try:
            await context.bot.send_message(
                target_id,
                "✓ Pembatasan akun kamu sudah dicabut.\n\n"
                "Kamu bisa mengirim menfess dan berkomentar lagi. "
                "Tolong ikuti rules supaya tidak kena lagi.",
            )
        except Exception:
            pass
        await log_event(context.bot, "✓ PEMBATASAN DICABUT", target_id, actor_id=actor_id)
        return f"✓ Pembatasan {user_label(target_id)} (<code>{target_id}</code>) dicabut."
    return f"ℹ️ {user_label(target_id)} (<code>{target_id}</code>) tidak sedang dibatasi."


# ------------------------------------------------------------
# COMMANDS
# ------------------------------------------------------------

@owner_only
async def whois_command(update, context):
    target, source, _ = resolve_mod_target(update, context.args)
    if target is None:
        await update.effective_message.reply_text(source or WHOIS_HELP)
        return
    await reply_html(
        update,
        f"🔎 <b>WHOIS</b> · <i>{html.escape(source)}</i>\n\n"
        f"{identity_block(target)}\n\n{recent_activity_text(target)}",
        reply_markup=mod_action_menu(target),
    )


@owner_only
async def ban_command(update, context):
    target, source, rest = resolve_mod_target(update, context.args)
    if target is None:
        await update.effective_message.reply_text(
            source or "Pakai: /ban <id|@username|#RU123> [alasan] atau reply pesannya."
        )
        return
    result = await apply_ban(
        context, update.effective_user.id, target, "ban", 0, " ".join(rest)
    )
    await reply_html(update, result, reply_markup=mod_action_menu(target))


@owner_only
async def mute_command(update, context):
    target, source, rest = resolve_mod_target(update, context.args)
    if target is None:
        await update.effective_message.reply_text(
            source or "Pakai: /mute <id|@username> <jam> [alasan] atau reply pesannya."
        )
        return

    hours = 24
    if rest and re.fullmatch(r"\d+", rest[0]):
        hours = int(rest[0])
        rest = rest[1:]
    if hours < 1 or hours > 24 * 365:
        await update.effective_message.reply_text("✕ Durasi mute 1–8760 jam.")
        return

    result = await apply_ban(
        context, update.effective_user.id, target, "mute",
        hours * 3600, " ".join(rest),
    )
    await reply_html(update, result, reply_markup=mod_action_menu(target))


@owner_only
async def shadowban_command(update, context):
    target, source, rest = resolve_mod_target(update, context.args)
    if target is None:
        await update.effective_message.reply_text(
            source or "Pakai: /shadowban <id|@username> [alasan] atau reply pesannya."
        )
        return
    result = await apply_ban(
        context, update.effective_user.id, target, "shadow", 0, " ".join(rest)
    )
    await reply_html(
        update,
        result + "\n\nUser tidak diberi tahu. Pesannya akan terlihat 'terkirim' "
        "tapi tidak pernah tayang.",
        reply_markup=mod_action_menu(target),
    )


@owner_only
async def unban_command(update, context):
    target, source, _ = resolve_mod_target(update, context.args)
    if target is None:
        await update.effective_message.reply_text(
            source or "Pakai: /unban <id|@username> atau reply pesannya."
        )
        return
    result = await apply_unban(context, update.effective_user.id, target)
    await reply_html(update, result)


@owner_only
async def warn_command(update, context):
    target, source, rest = resolve_mod_target(update, context.args)
    if target is None:
        await update.effective_message.reply_text(
            source or "Pakai: /warn <id|@username> [alasan] atau reply pesannya."
        )
        return
    reason = " ".join(rest)
    count = add_warning(target)
    log_mod_action(update.effective_user.id, target, "warn", reason)
    try:
        await context.bot.send_message(
            target,
            f"⚠️ Kamu mendapat warning {count}/{MAX_COMMENT_WARNINGS} dari admin."
            + (f"\nAlasan: {reason}" if reason else "")
            + "\n\nTolong baca ulang rules RANDOM UNDERGROUND.",
        )
    except Exception:
        pass
    await log_event(
        context.bot,
        f"⚠️ WARNING {count}/{MAX_COMMENT_WARNINGS}",
        target, reason, update.effective_user.id,
    )
    await reply_html(
        update,
        f"✓ Warning {count}/{MAX_COMMENT_WARNINGS} untuk {user_label(target)} "
        f"(<code>{target}</code>).",
        reply_markup=mod_action_menu(target),
    )


@owner_only
async def resetwarn_command(update, context):
    target, source, _ = resolve_mod_target(update, context.args)
    if target is None:
        await update.effective_message.reply_text(
            source or "Pakai: /resetwarn <id|@username> atau reply pesannya."
        )
        return
    reset_warnings(target)
    log_mod_action(update.effective_user.id, target, "resetwarn", "")
    await reply_html(
        update,
        f"✓ Warning {user_label(target)} (<code>{target}</code>) dinolkan.",
    )


def banlist_text():
    rows = list_bans()
    if not rows:
        return "✓ Tidak ada user yang sedang dibatasi."
    lines = [f"<b>🚫 DAFTAR PEMBATASAN</b> ({len(rows)})", ""]
    for row in rows:
        label = BAN_MODE_LABEL.get(row["mode"], row["mode"].upper())
        if row["banned_until"]:
            sisa = fmt_duration(int(row["banned_until"]) - int(time.time()))
            label += f" · sisa {sisa}"
        else:
            label += " · permanen"
        lines.append(
            f"• {user_label(row['user_id'], row)} — <code>{row['user_id']}</code>\n"
            f"  {label}"
            + (f"\n  Alasan: {html.escape(row['reason'])}" if row["reason"] else "")
        )
    lines.append("")
    lines.append("Cabut dengan: /unban &lt;user id&gt;")
    return "\n".join(lines)


def modlog_text(limit=15):
    rows = get_mod_actions(limit=limit)
    if not rows:
        return "Belum ada tindakan moderasi."
    lines = [f"<b>🛡 RIWAYAT MODERASI</b> (terakhir {len(rows)})", ""]
    for row in rows:
        actor = "bot" if row["actor_id"] in (0, BOT_USER_ID) else str(row["actor_id"])
        detail = f" — {html.escape(row['detail'])}" if row["detail"] else ""
        lines.append(
            f"• {fmt_ts(row['created_at'])} · <b>{row['action']}</b>{detail}\n"
            f"  target <code>{row['target_id']}</code> · oleh {actor}"
        )
    return "\n".join(lines)


@owner_only
async def banlist_command(update, context):
    await reply_html(update, banlist_text())


@owner_only
async def modlog_command(update, context):
    limit = 15
    if context.args and re.fullmatch(r"\d+", context.args[0]):
        limit = max(1, min(50, int(context.args[0])))
    await reply_html(update, modlog_text(limit))


async def chatid_command(update, context):
    """Dipakai saat setup: tampilkan chat id untuk diisi ke env log channel.

    Dua cara, karena keduanya punya keterbatasan masing-masing:

      - Dikirim di dalam grup: langsung membalas id grup itu.
      - Reply sebuah pesan yang di-forward (di DM): membalas id chat ASAL
        forward itu. Ini satu-satunya cara mengambil id CHANNEL, karena
        python-telegram-bot tidak meneruskan channel post ke CommandHandler
        (filter default UpdateType.MESSAGES), jadi /id yang diposting di
        dalam channel tidak akan pernah sampai ke bot.
    """
    message = update.effective_message
    chat = update.effective_chat
    if not message or not chat:
        return
    user = update.effective_user
    # Di chat privat hanya owner. Di grup dibolehkan supaya owner bisa
    # mengambil id grup tanpa perlu tool lain.
    if chat.type == "private" and (not user or not is_owner(user.id)):
        return

    reply = message.reply_to_message
    origin = getattr(reply, "forward_origin", None) if reply else None
    origin_chat = getattr(origin, "chat", None) if origin else None

    if reply is not None and origin_chat is not None:
        await message.reply_text(
            f"Chat asal forward:\n"
            f"Nama : {origin_chat.title or origin_chat.full_name or '-'}\n"
            f"Tipe : {origin_chat.type}\n"
            f"Id   : {origin_chat.id}\n\n"
            "Untuk log channel, isi di .envo:\n"
            f"RANDOMUNDERGROUND_LOG_CHAT_ID={origin_chat.id}"
        )
        return

    if reply is not None and origin is not None:
        await message.reply_text(
            "✕ Pengirim asli forward itu disembunyikan, jadi id-nya tidak "
            "terbaca.\n\nForward sebuah POSTINGAN dari channel log, bukan "
            "pesan dari orang."
        )
        return

    await message.reply_text(
        f"Chat id: {chat.id}\n"
        f"Tipe: {chat.type}\n\n"
        "Untuk log channel, isi di .envo:\n"
        f"RANDOMUNDERGROUND_LOG_CHAT_ID={chat.id}\n\n"
        "MAU ID CHANNEL?\n"
        "/id yang diposting di dalam channel tidak sampai ke bot (batasan "
        "Telegram). Caranya: forward satu postingan dari channel itu ke sini, "
        "lalu reply forward-nya dengan /id."
    )


async def set_log_channel(context, chat_id, query=None, update=None):
    """Pasang log channel lalu buktikan langsung dengan mengirim entri uji."""
    async def respond(text):
        try:
            if query is not None:
                await query.message.reply_text(text, parse_mode="HTML")
            elif update is not None:
                await reply_html(update, text)
        except Exception:
            logging.exception("Gagal membalas konfirmasi set_log_channel")

    # Pastikan bot benar-benar bisa memposting ke situ SEBELUM disimpan,
    # supaya log tidak diam-diam hilang ke chat yang tidak bisa diakses.
    try:
        chat = await context.bot.get_chat(chat_id)
    except Exception as exc:
        await respond(
            f"✕ Bot tidak bisa mengakses chat <code>{chat_id}</code>.\n\n"
            f"{html.escape(str(exc))}\n\n"
            "Pastikan bot sudah jadi admin di sana."
        )
        return False

    previous = get_setting("log_chat_id")
    set_setting("log_chat_id", chat_id)

    probe = await send_log(
        context.bot,
        "<b>✓ LOG CHANNEL AKTIF</b>\n\n"
        "Mulai sekarang setiap menfess beserta identitas pengirimnya "
        "dikirim ke sini, lengkap dengan tombol moderasi.",
    )
    if not probe:
        if previous:
            set_setting("log_chat_id", previous)
        else:
            delete_setting("log_chat_id")
        await respond(
            f"✕ Bot bisa melihat chat itu tapi gagal mengirim pesan ke sana.\n\n"
            "Beri bot izin <b>Post Messages</b> di channel tersebut, lalu coba lagi.\n"
            "Pengaturan lama dikembalikan."
        )
        return False

    title = html.escape(chat.title or "(tanpa nama)")
    logging.info("LOG CHANNEL diatur ke %s (%s)", chat_id, chat.title)
    await respond(
        f"✓ Log channel dipasang: <b>{title}</b>\n"
        f"Id: <code>{chat_id}</code>\n\n"
        "Entri uji sudah dikirim ke sana. Pengaturan ini tersimpan di database, "
        "jadi tetap bertahan walau container di-restart."
    )
    return True


@owner_only
async def setlog_command(update, context):
    """Pasang log channel manual: /setlog <id>, /setlog di chat itu, atau
    reply sebuah forward dari channel tujuan."""
    message = update.effective_message
    args = list(context.args or [])

    if args:
        raw = args[0]
        try:
            chat_id = int(raw)
        except ValueError:
            await message.reply_text("✕ Id harus angka. Contoh: /setlog -1002345678901")
            return
        await set_log_channel(context, chat_id, update=update)
        return

    reply = message.reply_to_message if message else None
    origin_chat = getattr(getattr(reply, "forward_origin", None), "chat", None)
    if origin_chat is not None:
        await set_log_channel(context, origin_chat.id, update=update)
        return

    chat = update.effective_chat
    if chat is not None and chat.type != "private":
        await set_log_channel(context, chat.id, update=update)
        return

    await message.reply_text(
        "PASANG LOG CHANNEL\n\n"
        "Salah satu dari:\n"
        "• /setlog -1002345678901\n"
        "• forward satu postingan dari channel tujuan ke sini, lalu reply "
        "forward itu dengan /setlog\n"
        "• kirim /setlog langsung di dalam grup tujuan\n\n"
        "Atau tunggu tawaran otomatis: begitu bot melihat channel barunya, "
        "kamu akan dikirimi tombol JADIKAN LOG CHANNEL."
    )


@owner_only
async def unsetlog_command(update, context):
    delete_setting("log_chat_id")
    await update.effective_message.reply_text(
        f"✓ Pengaturan log channel dihapus.\n\n"
        f"Log sekarang kembali ke: {log_target()} ({log_target_source()})."
    )


@owner_only
async def logtest_command(update, context):
    sent = await send_log(
        context.bot,
        "<b>✓ LOG CHANNEL AKTIF</b>\n\n"
        "Semua menfess baru beserta identitas pengirimnya akan masuk ke sini.",
    )
    if sent:
        await update.effective_message.reply_text(
            f"✓ Log berhasil dikirim ke {log_target()}\n"
            f"Sumber pengaturan: {log_target_source()}."
        )
    else:
        await update.effective_message.reply_text(
            f"✕ Gagal mengirim log ke {log_target()}.\n"
            f"Sumber pengaturan: {log_target_source()}.\n\n"
            "Pastikan bot sudah jadi admin di sana dengan izin Post Messages, "
            "lalu pasang ulang dengan /setlog."
        )


@owner_only
async def modhelp_command(update, context):
    await update.effective_message.reply_text(MOD_HELP)


# ------------------------------------------------------------
# TOMBOL AKSI DI LOG CHANNEL
# ------------------------------------------------------------

async def handle_mod_callback(update, context, data):
    query = update.callback_query
    actor = query.from_user
    if not actor or not is_owner(actor.id):
        try:
            await query.answer("Khusus owner.", show_alert=True)
        except Exception:
            pass
        return

    parts = data.split(":")
    action = parts[1] if len(parts) > 1 else ""
    try:
        arg = int(parts[2])
    except (IndexError, ValueError):
        return

    async def say(text, markup=None):
        try:
            await query.message.reply_text(
                text, parse_mode="HTML", reply_markup=markup,
                disable_web_page_preview=True,
            )
        except Exception:
            logging.exception("Gagal membalas aksi moderasi")

    if action == "setlog":
        await set_log_channel(context, arg, query=query)
        return

    if action == "skiplog":
        await say(
            f"✓ Chat <code>{arg}</code> diabaikan.\n\n"
            "Kalau berubah pikiran, pakai /setlog di chat itu atau "
            "reply forward-nya dengan /setlog."
        )
        return

    if action == "who":
        await say(
            f"🔎 <b>WHOIS</b>\n\n{identity_block(arg)}\n\n{recent_activity_text(arg)}",
            mod_action_menu(arg),
        )
        return

    if action in ("ban", "shadow"):
        result = await apply_ban(
            context, actor.id, arg, action, 0, "via tombol log channel"
        )
        await say(result, mod_action_menu(arg))
        return

    if action == "mute":
        result = await apply_ban(
            context, actor.id, arg, "mute", 24 * 3600, "via tombol log channel"
        )
        await say(result, mod_action_menu(arg))
        return

    if action == "unban":
        await say(await apply_unban(context, actor.id, arg))
        return

    if action == "warn":
        count = add_warning(arg)
        log_mod_action(actor.id, arg, "warn", "via tombol log channel")
        try:
            await context.bot.send_message(
                arg,
                f"⚠️ Kamu mendapat warning {count}/{MAX_COMMENT_WARNINGS} dari admin.\n\n"
                "Tolong baca ulang rules RANDOM UNDERGROUND.",
            )
        except Exception:
            pass
        await say(
            f"✓ Warning {count}/{MAX_COMMENT_WARNINGS} untuk "
            f"{user_label(arg)} (<code>{arg}</code>).",
            mod_action_menu(arg),
        )
        return

    if action == "delpost":
        menfess = get_menfess(arg)
        if not menfess:
            await say("✕ Menfess tidak ditemukan.")
            return
        try:
            await context.bot.delete_message(
                CHANNEL_CHAT_ID or CHANNEL_USERNAME,
                menfess["channel_message_id"],
            )
            log_mod_action(
                actor.id, menfess["sender_id"], "delete_post", f"#RU{arg}"
            )
            await say(
                f"✓ Postingan #RU{arg} dihapus dari channel.",
                mod_action_menu(menfess["sender_id"]),
            )
        except Exception:
            logging.exception("Gagal menghapus postingan channel")
            await say(
                "✕ Gagal menghapus postingan. Postingan yang lebih dari 48 jam "
                "tidak bisa dihapus bot, atau bot bukan admin di channel."
            )
        return

    if action == "delcom":
        comment = get_discussion_message_by_db_id(arg)
        if not comment:
            await say("✕ Komentar tidak ditemukan.")
            return
        try:
            await context.bot.delete_message(
                comment["discussion_chat_id"], comment["message_id"]
            )
            log_mod_action(
                actor.id, comment["author_user_id"], "delete_comment", str(arg)
            )
            await say(
                "✓ Komentar dihapus.",
                mod_action_menu(comment["author_user_id"]),
            )
        except Exception:
            await say("✕ Gagal menghapus komentar (mungkin sudah dihapus).")
        return



@owner_only
async def event_start_command(update, context):
    # Backward-compatible command; the normal flow is now through buttons.
    context.user_data["event_create_step"] = "name"
    await update.message.reply_text(
        "BUAT EVENT\n\n"
        "Kirim nama event-nya dulu.",
        reply_markup=event_cancel_menu(),
    )


@owner_only
async def event_stop_command(update, context):
    event = stop_event()
    if not event:
        await update.message.reply_text("✕ Tidak ada event yang sedang aktif.")
        return
    await announce_event_end(context.bot, event)
    await update.message.reply_text("Event sudah dihentikan dan hasil akhirnya diumumkan di base.")


@owner_only
async def event_status_command(update, context):
    event = get_active_event()
    if not event:
        await update.message.reply_text("✕ Tidak ada event yang sedang aktif.")
        return
    await update.message.reply_text(
        format_event_settings(event),
        reply_markup=owner_event_menu(),
    )


@owner_only
async def event_leaderboard_command(update, context):
    event = get_active_event()
    if not event:
        conn = db()
        event = conn.execute("SELECT * FROM events ORDER BY id DESC LIMIT 1").fetchone()
        conn.close()
    if not event:
        await update.message.reply_text("✕ Belum ada event.")
        return
    await update.message.reply_text(
        format_public_event_leaderboard(),
        reply_markup=owner_event_menu(),
    )


@owner_only
async def event_help_command(update, context):
    await update.message.reply_text(
        "EVENT\n\n"
        "Buka /start → OWNER CONTROL → EVENT.\n\n"
        "Di sana kamu bisa membuat, melihat, dan menghentikan event."
    )


async def community_watcher(application):
    while True:
        try:
            now=int(time.time())
            # Send one daily QOTD at ~20:00 local time, once per day.
            local=time.localtime(now); key=day_key(now)
            if local.tm_hour == 20 and local.tm_min == 0:
                conn=db(); sent=conn.execute("SELECT value FROM community_meta WHERE key=?",(f"qotd:{key}",)).fetchone()
                if not sent:
                    q=QOTD[int(time.strftime("%j",local)) % len(QOTD)]
                    await application.bot.send_message(CHANNEL_USERNAME,"QUESTION OF THE DAY\\n\\n"+q+"\\n\\n▸ Jawab di komentar.")
                    conn.execute("INSERT OR REPLACE INTO community_meta VALUES (?,?)",(f"qotd:{key}","sent")); conn.commit()
                conn.close()
            # If base has been quiet for 2h, send one prompt, max once per 6h.
            conn=db(); last=conn.execute("SELECT MAX(created_at) x FROM discussion_messages").fetchone()["x"] or 0
            cool=conn.execute("SELECT value FROM community_meta WHERE key='quiet:last'").fetchone(); last_prompt=int(cool["value"]) if cool else 0
            conn.close()
            if now-last>=7200 and now-last_prompt>=21600:
                await application.bot.send_message(CHANNEL_USERNAME,"BASE SEPI\\n\\nMending WiFi gratis seumur hidup atau makanan gratis seumur hidup?\\n\\n▸ Bahas di komentar.")
                conn=db(); conn.execute("INSERT OR REPLACE INTO community_meta VALUES ('quiet:last',?)",(str(now),)); conn.commit(); conn.close()
        except Exception:
            logging.exception("Community watcher error")
        await asyncio.sleep(30)


async def event_watcher(application):
    while True:
        try:
            event = get_active_event()
            if event and event["ends_at"] and int(time.time()) >= event["ends_at"]:
                ended = stop_event()
                if ended:
                    await announce_event_end(application.bot, ended)
        except Exception:
            logging.exception("Event watcher error")
        # 30 detik cukup presisi untuk mengakhiri event; hindari polling DB tiap detik.
        await asyncio.sleep(30)


@owner_only
async def event_cancel_command(update, context):
    context.user_data.pop("event_create_step", None)
    context.user_data.pop("event_name", None)
    context.user_data.pop("event_duration", None)
    context.user_data.pop("waiting_event_duration", None)
    await update.message.reply_text(
        "✕ Pembuatan event dibatalkan. Tidak ada event baru yang dibuat.",
        reply_markup=owner_event_menu(),
    )


# STARTUP / MAIN
# ============================================================

async def creative_files_janitor():
    """Hapus file upload/render creative yang lebih tua dari 1 jam agar disk tidak penuh."""
    from pathlib import Path
    base = Path(os.getenv("RANDOMUNDERGROUND_DATA_DIR", ".")).resolve()
    dirs = [base / "creative_uploads", base / "creative_renders"]
    max_age = 3600
    while True:
        try:
            now = time.time()
            for d in dirs:
                if not d.exists():
                    continue
                for p in d.iterdir():
                    try:
                        if p.is_file() and now - p.stat().st_mtime > max_age:
                            p.unlink(missing_ok=True)
                    except OSError:
                        continue
        except Exception:
            logging.exception("Creative janitor error")
        await asyncio.sleep(1800)


async def post_init(application):
    await load_chat_ids(application)
    application.create_task(event_watcher(application))
    application.create_task(community_watcher(application))
    application.create_task(creative_files_janitor())


async def error_handler(update, context):
    logging.error("Unhandled exception: %s", context.error)



def backfill_activity_log():
    """Backfill old menfess and comments into the permanent leaderboard log once."""
    conn = db()
    conn.execute("""
        CREATE TABLE IF NOT EXISTS activity_backfill_meta (
            key TEXT PRIMARY KEY,
            value TEXT
        )
    """)
    done = conn.execute(
        "SELECT value FROM activity_backfill_meta WHERE key='v7_all_activity'"
    ).fetchone()
    if done:
        conn.close()
        return

    # Existing menfess -> 2 points through activity_type='menfess'.
    menfess_rows = conn.execute("""
        SELECT id, sender_id, created_at
        FROM menfess
        WHERE sender_id IS NOT NULL
    """).fetchall()

    for row in menfess_rows:
        # Do not backfill owner accounts into public leaderboard data.
        if is_owner(row["sender_id"]):
            continue
        try:
            _insert_activity(
                conn,
                row["sender_id"],
                "menfess",
                row["created_at"],
                f"mf:{row['id']}",
            )
        except sqlite3.IntegrityError:
            pass

    # Existing discussion comments -> 1 point each.
    comment_rows = conn.execute("""
        SELECT id, author_user_id, created_at
        FROM discussion_messages
        WHERE author_user_id IS NOT NULL
    """).fetchall()

    for row in comment_rows:
        if is_owner(row["author_user_id"]):
            continue
        try:
            _insert_activity(
                conn,
                row["author_user_id"],
                "comment",
                row["created_at"],
                f"comment:{row['id']}",
            )
        except sqlite3.IntegrityError:
            pass

    conn.execute("""
        INSERT OR REPLACE INTO activity_backfill_meta(key, value)
        VALUES ('v7_all_activity', 'done')
    """)
    conn.commit()
    conn.close()


def main():
    logging.basicConfig(
        format="%(asctime)s - %(levelname)s - %(message)s",
        level=logging.INFO,
    )
    # httpx mencatat URL lengkap di level INFO, termasuk token bot di path.
    # Naikkan ke WARNING supaya token tidak bocor ke log container.
    logging.getLogger("httpx").setLevel(logging.WARNING)
    logging.getLogger("httpcore").setLevel(logging.WARNING)

    if not BOT_TOKEN:
        raise RuntimeError(
            "BOT_TOKEN belum diisi. Set environment variable "
            "RANDOMUNDERGROUND_BOT_TOKEN (jangan hardcode di source)."
        )

    init_db()
    # Leaderboards now read directly from menfess/discussion_messages.
    # Do not backfill activity_log on startup; that legacy log is not authoritative.

    app = (
        Application.builder()
        .token(BOT_TOKEN)
        .post_init(post_init)
        .build()
    )

    app.add_handler(CommandHandler("start", start))
    # V17 Creative/Fun/Text module. Registered before legacy private media handler.
    register_creative_handlers(app)

    # Event commands
    app.add_handler(CommandHandler("event_start", event_start_command))
    app.add_handler(CommandHandler("event_cancel", event_cancel_command))
    app.add_handler(CommandHandler("event_stop", event_stop_command))
    app.add_handler(CommandHandler("event_status", event_status_command))
    app.add_handler(CommandHandler("event_leaderboard", event_leaderboard_command))
    app.add_handler(CommandHandler("event_help", event_help_command))

    app.add_handler(CommandHandler("profile", profile_command))

    # Moderasi. Didaftarkan sebelum MessageHandler grup supaya perintah
    # yang dikirim di grup diskusi / log group tidak ikut tertelan.
    app.add_handler(CommandHandler("whois", whois_command))
    app.add_handler(CommandHandler("ban", ban_command))
    app.add_handler(CommandHandler("mute", mute_command))
    app.add_handler(CommandHandler("shadowban", shadowban_command))
    app.add_handler(CommandHandler("unban", unban_command))
    app.add_handler(CommandHandler("warn", warn_command))
    app.add_handler(CommandHandler("resetwarn", resetwarn_command))
    app.add_handler(CommandHandler("banlist", banlist_command))
    app.add_handler(CommandHandler("modlog", modlog_command))
    app.add_handler(CommandHandler("modhelp", modhelp_command))
    app.add_handler(CommandHandler("logtest", logtest_command))
    app.add_handler(CommandHandler("setlog", setlog_command))
    app.add_handler(CommandHandler("unsetlog", unsetlog_command))
    app.add_handler(CommandHandler("id", chatid_command))

    # Discussion group must be before private handler.
    app.add_handler(
        MessageHandler(
            filters.ChatType.GROUPS,
            discussion_comment_handler,
        )
    )

    app.add_handler(
        MessageHandler(
            filters.ChatType.PRIVATE & (filters.TEXT | filters.PHOTO),
            message_handler,
        )
    )

    app.add_handler(CallbackQueryHandler(callback_handler))

    # Group 1: pengamat pasif. Handler di group berbeda selalu ikut jalan dan
    # tidak pernah menghentikan pemrosesan handler di group 0.
    app.add_handler(
        ChatMemberHandler(my_chat_member_watcher, ChatMemberHandler.MY_CHAT_MEMBER),
        group=1,
    )
    app.add_handler(
        MessageHandler(filters.UpdateType.CHANNEL_POSTS, channel_post_watcher),
        group=1,
    )

    app.add_error_handler(error_handler)

    print("RANDOM UNDERGROUND // ONLINE")
    print("Menfess anonim aktif.")
    print("Komentar + reply anonim aktif untuk semua orang.")
    print("Leaderboards: ALL-TIME / WEEKLY / MONTHLY + EVENT.")
    print("Event + leaderboard aktif.")
    print("Community: missions, QOTD, titles, MVP, spotlight, mystery box, trending aktif.")
    print("✕ Moderasi kata terlarang aktif.")
    logging.info("LOG CHANNEL: %s (%s)", log_target(), log_target_source())
    print("🛡 Moderasi: /whois /ban /mute /shadowban /unban /banlist /modlog")
    print("Menunggu pesan...")

    app.run_polling()


if __name__ == "__main__":
    main()
