#!/usr/bin/env python3
"""
Telegram Bot - Admin & User Panel
Single file — v10
"""

import sqlite3
import atexit
import logging
import io
import csv
import threading
import zipfile
import tempfile
import asyncio
import os
import json
import re
import time
import hashlib
import math
import html as _html
import requests
from playwright.sync_api import (
    TimeoutError as PlaywrightTimeoutError,
    sync_playwright,
)
from decimal import Decimal, InvalidOperation, ROUND_HALF_UP
from html.parser import HTMLParser
from urllib.parse import urljoin, urlparse

import openpyxl
from telegram import (
    Bot, Message, MessageEntity, Update,
    InlineKeyboardButton as TelegramInlineKeyboardButton, InlineKeyboardMarkup,
    ReplyKeyboardMarkup, KeyboardButton as TelegramKeyboardButton, CopyTextButton
)
from telegram.request import HTTPXRequest
from telegram.ext import (
    Application, CommandHandler, CallbackQueryHandler,
    MessageHandler, filters, ContextTypes, ApplicationHandlerStop
)

# ─── CONFIG ───────────────────────────────────────────────────────────────────
SUPER_ADMINS = {7831629041, 8407207846}  # permanent; cannot be removed
# The bot token is loaded strictly from environment variables.
BOT_TOKEN  = os.getenv("BOT_TOKEN", "")
DB_FILE    = os.getenv("BOT_DB_FILE", "bot_data.db")
JSON_DB_DIR = os.getenv(
    "BOT_JSON_DB_DIR",
    os.path.dirname(os.path.abspath(DB_FILE)),
)


def _json_file_path(env_name: str, preferred_name: str, legacy_name: str) -> str:
    """Resolve the current JSON filename while keeping old uploads readable."""
    configured = os.getenv(env_name)
    if configured:
        return configured

    preferred = os.path.join(JSON_DB_DIR, preferred_name)
    legacy = os.path.join(JSON_DB_DIR, legacy_name)
    # The first archive used singular names. Prefer it when the new name is
    # not present so a redeploy does not silently start with an empty database.
    if not os.path.exists(preferred) and os.path.exists(legacy):
        return legacy
    return preferred


NUMBERS_FILE = _json_file_path(
    "BOT_NUMBERS_FILE", "numbers.json", "number.json"
)
USERS_FILE = _json_file_path(
    "BOT_USERS_FILE", "users.json", "user.json"
)
BOT_FILE   = os.path.abspath(__file__)

# Telegram's bot-wide broadcast ceiling is 30 messages per second. The
# limiter below uses that ceiling without an initial burst, reserves one
# steady slot per message, and backs off every worker together when Telegram
# returns 429/RetryAfter.
BROADCAST_RATE_PER_SECOND = 30
BROADCAST_WORKERS = 40
BROADCAST_PROGRESS_STEP = 250
BROADCAST_RETRY_ATTEMPTS = 3

# Telegram's documented per-group limit is 20 messages/minute. Group
# forwarding therefore runs in its own queue so a slow group never blocks
# direct OTP delivery to users.
OTP_GROUP_MESSAGES_PER_MINUTE = 20
OTP_GROUP_MIN_INTERVAL = 60 / (OTP_GROUP_MESSAGES_PER_MINUTE - 1)
OTP_GROUP_QUEUE_MAXSIZE = 50000
_otp_group_queue = None
_otp_group_worker_task = None
OTP_USER_MESSAGES_PER_SECOND = 25
_otp_user_rate_lock = None
_otp_user_last_sent_at = 0.0

# Operational safety limits. These are deliberately conservative defaults;
# admins can still add more panels, but one broken provider cannot consume all
# memory, flood an upstream API, or drain the entire number inventory at once.
MAX_NUMBERS_PER_USER_REQUEST = 10
NUMBER_REQUEST_COOLDOWN_SECONDS = 5
DEFAULT_NUMBER_VALID_TIME_MINUTES = 10
MIN_NUMBER_VALID_TIME_MINUTES = 1
MAX_NUMBER_VALID_TIME_MINUTES = 10080
MAX_NUMBER_UPLOAD_BYTES = 10 * 1024 * 1024
MAX_NUMBERS_PER_UPLOAD = 100_000
MAX_OTP_GROUPS = 100
API_MAX_RESPONSE_BYTES = 2 * 1024 * 1024
API_MAX_ROWS = 1_000
# The panel's configured scan interval is the source of truth.  In particular,
# an API panel configured for 3 seconds must be requested every 3 seconds.
# Keep the state/lock helpers below for safe serialization, but do not impose
# an unrelated minimum delay between requests.
API_MIN_REQUEST_INTERVAL_SECONDS = 0
API_BLOCK_RETRY_SECONDS = 10
_api_failure_at = {}
_api_failure_lock = threading.Lock()
_api_request_state = {}
_api_request_state_lock = threading.Lock()

logging.basicConfig(
    format="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
    level=logging.INFO
)
logger = logging.getLogger(__name__)
# HTTP request URLs contain the Telegram bot token; never emit them to logs.
logging.getLogger("httpx").setLevel(logging.WARNING)
logging.getLogger("httpcore").setLevel(logging.WARNING)

_API_SMS_CACHE_TTL = 3.0
_CAPTCHA_SMS_CACHE_TTL = 15.0
_PANEL_KEEPALIVE_INTERVAL = 60
_PANEL_UTC_ROLLOVER_CHECK_INTERVAL = 30
_PANEL_RELOGIN_NOTICE_COOLDOWN = 900
_panel_sms_cache = {}
_panel_sms_cache_lock = threading.Lock()
_panel_relogin_lock = threading.Lock()
_panel_relogin_notice_at = {}
_BROWSER_EXECUTABLE_CANDIDATES = (
    os.getenv("PANEL_BROWSER_EXECUTABLE", ""),
    "/repl/tools/bin/chromium",
    "/usr/bin/chromium",
    "/usr/bin/chromium-browser",
    "/usr/bin/google-chrome",
)


def _panel_type(panel_row) -> str:
    """Normalize supported panel modes for old and new saved rows."""
    if hasattr(panel_row, "get"):
        value = panel_row.get("panel_type")
    else:
        try:
            value = panel_row["panel_type"]
        except (KeyError, IndexError, TypeError):
            value = None
    normalized = str(value or "").strip().casefold().replace("-", "_").replace(" ", "_")
    if normalized == "api":
        return "api"
    if normalized in {"non_captcha", "noncaptcha", "web", "standard"}:
        return "non_captcha"
    return "captcha"


def _is_web_panel(panel_row) -> bool:
    """Return whether a panel uses a cookie-based web login."""
    return _panel_type(panel_row) in {"captcha", "non_captcha"}


def _panel_sms_cache_key(panel_row):
    """Use a stable key for both sqlite rows and plain dictionaries."""
    if hasattr(panel_row, "get"):
        return (
            panel_row.get("id")
            or panel_row.get("stats_url")
            or panel_row.get("name")
        )
    try:
        return (
            panel_row["id"]
            or panel_row["stats_url"]
            or panel_row["name"]
        )
    except (KeyError, IndexError, TypeError):
        return None


def _panel_sms_cached(panel_key, ttl):
    with _panel_sms_cache_lock:
        cached = _panel_sms_cache.get(panel_key)
        if not cached:
            return None
        fetched_at, rows = cached
        if time.monotonic() - fetched_at >= ttl:
            _panel_sms_cache.pop(panel_key, None)
            return None
        return list(rows)


def _panel_sms_stale(panel_key):
    """Return the last valid rows even when their normal cache TTL expired."""
    with _panel_sms_cache_lock:
        cached = _panel_sms_cache.get(panel_key)
        return list(cached[1]) if cached else []


def _panel_persisted_latest(panel_row):
    """Load the last successful SMS row saved with the panel configuration."""
    if hasattr(panel_row, "get"):
        raw = panel_row.get("last_sms_json")
    else:
        raw = None
    if not raw:
        return []
    try:
        row = json.loads(raw) if isinstance(raw, str) else raw
    except (TypeError, ValueError, json.JSONDecodeError):
        return []
    return [row] if isinstance(row, dict) and row.get("message") is not None else []


def _persist_panel_latest_sms(panel_row, rows):
    """Keep one last good row available across bot restarts/provider outages."""
    if not rows or not hasattr(panel_row, "get"):
        return
    panel_id = panel_row.get("id")
    if panel_id is None:
        return
    try:
        payload = json.dumps(rows[0], ensure_ascii=False)
        db_execute(
            "UPDATE panels SET last_sms_json=? WHERE id=?",
            (payload, panel_id),
        )
        try:
            panel_row["last_sms_json"] = payload
        except (TypeError, IndexError):
            pass
    except Exception:
        logger.debug("Could not persist latest SMS for panel %s", panel_id, exc_info=True)


def _panel_sms_store(panel_key, rows, limit=None):
    with _panel_sms_cache_lock:
        _panel_sms_cache[panel_key] = (time.monotonic(), list(rows))
    return list(rows[:limit] if limit else rows)


def _api_key_name(value) -> str:
    """Make API field matching tolerant of snake/camel/kebab case."""
    return re.sub(r"[^a-z0-9]", "", str(value).casefold())


def _api_row_values(row, number_idx, sender_idx, message_idx, field_map=None):
    """Read common named API fields, then fall back to configured columns.

    API providers do not agree on field spelling.  For example, all of
    ``phone_number``, ``phoneNumber`` and ``msisdn`` are common.  Comparing
    normalized names prevents a valid SMS from being discarded just because
    the provider changed snake_case to camelCase.
    """
    size = max(number_idx, sender_idx, message_idx, 1) + 1
    if isinstance(row, dict):
        normalized = {_api_key_name(k): v for k, v in row.items()}

        def first_value(names):
            for name in names:
                value = normalized.get(_api_key_name(name))
                if value is not None and str(value).strip():
                    return value
            return ""

        field_map = field_map or {}

        def configured_value(key, defaults):
            custom = _api_mapping_value(
                row, field_map.get(key), normalized
            )
            return custom if custom is not None and str(custom).strip() else first_value(defaults)

        timestamp = configured_value("timestamp", (
            "timestamp", "time", "date", "datetime", "created_at",
            "created", "createdAt", "received_at", "receivedAt",
            "sent_at", "sentAt", "date_time", "dateTime",
            "dt", "created_on", "createdOn", "received_on", "receivedOn",
            # Some SMS APIs have no date but do provide a monotonic id.
            "message_id", "messageId", "sms_id", "smsId", "id",
        ))
        number = configured_value("number", (
            "number", "phone", "phone_number", "phoneNumber", "msisdn",
            "mobile", "mobile_number", "mobileNumber", "recipient",
            "to", "destination", "num", "phone_num", "phoneNo",
            "recipient_number", "number_value",
        ))
        sender = configured_value("sender", (
            "sender", "cli", "service", "from", "origin", "source",
            "sender_id", "senderId", "from_number", "fromNumber",
        ))
        message = configured_value("message", (
            "message", "sms", "text", "body", "content", "message_text",
            "messageText", "sms_text", "smsText", "msg",
        ))
        if number or sender or message:
            values = [""] * size
            values[0] = timestamp
            values[1] = configured_value("range", (
                "range", "country", "country_code", "countryCode"
            ))
            values[number_idx] = number
            values[sender_idx] = sender
            values[message_idx] = message
            return values
        return list(row.values()) + [""] * max(0, size - len(row.values()))
    if isinstance(row, (list, tuple)):
        return list(row) + [""] * max(0, size - len(row))
    return ()


def _api_payload_rows(payload):
    """Extract SMS rows from common API envelopes without assuming one shape."""
    if isinstance(payload, list):
        return payload
    if not isinstance(payload, dict):
        return []

    preferred = (
        "data", "results", "messages", "aaData", "items", "rows",
        "records", "response", "result", "payload",
    )
    normalized = {_api_key_name(key): value for key, value in payload.items()}
    for key in preferred:
        value = normalized.get(_api_key_name(key))
        if isinstance(value, list):
            return value
        if isinstance(value, dict):
            nested = _api_payload_rows(value)
            if nested:
                return nested

    # A single SMS object should not be mistaken for an empty response
    # envelope.  Check collection keys first because providers often return
    # {"message": "ok", "data": [...]}.
    field_names = {_api_key_name(key) for key in payload}
    sms_fields = {
        "number", "phone", "phonenumber", "msisdn", "mobile",
        "message", "sms", "text", "body", "content",
    }
    if field_names & sms_fields:
        return [payload]

    # Last-resort support for wrappers whose collection is named differently.
    for value in payload.values():
        if isinstance(value, list):
            return value
    return []


def _api_path_value(value, path):
    """Read a dotted JSON path such as data.items or response.rows."""
    if not path:
        return value
    current = value
    for part in str(path).strip().split("."):
        if not part:
            continue
        if isinstance(current, dict):
            if part not in current:
                return None
            current = current[part]
        elif isinstance(current, (list, tuple)) and part.isdigit():
            index = int(part)
            if index >= len(current):
                return None
            current = current[index]
        else:
            return None
    return current


def _api_mapping_value(row, custom_name, normalized):
    """Resolve a configured field before falling back to normalized keys."""
    if not custom_name:
        return None
    custom_name = str(custom_name).strip()
    if "." in custom_name:
        return _api_path_value(row, custom_name)
    return normalized.get(_api_key_name(custom_name))


def _parse_api_mapping(raw):
    """Parse optional mapping input from the API-panel wizard."""
    mapping = {}
    text = str(raw or "").strip()
    if not text or text.casefold() in {"none", "auto", "-"}:
        return mapping
    for item in re.split(r"[;,]\s*", text):
        if "=" not in item:
            continue
        key, value = item.split("=", 1)
        key = key.strip().casefold()
        value = value.strip()
        aliases = {
            "rows": "rows_path",
            "path": "rows_path",
            "number": "number_field",
            "phone": "number_field",
            "sender": "sender_field",
            "cli": "sender_field",
            "message": "message_field",
            "sms": "message_field",
            "time": "timestamp_field",
            "timestamp": "timestamp_field",
            "range": "range_field",
            "country": "range_field",
        }
        if key in aliases and value:
            mapping[aliases[key]] = value
    return mapping


def api_auth_markup():
    """Render the authentication choices shared by every API-panel wizard."""
    return InlineKeyboardMarkup([
        [
            InlineKeyboardButton("🤖 Auto", callback_data="api_auth_auto"),
            InlineKeyboardButton("Bearer", callback_data="api_auth_bearer"),
        ],
        [
            InlineKeyboardButton("X-API-Key", callback_data="api_auth_x_api_key"),
            InlineKeyboardButton("Raw Authorization", callback_data="api_auth_raw"),
        ],
        [
            InlineKeyboardButton("Token", callback_data="api_auth_token"),
            InlineKeyboardButton("X-Auth-Token", callback_data="api_auth_x_auth_token"),
        ],
        [
            InlineKeyboardButton("api-key header", callback_data="api_auth_api_key_header"),
            InlineKeyboardButton("Basic user:pass", callback_data="api_auth_basic"),
        ],
        [
            InlineKeyboardButton("Custom header", callback_data="api_auth_custom_header"),
            InlineKeyboardButton("Custom query", callback_data="api_auth_custom_query"),
        ],
        [
            InlineKeyboardButton("Token query (?token=)", callback_data="api_auth_token_query"),
        ],
        [
            InlineKeyboardButton("POST form", callback_data="api_auth_post_form"),
            InlineKeyboardButton("POST JSON", callback_data="api_auth_post_json"),
        ],
        [
            InlineKeyboardButton("No authentication", callback_data="api_auth_none"),
            InlineKeyboardButton("❌ Cancel", callback_data="cancel_input"),
        ],
    ])


def _api_token(value):
    return re.sub(
        r"^\s*(?:bearer|token|api[\s_-]*key)\s+",
        "",
        str(value or "").strip(),
        flags=re.IGNORECASE,
    )


def _api_request_attempts(panel):
    """Build explicit, provider-configurable request/auth attempts."""
    method = str(panel.get("api_method") or "GET").upper()
    if method not in {"GET", "POST"}:
        method = "GET"
    key = str(panel.get("api_key") or "").strip()
    auth_type = str(panel.get("api_auth_type") or "auto").casefold()
    auth_name = str(panel.get("api_auth_name") or "").strip()
    token = _api_token(key)
    base = {
        "method": method,
        "headers": {
            "Accept": "application/json, text/plain, */*",
            "User-Agent": (
                "Mozilla/5.0 (compatible; SMSBot/1.0; "
                "+https://telegram.org)"
            ),
        },
        "timeout": 15,
    }

    def one(**kwargs):
        request = dict(base)
        request["headers"] = dict(base["headers"])
        custom_headers = kwargs.pop("headers", None)
        if custom_headers:
            request["headers"].update(custom_headers)
        request.update(kwargs)
        return request

    if auth_type == "none" or not token:
        return [one()]
    if auth_type == "basic":
        if ":" not in key:
            return []
        username, password = key.split(":", 1)
        return [one(auth=(username, password))]
    if auth_type == "bearer":
        return [one(headers={"Authorization": f"Bearer {token}"})]
    if auth_type == "raw_authorization":
        return [one(headers={"Authorization": key})]
    if auth_type == "token":
        return [one(headers={"Authorization": f"Token {token}"})]
    if auth_type == "x_auth_token":
        return [one(headers={"X-Auth-Token": token})]
    if auth_type == "x_api_key":
        return [one(headers={"X-API-Key": token})]
    if auth_type == "api_key_header":
        return [one(headers={"api-key": token})]
    if auth_type == "custom_header":
        return [one(headers={auth_name or "Authorization": token})]
    if auth_type in {"query", "custom_query"}:
        return [one(params={auth_name or "api_key": token})]
    if auth_type == "token_query":
        return [one(params={"token": token})]
    if auth_type == "post_form":
        request = one(data={auth_name or "api_key": token})
        request["method"] = "POST"
        return [request]
    if auth_type == "post_json":
        request = one(json={auth_name or "api_key": token})
        request["method"] = "POST"
        return [request]

    # Auto mode tries common read-only authentication formats.  Query-string
    # auth is included last for providers that do not accept headers.
    return [
        one(headers={"Authorization": f"Bearer {token}"}),
        one(headers={"X-API-Key": token}),
        one(headers={"Authorization": token}),
        one(headers={"Authorization": f"Token {token}"}),
        one(headers={"X-Auth-Token": token}),
        one(headers={"api-key": token}),
        one(params={"token": token}),
        one(params={"api_key": token}),
        one(params={"access_token": token}),
    ]


def _api_auto_auth_config(attempt_index):
    """Return the saved auth setting matching an auto-auth attempt."""
    configs = (
        ("bearer", ""),
        ("x_api_key", ""),
        ("raw_authorization", ""),
        ("token", ""),
        ("x_auth_token", ""),
        ("api_key_header", ""),
        ("token_query", ""),
        ("custom_query", "api_key"),
        ("custom_query", "access_token"),
    )
    if 0 <= attempt_index < len(configs):
        return configs[attempt_index]
    return None, ""


def _api_remember_auto_auth(panel, attempt_index):
    """Persist a working auto-detected auth format for future scans."""
    if str(panel.get("api_auth_type") or "auto").casefold() != "auto":
        return
    panel_id = panel.get("id")
    auth_type, auth_name = _api_auto_auth_config(attempt_index)
    if panel_id is None or not auth_type:
        return
    try:
        db_execute(
            "UPDATE panels SET api_auth_type=?, api_auth_name=? WHERE id=?",
            (auth_type, auth_name, panel_id),
        )
        panel["api_auth_type"] = auth_type
        panel["api_auth_name"] = auth_name
        logger.info(
            "Saved working API auth format for panel %s: %s",
            panel.get("name", "?"),
            auth_type if not auth_name else f"{auth_type}:{auth_name}",
        )
    except Exception:
        logger.debug("Could not save API auth format", exc_info=True)


def _api_response_is_auth_error(response):
    """Recognize HTTP and application-level authentication failures."""
    if response.status_code in (401, 403):
        return True
    try:
        payload = response.json()
    except ValueError:
        return False
    if not isinstance(payload, dict):
        return False
    status = str(
        payload.get("status")
        or payload.get("state")
        or payload.get("result")
        or ""
    ).casefold()
    success = payload.get("success")
    error_values = []
    for key, value in payload.items():
        normalized_key = _api_key_name(key)
        if normalized_key in {
            "status", "state", "result", "success", "error", "errors",
            "message", "msg", "detail", "reason", "code",
        }:
            if isinstance(value, (dict, list)):
                error_values.append(json.dumps(value, ensure_ascii=False))
            else:
                error_values.append(str(value or ""))
    message = " ".join(error_values).casefold()
    auth_words = (
        "unauthor", "invalid key", "invalid token", "authentication",
        "access denied", "forbidden", "not allowed",
    )
    auth_match = any(word in message for word in auth_words)
    return (
        auth_match
        and (
            status in {"error", "failed", "failure", "false"}
            or success is False
            # Some providers return only {"message": "Unauthorized"} with
            # HTTP 200 and omit both status and success fields.
            or "unauthor" in message
        )
    )


def _api_error_is_throttled(panel_key):
    """Return whether an upstream rate-limit recovery window is still active."""
    now = time.monotonic()
    with _api_request_state_lock:
        state = _api_request_state.get(panel_key)
        return bool(state and state["blocked_until"] > now)


def _api_mark_failure(panel_key):
    with _api_failure_lock:
        _api_failure_at[panel_key] = time.monotonic()


def _api_clear_failure(panel_key):
    with _api_failure_lock:
        _api_failure_at.pop(panel_key, None)


def _api_request_lock(panel_key):
    """Return the per-panel lock used to prevent overlapping API calls."""
    with _api_request_state_lock:
        state = _api_request_state.setdefault(
            panel_key,
            {
                "lock": threading.RLock(),
                "last_request_at": 0.0,
                "blocked_until": 0.0,
            },
        )
        return state["lock"]


def _api_retry_after_seconds(response) -> float:
    """Read a provider's Retry-After hint without trusting malformed values."""
    raw = getattr(response, "headers", {}).get("Retry-After")
    try:
        return max(0.0, float(raw))
    except (TypeError, ValueError):
        return 0.0


def _api_wait_for_slot(panel_key):
    """Wait only for an active provider cooldown; never add a scan delay."""
    while True:
        with _api_request_state_lock:
            state = _api_request_state.setdefault(
                panel_key,
                {
                    "lock": threading.RLock(),
                    "last_request_at": 0.0,
                    "blocked_until": 0.0,
                },
            )
            now = time.monotonic()
            next_allowed = state["blocked_until"]
            wait_for = next_allowed - now
            if wait_for <= 0:
                # Reserve this slot before releasing the state lock so a
                # second worker cannot reserve the same timestamp.
                state["last_request_at"] = now
                return
        time.sleep(wait_for)


def _api_mark_throttled(panel_key, response) -> int:
    """Start a bounded provider cooldown and return its effective seconds."""
    retry_after = _api_retry_after_seconds(response)
    delay = max(API_BLOCK_RETRY_SECONDS, retry_after)
    with _api_request_state_lock:
        state = _api_request_state.setdefault(
            panel_key,
            {
                "lock": threading.RLock(),
                "last_request_at": 0.0,
                "blocked_until": 0.0,
            },
        )
        state["blocked_until"] = max(
            state["blocked_until"],
            time.monotonic() + delay,
        )
    return int(math.ceil(delay))


def _api_request_with_limits(panel_key, request_kwargs):
    """Send one serialized API request, honoring only provider cooldowns."""
    with _api_request_lock(panel_key):
        _api_wait_for_slot(panel_key)
        try:
            return requests.request(**request_kwargs)
        finally:
            # Measure the cooldown from response completion so a slow request
            # cannot make the next request start immediately.
            with _api_request_state_lock:
                state = _api_request_state.get(panel_key)
                if state is not None:
                    state["last_request_at"] = time.monotonic()


def _forget_panel_runtime_state(panel_row_or_key):
    """Drop cached/API diagnostic state when a panel is removed or replaced."""
    if isinstance(panel_row_or_key, (str, int)) or panel_row_or_key is None:
        panel_key = panel_row_or_key
    else:
        panel_key = _panel_sms_cache_key(panel_row_or_key)
    with _panel_sms_cache_lock:
        _panel_sms_cache.pop(panel_key, None)
        _panel_relogin_notice_at.pop(panel_key, None)
    _api_clear_failure(panel_key)
    with _api_request_state_lock:
        _api_request_state.pop(panel_key, None)


def _api_set_last_error(panel, message):
    """Persist a short, credential-free API diagnostic for the admin panel."""
    panel_id = panel.get("id") if hasattr(panel, "get") else None
    if panel_id is None:
        return
    safe_message = " ".join(str(message or "").split())[:300]
    try:
        current = db_query(
            "SELECT api_last_error FROM panels WHERE id=?",
            (panel_id,),
        )
        if current and current[0]["api_last_error"] == (safe_message or None):
            return
        db_execute(
            "UPDATE panels SET api_last_error=? WHERE id=?",
            (safe_message or None, panel_id),
        )
    except Exception:
        # Diagnostics must never take down SMS polling.
        logger.debug("Could not persist API panel diagnostic", exc_info=True)


def format_price(value) -> str:
    """Render prices without rounding away small decimal amounts.

    SQLite returns REAL values as floats, so use their string representation
    before formatting.  Fixed-point output keeps values such as 0.000076
    visible instead of reducing them to $0.00.
    """
    try:
        amount = Decimal(str(value if value is not None else 0))
    except (InvalidOperation, ValueError, TypeError):
        amount = Decimal("0")

    rendered = format(amount, "f")
    if "." in rendered:
        rendered = rendered.rstrip("0").rstrip(".")
    return rendered or "0"

# Telegram supports three inline-button styles:
# primary (blue), success (green), and danger (red).  Keep the style decision
# in one place so every keyboard in this single-file bot stays consistent.
INLINE_PRIMARY = "primary"
INLINE_SUCCESS = "success"
INLINE_DANGER = "danger"


def _inline_button_style(text: str, callback_data=None) -> str:
    """Choose a Telegram inline-button color from its action semantics."""
    label = str(text).casefold()
    callback = str(callback_data or "").casefold()

    danger_terms = (
        "cancel", "reject", "delete", "remove", "zero", "danger",
        "বাতিল", "মুছুন", "না",
    )
    success_terms = (
        "approve", "confirm", "yes", "joined", "add", "resume",
        "check again", "হ্যাঁ",
    )

    if any(term in label or term in callback for term in danger_terms):
        return INLINE_DANGER
    if any(term in label or term in callback for term in success_terms):
        return INLINE_SUCCESS
    return INLINE_PRIMARY


def InlineKeyboardButton(text: str, *args, **kwargs):
    """Create a Telegram inline button with automatic style injection via api_kwargs."""
    # Pop legacy direct-kwarg style/icon (not supported by Telegram constructor)
    style = kwargs.pop("style", None)
    icon_emoji_id = kwargs.pop("icon_custom_emoji_id", None)
    # Determine style if not supplied
    if style is None:
        style = _inline_button_style(text, kwargs.get("callback_data"))
    # Inject into api_kwargs so Telegram Bot API receives it
    api_kw = dict(kwargs.pop("api_kwargs", None) or {})
    api_kw.setdefault("style", style)
    if icon_emoji_id:
        api_kw["icon_custom_emoji_id"] = icon_emoji_id
    kwargs["api_kwargs"] = api_kw
    return TelegramInlineKeyboardButton(text, *args, **kwargs)


def _reply_button_style(text: str) -> str:
    """Choose a Telegram phone-keyboard button color from its label."""
    label = str(text).casefold()

    danger_terms = (
        "cancel", "delete", "remove", "back", "off", "danger",
        "বাতিল", "মুছুন", "পিছনে",
    )
    success_terms = (
        "add", "approve", "confirm", "yes", "get number", "support",
        "join", "resume", "check", "হ্যাঁ",
    )

    if any(term in label for term in danger_terms):
        return INLINE_DANGER
    if any(term in label for term in success_terms):
        return INLINE_SUCCESS
    return INLINE_PRIMARY


def KeyboardButton(text: str, *args, **kwargs):
    """Create a Telegram phone-keyboard button with automatic style injection via api_kwargs."""
    # Pop legacy direct-kwarg style (not supported by Telegram constructor)
    style = kwargs.pop("style", None)
    icon_emoji_id = kwargs.pop("icon_custom_emoji_id", None)
    # Determine style if not supplied
    if style is None:
        style = _reply_button_style(text)
    # Inject into api_kwargs so Telegram Bot API receives it
    api_kw = dict(kwargs.pop("api_kwargs", None) or {})
    api_kw.setdefault("style", style)
    if icon_emoji_id:
        api_kw["icon_custom_emoji_id"] = icon_emoji_id
    kwargs["api_kwargs"] = api_kw
    return TelegramKeyboardButton(text, *args, **kwargs)


# These IDs are from the custom emoji pack supplied by the bot owner. Telegram
# sends them as the KeyboardButton icon_custom_emoji_id field, so the phone
# keyboard can render the animated icon separately from the bold button text.
PREMIUM_EMOJI_IDS = (
    "6068947681563123753",
    "6069135298619515145",
    "6071037500980207465",
    "6068827654407070288",
    "6069064298515144683",
    "6068876810307772648",
    "6068652724684070452",
    "6068984648346641323",
    "6069038726279864720",
    "6068931596910599428",
    "6068895076803682214",
    "6068617149469957350",
    "6069042858038403362",
    "6068742489500557555",
    "6069103451437015093",
    "6068892693096833337",
    "6069031789907681337",
    "6068793084215303599",
    "6069072506197646391",
    "6068866193148616714",
    "6068741329859387619",
    "6068923758595284398",
    "6069003460303395931",
    "6068607339764653118",
    "6071244411029692470",
    "6068808709306327277",
    "6071131436209937959",
    "6069073197687383247",
    "6068957890700386389",
    "6068808133780709526",
    "6068997211125980742",
    "6068893371701667530",
    "6068960751148604995",
    "6069006870507430323",
    "6069081100427206871",
    "6068625520361217686",
    "6068616324836238233",
    "6068653716821516079",
    "6068796820836851479",
    "6068892242125266188",
    "6068951821911596988",
    "6068709083244927986",
    "6068633264187253513",
    "6068649679552257644",
    "6068737099316600020",
    "6069056120897413110",
    "6068988762925311478",
    "6068886276415694344",
    "6069022310914858057",
    "6068725142127648372",
    "6068944949963923893",
    "6068974954605453642",
    "6068801498056244942",
    "6069147577931013401",
    "6068743984149175274",
    "6068695292104941845",
    "6068703877744565363",
    "6068719846432972154",
    "6069008085983174719",
    "6069134924957359630",
    "6068885563451122195",
    "6070944252945243734",
    "6068727156467309816",
    "6069120846054564114",
    "6068963366783688390",
    "6070915764427168620",
    "6069070212685111179",
    "6071322098398141379",
    "6068984751425854980",
    "6069095879409671989",
    "6068669698394825739",
    "6068709087539896145",
    "6068647824126386686",
    "6069044743529046223",
    "6069061738714636911",
    "6068954660884979175",
    "6069004611354633299",
    "6069080670930476107",
    "6068998276277871051",
    "6068791980408708388",
    "6068954476201384869",
    "6068651693891918945",
    "6071140631734918364",
    "6068772120479932812",
    "6069143549251690102",
    "6069098151447371295",
    "6068712802686607522",
    "6068735273955498815",
    "6069081697427659834",
    "6069153612360066093",
    "6068705166234755288",
    "6069093289544392422",
    "6068874005694127956",
    "6069075504084819577",
    "6068974817166500981",
    "6068707416797618717",
    "6068763603559785080",
    "6070886498520015076",
    "6070925896255021782",
    "6068895407516164537",
    "6068682415792987450",
    "6068852152900525531",
    "6069050752188292003",
    "6069161205862243398",
    "6068743906839765045",
    "6069085116221627866",
    "6068863435779611897",
    "6068905891531332936",
    "6068768181994921479",
    "6068678932574510264",
    "6068894247874993666",
    "6068881255598923347",
    "6068822332942589239",
    "6068681067173257148",
    "6068780628810145632",
    "6068768018786164849",
    "6068738834483388555",
    "6069147281578271023",
    "6069061601275682117",
    "6068793706985562431",
    "6068623673525280366",
    "6068695463903632404",
    "6068988221759432396",
    "6071254598692117816",
    "6068616917541725165",
    "6068881526181863264",
    "6069136299346895222",
    "6069001158200925850",
    "6068924763617632668",
    "6068759755269086959",
    "6068817196161703464",
    "6068832039568681721",
    "6068789777090486404",
    "6069079953670939405",
    "6068659167135015404",
    "6069072364463725579",
    "6069091021801660249",
    "6068929054289960960",
    "6068736626870198042",
    "6069158388363698342",
    "6068648507026185893",
)

# Keep the original emoji as the fallback glyph in clients that do not
# support custom emoji. Telegram uses UTF-16 offsets for MessageEntity.
PREMIUM_EMOJI_TOKENS = tuple(sorted({
    "⬅️", "➡️", "⚙️", "⏱️", "🗺️", "📲", "🔐", "📱", "📢", "👥",
    "👤", "🛡", "🚫", "🗑", "➕", "➖", "✅", "❌", "⚠️", "⏳",
    "🎉", "🎁", "💎", "💰", "💸", "💵", "💳", "📤", "📥", "📊",
    "📋", "📡", "📦", "📞", "🌍", "🌐", "🆘", "🔗", "🔢", "🎨",
    "🛠", "👋", "🔴", "🟢", "✏️", "💡", "⭐", "🔥", "🎯", "🤖", "📌",
    "🔑", "🔒", "📭", "🧹", "🏆", "🥇", "🥈", "🥉", "🏅", "💡", "▶️", "⚡", "💹", "👇",
    "✨", "✉️",
}, key=len, reverse=True))

# Stable emoji → premium ID mapping used by InlineKeyboardButton icon auto-injection.
EMOJI_TO_PREMIUM_ID: dict[str, str] = {
    token: PREMIUM_EMOJI_IDS[i % len(PREMIUM_EMOJI_IDS)]
    for i, token in enumerate(PREMIUM_EMOJI_TOKENS)
}

# User-specified premium emoji IDs for user panel buttons
EMOJI_TO_PREMIUM_ID["📱"] = "6068707416797618717"   # Get Number
EMOJI_TO_PREMIUM_ID["🌐"] = "5447410659077661506"   # Available Country
EMOJI_TO_PREMIUM_ID["📊"] = "6276077203876745608"   # Live Traffic
EMOJI_TO_PREMIUM_ID["💰"] = "6068607339764653118"   # My Balance
EMOJI_TO_PREMIUM_ID["🎁"] = "6068892242125266188"   # Refer & Earn
EMOJI_TO_PREMIUM_ID["🆘"] = "6068648507026185893"   # Support

PER_OTP_PREMIUM_EMOJI_ID = "6068951821911596988"
PER_OTP_TRAILING_EMOJI_ID = "6068772120479932812"
FULL_MESSAGE_BUTTON_EMOJI_ID = "6068974954605453642"
GET_NUMBER_BACK_EMOJI_ID = "6068974817166500981"
LEADERBOARD_PREMIUM_EMOJI_ID = "5316979941181496594"
ASSIGNED_OTP_USD_TO_BDT = Decimal("130")
DEFAULT_REFERRAL_QUALIFICATION_OTPS = 50
DEFAULT_REFERRAL_QUALIFIED_REWARD = 0.10
DEFAULT_REFERRAL_OTP_COMMISSION_RATE = 0.10
USD_TO_BDT = 130
BOARD_CURRENCY_SETTING = "board_currency"

def board_currency() -> str:
    """Return the active display/input currency, defaulting to USDT."""
    configured = str(get_setting(BOARD_CURRENCY_SETTING, "USDT")).upper()
    return "BDT" if configured == "BDT" else "USDT"

def format_currency(value, decimals: int = 2) -> str:
    """Format a stored USDT amount in the currency currently selected on the board."""
    try:
        amount = Decimal(str(value if value is not None else 0))
    except (TypeError, ValueError):
        amount = Decimal("0")
    except InvalidOperation:
        amount = Decimal("0")
    if not amount.is_finite():
        amount = Decimal("0")
    unit = board_currency()
    if unit == "BDT":
        amount *= Decimal(str(USD_TO_BDT))
    symbol = "৳" if unit == "BDT" else "$"
    return f"{symbol}{format(amount, f',.{decimals}f')} {unit}"

def format_currency_price(value) -> str:
    """Format a stored USDT price without exposing float-conversion noise."""
    try:
        amount = Decimal(str(value if value is not None else 0))
    except (InvalidOperation, ValueError, TypeError):
        amount = Decimal("0")
    if not amount.is_finite():
        amount = Decimal("0")
    unit = board_currency()
    if unit == "BDT":
        amount *= Decimal(str(USD_TO_BDT))
        amount = amount.quantize(Decimal("0.01"), rounding=ROUND_HALF_UP)
        rendered = format(amount, ".2f")
    else:
        rendered = format(amount, "f")
        if "." in rendered:
            rendered = rendered.rstrip("0").rstrip(".")
    symbol = "৳" if unit == "BDT" else "$"
    return f"{symbol}{rendered or '0'} {unit}"

def currency_input_to_usdt(value):
    """Convert input currency to USDT, preserving Decimal precision when supplied."""
    if board_currency() == "BDT":
        rate = Decimal(str(USD_TO_BDT)) if isinstance(value, Decimal) else USD_TO_BDT
        return value / rate
    return value

def parse_currency_input(value, *, allow_zero: bool = False) -> float:
    """Parse a user-entered board-currency amount and convert it to stored USDT."""
    try:
        entered = Decimal(str(value).strip())
        if not entered.is_finite() or entered < 0:
            raise ValueError
        if not allow_zero and entered == 0:
            raise ValueError
        converted = currency_input_to_usdt(entered)
        amount = float(converted)
    except (InvalidOperation, TypeError, ValueError, OverflowError) as exc:
        raise ValueError("Invalid currency amount") from exc
    if not math.isfinite(amount) or amount < 0:
        raise ValueError("Invalid currency amount")
    if not allow_zero and amount == 0:
        raise ValueError("Invalid currency amount")
    return amount

def minimum_withdraw_usdt() -> float:
    """Read the configured minimum safely; match the default used by withdrawals."""
    default = 0.50
    try:
        value = Decimal(str(get_setting("min_withdraw", "0.50")))
        if not value.is_finite() or value < 0:
            return default
        amount = float(value)
        return amount if math.isfinite(amount) else default
    except (InvalidOperation, TypeError, ValueError, OverflowError):
        return default


# Custom emoji IDs supplied for referral notifications. Keep these explicit
# instead of letting the generic emoji pack replace them.
REFERRAL_NOTIFICATION_EMOJIS = {
    "bonus": "6069098151447371295",
    "otp_success": "6307589808424228455",
    "amount": "6068607339764653118",
    "balance": "5409048419211682843",
    "more_earn_left": "6068954660884979175",
    "more_earn_right": "6068736626870198042",
}


def _premium_entity_data(text: str):
    """Return custom-emoji entities for all recognized emoji in text."""
    entities = []
    id_index = 0
    for token in PREMIUM_EMOJI_TOKENS:
        start = 0
        while True:
            index = text.find(token, start)
            if index < 0:
                break
            before = text[:index]
            offset = len(before.encode("utf-16-le")) // 2
            length = len(token.encode("utf-16-le")) // 2
            entities.append(MessageEntity(
                type="custom_emoji",
                offset=offset,
                length=length,
                custom_emoji_id=EMOJI_TO_PREMIUM_ID.get(token, PREMIUM_EMOJI_IDS[id_index % len(PREMIUM_EMOJI_IDS)]),
            ))
            id_index += 1
            start = index + len(token)
    return sorted(entities, key=lambda entity: entity.offset)


def _premiumize_message_args(kwargs: dict) -> dict:
    """Add the supplied pack's custom emoji entities without changing text."""
    text = kwargs.get("text")
    if not isinstance(text, str):
        return kwargs

    # Existing HTML messages already use parse_mode. Inject Telegram's
    # official tg-emoji HTML tag so the existing markup remains intact.
    parse_mode = kwargs.get("parse_mode")
    if isinstance(parse_mode, str) and parse_mode.upper() == "HTML":
        # Preserve country names and other content that already carries an
        # exact custom emoji entity. Without this guard, the fallback glyph
        # inside the tag would be replaced with the bot's default emoji pack.
        existing_tags = []

        def protect_existing_tag(match):
            existing_tags.append(match.group(0))
            return f"\x00TG_EMOJI_{len(existing_tags) - 1}\x00"

        text = re.sub(
            r"<tg-emoji\b[^>]*>.*?</tg-emoji>",
            protect_existing_tag,
            text,
            flags=re.DOTALL | re.IGNORECASE,
        )
        for index, token in enumerate(PREMIUM_EMOJI_TOKENS):
            replacement = (
                f'<tg-emoji emoji-id="'
                f'{EMOJI_TO_PREMIUM_ID.get(token, PREMIUM_EMOJI_IDS[index % len(PREMIUM_EMOJI_IDS)])}">'
                f'{token}</tg-emoji>'
            )
            text = text.replace(token, replacement)
        for index, tag in enumerate(existing_tags):
            text = text.replace(f"\x00TG_EMOJI_{index}\x00", tag)
        kwargs["text"] = text
        return kwargs

    # For plain text, entities preserve the original message and its
    # fallback glyph. Do not combine entities with another parse mode.
    if parse_mode is None:
        existing = kwargs.get("entities")
        kwargs["entities"] = list(existing or []) + _premium_entity_data(text)
    return kwargs


USER_PANEL_WELCOME_TEXT = (
    '<tg-emoji emoji-id="5325547803936572038">✨</tg-emoji>'
    "<b>Welcome MD!</b>"
    '<tg-emoji emoji-id="5201873494798776013">✨</tg-emoji>\n\n'
    '<tg-emoji emoji-id="6068931596910599428">🟢</tg-emoji> '
    "<b>Main Menu</b>\n\n"
    '<tg-emoji emoji-id="6068737099316600020">⬇️</tg-emoji> '
    "Please select an option below:"
)


_original_bot_send_message = Bot.send_message
_original_bot_edit_message_text = Bot.edit_message_text


async def _send_message_with_premium_emoji(self, *args, **kwargs):
    if "text" in kwargs:
        kwargs = _premiumize_message_args(dict(kwargs))
    elif len(args) >= 2 and isinstance(args[1], str):
        args = list(args)
        message_kwargs = _premiumize_message_args({"text": args[1]})
        args[1] = message_kwargs["text"]
        if "entities" in message_kwargs:
            kwargs["entities"] = message_kwargs["entities"]
    return await _original_bot_send_message(self, *args, **kwargs)


async def _edit_message_text_with_premium_emoji(self, *args, **kwargs):
    if "text" in kwargs:
        kwargs = _premiumize_message_args(dict(kwargs))
    elif len(args) >= 2 and isinstance(args[1], str):
        args = list(args)
        message_kwargs = _premiumize_message_args({"text": args[1]})
        args[1] = message_kwargs["text"]
        if "entities" in message_kwargs:
            kwargs["entities"] = message_kwargs["entities"]
    return await _original_bot_edit_message_text(self, *args, **kwargs)


Bot.send_message = _send_message_with_premium_emoji
Bot.edit_message_text = _edit_message_text_with_premium_emoji

_original_reply_text = Message.reply_text

async def _reply_with_last_message(self, text, *args, **kwargs):
    send_kwargs = dict(kwargs)
    send_kwargs.setdefault("do_quote", False)
    # Every admin command gets a new message so the conversation remains a
    # complete history instead of replacing the previous response.
    return await _original_reply_text(self, text, *args, **send_kwargs)

Message.reply_text = _reply_with_last_message

async def delete_incoming_message(update: Update):
    """Keep incoming user/admin messages visible; replies provide the result."""
    return

# ─── KEYBOARD LABELS ─────────────────────────────────────────────────────────
BTN_COUNTRY_MGMT  = "Country Management"
BTN_BROADCAST     = "Broadcast"
BTN_USER_MGMT     = "User Management"
BTN_LIVE_TRAFFIC   = "𝗟𝗶𝘃𝗲 𝗧𝗿𝗮𝗳𝗳𝗶𝗰"
BTN_ADD_COUNTRY   = "Add Country"
BTN_ADD_NUMBER    = "Add Number"
BTN_SERVICE       = "Service"
BTN_COUNTRY_PRICE = "Country Price"
BTN_ADD_SERVICE   = "Add Service"
BTN_SERVICE_MANAGE = "Service Management"
BTN_SERVICE_MAP   = "Service Map"
BTN_BACK_COUNTRY_MGMT = "Back to Country Mgmt"
BTN_NUM_PER_USER  = "Number Per User"
BTN_RESET_NUMBER  = "🗑 Reset Number"
BTN_BACK_ADMIN    = "Back to Admin Panel"
BTN_STATS         = "Stats"
BTN_GET_NUMBER    = "𝗚𝗲𝘁 𝗡𝘂𝗺𝗯𝗲𝗿"
BTN_AVAIL         = "𝗔𝘃𝗮𝗶𝗹𝗮𝗯𝗹𝗲 𝗖𝗼𝘂𝗻𝘁𝗿𝘆"
BTN_BALANCE       = "𝗠𝘆 𝗕𝗮𝗹𝗮𝗻𝗰𝗲"
BTN_BOARD_CURRENCY = "Board Currency"
BTN_LEADERBOARD   = "Leaderboard"
BTN_SETTINGS      = "⚙️ Settings"
LEADERBOARD_MIN_ORDERS = 5
WEEKLY_LEADERBOARD_LAST_END_KEY = "weekly_leaderboard_last_report_end"
BTN_WITHDRAW      = "𝗪𝗶𝘁𝗵𝗱𝗿𝗮𝘄"

# User Management sub-panel
BTN_USER_LIST       = "User List"
BTN_WITHDRAWALS     = "Withdrawal Requests"
BTN_ADD_ADMIN       = "Add Admin"
BTN_REMOVE_ADMIN    = "Remove Admin"
BTN_ADD_BALANCE     = "Add Balance"
BTN_REFERRAL_REWARD    = "Referral Reward"
BTN_WITHDRAW_TOGGLE    = "Withdraw ON/OFF"
BTN_MIN_WITHDRAW       = "Min Withdraw"
BTN_NUMBER_VALID_TIME  = "Number Valid Time"
BTN_WITHDRAW_METHODS   = "Withdraw Methods"
BTN_MY_REFERRAL     = "𝗠𝘆 𝗥𝗲𝗳𝗲𝗿𝗿𝗮𝗹"
BTN_REFER_EARN      = "𝗥𝗲𝗳𝗲𝗿 & 𝗘𝗮𝗿𝗻"
GET_NUMBER_SERVICE_PROMPT = (
    "📱 <b>Get Number</b>\n\n"
    "Select a service:\n"
    "<i>Choose any service to get started.</i>"
)
BTN_BACK_USER_MGMT  = "Back to User Mgmt"
BTN_SUPPORT         = "𝗦𝘂𝗽𝗽𝗼𝗿𝘁"
BTN_SUPPORT_LINK    = "Support Link"
BTN_OTP_LINK         = "OTP Link"
BTN_GET_NUMBER_LINK  = "Get Number Link"
BTN_CHANNEL_LINK     = "Channel Link"
BTN_OTP_GROUP_CHAT   = "OTP Group Chat"
BTN_OTP_GROUP_PREFIX = "OTP Group Prefix"
BTN_OTP_DEMO_SEND    = "Send Demo OTP"
BTN_FORCE_JOIN       = "Force Join Channels"
BTN_LINKS            = "Links"
# Panel management
BTN_PANELS        = "Panels"
BTN_LAST_MSGS     = "Last Message"
BTN_PANEL_ADD     = "Add Panel"
BTN_SCAN_INTERVAL = "Scan Interval"
BTN_BACK_PANELS   = "Back to Panels"

# Animated custom emoji shown before each user-panel phone-keyboard label.
USER_PANEL_BUTTON_EMOJI_IDS = {
    BTN_GET_NUMBER: "6068707416797618717",
    BTN_AVAIL: "5447410659077661506",
    BTN_LIVE_TRAFFIC: "6276077203876745608",
    BTN_BALANCE: "6068607339764653118",
    BTN_REFER_EARN: "6069098151447371295",
    BTN_SUPPORT: "6068648507026185893",
    BTN_LEADERBOARD: LEADERBOARD_PREMIUM_EMOJI_ID,
}


def user_panel_button(default_label: str):
    """Build a bold user-menu phone button with its animated custom icon."""
    return KeyboardButton(
        button_label(default_label),
        icon_custom_emoji_id=USER_PANEL_BUTTON_EMOJI_IDS[default_label],
    )

# ─── CUSTOMIZABLE BUTTONS LIST ────────────────────────────────────────────────
# List of (default_label, description) tuples for all keyboard buttons that
# admins can rename.  The second element is a human-readable hint shown in the
# settings panel; it is not used programmatically.
CUSTOMIZABLE_BUTTONS = [
    (BTN_COUNTRY_MGMT,      "Country Management"),
    (BTN_BROADCAST,         "Broadcast"),
    (BTN_USER_MGMT,         "User Management"),
    (BTN_LIVE_TRAFFIC,      "Live Traffic"),
    (BTN_ADD_COUNTRY,       "Add Country"),
    (BTN_ADD_NUMBER,        "Add Number"),
    (BTN_SERVICE,           "Service"),
    (BTN_COUNTRY_PRICE,     "Country Price"),
    (BTN_ADD_SERVICE,       "Add Service"),
    (BTN_SERVICE_MANAGE,    "Service Management"),
    (BTN_SERVICE_MAP,       "Service Map"),
    (BTN_BACK_COUNTRY_MGMT, "Back to Country Mgmt"),
    (BTN_NUM_PER_USER,      "Number Per User"),
    (BTN_RESET_NUMBER,      "Reset Number"),
    (BTN_BACK_ADMIN,        "Back to Admin Panel"),
    (BTN_STATS,             "Stats"),
    (BTN_GET_NUMBER,        "Get Number"),
    (BTN_AVAIL,             "Available Country"),
    (BTN_BALANCE,           "My Balance"),
    (BTN_BOARD_CURRENCY,    "Board Currency"),
    (BTN_LEADERBOARD,       "Leaderboard"),
    (BTN_SETTINGS,          "Settings"),
    (BTN_WITHDRAW,          "Withdraw"),
    (BTN_USER_LIST,         "User List"),
    (BTN_WITHDRAWALS,       "Withdrawal Requests"),
    (BTN_ADD_ADMIN,         "Add Admin"),
    (BTN_REMOVE_ADMIN,      "Remove Admin"),
    (BTN_ADD_BALANCE,       "Add Balance"),
    (BTN_REFERRAL_REWARD,   "Referral Reward"),
    (BTN_WITHDRAW_TOGGLE,   "Withdraw ON/OFF"),
    (BTN_MIN_WITHDRAW,      "Min Withdraw"),
    (BTN_NUMBER_VALID_TIME, "Number Valid Time"),
    (BTN_WITHDRAW_METHODS,  "Withdraw Methods"),
    (BTN_MY_REFERRAL,       "My Referral"),
    (BTN_REFER_EARN,        "Refer & Earn"),
    (BTN_BACK_USER_MGMT,    "Back to User Mgmt"),
    (BTN_SUPPORT,           "Support"),
    (BTN_SUPPORT_LINK,      "Support Link"),
    (BTN_OTP_LINK,          "OTP Link"),
    (BTN_GET_NUMBER_LINK,   "Get Number Link"),
    (BTN_CHANNEL_LINK,      "Channel Link"),
    (BTN_FORCE_JOIN,        "Force Join Channels"),
    (BTN_LINKS,             "Links"),
    (BTN_PANELS,            "Panels"),
    (BTN_LAST_MSGS,         "Last Message"),
    (BTN_PANEL_ADD,         "Add Panel"),
    (BTN_SCAN_INTERVAL,     "Scan Interval"),
    (BTN_BACK_PANELS,       "Back to Panels"),
]

# ─── DATABASE ─────────────────────────────────────────────────────────────────
_db_lock = threading.RLock()
_memory_conn = None
_JSON_VERSION = 1
_JSON_FLUSH_INTERVAL = 0.75
_json_flush_condition = threading.Condition()
_json_dirty = False
_json_last_dirty_at = 0.0
_json_writer_thread = None
_json_writer_stop = False
_JSON_TABLES = (
    "users",
    "admins",
    "withdrawal_requests",
    "countries",
    "numbers",
    "services",
    "service_countries",
    "settings",
    "panels",
    "traffic_events",
    "leaderboard_events",
    "leaderboard_weekly_counts",
)
_JSON_NON_NUMBER_TABLES = tuple(table for table in _JSON_TABLES if table != "numbers")


def _create_schema(conn):
    conn.executescript("""
        CREATE TABLE IF NOT EXISTS users (
            uid        INTEGER PRIMARY KEY,
            username   TEXT,
            first_name TEXT,
            balance    REAL DEFAULT 0.0,
            banned     INTEGER DEFAULT 0,
            last_number_request_at DATETIME DEFAULT NULL,
            joined_at  DATETIME DEFAULT CURRENT_TIMESTAMP
        );
        CREATE TABLE IF NOT EXISTS admins (
            uid      INTEGER PRIMARY KEY,
            added_by INTEGER,
            added_at DATETIME DEFAULT CURRENT_TIMESTAMP
        );
        CREATE TABLE IF NOT EXISTS withdrawal_requests (
            id         INTEGER PRIMARY KEY AUTOINCREMENT,
            uid        INTEGER REFERENCES users(uid),
            amount     REAL NOT NULL,
            status     TEXT DEFAULT 'pending',
            created_at DATETIME DEFAULT CURRENT_TIMESTAMP
        );
        CREATE TABLE IF NOT EXISTS countries (
            id             INTEGER PRIMARY KEY AUTOINCREMENT,
            name           TEXT UNIQUE NOT NULL,
            price          REAL DEFAULT 0.0,
            active         INTEGER DEFAULT 1,
            emoji_entities TEXT DEFAULT NULL
        );
        CREATE TABLE IF NOT EXISTS numbers (
            id         INTEGER PRIMARY KEY AUTOINCREMENT,
            country_id INTEGER REFERENCES countries(id),
            number     TEXT NOT NULL,
            used       INTEGER DEFAULT 0,
            added_at   DATETIME DEFAULT CURRENT_TIMESTAMP
        );
        CREATE TABLE IF NOT EXISTS services (
            id             INTEGER PRIMARY KEY AUTOINCREMENT,
            name           TEXT UNIQUE NOT NULL,
            active         INTEGER DEFAULT 1,
            emoji_entities TEXT DEFAULT NULL
        );
        CREATE TABLE IF NOT EXISTS service_countries (
            id         INTEGER PRIMARY KEY AUTOINCREMENT,
            service_id INTEGER REFERENCES services(id),
            country_id INTEGER REFERENCES countries(id),
            amount     REAL DEFAULT 0.0,
            UNIQUE(service_id, country_id)
        );
        CREATE TABLE IF NOT EXISTS settings (
            key   TEXT PRIMARY KEY,
            value TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS panels (
            id                INTEGER PRIMARY KEY AUTOINCREMENT,
            name              TEXT NOT NULL,
            login_url         TEXT NOT NULL,
            username          TEXT NOT NULL,
            password          TEXT NOT NULL,
            stats_url         TEXT NOT NULL,
            cookies           TEXT DEFAULT NULL,
            browser_state    TEXT DEFAULT NULL,
            last_seen_ts      TEXT DEFAULT NULL,
            last_seen_key     TEXT DEFAULT NULL,
            active            INTEGER DEFAULT 1,
            number_col_name   TEXT DEFAULT 'Number',
            number_col_idx    INTEGER DEFAULT 2,
            sender_col_name   TEXT DEFAULT 'CLI',
            sender_col_idx    INTEGER DEFAULT 3,
            message_col_name  TEXT DEFAULT 'Message',
            message_col_idx   INTEGER DEFAULT 5,
            api_method        TEXT DEFAULT 'GET',
            api_auth_type     TEXT DEFAULT 'auto',
            api_auth_name     TEXT DEFAULT NULL,
            api_rows_path     TEXT DEFAULT NULL,
            api_number_field  TEXT DEFAULT NULL,
            api_sender_field  TEXT DEFAULT NULL,
            api_message_field TEXT DEFAULT NULL,
            api_timestamp_field TEXT DEFAULT NULL,
            api_range_field   TEXT DEFAULT NULL,
            api_last_error    TEXT DEFAULT NULL,
            last_sms_json     TEXT DEFAULT NULL,
            added_at          DATETIME DEFAULT CURRENT_TIMESTAMP
        );
        CREATE TABLE IF NOT EXISTS traffic_events (
            id                     INTEGER PRIMARY KEY AUTOINCREMENT,
            event_key              TEXT UNIQUE NOT NULL,
            occurred_at            DATETIME NOT NULL,
            service_name           TEXT NOT NULL,
            service_emoji_entities TEXT DEFAULT NULL,
            iso2                   TEXT DEFAULT NULL,
            country_name           TEXT DEFAULT NULL,
            country_emoji_entities TEXT DEFAULT NULL
        );
        CREATE TABLE IF NOT EXISTS leaderboard_events (
            id          INTEGER PRIMARY KEY AUTOINCREMENT,
            uid         INTEGER NOT NULL,
            event_type  TEXT NOT NULL,
            related_uid INTEGER DEFAULT NULL,
            occurred_at DATETIME NOT NULL
        );
        CREATE TABLE IF NOT EXISTS leaderboard_weekly_counts (
            week_start DATETIME NOT NULL,
            uid        INTEGER NOT NULL,
            otp_count  INTEGER NOT NULL DEFAULT 0,
            PRIMARY KEY (week_start, uid)
        );
    """)
    # Apply the same forward-compatible columns used by the original SQLite
    # implementation before importing JSON data.
    for col_sql in [
        "ALTER TABLE countries ADD COLUMN price REAL DEFAULT 0.0",
        "ALTER TABLE countries ADD COLUMN emoji_entities TEXT DEFAULT NULL",
        "ALTER TABLE users ADD COLUMN banned INTEGER DEFAULT 0",
        "ALTER TABLE users ADD COLUMN referred_by INTEGER DEFAULT NULL",
        "ALTER TABLE users ADD COLUMN referral_count INTEGER DEFAULT 0",
        "ALTER TABLE users ADD COLUMN otp_count INTEGER DEFAULT 0",
        "ALTER TABLE users ADD COLUMN referral_qualified INTEGER DEFAULT 0",
        "ALTER TABLE users ADD COLUMN qualified_referrals INTEGER DEFAULT 0",
        "ALTER TABLE users ADD COLUMN referral_earnings REAL DEFAULT 0.0",
        "ALTER TABLE users ADD COLUMN referral_earnings_generated REAL DEFAULT 0.0",
        "ALTER TABLE users ADD COLUMN last_number_request_at DATETIME DEFAULT NULL",
        "ALTER TABLE withdrawal_requests ADD COLUMN wallet TEXT",
        "ALTER TABLE numbers ADD COLUMN assigned_uid INTEGER DEFAULT NULL",
        "ALTER TABLE panels ADD COLUMN number_col_name TEXT DEFAULT 'Number'",
        "ALTER TABLE panels ADD COLUMN number_col_idx INTEGER DEFAULT 2",
        "ALTER TABLE panels ADD COLUMN sender_col_name TEXT DEFAULT 'CLI'",
        "ALTER TABLE panels ADD COLUMN sender_col_idx INTEGER DEFAULT 3",
        "ALTER TABLE panels ADD COLUMN message_col_name TEXT DEFAULT 'Message'",
        "ALTER TABLE panels ADD COLUMN message_col_idx INTEGER DEFAULT 5",
        "ALTER TABLE panels ADD COLUMN scan_interval INTEGER DEFAULT 60",
        "ALTER TABLE panels ADD COLUMN last_scanned_at TEXT DEFAULT NULL",
        "ALTER TABLE panels ADD COLUMN last_seen_key TEXT DEFAULT NULL",
        "ALTER TABLE panels ADD COLUMN panel_type TEXT DEFAULT 'captcha'",
        "ALTER TABLE panels ADD COLUMN api_key TEXT DEFAULT NULL",
        "ALTER TABLE panels ADD COLUMN api_method TEXT DEFAULT 'GET'",
        "ALTER TABLE panels ADD COLUMN api_auth_type TEXT DEFAULT 'auto'",
        "ALTER TABLE panels ADD COLUMN api_auth_name TEXT DEFAULT NULL",
        "ALTER TABLE panels ADD COLUMN api_rows_path TEXT DEFAULT NULL",
        "ALTER TABLE panels ADD COLUMN api_number_field TEXT DEFAULT NULL",
        "ALTER TABLE panels ADD COLUMN api_sender_field TEXT DEFAULT NULL",
        "ALTER TABLE panels ADD COLUMN api_message_field TEXT DEFAULT NULL",
        "ALTER TABLE panels ADD COLUMN api_timestamp_field TEXT DEFAULT NULL",
        "ALTER TABLE panels ADD COLUMN api_range_field TEXT DEFAULT NULL",
        "ALTER TABLE panels ADD COLUMN api_last_error TEXT DEFAULT NULL",
        "ALTER TABLE panels ADD COLUMN last_sms_json TEXT DEFAULT NULL",
        "ALTER TABLE panels ADD COLUMN browser_state TEXT DEFAULT NULL",
        "ALTER TABLE services ADD COLUMN emoji_entities TEXT DEFAULT NULL",
        "ALTER TABLE numbers ADD COLUMN assigned_at DATETIME DEFAULT NULL",
    ]:
        try:
            conn.execute(col_sql)
        except sqlite3.OperationalError as exc:
            if "duplicate column name" not in str(exc).lower():
                raise
    conn.executescript("""
        CREATE INDEX IF NOT EXISTS idx_users_referred_by
            ON users(referred_by);
        CREATE INDEX IF NOT EXISTS idx_numbers_country_used
            ON numbers(country_id, used);
        CREATE INDEX IF NOT EXISTS idx_numbers_number
            ON numbers(number);
        CREATE INDEX IF NOT EXISTS idx_numbers_assigned_uid
            ON numbers(assigned_uid);
        CREATE INDEX IF NOT EXISTS idx_panels_active
            ON panels(active);
        CREATE INDEX IF NOT EXISTS idx_withdrawals_status
            ON withdrawal_requests(status);
        CREATE INDEX IF NOT EXISTS idx_traffic_events_occurred_at
            ON traffic_events(occurred_at);
        CREATE INDEX IF NOT EXISTS idx_leaderboard_events_week
            ON leaderboard_events(event_type, occurred_at, uid);
        CREATE INDEX IF NOT EXISTS idx_leaderboard_weekly_counts
            ON leaderboard_weekly_counts(week_start, otp_count DESC);
    """)


def _read_json_file(path):
    if not os.path.exists(path):
        return None
    try:
        with open(path, "r", encoding="utf-8") as json_file:
            return json.load(json_file)
    except (OSError, json.JSONDecodeError) as exc:
        raise RuntimeError(f"Cannot read JSON database file {path}: {exc}") from exc


def _read_legacy_sqlite_state():
    if not os.path.exists(DB_FILE):
        return {}
    legacy_conn = sqlite3.connect(DB_FILE)
    legacy_conn.row_factory = sqlite3.Row
    try:
        tables = {
            row[0]
            for row in legacy_conn.execute(
                "SELECT name FROM sqlite_master "
                "WHERE type='table' AND name NOT LIKE 'sqlite_%'"
            ).fetchall()
        }
        return {
            table: [
                dict(row)
                for row in legacy_conn.execute(
                    f'SELECT * FROM "{table}"'
                ).fetchall()
            ]
            for table in _JSON_TABLES
            if table in tables
        }
    finally:
        legacy_conn.close()


def _load_json_state(conn):
    users_payload = _read_json_file(USERS_FILE)
    numbers_payload = _read_json_file(NUMBERS_FILE)
    legacy_state = (
        _read_legacy_sqlite_state()
        if users_payload is None and numbers_payload is None
        else {}
    )

    if users_payload is None:
        user_tables = {
            table: legacy_state.get(table, [])
            for table in _JSON_NON_NUMBER_TABLES
        }
    elif isinstance(users_payload, list):
        # Backward compatibility with the original upload format:
        # user.json was a plain array of user rows.
        user_tables = {"users": users_payload}
    elif isinstance(users_payload, dict):
        user_tables = users_payload.get("tables", users_payload)
        if not isinstance(user_tables, dict):
            raise RuntimeError(f"Invalid tables object in {USERS_FILE}")
    else:
        raise RuntimeError(f"Invalid JSON root in {USERS_FILE}")

    if numbers_payload is None:
        number_rows = legacy_state.get("numbers", [])
    elif isinstance(numbers_payload, list):
        # Backward compatibility with the original upload format:
        # number.json was a plain array of number rows.
        number_rows = numbers_payload
    elif isinstance(numbers_payload, dict):
        number_rows = numbers_payload.get("numbers", [])
        if not isinstance(number_rows, list):
            raise RuntimeError(f"Invalid numbers array in {NUMBERS_FILE}")
    else:
        raise RuntimeError(f"Invalid JSON root in {NUMBERS_FILE}")

    ordered_tables = (
        "users",
        "admins",
        "countries",
        "services",
        "service_countries",
        "withdrawal_requests",
        "settings",
        "panels",
        "traffic_events",
        "leaderboard_events",
        "leaderboard_weekly_counts",
    )
    for table in ordered_tables:
        _insert_json_rows(conn, table, user_tables.get(table, []))
    _insert_json_rows(conn, "numbers", number_rows)


def _insert_json_rows(conn, table, rows):
    if not isinstance(rows, list):
        raise RuntimeError(f"Invalid row list for table {table}")
    valid_columns = {
        row[1]
        for row in conn.execute(f'PRAGMA table_info("{table}")').fetchall()
    }
    for row in rows:
        if not isinstance(row, dict):
            raise RuntimeError(f"Invalid row in JSON table {table}")
        columns = [column for column in row if column in valid_columns]
        if not columns:
            continue
        quoted_columns = ", ".join(f'"{column}"' for column in columns)
        placeholders = ", ".join("?" for _ in columns)
        conn.execute(
            f'INSERT OR REPLACE INTO "{table}" ({quoted_columns}) '
            f"VALUES ({placeholders})",
            tuple(row[column] for column in columns),
        )


def _snapshot_rows(conn, table):
    return [dict(row) for row in conn.execute(f'SELECT * FROM "{table}"').fetchall()]


def _json_default(value):
    if isinstance(value, (bytes, bytearray)):
        return value.decode("utf-8", errors="replace")
    return str(value)


def _write_json_pair(users_payload, numbers_payload):
    os.makedirs(JSON_DB_DIR, exist_ok=True)
    temp_paths = []
    try:
        for path, payload in (
            (USERS_FILE, users_payload),
            (NUMBERS_FILE, numbers_payload),
        ):
            directory = os.path.dirname(os.path.abspath(path))
            os.makedirs(directory, exist_ok=True)
            fd, temp_path = tempfile.mkstemp(
                prefix=f".{os.path.basename(path)}.",
                suffix=".tmp",
                dir=directory,
            )
            temp_paths.append((temp_path, path))
            with os.fdopen(fd, "w", encoding="utf-8") as json_file:
                json.dump(
                    payload,
                    json_file,
                    ensure_ascii=False,
                    indent=2,
                    default=_json_default,
                )
                json_file.write("\n")
                json_file.flush()
                os.fsync(json_file.fileno())
        for temp_path, path in temp_paths:
            os.replace(temp_path, path)
    finally:
        for temp_path, _ in temp_paths:
            try:
                os.remove(temp_path)
            except FileNotFoundError:
                pass


def _persist_json_state(conn):
    users_payload, numbers_payload = _database_json_payloads(conn)
    _write_json_pair(users_payload, numbers_payload)


def _mark_json_dirty():
    """Schedule one coalesced JSON flush instead of blocking each database write."""
    global _json_dirty, _json_last_dirty_at
    with _json_flush_condition:
        _json_dirty = True
        _json_last_dirty_at = time.monotonic()
        _json_flush_condition.notify()


def _flush_json_state_now():
    """Snapshot memory and synchronously flush both JSON files."""
    global _json_dirty
    with _db_lock:
        if _memory_conn is None:
            return
        users_payload, numbers_payload = _database_json_payloads(_memory_conn)
    _write_json_pair(users_payload, numbers_payload)
    with _json_flush_condition:
        _json_dirty = False


def _json_writer_loop():
    """Coalesce bursts of writes and persist them off the Telegram event loop."""
    global _json_dirty
    while True:
        with _json_flush_condition:
            while not _json_dirty and not _json_writer_stop:
                _json_flush_condition.wait()
            if _json_writer_stop:
                return
            remaining = (
                _JSON_FLUSH_INTERVAL
                - (time.monotonic() - _json_last_dirty_at)
            )
            if remaining > 0:
                _json_flush_condition.wait(timeout=remaining)
                continue
            _json_dirty = False

        try:
            with _db_lock:
                if _memory_conn is None:
                    continue
                users_payload, numbers_payload = _database_json_payloads(_memory_conn)
            _write_json_pair(users_payload, numbers_payload)
            try:
                from firebase_sync import sync_database_to_firebase
                sync_database_to_firebase(users_payload, numbers_payload)
            except Exception as fe:
                logger.debug(f"Firebase sync notice: {fe}")
        except Exception:
            logger.exception("Background JSON database flush failed")
            _mark_json_dirty()


def _start_json_writer():
    global _json_writer_thread
    if _json_writer_thread and _json_writer_thread.is_alive():
        return
    _json_writer_thread = threading.Thread(
        target=_json_writer_loop,
        name="json-database-writer",
        daemon=True,
    )
    _json_writer_thread.start()


def _shutdown_json_writer():
    global _json_writer_stop
    with _json_flush_condition:
        _json_writer_stop = True
        _json_flush_condition.notify_all()
    if _json_writer_thread and _json_writer_thread.is_alive():
        _json_writer_thread.join(timeout=3)
    try:
        _flush_json_state_now()
    except Exception:
        logger.exception("Final JSON database flush failed")


atexit.register(_shutdown_json_writer)


def _database_json_payloads(conn):
    users_payload = {
        "version": _JSON_VERSION,
        "database": "users",
        "tables": {
            table: _snapshot_rows(conn, table)
            for table in _JSON_NON_NUMBER_TABLES
        },
    }
    numbers_payload = {
        "version": _JSON_VERSION,
        "database": "numbers",
        "numbers": _snapshot_rows(conn, "numbers"),
    }
    return users_payload, numbers_payload


def _json_payload_bytes(payload):
    return json.dumps(
        payload,
        ensure_ascii=False,
        indent=2,
        default=_json_default,
    ).encode("utf-8")


def build_json_database_files():
    """Return a consistent in-memory snapshot of both downloadable JSON files."""
    with _db_lock:
        users_payload, numbers_payload = _database_json_payloads(get_db())
        return {
            "users.json": _json_payload_bytes(users_payload),
            "numbers.json": _json_payload_bytes(numbers_payload),
        }


def get_db():
    if _memory_conn is None:
        init_db()
    return _memory_conn


def build_database_backup():
    """Create a consistent ZIP backup of the two active JSON database files."""
    with _db_lock:
        users_payload, numbers_payload = _database_json_payloads(get_db())
        archive = io.BytesIO()
        with zipfile.ZipFile(archive, "w", zipfile.ZIP_DEFLATED) as zf:
            zf.writestr("users.json", _json_payload_bytes(users_payload))
            zf.writestr("numbers.json", _json_payload_bytes(numbers_payload))
        return archive.getvalue()


def init_db():
    global _memory_conn
    with _db_lock:
        if _memory_conn is not None:
            return
        conn = sqlite3.connect(":memory:", check_same_thread=False)
        conn.row_factory = sqlite3.Row
        _create_schema(conn)
        _load_json_state(conn)
        repair_number_inventory(conn)
        # Auto-clean legacy channels/links (e.g. A_TOOLSx2, sxsupportgroup) and enforce official links
        conn.execute("UPDATE settings SET value='https://t.me/EarnAirdropX' WHERE key IN ('channel_link', 'support_link') AND (value LIKE '%A_TOOLSx2%' OR value LIKE '%sxsupportgroup%' OR value IS NULL OR value='')")
        conn.execute("UPDATE settings SET value='https://t.me/OtpZoneAZ_Bot' WHERE key IN ('otp_link', 'get_number_link') AND (value LIKE '%sxotp99%' OR value IS NULL OR value='')")
        conn.execute("UPDATE settings SET value='𝗢𝗧𝗣 𝗭𝗢𝗡𝗘' WHERE key='otp_group_prefix' AND (value LIKE '%confirmsms%' OR value LIKE '%ConfirmSMS%' OR value IS NULL OR value='')")
        # Keep only the supported panel modes. This also cleans up any
        # legacy panel rows created by older builds before the data is served
        # to the admin panel.
        conn.execute(
            "DELETE FROM panels "
            "WHERE panel_type IS NOT NULL "
            "AND lower(replace(trim(panel_type), '-', '_')) "
            "NOT IN ('captcha', 'non_captcha', 'api')"
        )
        conn.commit()
        _memory_conn = conn
        _persist_json_state(conn)
        _start_json_writer()
        try:
            from firebase_sync import init_firebase
            init_firebase()
        except Exception as fe:
            logger.debug(f"Firebase init notice: {fe}")


def db_query(sql, params=()):
    with _db_lock:
        conn = get_db()
        return conn.execute(sql, params).fetchall()


def db_execute(sql, params=()):
    with _db_lock:
        conn = get_db()
        cursor = conn.execute(sql, params)
        conn.commit()
        _mark_json_dirty()
        return cursor.rowcount


def db_insert_many(sql, data_list):
    with _db_lock:
        conn = get_db()
        count = 0
        try:
            for params in data_list:
                cursor = conn.execute(sql, params)
                if cursor.rowcount > 0:
                    count += cursor.rowcount
            conn.commit()
            _mark_json_dirty()
            return count
        except Exception:
            conn.rollback()
            raise


def create_withdrawal_request(uid: int, amount: float, wallet: str):
    """Debit and create a withdrawal request in one atomic transaction."""
    with _db_lock:
        conn = get_db()
        try:
            cursor = conn.execute(
                "UPDATE users SET balance=balance-? "
                "WHERE uid=? AND balance>=?",
                (amount, uid, amount),
            )
            if cursor.rowcount != 1:
                conn.rollback()
                return None
            cursor = conn.execute(
                "INSERT INTO withdrawal_requests (uid, amount, wallet) "
                "VALUES (?, ?, ?)",
                (uid, amount, wallet),
            )
            request_id = cursor.lastrowid
            conn.commit()
            _mark_json_dirty()
            return request_id
        except Exception:
            conn.rollback()
            raise


def reject_withdrawal_request(request_id: int):
    """Reject a pending withdrawal and refund its debited balance atomically."""
    with _db_lock:
        conn = get_db()
        try:
            row = conn.execute(
                "SELECT uid, amount, wallet, status "
                "FROM withdrawal_requests WHERE id=?",
                (request_id,),
            ).fetchone()
            if row is None or row["status"] != "pending":
                conn.rollback()
                return None

            updated = conn.execute(
                "UPDATE withdrawal_requests SET status='rejected' "
                "WHERE id=? AND status='pending'",
                (request_id,),
            )
            if updated.rowcount != 1:
                conn.rollback()
                return None

            refunded = conn.execute(
                "UPDATE users SET balance=balance+? WHERE uid=?",
                (row["amount"], row["uid"]),
            )
            if refunded.rowcount != 1:
                conn.rollback()
                raise RuntimeError(
                    f"Cannot refund withdrawal {request_id}: user {row['uid']} not found"
                )

            conn.commit()
            _mark_json_dirty()
            return row
        except Exception:
            conn.rollback()
            raise


def adjust_user_balance(uid: int, delta: float):
    """Apply an admin balance adjustment without allowing a negative result."""
    if not math.isfinite(delta):
        return None
    with _db_lock:
        conn = get_db()
        try:
            cursor = conn.execute(
                "UPDATE users SET balance=balance+? "
                "WHERE uid=? AND balance+? >= 0",
                (delta, uid, delta),
            )
            if cursor.rowcount != 1:
                conn.rollback()
                return None
            row = conn.execute(
                "SELECT balance FROM users WHERE uid=?", (uid,)
            ).fetchone()
            conn.commit()
            _mark_json_dirty()
            return float(row["balance"]) if row else None
        except Exception:
            conn.rollback()
            raise


def claim_available_numbers(
    uid: int,
    country_id: int,
    count: int,
    *,
    bypass_cooldown: bool = False,
):
    """Atomically reserve available numbers so concurrent users cannot collide."""
    count = min(
        MAX_NUMBERS_PER_USER_REQUEST,
        max(1, int(count)),
    )
    with _db_lock:
        conn = get_db()
        cooldown = conn.execute(
            "SELECT last_number_request_at FROM users WHERE uid=?",
            (uid,),
        ).fetchone()
        if not bypass_cooldown and cooldown and cooldown["last_number_request_at"]:
            elapsed = conn.execute(
                "SELECT (julianday('now') - julianday(?)) * 86400",
                (cooldown["last_number_request_at"],),
            ).fetchone()[0]
            if elapsed is not None and elapsed < NUMBER_REQUEST_COOLDOWN_SECONDS:
                return []
        rows = conn.execute(
            "SELECT id, number FROM numbers "
            "WHERE country_id=? AND used=0 ORDER BY id LIMIT ?",
            (country_id, count),
        ).fetchall()
        if not rows:
            return []

        ids = [row["id"] for row in rows]
        placeholders = ", ".join("?" for _ in ids)
        assigned_at = _dt.datetime.now(_dt.timezone.utc).replace(
            microsecond=0
        ).strftime("%Y-%m-%d %H:%M:%S")
        cursor = conn.execute(
            f"UPDATE numbers SET used=1, assigned_uid=?, assigned_at=? "
            f"WHERE used=0 AND id IN ({placeholders})",
            (uid, assigned_at, *ids),
        )
        if cursor.rowcount != len(ids):
            conn.rollback()
            return []
        conn.execute(
            "UPDATE users SET last_number_request_at=? WHERE uid=?",
            (assigned_at, uid),
        )
        conn.commit()
        _mark_json_dirty()
        return rows

def register_user(user):
    db_execute(
        "INSERT OR IGNORE INTO users (uid, username, first_name) VALUES (?, ?, ?)",
        (user.id, user.username, user.first_name)
    )
    # Keep profile data current when Telegram user details change.
    db_execute(
        "UPDATE users SET username=?, first_name=? WHERE uid=?",
        (user.username, user.first_name, user.id),
    )

def is_admin(uid):
    if uid in SUPER_ADMINS:
        return True
    rows = db_query("SELECT uid FROM admins WHERE uid=?", (uid,))
    return len(rows) > 0

def is_banned(uid):
    rows = db_query("SELECT banned FROM users WHERE uid=?", (uid,))
    return rows and rows[0]["banned"] == 1

def get_setting(key: str, default=None):
    rows = db_query("SELECT value FROM settings WHERE key=?", (key,))
    return rows[0]["value"] if rows else default


def _normalize_otp_group_id(value):
    """Return a supported Telegram group identifier or None."""
    value = str(value or "").strip()
    if value.startswith("@") or value.lstrip("-").isdigit():
        return value
    return None


def get_otp_group_ids():
    """Return configured OTP groups, migrating the legacy single-group setting."""
    raw = get_setting("otp_group_ids", None)
    values = []
    if raw:
        try:
            parsed = json.loads(raw)
        except (TypeError, ValueError):
            parsed = raw
        if isinstance(parsed, str):
            parsed = [parsed]
        if isinstance(parsed, list):
            values = parsed

    # Keep existing deployments working when they only have otp_group_id.
    if not values:
        legacy = get_setting("otp_group_id", "")
        if legacy:
            values = [legacy]

    normalized = []
    seen = set()
    for value in values:
        group_id = _normalize_otp_group_id(value)
        if group_id and group_id not in seen:
            normalized.append(group_id)
            seen.add(group_id)
        if len(normalized) >= MAX_OTP_GROUPS:
            break
    return normalized


def set_otp_group_ids(group_ids):
    """Persist the multi-group setting and keep the legacy key in sync."""
    normalized = []
    seen = set()
    for value in group_ids:
        group_id = _normalize_otp_group_id(value)
        if group_id and group_id not in seen:
            normalized.append(group_id)
            seen.add(group_id)
        if len(normalized) >= MAX_OTP_GROUPS:
            break
    set_setting("otp_group_ids", json.dumps(normalized, ensure_ascii=False))
    # This keeps older backups/tools readable without making it the source of
    # truth for the new multi-group delivery path.
    set_setting("otp_group_id", normalized[0] if normalized else "")
    return normalized


def otp_group_settings_text(extra_message=""):
    """Build the admin-facing multi-group configuration prompt."""
    group_ids = get_otp_group_ids()
    if group_ids:
        current = "\n".join(
            f"  {index}. <code>{_html.escape(group_id)}</code>"
            for index, group_id in enumerate(group_ids, start=1)
        )
    else:
        current = "<i>Not set</i>"
    prefix = f"{extra_message}\n\n" if extra_message else ""
    return (
        f"{prefix}📢 <b>OTP Group Chat</b>\n\n"
        f"<b>Current groups ({len(group_ids)}):</b>\n{current}\n\n"
        "নতুন group যোগ করতে একটি বা একাধিক Chat ID/username দিন "
        "(কমা বা আলাদা লাইনে):\n"
        "  • গ্রুপ ID: <code>-1001234567890</code>\n"
        "  • Username: <code>@mygroupname</code>\n\n"
        "একটি group সরাতে লিখুন: <code>remove -1001234567890</code>\n"
        "সব group মুছতে লিখুন: <code>clear</code>\n\n"
        "💡 বটকে প্রতিটি group-এর <b>Admin</b> করতে ভুলবেন না।"
    )


def configured_numbers_per_user() -> int:
    """Return the validated admin-configured number count for user requests."""
    try:
        value = int(get_setting("num_per_user", "1"))
    except (TypeError, ValueError):
        value = 1
    return min(MAX_NUMBERS_PER_USER_REQUEST, max(1, value))


def configured_number_valid_time_minutes() -> int:
    """Return the admin-configured lifetime for an assigned number."""
    try:
        value = int(
            get_setting(
                "number_valid_time_minutes",
                str(DEFAULT_NUMBER_VALID_TIME_MINUTES),
            )
        )
    except (TypeError, ValueError):
        value = DEFAULT_NUMBER_VALID_TIME_MINUTES
    return min(
        MAX_NUMBER_VALID_TIME_MINUTES,
        max(MIN_NUMBER_VALID_TIME_MINUTES, value),
    )


def set_setting(key: str, value: str):
    db_execute("INSERT OR REPLACE INTO settings (key, value) VALUES (?, ?)", (key, value))


def referral_qualification_otps() -> int:
    """Return the live OTP threshold required to qualify a referral."""
    try:
        value = int(float(get_setting(
            "referral_qualification_otps",
            str(DEFAULT_REFERRAL_QUALIFICATION_OTPS),
        )))
    except (TypeError, ValueError):
        value = DEFAULT_REFERRAL_QUALIFICATION_OTPS
    return max(1, min(100_000, value))


def referral_qualified_reward() -> float:
    """Return the live dollar reward credited for one qualified referral."""
    try:
        value = float(get_setting(
            "referral_qualified_reward",
            str(DEFAULT_REFERRAL_QUALIFIED_REWARD),
        ))
    except (TypeError, ValueError):
        value = DEFAULT_REFERRAL_QUALIFIED_REWARD
    if not math.isfinite(value):
        value = DEFAULT_REFERRAL_QUALIFIED_REWARD
    return max(0.0, value)


def referral_otp_commission_rate() -> float:
    """Return the live commission fraction paid to a qualified referrer."""
    try:
        value = float(get_setting(
            "referral_otp_commission_rate",
            str(DEFAULT_REFERRAL_OTP_COMMISSION_RATE),
        ))
    except (TypeError, ValueError):
        value = DEFAULT_REFERRAL_OTP_COMMISSION_RATE
    if not math.isfinite(value):
        value = DEFAULT_REFERRAL_OTP_COMMISSION_RATE
    return max(0.0, min(1.0, value))


def referral_settings_text(extra_message: str = "") -> str:
    reward = referral_qualified_reward()
    qualification = referral_qualification_otps()
    commission = referral_otp_commission_rate() * 100
    lines = [
        "🎁 <b>Referral Settings</b>",
        "",
        f"🔥 Per successful referral: <b>{format_currency(reward)}</b>",
        f"🎯 Active referral threshold: <b>{qualification} OTPs</b>",
        f"💸 Qualified referrer commission: <b>{commission:.2f}%</b> "
        "of every referred-user OTP reward",
        "",
        "নিচের option থেকে যেকোনো rule পরিবর্তন করুন।",
    ]
    if extra_message:
        lines.extend(["", extra_message])
    return "\n".join(lines)


def referral_settings_markup():
    return InlineKeyboardMarkup([
        [InlineKeyboardButton(
            "🔥 Per Referral Reward",
            callback_data="refcfg_reward",
        )],
        [InlineKeyboardButton(
            "🎯 Qualification OTPs",
            callback_data="refcfg_otps",
        )],
        [InlineKeyboardButton(
            "💸 User Commission %",
            callback_data="refcfg_commission",
        )],
        [InlineKeyboardButton(
            "⬅️ Back to User Management",
            callback_data="refcfg_back",
        )],
    ])


def record_otp_rewards_after_delivery(
    target_uid: int,
    otp_bonus: float,
    referrer_uid: int | None,
):
    """Credit one delivered OTP and any eligible referral rewards atomically.

    A referral becomes active when the referred user reaches the configured
    OTP threshold. The threshold OTP triggers the one-time qualification
    reward and is also the first OTP eligible for recurring commission.
    Both credits go to the referrer, never to the referred user.
    """
    try:
        otp_bonus = float(otp_bonus or 0.0)
    except (TypeError, ValueError):
        otp_bonus = 0.0
    if not math.isfinite(otp_bonus) or otp_bonus < 0:
        otp_bonus = 0.0

    with _db_lock:
        conn = get_db()
        row = conn.execute(
            """
            SELECT uid, first_name, username, balance, otp_count,
                   referred_by, referral_qualified
            FROM users
            WHERE uid=?
            """,
            (target_uid,),
        ).fetchone()
        if row is None:
            return None

        # Trust the persisted relationship rather than a stale scanner value.
        referrer_uid = row["referred_by"]
        previous_count = int(row["otp_count"] or 0)
        new_count = previous_count + 1
        previous_balance = float(row["balance"] or 0.0)
        new_target_balance = previous_balance + otp_bonus
        was_qualified = bool(row["referral_qualified"])
        became_qualified = False
        qualification_reward = 0.0
        commission = 0.0
        referral_credit_generated = 0.0
        referrer_balance = None

        conn.execute(
            """
            UPDATE users
            SET balance=?, otp_count=?
            WHERE uid=?
            """,
            (new_target_balance, new_count, target_uid),
        )
        otp_event_timestamp = leaderboard_event_timestamp()
        otp_week_start = leaderboard_week_start_key(otp_event_timestamp)
        conn.execute(
            """
            INSERT INTO leaderboard_weekly_counts (week_start, uid, otp_count)
            VALUES (?, ?, 1)
            ON CONFLICT(week_start, uid)
            DO UPDATE SET otp_count=otp_count+1
            """,
            (otp_week_start, target_uid),
        )

        if (
            referrer_uid
            and not was_qualified
            and new_count >= referral_qualification_otps()
        ):
            marked = conn.execute(
                """
                UPDATE users
                SET referral_qualified=1
                WHERE uid=? AND referral_qualified=0
                """,
                (target_uid,),
            )
            if marked.rowcount:
                became_qualified = True
                qualification_reward = referral_qualified_reward()
                conn.execute(
                    """
                    INSERT INTO leaderboard_events
                        (uid, event_type, related_uid, occurred_at)
                    VALUES (?, 'qualified_referral', ?, ?)
                    """,
                    (referrer_uid, target_uid, otp_event_timestamp),
                )
                conn.execute(
                    """
                    UPDATE users
                    SET qualified_referrals=COALESCE(qualified_referrals, 0)+1
                    WHERE uid=?
                    """,
                    (referrer_uid,),
                )
                if qualification_reward > 0:
                    credited = conn.execute(
                        """
                        UPDATE users
                        SET balance=balance+?,
                            referral_earnings=COALESCE(referral_earnings, 0)+?
                        WHERE uid=?
                        """,
                        (qualification_reward, qualification_reward, referrer_uid),
                    )
                    if credited.rowcount:
                        referral_credit_generated += qualification_reward

        # The qualifying OTP is eligible too. Every later OTP remains eligible
        # because referral_qualified is now persisted on the referred user.
        if (
            referrer_uid
            and (was_qualified or became_qualified)
            and otp_bonus > 0
        ):
            commission = otp_bonus * referral_otp_commission_rate()
            updated = conn.execute(
                """
                UPDATE users
                SET balance=balance+?,
                    referral_earnings=COALESCE(referral_earnings, 0)+?
                WHERE uid=?
                """,
                (commission, commission, referrer_uid),
            )
            if not updated.rowcount:
                commission = 0.0
            else:
                referral_credit_generated += commission

        if referrer_uid and referral_credit_generated > 0:
            conn.execute(
                """
                UPDATE users
                SET referral_earnings_generated=
                    COALESCE(referral_earnings_generated, 0)+?
                WHERE uid=?
                """,
                (referral_credit_generated, target_uid),
            )

        if referrer_uid:
            balance_row = conn.execute(
                "SELECT balance FROM users WHERE uid=?",
                (referrer_uid,),
            ).fetchone()
            if balance_row:
                referrer_balance = float(balance_row["balance"] or 0.0)

        conn.commit()
        _mark_json_dirty()
        return {
            "first_name": row["first_name"] or row["username"] or "User",
            "username": row["username"] or "",
            "target_balance": new_target_balance,
            "otp_count": new_count,
            "referrer_uid": referrer_uid,
            "referrer_balance": referrer_balance,
            "became_qualified": became_qualified,
            "qualification_reward": qualification_reward,
            "commission": commission,
            "referral_credit": referral_credit_generated,
        }


def get_force_join_channels():
    """Return the live force-join channel configuration from settings."""
    raw = get_setting("force_join_channels", "")
    items = []
    if raw:
        try:
            items = json.loads(raw)
        except (TypeError, ValueError):
            logger.warning("Invalid force_join_channels setting; ignoring it.")
            items = []
    if not isinstance(items, list):
        items = []

    channels = []
    for item in items:
        if not isinstance(item, dict):
            continue
        chat_id = str(item.get("chat_id", "")).strip()
        invite_link = str(item.get("invite_link", "")).strip()
        title = str(item.get("title", "")).strip()

        # Filter out legacy/unwanted links like A_TOOLSx2 or sxsupportgroup
        if any(unwanted in (chat_id + invite_link + title) for unwanted in ["A_TOOLSx2", "sxsupportgroup", "ConfirmSMS"]):
            continue

        if chat_id and invite_link:
            channels.append({
                "chat_id": chat_id,
                "invite_link": invite_link,
                "title": title or chat_id,
            })

    # Default fallback to official channel if empty
    if not channels:
        channels = [{
            "chat_id": "@EarnAirdropX",
            "invite_link": "https://t.me/EarnAirdropX",
            "title": "EarnAirdropX Channel",
        }]

    return channels

def set_force_join_channels(channels):
    set_setting(
        "force_join_channels",
        json.dumps(channels, ensure_ascii=False, separators=(",", ":")),
    )

def force_join_is_enabled() -> bool:
    return get_setting("force_join_enabled", "0") == "1" and bool(get_force_join_channels())

def _force_join_status_label() -> str:
    channels = get_force_join_channels()
    if not channels:
        return "🔴 OFF"
    return "✅ ON" if force_join_is_enabled() else "🔴 OFF"

def force_join_settings_text(extra_msg: str = "") -> str:
    channels = get_force_join_channels()
    lines = []
    if extra_msg:
        lines.extend([extra_msg, ""])
    lines.extend([
        "📢 <b>Force Join Channels</b>",
        "",
        f"Status: <b>{_force_join_status_label()}</b>",
        f"Channels: <b>{len(channels)}</b>",
        "",
    ])
    if channels:
        lines.append("<b>Configured channels:</b>")
        for index, channel in enumerate(channels, 1):
            lines.append(
                f"{index}. <b>{_html.escape(channel['title'])}</b>\n"
                f"   Chat: <code>{_html.escape(channel['chat_id'])}</code>\n"
                f"   Link: <code>{_html.escape(channel['invite_link'])}</code>"
            )
    else:
        lines.append("<i>No force-join channel has been configured.</i>")
    lines.extend([
        "",
        "Add format:",
        "<code>@channelusername</code> অথবা <code>channelusername</code>",
        "চাইলে full format-ও ব্যবহার করতে পারেন:",
        "<code>@channel | https://t.me/channel | Channel Name</code>",
        "",
        "The bot must be an admin in each channel so it can verify membership.",
    ])
    return "\n".join(lines)

def force_join_settings_markup():
    channels = get_force_join_channels()
    rows = [[
        InlineKeyboardButton("➕ Add Channel", callback_data="fj_add"),
        InlineKeyboardButton(
            f"{_force_join_status_label()} Toggle",
            callback_data="fj_toggle",
        ),
    ]]
    for index, channel in enumerate(channels):
        rows.append([
            InlineKeyboardButton(
                f"🗑 Remove {channel['title'][:32]}",
                callback_data=f"fj_remove_{index}",
            )
        ])
    rows.append([InlineKeyboardButton("⬅️ Back to Links", callback_data="fj_back")])
    return InlineKeyboardMarkup(rows)

def force_join_user_markup(channels):
    rows = [
        [InlineKeyboardButton(
            f"📢 Join {channel['title'][:40]}",
            url=channel["invite_link"],
        )]
        for channel in channels
    ]
    rows.append([InlineKeyboardButton(
        "✅ I Joined — Check Again",
        callback_data="forcejoin_check",
    )])
    return InlineKeyboardMarkup(rows)

def force_join_user_text(channels) -> str:
    channel_lines = []
    for channel in channels:
        link = _html.escape(channel['invite_link'])
        channel_lines.append(f"🚀 To use this bot, you must join our channel: {link}")

    return (
        "<b>𝗢𝗧𝗣 𝗭𝗢𝗡𝗘</b>\n\n"
        + "\n".join(channel_lines)
        + "\n\nJoin করার পর <b>Check Again</b> বাটনে চাপুন।"
    )

async def missing_force_join_channels(bot, uid: int):
    """Fail closed when an enabled channel cannot verify a user's membership."""
    if not force_join_is_enabled() or is_admin(uid):
        return []

    missing = []
    for channel in get_force_join_channels():
        try:
            member = await bot.get_chat_member(
                chat_id=channel["chat_id"],
                user_id=uid,
            )
            status = getattr(member, "status", "")
            is_member = getattr(member, "is_member", False)
            joined = status in {"creator", "administrator", "member"}
            joined = joined or (status == "restricted" and is_member)
            if not joined:
                missing.append(channel)
        except Exception as exc:
            logger.warning(
                "Force-join verification failed for %s: %s",
                channel["chat_id"],
                exc,
            )
            missing.append(channel)
    return missing

async def enforce_force_join_message(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> bool:
    """Gate normal user messages while keeping the admin panel unrestricted."""
    user = update.effective_user
    if user is None or is_admin(user.id):
        return True
    missing = await missing_force_join_channels(ctx.bot, user.id)
    if not missing:
        return True
    if update.message:
        await update.message.reply_text(
            force_join_user_text(missing),
            parse_mode="HTML",
            reply_markup=force_join_user_markup(missing),
        )
    return False

async def enforce_force_join_callback(query, ctx: ContextTypes.DEFAULT_TYPE) -> bool:
    """Gate inline button callbacks for users who have not joined."""
    uid = query.from_user.id
    if is_admin(uid):
        return True
    missing = await missing_force_join_channels(ctx.bot, uid)
    if not missing:
        return True
    text = force_join_user_text(missing)
    markup = force_join_user_markup(missing)
    if query.message:
        await query.edit_message_text(text, parse_mode="HTML", reply_markup=markup)
    else:
        await ctx.bot.send_message(
            chat_id=uid, text=text, parse_mode="HTML", reply_markup=markup
        )
    return False

def button_label(default_label: str) -> str:
    """Return the admin-customized label, or the original label."""
    return get_setting(f"button_label:{default_label}", default_label)

# Public Telegram custom-emoji set used for every country flag rendered by the
# bot.  The set is loaded through Bot API at runtime so the IDs do not need to
# be copied into the source and stay in sync with the pack.
FLAG_EMOJI_SET_NAME = "FlagSXSponsor"
FLAG_CUSTOM_EMOJI_IDS = {}
_flag_emoji_pack_loaded = False
_flag_emoji_pack_last_attempt = 0.0

async def refresh_flag_emoji_pack(bot) -> bool:
    """Load the sponsor flag pack and map each Unicode flag to its emoji ID."""
    global _flag_emoji_pack_loaded, _flag_emoji_pack_last_attempt
    if _flag_emoji_pack_loaded:
        return bool(FLAG_CUSTOM_EMOJI_IDS)
    now = time.monotonic()
    if now - _flag_emoji_pack_last_attempt < 300:
        return bool(FLAG_CUSTOM_EMOJI_IDS)
    _flag_emoji_pack_last_attempt = now

    try:
        sticker_set = await bot.get_sticker_set(FLAG_EMOJI_SET_NAME)
        loaded = {}
        for sticker in getattr(sticker_set, "stickers", ()) or ():
            emoji = str(getattr(sticker, "emoji", "") or "")
            custom_id = getattr(sticker, "custom_emoji_id", None)
            if emoji and custom_id and re.fullmatch(
                r"[\U0001F1E6-\U0001F1FF]{2}", emoji
            ):
                loaded[emoji] = str(custom_id)
        FLAG_CUSTOM_EMOJI_IDS.clear()
        FLAG_CUSTOM_EMOJI_IDS.update(loaded)
        _flag_emoji_pack_loaded = True
        logger.info(
            "Loaded %d premium country flags from %s",
            len(FLAG_CUSTOM_EMOJI_IDS),
            FLAG_EMOJI_SET_NAME,
        )
        return bool(FLAG_CUSTOM_EMOJI_IDS)
    except Exception as exc:
        logger.warning(
            "Could not load premium flag set %s: %s",
            FLAG_EMOJI_SET_NAME,
            exc,
        )
        return False

def _flag_custom_emoji_id(flag: str) -> str | None:
    """Return the loaded sponsor-pack ID for a two-letter Unicode flag."""
    return FLAG_CUSTOM_EMOJI_IDS.get(str(flag or ""))

def _country_text_html(text: str) -> str:
    """Escape country text while upgrading every ordinary flag to the pack."""
    pieces = []
    cursor = 0
    for match in re.finditer(
        r"[\U0001F1E6-\U0001F1FF]{2}",
        str(text or ""),
    ):
        pieces.append(_html.escape(str(text)[cursor:match.start()]))
        pieces.append(_premium_flag_html(match.group(0)))
        cursor = match.end()
    pieces.append(_html.escape(str(text or "")[cursor:]))
    return "".join(pieces)

def _message_custom_emoji_entities(message) -> str | None:
    """Serialize custom-emoji entities so a country name can keep its exact pack."""
    entities = []
    for entity in (getattr(message, "entities", None) or []):
        if getattr(entity, "type", None) != "custom_emoji":
            continue
        emoji_id = getattr(entity, "custom_emoji_id", None)
        if emoji_id:
            entities.append({
                "offset": int(entity.offset),
                "length": int(entity.length),
                "id": str(emoji_id),
            })
    return json.dumps(entities, ensure_ascii=False) if entities else None


def _normalized_message_custom_emoji_entities(
    message,
    text_limit: str | None = None,
) -> str | None:
    """Serialize service emoji entities after service-name whitespace cleanup."""
    message_text = str(getattr(message, "text", "") or "")
    normalized_text = " ".join(message_text.strip().split())
    limit_text = normalized_text if text_limit is None else text_limit
    limit_units = len(limit_text.encode("utf-16-le")) // 2
    entities = []

    for entity in getattr(message, "entities", None) or []:
        if getattr(entity, "type", None) != "custom_emoji":
            continue
        emoji_id = getattr(entity, "custom_emoji_id", None)
        if not emoji_id:
            continue

        raw_start = _utf16_index(message_text, int(entity.offset))
        normalized_prefix = re.sub(
            r"\s+",
            " ",
            message_text[:raw_start],
        ).lstrip()
        normalized_offset = (
            len(normalized_prefix.encode("utf-16-le")) // 2
        )
        length = int(entity.length)
        if normalized_offset + length > limit_units:
            continue
        entities.append({
            "offset": normalized_offset,
            "length": length,
            "id": str(emoji_id),
        })

    return json.dumps(entities, ensure_ascii=False) if entities else None


def _utf16_index(text: str, target_units: int) -> int:
    """Convert Telegram's UTF-16 offset into Python's string index."""
    units = 0
    for index, char in enumerate(text):
        if units >= target_units:
            return index
        units += len(char.encode("utf-16-le")) // 2
    return len(text)

def country_name_html(name: str, emoji_entities=None) -> str:
    """Escape a country name and restore its saved premium emoji entities."""
    if isinstance(emoji_entities, str):
        try:
            emoji_entities = json.loads(emoji_entities)
        except (TypeError, ValueError):
            emoji_entities = None
    if not emoji_entities:
        return _country_text_html(name)

    pieces = []
    cursor = 0
    for entity in sorted(emoji_entities, key=lambda item: int(item.get("offset", 0))):
        start_units = int(entity.get("offset", 0))
        end_units = start_units + int(entity.get("length", 0))
        start = _utf16_index(name, start_units)
        end = _utf16_index(name, end_units)
        emoji_id = str(entity.get("id", ""))
        if not emoji_id or start < cursor or end <= start:
            continue
        pieces.append(_country_text_html(name[cursor:start]))
        glyph = name[start:end]
        sponsor_id = _flag_custom_emoji_id(glyph)
        if sponsor_id:
            pieces.append(
                f'<tg-emoji emoji-id="{_html.escape(sponsor_id, quote=True)}">'
                f'{_html.escape(glyph)}</tg-emoji>'
            )
        else:
            pieces.append(
                f'<tg-emoji emoji-id="{_html.escape(emoji_id, quote=True)}">'
                f'{_html.escape(glyph)}</tg-emoji>'
            )
        cursor = end
    pieces.append(_country_text_html(name[cursor:]))
    return "".join(pieces)

def country_display_html(country) -> str:
    return country_name_html(country["name"], country["emoji_entities"] if "emoji_entities" in country.keys() else None)

def country_icon_custom_emoji_id(country) -> str | None:
    """Return the sponsor-pack flag ID for use as an inline button icon."""
    raw = country["emoji_entities"] if "emoji_entities" in country.keys() else None
    name = str(country["name"])
    if raw:
        try:
            entities = json.loads(raw) if isinstance(raw, str) else raw
        except (TypeError, ValueError):
            entities = None
        if isinstance(entities, list):
            for entity in entities:
                if not isinstance(entity, dict):
                    continue
                start_units = int(entity.get("offset", 0))
                end_units = start_units + int(entity.get("length", 0))
                glyph = name[
                    _utf16_index(name, start_units):
                    _utf16_index(name, end_units)
                ]
                sponsor_id = _flag_custom_emoji_id(glyph)
                if sponsor_id:
                    return sponsor_id
                emoji_id = entity.get("id")
                if emoji_id:
                    return str(emoji_id)

    leading_flag = re.match(
        r"^\s*([\U0001F1E6-\U0001F1FF]{2})",
        name,
    )
    if leading_flag:
        return _flag_custom_emoji_id(leading_flag.group(1))
    return None

def country_button_name(country) -> str:
    """Remove the stored fallback glyph; Telegram renders the saved emoji as the icon."""
    name = country["name"]
    raw = country["emoji_entities"] if "emoji_entities" in country.keys() else None
    if not raw:
        return re.sub(
            r"^\s*[\U0001F1E6-\U0001F1FF]{2}\s*",
            "",
            name,
        ).strip()
    try:
        entities = json.loads(raw) if isinstance(raw, str) else raw
    except (TypeError, ValueError):
        return name
    if not isinstance(entities, list):
        return name

    ranges = []
    for entity in entities:
        if not isinstance(entity, dict):
            continue
        start_units = int(entity.get("offset", 0))
        end_units = start_units + int(entity.get("length", 0))
        if end_units > start_units:
            ranges.append((
                _utf16_index(name, start_units),
                _utf16_index(name, end_units),
            ))
    for start, end in sorted(ranges, reverse=True):
        name = name[:start] + name[end:]
    return re.sub(
        r"^\s*[\U0001F1E6-\U0001F1FF]{2}\s*",
        "",
        name,
    ).strip()


def copyable_country_name(country) -> str:
    """Return only the country name when a display flag/emoji is present."""
    name = country_button_name(country)
    # Also support ordinary regional-indicator flags that were typed without
    # Telegram custom-emoji entities.
    name = re.sub(
        r"^\s*(?:[\U0001F1E6-\U0001F1FF]{2})\s*",
        "",
        name,
    )
    return name.strip()


def service_display_html(service) -> str:
    """Render the service's saved emoji first, then a built-in service icon."""
    mapping_key = _service_mapping_key(
        service.get("name", "") if hasattr(service, "get") else service["name"]
    )
    fallback = SERVICE_CUSTOM_EMOJI_FALLBACKS.get(mapping_key, "💠")
    if service_icon_custom_emoji_id(service):
        logo = service_logo_html(service, fallback=fallback)
        return f"{logo} {_html.escape(service_button_name(service))}"

    return country_name_html(
        service["name"],
        service["emoji_entities"] if "emoji_entities" in service.keys() else None
    )


SERVICE_CUSTOM_EMOJI_IDS = {
    "whatsapp": "6298480844214379008",
    "facebook": "6298648828975259524",
    "instagram": "6298402555550508419",
    "tiktok": "6298389279806594462",
    "telegram": "6298478396083019849",
}

SERVICE_CUSTOM_EMOJI_FALLBACKS = {
    "whatsapp": "🟢",
    "facebook": "🔵",
    "instagram": "📸",
    "tiktok": "🎵",
    "telegram": "✈️",
}


def _service_mapping_key(name: str) -> str:
    """Normalize service names such as 'Tik Tok' for built-in emoji lookup."""
    return re.sub(r"[^a-z0-9]", "", str(name or "").casefold())


def service_icon_custom_emoji_id(service) -> str | None:
    """Return the service's saved emoji ID before any built-in fallback."""
    mapping_key = _service_mapping_key(
        service.get("name", "") if hasattr(service, "get") else service["name"]
    )
    raw = service["emoji_entities"] if "emoji_entities" in service.keys() else None
    if raw:
        try:
            entities = json.loads(raw) if isinstance(raw, str) else raw
        except (TypeError, ValueError):
            entities = None
        if isinstance(entities, list):
            for entity in entities:
                emoji_id = entity.get("id") if isinstance(entity, dict) else None
                if emoji_id:
                    return str(emoji_id)
    return SERVICE_CUSTOM_EMOJI_IDS.get(mapping_key)


def service_logo_html(service, fallback: str = "🔔") -> str:
    """Render the explicitly saved service emoji before a built-in fallback."""
    if not service:
        return _html.escape(fallback)
    saved_logo = _saved_service_logo_html(service, fallback=fallback)
    if saved_logo:
        return saved_logo

    name = str(service["name"])
    mapping_key = _service_mapping_key(name)
    builtin_id = SERVICE_CUSTOM_EMOJI_IDS.get(mapping_key)
    if builtin_id:
        glyph = SERVICE_CUSTOM_EMOJI_FALLBACKS.get(mapping_key, fallback or "🔔")
        return (
            f'<tg-emoji emoji-id="{_html.escape(builtin_id, quote=True)}">'
            f"{_html.escape(glyph)}</tg-emoji>"
        )

    raw = service["emoji_entities"] if "emoji_entities" in service.keys() else None
    if raw:
        try:
            entities = json.loads(raw) if isinstance(raw, str) else raw
        except (TypeError, ValueError):
            entities = None
        if isinstance(entities, list):
            for entity in entities:
                if not isinstance(entity, dict):
                    continue
                emoji_id = str(entity.get("id") or "")
                if not emoji_id:
                    continue
                start_units = int(entity.get("offset", 0))
                end_units = start_units + int(entity.get("length", 0))
                start = _utf16_index(name, start_units)
                end = _utf16_index(name, end_units)
                glyph = name[start:end] or fallback
                return (
                    f'<tg-emoji emoji-id="{_html.escape(emoji_id, quote=True)}">'
                    f"{_html.escape(glyph)}</tg-emoji>"
                )
    return _html.escape(fallback)


def _saved_service_logo_html(service, fallback: str = "💠") -> str | None:
    """Prefer the custom emoji explicitly saved on a service over built-ins."""
    if not service:
        return None
    raw = service["emoji_entities"] if "emoji_entities" in service.keys() else None
    if not raw:
        return None
    try:
        entities = json.loads(raw) if isinstance(raw, str) else raw
    except (TypeError, ValueError):
        entities = None
    if not isinstance(entities, list):
        return None
    name = str(service["name"])
    for entity in entities:
        if not isinstance(entity, dict):
            continue
        emoji_id = str(entity.get("id") or "")
        if not emoji_id:
            continue
        start_units = int(entity.get("offset", 0))
        end_units = start_units + int(entity.get("length", 0))
        glyph = name[
            _utf16_index(name, start_units):
            _utf16_index(name, end_units)
        ] or fallback
        return (
            f'<tg-emoji emoji-id="{_html.escape(emoji_id, quote=True)}">'
            f"{_html.escape(glyph)}</tg-emoji>"
        )
    return None


def service_button_name(service) -> str:
    """Return service name with the fallback glyph removed (icon is set separately)."""
    name = service["name"]
    raw = service["emoji_entities"] if "emoji_entities" in service.keys() else None
    if not raw:
        return name
    try:
        entities = json.loads(raw) if isinstance(raw, str) else raw
    except (TypeError, ValueError):
        return name
    if not isinstance(entities, list):
        return name
    ranges = []
    for entity in entities:
        if not isinstance(entity, dict):
            continue
        start_units = int(entity.get("offset", 0))
        end_units = start_units + int(entity.get("length", 0))
        if end_units > start_units:
            ranges.append((_utf16_index(name, start_units), _utf16_index(name, end_units)))
    for start, end in sorted(ranges, reverse=True):
        name = name[:start] + name[end:]
    return name.strip()


def copyable_service_name(service) -> str:
    name = service_button_name(service)
    name = re.sub(
        r"^\s*(?:[\U0001F1E6-\U0001F1FF]{2})\s*",
        "",
        name,
    )
    return name.strip()


def _format_otp_tk(value) -> str:
    """Show the configured OTP reward with at least two decimal places."""
    rendered = format_price(value)
    if "." not in rendered:
        return f"{rendered}.00"
    whole, fraction = rendered.split(".", 1)
    return f"{whole}.{fraction.ljust(2, '0')}"


def _format_assigned_otp_bdt(value) -> str:
    """Convert this user-facing OTP rate from USD to BDT at ৳130 per USD."""
    try:
        amount = Decimal(str(value if value is not None else 0))
        if not amount.is_finite():
            amount = Decimal("0")
        taka = (amount * ASSIGNED_OTP_USD_TO_BDT).quantize(
            Decimal("0.01"),
            rounding=ROUND_HALF_UP,
        )
    except (InvalidOperation, TypeError, ValueError):
        taka = Decimal("0.00")
    return f"{taka:.2f}"


def _per_otp_premium_emoji_html() -> str:
    return (
        f'<tg-emoji emoji-id="{PER_OTP_PREMIUM_EMOJI_ID}">'
        "💠</tg-emoji>"
    )


def _number_button_text(number, remove_country_code: bool = False) -> str:
    """Render a copyable assigned number with an optional country-code toggle."""
    digits = re.sub(r"\D", "", str(number or ""))
    if not digits:
        return "+"
    if remove_country_code:
        _, dial_code = _phone_to_iso2(digits)
        if dial_code and digits.startswith(dial_code):
            digits = digits[len(dial_code):] or digits
        return digits
    return f"+{digits}"


def number_services_markup(services) -> InlineKeyboardMarkup:
    """Render Get Number service buttons two per row."""
    buttons = []
    for index in range(0, len(services), 2):
        buttons.append([
            InlineKeyboardButton(
                service_button_name(service),
                callback_data=f"gnsvc_{service['id']}",
                icon_custom_emoji_id=service_icon_custom_emoji_id(service),
            )
            for service in services[index:index + 2]
        ])
    return InlineKeyboardMarkup(buttons)


def _current_assigned_number_rows(uid: int, country_id: int):
    """Find the latest assignment group for this user's number card."""
    latest = db_query(
        "SELECT last_number_request_at FROM users WHERE uid=?",
        (uid,),
    )
    request_at = latest[0]["last_number_request_at"] if latest else None
    if request_at:
        rows = db_query(
            "SELECT id, number FROM numbers "
            "WHERE assigned_uid=? AND country_id=? AND assigned_at=? "
            "ORDER BY id",
            (uid, country_id, request_at),
        )
        if rows:
            return rows

    # Backward-compatible fallback for legacy rows without matching timestamps.
    rows = db_query(
        "SELECT id, number FROM numbers "
        "WHERE assigned_uid=? AND country_id=? "
        "ORDER BY assigned_at DESC, id DESC LIMIT ?",
        (uid, country_id, configured_numbers_per_user()),
    )
    return list(reversed(rows))


def number_assigned_text(rows, service_id: int, country_id: int) -> str:
    """Build the user-facing message shown after a number is assigned."""
    country_rows = db_query(
        "SELECT id, name, emoji_entities, price FROM countries "
        "WHERE id=? AND active=1",
        (country_id,),
    )
    country = country_rows[0] if country_rows else None

    service = None
    amount = country["price"] if country else 0
    if service_id:
        service_rows = db_query(
            """
            SELECT s.id, s.name, s.emoji_entities,
                   COALESCE(sc.amount, c.price, 0) AS amount
            FROM services s
            JOIN service_countries sc ON sc.service_id=s.id
            JOIN countries c ON c.id=sc.country_id
            WHERE s.id=? AND c.id=?
            LIMIT 1
            """,
            (service_id, country_id),
        )
        if service_rows:
            service = service_rows[0]
            amount = service["amount"]

    if country:
        country_html = country_display_html(country)
        # If no saved country icon exists, derive the standard flag from the
        # assigned number while keeping the complete country name visible.
        has_saved_icon = bool(country["emoji_entities"]) or bool(
            re.match(r"^\s*[\U0001F1E6-\U0001F1FF]{2}", str(country["name"]))
        )
        if not has_saved_icon and rows:
            iso2, _ = _phone_to_iso2(str(rows[0]["number"]))
            flag = _country_flag(iso2) if iso2 else "🌐"
            country_html = (
                f"{_html.escape(flag)} "
                f"{_html.escape(copyable_country_name(country))}"
            )
    else:
        country_html = "🌐 Unknown"

    if service:
        service_html = (
            f"{service_logo_html(service, fallback='💠')} "
            f"{_html.escape(service_button_name(service))}"
        )
    else:
        service_html = "💠 OTP"

    display = (
        f"💰 <b>Per OTP: {format_currency_price(amount)}</b> "
        f"{_per_otp_premium_emoji_html()}"
    )
    if board_currency() == "USDT":
        display += f" <b>প্রতি OTP : {_format_assigned_otp_bdt(amount)}৳</b>"
    return f"{country_html} {service_html} <b>Number Assigned</b>\n\n{display}"


def get_country_manager_countries():
    return db_query(
        """
        SELECT c.id, c.name, c.emoji_entities,
               COUNT(n.id) AS total,
               COALESCE(SUM(CASE WHEN n.used=1 THEN 1 ELSE 0 END), 0) AS used,
               COALESCE(SUM(CASE WHEN n.used=0 THEN 1 ELSE 0 END), 0) AS available
        FROM countries c
        LEFT JOIN numbers n ON n.country_id=c.id
        WHERE c.active=1
        GROUP BY c.id, c.name, c.emoji_entities
        ORDER BY c.name COLLATE NOCASE
        """
    )


def _find_service_by_input(name: str, active_only: bool = True):
    """Match stored/clean names, ignoring spaces and service emoji glyphs."""
    clause = "WHERE active=1" if active_only else ""
    rows = db_query(
        f"SELECT id, name, active, emoji_entities FROM services {clause} "
        "ORDER BY LENGTH(name) DESC"
    )
    target = " ".join(name.strip().split()).casefold()
    target_key = _service_mapping_key(target)
    for row in rows:
        candidates = {
            " ".join(str(row["name"]).split()).casefold(),
            copyable_service_name(row).casefold(),
        }
        candidate_keys = {_service_mapping_key(candidate) for candidate in candidates}
        if target in candidates or (target_key and target_key in candidate_keys):
            return row
    return None


def _normalize_country_input(name: str) -> str:
    """Normalize admin-entered country names without changing their meaning."""
    return " ".join(str(name or "").strip().split()).casefold()


def _find_country_by_input(name: str):
    rows = db_query(
        "SELECT id, name, price, emoji_entities FROM countries "
        "WHERE active=1 ORDER BY LENGTH(name) DESC"
    )
    target = _normalize_country_input(name)
    for row in rows:
        if target in {
            _normalize_country_input(row["name"]),
            _normalize_country_input(copyable_country_name(row)),
        }:
            return row
    return None


def _delete_country_permanently(country_id: int):
    """Remove a country and all data owned by that country.

    Countries used to be soft-deleted by setting active=0.  That left the
    unique country name behind, which prevented an admin from adding the
    same country again.  Remove dependent mappings and numbers first, then
    remove the country row itself.
    """
    with _db_lock:
        conn = get_db()
        conn.execute(
            "DELETE FROM service_countries WHERE country_id=?",
            (country_id,),
        )
        conn.execute(
            "DELETE FROM numbers WHERE country_id=?",
            (country_id,),
        )
        conn.execute(
            "DELETE FROM countries WHERE id=?",
            (country_id,),
        )
        conn.commit()
        _mark_json_dirty()


def _purge_inactive_country_by_name(name: str):
    """Remove legacy soft-deleted rows before re-adding their country name."""
    target = _normalize_country_input(name)
    rows = db_query(
        "SELECT id, name FROM countries WHERE active=0"
    )
    for row in rows:
        if _normalize_country_input(row["name"]) == target:
            _delete_country_permanently(row["id"])


def _country_delete_name(text: str) -> str | None:
    """Return the country portion of a supported delete/remove command."""
    normalized = " ".join(str(text or "").strip().split())
    lowered = normalized.casefold()
    for prefix in (
        "delete country ",
        "remove country ",
        "delete ",
        "remove ",
    ):
        if lowered.startswith(prefix):
            country_name = normalized[len(prefix):].strip()
            return country_name or None
    return None


def resolve_button_text(text: str) -> str:
    """Map a customized keyboard label back to its internal button key."""
    for default_label, _ in sorted(
        CUSTOMIZABLE_BUTTONS,
        key=lambda item: len(button_label(item[0])),
        reverse=True,
    ):
        customized = button_label(default_label)
        if text == customized:
            return default_label
        # Withdraw buttons add a live status suffix to their label.
        if text.startswith(f"{customized} ["):
            return default_label + text[len(customized):]
    return text

# ─── WITHDRAW METHODS HELPERS ────────────────────────────────────────────────
DEFAULT_WITHDRAW_METHODS = ["Bkash", "Binance"]

def _normalize_withdraw_method(method):
    """Normalize legacy string methods and emoji-aware method records."""
    if isinstance(method, dict):
        name = str(method.get("name") or "").strip()
        entities = method.get("emoji_entities")
    else:
        name = str(method or "").strip()
        entities = None
    return {"name": name, "emoji_entities": entities} if name else None


def withdraw_method_name(method) -> str:
    normalized = _normalize_withdraw_method(method)
    return normalized["name"] if normalized else ""


def withdraw_method_html(method) -> str:
    normalized = _normalize_withdraw_method(method)
    if not normalized:
        return ""
    return country_name_html(
        normalized["name"],
        normalized["emoji_entities"],
    )


def withdraw_method_button_label(method) -> str:
    normalized = _normalize_withdraw_method(method)
    if not normalized:
        return ""
    # Reuse the entity-aware label cleaner so the custom emoji is rendered as
    # the Telegram button icon instead of appearing twice in the label.
    return service_button_name(normalized)


def withdraw_method_icon_custom_emoji_id(method) -> str | None:
    normalized = _normalize_withdraw_method(method)
    return service_icon_custom_emoji_id(normalized) if normalized else None


def withdraw_wallet_value(wallet_full: str) -> str:
    """Return only the wallet address/number from ``Method — address``."""
    raw = str(wallet_full or "").strip()
    _method, separator, wallet = raw.partition(" — ")
    return wallet.strip() if separator else raw


def withdraw_wallet_html(wallet_full: str) -> str:
    """Render a stored withdrawal wallet while restoring its method emoji."""
    raw = str(wallet_full or "")
    method_text, separator, wallet = raw.partition(" — ")
    if not separator:
        return f"<code>{_html.escape(raw)}</code>"

    method = next(
        (
            item for item in get_withdraw_methods()
            if method_text.casefold() in {
                withdraw_method_name(item).casefold(),
                withdraw_method_button_label(item).casefold(),
            }
        ),
        None,
    )
    if not method:
        return f"<code>{_html.escape(raw)}</code>"
    return (
        f"{withdraw_method_html(method)} — "
        f"<code>{_html.escape(wallet)}</code>"
    )


def get_withdraw_methods() -> list:
    raw = get_setting("withdraw_methods", None)
    if raw:
        try:
            methods = json.loads(raw)
            if isinstance(methods, list) and methods:
                return [
                    normalized for item in methods
                    if (normalized := _normalize_withdraw_method(item))
                ]
        except Exception:
            pass
    return [
        _normalize_withdraw_method(method)
        for method in DEFAULT_WITHDRAW_METHODS
    ]

def set_withdraw_methods(methods: list):
    normalized = [
        item for method in methods
        if (item := _normalize_withdraw_method(method))
    ]
    set_setting("withdraw_methods", json.dumps(normalized, ensure_ascii=False))

def build_wtype_markup(bal: float) -> InlineKeyboardMarkup:
    """Build dynamic wallet-type selection keyboard."""
    methods = get_withdraw_methods()
    # Use a short numeric reference instead of embedding an arbitrary method
    # name in callback_data (Telegram limits callback_data to 64 bytes).
    btns = [
        InlineKeyboardButton(
            withdraw_method_button_label(method),
            callback_data=f"wtype_{index}",
            icon_custom_emoji_id=withdraw_method_icon_custom_emoji_id(method),
        )
        for index, method in enumerate(methods)
    ]
    # Row them 2 per row
    rows = [btns[i:i+2] for i in range(0, len(btns), 2)]
    rows.append([InlineKeyboardButton("❌ Cancel", callback_data="cancel_input")])
    return InlineKeyboardMarkup(rows)

def withdraw_methods_panel_text() -> str:
    methods = get_withdraw_methods()
    lines = (
        "\n".join(f"  • {withdraw_method_html(method)}" for method in methods)
        if methods else "  (none)"
    )
    return (
        f"💳 <b>Withdraw Methods</b>\n\n"
        f"Current methods:\n{lines}\n\n"
        f"Use buttons below to add or remove."
    )

def withdraw_methods_panel_markup() -> InlineKeyboardMarkup:
    methods = get_withdraw_methods()
    rows = [
        [InlineKeyboardButton(
            f"🗑 Remove {withdraw_method_button_label(method)}",
            callback_data=f"wm_remove_{index}",
            icon_custom_emoji_id=withdraw_method_icon_custom_emoji_id(method),
        )]
        for index, method in enumerate(methods)
    ]
    rows.append([InlineKeyboardButton("➕ Add Method", callback_data="wm_add")])
    return InlineKeyboardMarkup(rows)

# ─── ZIP SENDER ───────────────────────────────────────────────────────────────
# ─── COUNTRY LIST HELPER ──────────────────────────────────────────────────────
def country_list_text(extra_msg: str = "") -> str:
    countries = get_country_manager_countries()
    lines = []
    if extra_msg:
        lines.append(extra_msg)
        lines.append("")
    lines.append("🌐 <b>Country Manager</b>")
    lines.append("")
    if countries:
        for index, country in enumerate(countries):
            total = int(country["total"] or 0)
            available = int(country["available"] or 0)
            used = int(country["used"] or 0)
            lines.extend([
                f"<code>{_html.escape(copyable_country_name(country))}</code>",
                f"  ➕ Added: {total:,}  ✅ Available: {available:,}  🔴 Used: {used:,}",
            ])
            if index < len(countries) - 1:
                lines.append("─" * 30)

        total_numbers = sum(int(c["total"] or 0) for c in countries)
        total_available = sum(int(c["available"] or 0) for c in countries)
        total_used = sum(int(c["used"] or 0) for c in countries)
        lines.extend([
            "",
            f"📌 <b>Total Countries: {len(countries)}</b>",
            f"Total Numbers: {total_numbers:,}",
            f"✅ Available: {total_available:,}  🔴 Used: {total_used:,}",
        ])
    else:
        lines.append("No countries found.")
    lines.extend([
        "",
        "✏️ Type a country name (e.g. Bangladesh), ISO code (BD) or phone code (+880).",
        "🗑️ To delete: <code>delete [country name]</code>",
    ])
    return "\n".join(lines)

def copy_countries_markup(countries, include_cancel: bool = False):
    rows = [
        [InlineKeyboardButton(
            f"📋 {country_button_name(country)}",
            copy_text=CopyTextButton(text=copyable_country_name(country)),
            icon_custom_emoji_id=country_icon_custom_emoji_id(country),
        )]
        for country in countries
    ]
    if include_cancel:
        rows.append([InlineKeyboardButton("❌ Cancel", callback_data="cancel_input")])
    return InlineKeyboardMarkup(rows) if rows else None

def add_number_countries_text(countries) -> str:
    """Render Add Number country inventory with total, used, and available counts."""
    lines = [
        "📱 <b>Add Number</b>",
        "",
        "Available countries:",
    ]
    for country in countries:
        lines.append(
            f"• <code>{_html.escape(copyable_country_name(country))}</code> — "
            f"Total: {int(country['total'] or 0):,} | "
            f"Used: {int(country['used'] or 0):,} | "
            f"Available: {int(country['available'] or 0):,}"
        )
    lines.extend([
        "",
        "উপরের দেশের নামের উপর ক্লিক করে কপি করুন, তারপর নামটি পাঠান।",
    ])
    return "\n".join(lines)

def get_add_number_countries():
    return db_query(
        """
        SELECT c.id, c.name, c.emoji_entities,
               COUNT(n.id) AS total,
               COALESCE(SUM(CASE WHEN n.used=1 THEN 1 ELSE 0 END), 0) AS used,
               COALESCE(SUM(CASE WHEN n.used=0 THEN 1 ELSE 0 END), 0) AS available
        FROM countries c
        LEFT JOIN numbers n ON n.country_id=c.id
        WHERE c.active=1
        GROUP BY c.id, c.name, c.emoji_entities
        ORDER BY c.name COLLATE NOCASE
        """
    )

def active_services():
    return db_query(
        "SELECT id, name, emoji_entities FROM services WHERE active=1 ORDER BY name COLLATE NOCASE"
    )

def service_manage_text(extra_msg: str = "") -> str:
    services = db_query(
        "SELECT id, name, emoji_entities FROM services WHERE active=1 ORDER BY name COLLATE NOCASE"
    )
    mappings = db_query(
        """
        SELECT s.name AS service_name, s.emoji_entities AS service_emoji,
               c.name AS country_name,
               COALESCE(sc.amount, c.price, 0) AS bonus,
               COUNT(n.id) AS number_count
        FROM service_countries sc
        JOIN services s ON s.id=sc.service_id AND s.active=1
        JOIN countries c ON c.id=sc.country_id AND c.active=1
        LEFT JOIN numbers n ON n.country_id=c.id AND n.used=0
        GROUP BY s.id, s.name, c.id, c.name, sc.amount, c.price
        ORDER BY s.name COLLATE NOCASE, c.name COLLATE NOCASE
        """
    )
    lines = []
    if extra_msg:
        lines.extend([extra_msg, ""])
    lines.extend(["🛠️ <b>Service Management</b>", ""])
    lines.append("📋 <b>Services:</b>")
    if services:
        lines.extend(f"• <code>{_html.escape(s['name'])}</code>" for s in services)
    else:
        lines.append("• No services added yet")

    lines.extend(["", "🌍 <b>Countries:</b>"])
    if mappings:
        for row in mappings:
            lines.append(
                f"• <code>{_html.escape(row['country_name'])}</code> — "
                f"{row['number_count']} numbers — "
                f"OTP Bonus: {format_currency_price(row['bonus'] or 0)}"
            )
    else:
        lines.append("• No mapped countries yet")

    lines.extend([
        "",
        "━━━━━━━━━━━━━━━━━━━━━",
        "➕ নতুন Service যোগ করতে লিখুন:",
        "<i>উদাহরণ:</i> <code>WhatsApp</code>",
        "",
        "➖ Service ডিলিট করতে লিখুন:",
        "<i>উদাহরণ:</i> <code>delete WhatsApp</code>",
        "",
        "➕ Country-এর সঙ্গে Map করতে লিখুন:",
        "<i>উদাহরণ:</i> <code>WhatsApp Bangladesh</code>",
        "",
        "➖ Unmap করতে লিখুন:",
        "<i>উদাহরণ:</i> <code>unmap WhatsApp Bangladesh</code>",
        "",
        "<i>Cancel করতে যেকোনো menu বাটন চাপুন।</i>",
    ])
    return "\n".join(lines)

# ─── KEYBOARDS ───────────────────────────────────────────────────────────────
def admin_keyboard():
    return ReplyKeyboardMarkup(
        [[KeyboardButton(button_label(BTN_COUNTRY_MGMT)), KeyboardButton(button_label(BTN_USER_MGMT))],
         [KeyboardButton(button_label(BTN_SETTINGS)),    KeyboardButton(button_label(BTN_BROADCAST))],
         [KeyboardButton(button_label(BTN_LINKS)),        KeyboardButton(button_label(BTN_STATS))],
         [KeyboardButton(button_label(BTN_PANELS))]],
        resize_keyboard=True
    )

def panels_keyboard():
    panels = db_query("SELECT id, name, active FROM panels ORDER BY id")
    panel_btns = []
    for p in panels:
        icon = "🟢" if p["active"] else "🔴"
        panel_btns.append(KeyboardButton(f"{icon} {p['name']}"))
    rows = [[
        KeyboardButton(button_label(BTN_PANEL_ADD)),
        KeyboardButton(button_label(BTN_LAST_MSGS)),
    ]]
    # pair panels 2 per row
    for i in range(0, len(panel_btns), 2):
        rows.append(panel_btns[i:i + 2])
    rows.append([KeyboardButton(button_label(BTN_BACK_ADMIN))])
    return ReplyKeyboardMarkup(rows, resize_keyboard=True)

def country_mgmt_keyboard():
    return ReplyKeyboardMarkup(
        [[KeyboardButton(button_label(BTN_ADD_COUNTRY)),   KeyboardButton(button_label(BTN_ADD_NUMBER))],
         [KeyboardButton(button_label(BTN_COUNTRY_PRICE)), KeyboardButton(button_label(BTN_NUM_PER_USER))],
         [KeyboardButton(button_label(BTN_RESET_NUMBER)),  KeyboardButton(button_label(BTN_SERVICE_MANAGE))],
         [KeyboardButton(button_label(BTN_BACK_ADMIN))]],
        resize_keyboard=True
    )

def user_mgmt_keyboard():
    wd_status  = "✅ ON" if get_setting("withdraw_enabled", "1") == "1" else "🔴 OFF"
    min_wd     = minimum_withdraw_usdt()
    min_label  = format_currency(min_wd) if min_wd > 0 else "None"
    return ReplyKeyboardMarkup(
        [[KeyboardButton(button_label(BTN_USER_LIST)),       KeyboardButton(button_label(BTN_WITHDRAWALS))],
         [KeyboardButton(button_label(BTN_ADD_BALANCE)),     KeyboardButton(button_label(BTN_ADD_ADMIN))],
         [KeyboardButton(f"{button_label(BTN_BOARD_CURRENCY)} [{board_currency()}]"),
          KeyboardButton(button_label(BTN_REFERRAL_REWARD))],
         [KeyboardButton(f"{button_label(BTN_WITHDRAW_TOGGLE)} [{wd_status}]"),
          KeyboardButton(f"{button_label(BTN_MIN_WITHDRAW)} [{min_label}]")],
         [KeyboardButton(button_label(BTN_WITHDRAW_METHODS)),
          KeyboardButton(button_label(BTN_NUMBER_VALID_TIME))],
         [KeyboardButton(button_label(BTN_BACK_ADMIN))]],
        resize_keyboard=True
    )

def user_keyboard(show_live_traffic=None):
    """Build the user menu with optional Live Traffic and leaderboard buttons.

    Admins always receive the Live Traffic button so they can turn the public
    view back on even after hiding it from ordinary users.
    """
    if show_live_traffic is None:
        show_live_traffic = get_setting("live_traffic_user_enabled", "1") == "1"
    show_leaderboard = leaderboard_is_enabled()

    buttons = [
        user_panel_button(BTN_GET_NUMBER),
        user_panel_button(BTN_AVAIL),
    ]
    if show_live_traffic:
        buttons.append(user_panel_button(BTN_LIVE_TRAFFIC))
    buttons.append(user_panel_button(BTN_BALANCE))
    if show_leaderboard:
        buttons.append(user_panel_button(BTN_LEADERBOARD))
    buttons.extend([
        user_panel_button(BTN_REFER_EARN),
        user_panel_button(BTN_SUPPORT),
    ])
    rows = [buttons[index:index + 2] for index in range(0, len(buttons), 2)]
    return ReplyKeyboardMarkup(rows, resize_keyboard=True)

def balance_inline():
    withdraw_enabled = get_setting("withdraw_enabled", "1") == "1"
    withdraw_status = "ON" if withdraw_enabled else "OFF"
    withdraw_icon = (
        EMOJI_TO_PREMIUM_ID["💸"]
        if withdraw_enabled
        else EMOJI_TO_PREMIUM_ID["🚫"]
    )
    return InlineKeyboardMarkup([
        [InlineKeyboardButton(
            f"Withdraw [{withdraw_status}]",
            callback_data="bal_withdraw",
            icon_custom_emoji_id=withdraw_icon,
        )],
    ])

def links_keyboard():
    otp_group_ids = get_otp_group_ids()
    group_status = (
        f"✅ {len(otp_group_ids)} set" if otp_group_ids else "❌ Not set"
    )
    force_join_status = _force_join_status_label()
    return ReplyKeyboardMarkup(
        [[KeyboardButton(button_label(BTN_SUPPORT_LINK)), KeyboardButton(button_label(BTN_OTP_LINK))],
         [KeyboardButton(button_label(BTN_GET_NUMBER_LINK)), KeyboardButton(button_label(BTN_CHANNEL_LINK))],
         [KeyboardButton(f"{button_label(BTN_FORCE_JOIN)} [{force_join_status}]"),
          KeyboardButton(f"{button_label(BTN_OTP_GROUP_CHAT)} [{group_status}]")],
         [KeyboardButton(button_label(BTN_OTP_DEMO_SEND))],
         [KeyboardButton(button_label(BTN_BACK_ADMIN))]],
        resize_keyboard=True
    )

def get_number_services():
    return db_query(
        """
        SELECT s.id, s.name, s.emoji_entities, COUNT(DISTINCT CASE WHEN n.used=0 THEN n.id END) AS cnt
        FROM services s
        LEFT JOIN service_countries sc ON sc.service_id=s.id
        LEFT JOIN countries c ON c.id=sc.country_id AND c.active=1
        LEFT JOIN numbers n ON n.country_id=c.id
        WHERE s.active=1
        GROUP BY s.id, s.name, s.emoji_entities
        HAVING COUNT(DISTINCT CASE WHEN n.used=0 THEN n.id END) > 0
        ORDER BY s.name COLLATE NOCASE
        """
    )

def get_number_countries(service_id: int):
    return db_query(
        """
        SELECT c.id, c.name, c.emoji_entities, COUNT(n.id) AS cnt
        FROM service_countries sc
        JOIN countries c ON c.id=sc.country_id AND c.active=1
        JOIN numbers n ON n.country_id=c.id AND n.used=0
        WHERE sc.service_id=?
        GROUP BY c.id, c.name, c.emoji_entities
        HAVING cnt > 0
        ORDER BY c.name COLLATE NOCASE
        """,
        (service_id,),
    )

def get_available_service_countries():
    """Return only mapped service/country pairs with at least one free number."""
    return db_query(
        """
        SELECT
            s.id AS service_id,
            s.name AS service_name,
            s.emoji_entities AS service_emoji_entities,
            c.id AS country_id,
            c.name AS country_name,
            c.emoji_entities AS country_emoji_entities,
            COALESCE(sc.amount, c.price, 0) AS country_price,
            COUNT(n.id) AS available_count
        FROM service_countries sc
        JOIN services s
          ON s.id=sc.service_id AND s.active=1
        JOIN countries c
          ON c.id=sc.country_id AND c.active=1
        JOIN numbers n
          ON n.country_id=c.id AND n.used=0
        GROUP BY
            s.id, s.name, s.emoji_entities,
            c.id, c.name, c.emoji_entities, sc.amount, c.price
        HAVING COUNT(n.id) > 0
        ORDER BY s.name COLLATE NOCASE, c.name COLLATE NOCASE
        """
    )

def available_country_text():
    """Format the user-facing service → country availability list."""
    rows = get_available_service_countries()
    lines = ["🌍 <b>Available Country</b>", ""]
    if not rows:
        lines.append("No country is available right now.")
        return "\n".join(lines)

    current_service_id = None
    for row in rows:
        service = {
            "name": row["service_name"],
            "emoji_entities": row["service_emoji_entities"],
        }
        country = {
            "name": row["country_name"],
            "emoji_entities": row["country_emoji_entities"],
        }
        if row["service_id"] != current_service_id:
            if current_service_id is not None:
                lines.append("")
            lines.append(f" <b>{service_display_html(service)}</b>")
            lines.append("")
            current_service_id = row["service_id"]
        lines.append(
            f" {country_display_html(country)} | "
            f"<b>{format_currency_price(row['country_price'])}</b>"
        )
    return "\n".join(lines)

def reset_number_country_markup(countries):
    """Build the admin reset-country picker with two countries per row."""
    rows = []
    for i in range(0, len(countries), 2):
        rows.append([
            InlineKeyboardButton(
                f"{country_button_name(country)} "
                f"({int(country['total'])})",
                callback_data=f"rstn_country_{country['id']}",
                icon_custom_emoji_id=country_icon_custom_emoji_id(country),
            )
            for country in countries[i:i + 2]
        ])
    rows.append([InlineKeyboardButton("❌ Cancel", callback_data="rstn_cancel")])
    return InlineKeyboardMarkup(rows)

def cancel_inline():
    return InlineKeyboardMarkup([[InlineKeyboardButton("❌ Cancel", callback_data="cancel_input")]])

# ─── SERVICE MAP ──────────────────────────────────────────────────────────────
def service_map_country_markup(service_id: int):
    """Show every active country and mark whether it is mapped to a service."""
    countries = db_query(
        """
        SELECT c.id, c.name, c.emoji_entities,
               CASE WHEN sc.id IS NULL THEN 0 ELSE 1 END AS mapped
        FROM countries c
        LEFT JOIN service_countries sc
          ON sc.country_id=c.id AND sc.service_id=?
        WHERE c.active=1
        ORDER BY c.name COLLATE NOCASE
        """,
        (service_id,),
    )
    rows = [
        [InlineKeyboardButton(
            f"{'✅' if country['mapped'] else '➕'} "
            f"{country_button_name(country)}",
            callback_data=f"service_map_country_{service_id}_{country['id']}",
            icon_custom_emoji_id=country_icon_custom_emoji_id(country),
        )]
        for country in countries
    ]
    rows.append([
        InlineKeyboardButton("📋 Copy Service Name", callback_data=f"service_map_copy_{service_id}"),
    ])
    rows.append([
        InlineKeyboardButton("⬅️ Back to Service Management", callback_data="service_map_back"),
    ])
    return InlineKeyboardMarkup(rows)

def _service_map_menu_texts():
    """Buttons that should cancel the map input and continue normal navigation."""
    return {
        BTN_COUNTRY_MGMT, BTN_BACK_ADMIN, BTN_USER_MGMT, BTN_BROADCAST,
        BTN_LINKS, BTN_STATS, BTN_PANELS, BTN_ADD_COUNTRY, BTN_ADD_NUMBER,
        BTN_COUNTRY_PRICE, BTN_NUM_PER_USER, BTN_ADD_SERVICE,
        BTN_SERVICE_MANAGE, BTN_SERVICE, BTN_BACK_COUNTRY_MGMT,
        BTN_RESET_NUMBER,
    }

def _resolve_service_country(raw_text: str, create_service: bool = False):
    """
    Resolve a command such as 'WhatsApp Bangladesh'.
    Countries are matched from the end, allowing service and country names
    themselves to contain spaces.
    """
    cleaned = " ".join(raw_text.strip().split())
    normalized = cleaned.casefold()
    if not normalized:
        return None, None, None

    countries = db_query(
        "SELECT id, name, price, emoji_entities FROM countries "
        "WHERE active=1 ORDER BY LENGTH(name) DESC"
    )
    for country in countries:
        country_names = {
            " ".join(str(country["name"]).split()).casefold(),
            copyable_country_name(country).casefold(),
        }
        matched_country_name = next(
            (name for name in country_names if normalized.endswith(f" {name}")),
            None,
        )
        if not matched_country_name:
            continue

        service_name = cleaned[:-(len(matched_country_name) + 1)].strip()
        if not service_name:
            continue

        service = _find_service_by_input(service_name)
        if service:
            return service, country, service_name

        if create_service:
            existing = _find_service_by_input(service_name, active_only=False)
            if existing:
                if not existing["active"]:
                    db_execute(
                        "UPDATE services SET active=1 WHERE id=?",
                        (existing["id"],)
                    )
                return existing, country, service_name
            try:
                db_execute("INSERT INTO services (name) VALUES (?)", (service_name,))
            except sqlite3.IntegrityError:
                pass
            services = db_query(
                "SELECT id, name, active, emoji_entities FROM services "
                "WHERE active=1 AND lower(name)=lower(?)",
                (service_name,)
            )
            if services:
                return services[0], country, service_name
    return None, None, None

# ─── MISC HELPERS ─────────────────────────────────────────────────────────────
def normalize_phone_number(value):
    """Return one canonical digit-only representation for a phone number."""
    text = str(value or "").strip()
    digits = re.sub(r"\D", "", text)
    if not 7 <= len(digits) <= 15:
        return ""
    return digits


def normalize_unique_numbers(values):
    """Drop headers, malformed values, and duplicate phone numbers."""
    result = []
    seen = set()
    for value in values:
        number = normalize_phone_number(value)
        if not number or number in seen:
            continue
        seen.add(number)
        result.append(number)
    return result


def repair_number_inventory(conn):
    """Canonicalize legacy numbers and retain at most one row per number."""
    rows = conn.execute(
        "SELECT id, number, assigned_uid FROM numbers ORDER BY id"
    ).fetchall()
    kept = {}
    for row in rows:
        raw = str(row["number"] or "").strip()
        canonical = normalize_phone_number(raw)
        normalized = canonical or raw
        if not normalized and row["assigned_uid"] is None:
            conn.execute("DELETE FROM numbers WHERE id=?", (row["id"],))
            continue

        previous = kept.get(normalized)
        if previous is not None:
            current_assigned = previous["assigned_uid"] is not None
            row_assigned = row["assigned_uid"] is not None
            # Preserve an assigned row over an unused duplicate. If both are
            # assigned, keep the oldest row and prevent double crediting.
            if row_assigned and not current_assigned:
                conn.execute("DELETE FROM numbers WHERE id=?", (previous["id"],))
                kept[normalized] = row
            else:
                conn.execute("DELETE FROM numbers WHERE id=?", (row["id"],))
            continue

        if canonical and raw != canonical:
            conn.execute(
                "UPDATE numbers SET number=? WHERE id=?",
                (canonical, row["id"]),
            )
        kept[normalized] = row

    conn.execute(
        "CREATE UNIQUE INDEX IF NOT EXISTS idx_numbers_unique_number "
        "ON numbers(number)"
    )


def parse_txt(data):
    return [l.strip() for l in data.decode("utf-8", errors="ignore").splitlines() if l.strip()]

def parse_csv(data):
    reader = csv.reader(io.StringIO(data.decode("utf-8", errors="ignore")))
    return [cell.strip() for row in reader for cell in row if cell.strip()]

def parse_excel(data):
    wb = openpyxl.load_workbook(io.BytesIO(data), read_only=True, data_only=True)
    nums = []
    try:
        for ws in wb.worksheets:
            for row in ws.iter_rows(values_only=True):
                for cell in row:
                    if cell is not None:
                        n = str(cell).strip()
                        if n and n.lower() not in ("none", ""):
                            nums.append(n)
    finally:
        wb.close()
    return nums

async def notify_admin(bot, text: str, reply_markup=None):
    """Send a notification to all super-admins."""
    for sa_uid in SUPER_ADMINS:
        try:
            await bot.send_message(
                chat_id=sa_uid, text=text, parse_mode="HTML",
                reply_markup=reply_markup
            )
        except Exception:
            pass

# ─── /start ──────────────────────────────────────────────────────────────────
async def start(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    await delete_incoming_message(update)
    # Channel posts have no effective_user — just ignore silently
    if update.effective_user is None:
        return
    user = update.effective_user
    is_new = len(db_query("SELECT uid FROM users WHERE uid=?", (user.id,))) == 0
    register_user(user)
    ctx.user_data.clear()

    if is_banned(user.id):
        await update.message.reply_text("🚫 You have been banned from using this bot.")
        return

    if not await enforce_force_join_message(update, ctx):
        return

    # Load the configured sponsor flag pack before rendering any country UI.
    await refresh_flag_emoji_pack(ctx.bot)

    # ── Process referral link (/start ref_XXXXX) ─────────────────────────────
    args = ctx.args
    if is_new and args and args[0].startswith("ref_"):
        try:
            referrer_uid = int(args[0][4:])
        except ValueError:
            referrer_uid = None
        if referrer_uid and referrer_uid != user.id:
            referrer_exists = db_query("SELECT uid FROM users WHERE uid=?", (referrer_uid,))
            if referrer_exists:
                db_execute(
                    "UPDATE users SET referred_by=? WHERE uid=?",
                    (referrer_uid, user.id)
                )
                db_execute(
                    "UPDATE users SET referral_count=referral_count+1 WHERE uid=?",
                    (referrer_uid,)
                )
                db_execute(
                    """
                    INSERT INTO leaderboard_events
                        (uid, event_type, related_uid, occurred_at)
                    VALUES (?, 'referral', ?, ?)
                    """,
                    (
                        referrer_uid,
                        user.id,
                        leaderboard_event_timestamp(),
                    ),
                )

    if is_admin(user.id):
        await update.message.reply_text(
            USER_PANEL_WELCOME_TEXT,
            parse_mode="HTML", reply_markup=admin_keyboard()
        )
    else:
        await update.message.reply_text(
                USER_PANEL_WELCOME_TEXT,
                parse_mode="HTML",
                reply_markup=user_keyboard(),
            )

# ─── /userpanel ──────────────────────────────────────────────────────────────
async def userpanel_cmd(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    await delete_incoming_message(update)
    if update.effective_user is None:
        return
    user = update.effective_user
    if not is_admin(user.id):
        await update.message.reply_text("❌ This command is for admins only.")
        return
    await refresh_flag_emoji_pack(ctx.bot)
    ctx.user_data.clear()
    await update.message.reply_text(
        USER_PANEL_WELCOME_TEXT,
        parse_mode="HTML", reply_markup=user_keyboard(show_live_traffic=True)
    )

# ─── /users ──────────────────────────────────────────────────────────────────
async def users_cmd(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    await delete_incoming_message(update)
    uid = update.effective_user.id
    if not is_admin(uid):
        await update.message.reply_text("❌ Access denied.")
        return
    await send_user_list(update.message.reply_text)

def build_user_excel() -> tuple[io.BytesIO, int]:
    """Generate an Excel file with all users and return as BytesIO."""
    users = db_query(
        """
        SELECT u.uid, u.username, u.first_name, u.balance, u.banned,
               u.otp_count, u.referral_earnings, u.joined_at,
               COALESCE(invited.total_invited, 0) AS total_invited,
               COALESCE(qualified.qualified_referrals, 0) AS qualified_referrals
        FROM users u
        LEFT JOIN (
            SELECT referred_by, COUNT(*) AS total_invited
            FROM users
            WHERE referred_by IS NOT NULL
            GROUP BY referred_by
        ) invited ON invited.referred_by=u.uid
        LEFT JOIN (
            SELECT referred_by, COUNT(*) AS qualified_referrals
            FROM users
            WHERE referred_by IS NOT NULL AND referral_qualified=1
            GROUP BY referred_by
        ) qualified ON qualified.referred_by=u.uid
        ORDER BY u.joined_at DESC
        """
    )
    wb = openpyxl.Workbook()
    ws = wb.active
    ws.title = "Users"

    # Header row
    headers = [
        "User ID", "Username", "Name", "Balance ($)", "Banned", "OTP Count",
        "Total Invited", "Qualified Referrals", "Referral Earnings ($)",
        "Referral Earnings (৳)", "Joined At",
    ]
    for col, h in enumerate(headers, 1):
        cell = ws.cell(row=1, column=col, value=h)
        cell.font = openpyxl.styles.Font(bold=True)
        cell.fill = openpyxl.styles.PatternFill("solid", fgColor="4472C4")
        cell.font = openpyxl.styles.Font(bold=True, color="FFFFFF")

    # Data rows
    for row_idx, u in enumerate(users, 2):
        ws.cell(row=row_idx, column=1, value=u["uid"])
        ws.cell(row=row_idx, column=2, value=f"@{u['username']}" if u["username"] else "")
        ws.cell(row=row_idx, column=3, value=u["first_name"] or "")
        ws.cell(row=row_idx, column=4, value=round(u["balance"], 2))
        ws.cell(row=row_idx, column=5, value="Yes" if u["banned"] else "No")
        ws.cell(row=row_idx, column=6, value=u["otp_count"] or 0)
        ws.cell(row=row_idx, column=7, value=u["total_invited"] or 0)
        ws.cell(row=row_idx, column=8, value=u["qualified_referrals"] or 0)
        earnings = round(float(u["referral_earnings"] or 0), 4)
        ws.cell(row=row_idx, column=9, value=earnings)
        ws.cell(row=row_idx, column=10, value=round(earnings * USD_TO_BDT, 2))
        ws.cell(row=row_idx, column=11, value=u["joined_at"][:19] if u["joined_at"] else "")

    # Summary row
    summary_row = len(users) + 3
    ws.cell(row=summary_row, column=1, value="TOTAL USERS").font = openpyxl.styles.Font(bold=True)
    ws.cell(row=summary_row, column=2, value=len(users))
    ws.cell(row=summary_row + 1, column=1, value="TOTAL BALANCE").font = openpyxl.styles.Font(bold=True)
    ws.cell(row=summary_row + 1, column=2, value=round(sum(u["balance"] for u in users), 2))
    ws.cell(row=summary_row + 2, column=1, value="BANNED").font = openpyxl.styles.Font(bold=True)
    ws.cell(row=summary_row + 2, column=2, value=sum(1 for u in users if u["banned"]))

    # Column widths
    for col, width in zip(
        "ABCDEFGHIJK",
        [14, 18, 20, 14, 10, 12, 14, 18, 20, 22, 20],
    ):
        ws.column_dimensions[col].width = width

    buf = io.BytesIO()
    wb.save(buf)
    buf.seek(0)
    return buf, len(users)


def build_user_data_zip() -> tuple[io.BytesIO, int]:
    """Package the user workbook and both active JSON databases together."""
    excel_buf, total = build_user_excel()
    json_files = build_json_database_files()
    archive = io.BytesIO()
    with zipfile.ZipFile(archive, "w", compression=zipfile.ZIP_DEFLATED) as zf:
        excel_buf.seek(0)
        zf.writestr(
            f"users_{_dt.datetime.now().strftime('%Y%m%d_%H%M')}.xlsx",
            excel_buf.read(),
        )
        zf.writestr("users.json", json_files["users.json"])
        zf.writestr("numbers.json", json_files["numbers.json"])
    archive.seek(0)
    return archive, total


def get_referral_stats(uid: int):
    """Return live referral totals for a user from referred user records."""
    rows = db_query(
        """
        SELECT
            (SELECT COUNT(*) FROM users invited WHERE invited.referred_by=?) AS total_invited,
            (SELECT COUNT(*) FROM users qualified
             WHERE qualified.referred_by=? AND qualified.referral_qualified=1)
             AS qualified_referrals,
            COALESCE((SELECT referral_earnings FROM users WHERE uid=?), 0)
             AS referral_earnings
        """,
        (uid, uid, uid),
    )
    row = rows[0] if rows else None
    return (
        int(row["total_invited"] or 0) if row else 0,
        int(row["qualified_referrals"] or 0) if row else 0,
        float(row["referral_earnings"] or 0) if row else 0.0,
    )


async def build_referral_panel(bot, uid: int):
    """Build the public referral panel using the current live rules."""
    total_invited, qualified_referrals, referral_earnings = get_referral_stats(uid)
    bot_info = await bot.get_me()
    ref_link = f"https://t.me/{bot_info.username}?start=ref_{uid}"
    reward = referral_qualified_reward()
    qualification = referral_qualification_otps()
    commission = referral_otp_commission_rate() * 100
    text = (
        "🎁<b>REFERRAL BONUS</b>\n"
        "━━━━━━━━━━━━━━━━━━\n"
        f"🔥 {format_currency(reward)} per successful referral\n"
        f"💸{commission:.2f}% commission on every OTP reward from qualification\n\n"
        f"📍 <b>Rule:</b> Credited after referred user receives "
        f"{qualification} OTPs.\n"
        "✅ Anti-fake verification protection active.\n\n"
        "━━━━━━━━━━━━━━━━━━\n"
        "🔗<b>Your Referral Link:</b>\n"
        f"<code>{_html.escape(ref_link)}</code>\n"
        f"💸 You earn {commission:.2f}% from the qualifying OTP and every OTP after it.\n"
        f"💬 Total Invited: <b>{total_invited}</b>\n"
        f"✅ Qualified ({qualification}+ OTPs): <b>{qualified_referrals}</b>\n"
        f"💰 Referral Earnings: <b>{format_currency(referral_earnings, 4)}</b>\n"
        "━━━━━━━━━━━━━━━━━━"
    )
    buttons = [InlineKeyboardButton(
        "Copy Referral Link",
        copy_text=CopyTextButton(text=ref_link),
        icon_custom_emoji_id="6068727156467309816",
    )]
    if leaderboard_is_enabled() or is_admin(uid):
        buttons.append(InlineKeyboardButton(
            "Top 10 Referrers",
            callback_data="top_referrals",
            icon_custom_emoji_id=LEADERBOARD_PREMIUM_EMOJI_ID,
        ))
    markup = InlineKeyboardMarkup([buttons])
    return text, markup


def build_top_referrals_panel(uid: int, admin_view: bool = False):
    """Rank users by referrals gained during the current Friday-to-Friday week."""
    week_start, week_end = leaderboard_active_period()
    rows = weekly_referral_leaderboard_rows(week_start, week_end)
    lines = [
        "🏆 <b>WEEKLY TOP 10 REFERRERS</b>",
        "━━━━━━━━━━━━━━━━━━",
        f"UTC period: <code>{week_start}</code> – <code>{week_end}</code>",
        "Shows total referrals, valid referrals, referral earnings, and current balance.",
        "",
    ]
    if not rows:
        lines.append("📭 No referrals have been received this UTC week.")
    else:
        for index, row in enumerate(rows, 1):
            name = _leaderboard_identity(row, admin_view)
            valid_referrals = int(row["valid_referrals"] or 0)
            total_invited = int(row["total_invited"] or 0)
            earnings = float(row["referral_earnings"] or 0)
            balance = float(row["balance"] or 0)
            lines.append(
                f"<b>{index}.</b> {name}\n"
                f"   👥 Total referrals: <b>{total_invited}</b> "
                f"| ✅ Valid: <b>{valid_referrals}</b>\n"
                f"   🎁 Referral earnings: <b>{format_currency(earnings, 4)}</b> "
                f"| 💰 Balance: <b>{format_currency(balance)}</b>"
            )
    lines.extend([
        "━━━━━━━━━━━━━━━━━━",
    ])
    back_button = InlineKeyboardButton(
        "Back to Referral",
        callback_data="referral_panel",
        icon_custom_emoji_id=GET_NUMBER_BACK_EMOJI_ID,
    )
    markup_rows = [[back_button]]
    if admin_view:
        markup_rows.append([
            InlineKeyboardButton("⚙️ Back to Settings", callback_data="settings_panel")
        ])
    markup = InlineKeyboardMarkup(markup_rows)
    return "\n".join(lines), markup


def build_add_balance_user_zip(
    profile,
    total_invited: int,
    qualified_referrals: int,
    referral_earnings: float,
    withdrawal_totals: dict,
    recent_withdrawals,
) -> io.BytesIO:
    """Package the Add Balance user summary and the last three withdrawals."""
    uid = int(profile["uid"])
    summary = {
        "uid": uid,
        "first_name": profile["first_name"],
        "username": profile["username"],
        "balance": float(profile["balance"] or 0),
        "banned": bool(profile["banned"]),
        "otp_count": int(profile["otp_count"] or 0),
        "joined_at": profile["joined_at"],
        "referrals": {
            "total": total_invited,
            "qualified": qualified_referrals,
            "earnings": referral_earnings,
        },
        "withdrawals": {
            status: {
                "count": count,
                "amount": amount,
            }
            for status, (count, amount) in withdrawal_totals.items()
        },
        "recent_withdrawals_limit": 3,
    }
    recent_rows = []
    for row in recent_withdrawals:
        wallet_full = str(row["wallet"] or "")
        recent_rows.append({
            "id": int(row["id"]),
            "amount": float(row["amount"] or 0),
            "status": str(row["status"] or "unknown"),
            "wallet": wallet_full,
            "wallet_address": withdraw_wallet_value(wallet_full),
            "created_at": row["created_at"],
        })
    summary["recent_withdrawals"] = recent_rows

    archive = io.BytesIO()
    with zipfile.ZipFile(archive, "w", compression=zipfile.ZIP_DEFLATED) as zf:
        zf.writestr(
            "user_details.json",
            json.dumps(summary, ensure_ascii=False, indent=2, default=str),
        )
        csv_buffer = io.StringIO()
        writer = csv.DictWriter(
            csv_buffer,
            fieldnames=[
                "request_id",
                "status",
                "amount",
                "wallet",
                "wallet_address",
                "created_at",
            ],
        )
        writer.writeheader()
        for row in recent_rows:
            writer.writerow({
                "request_id": row["id"],
                "status": row["status"],
                "amount": f"{row['amount']:.2f}",
                "wallet": row["wallet"],
                "wallet_address": row["wallet_address"],
                "created_at": row["created_at"] or "",
            })
        zf.writestr("recent_withdrawals_last_3.csv", csv_buffer.getvalue())
        zf.writestr(
            "README.txt",
            (
                "Add Balance user details export.\n"
                "user_details.json contains the profile, referral, balance, "
                "withdrawal summary, and the latest three withdrawal requests.\n"
                "recent_withdrawals_last_3.csv contains the same latest three "
                "requests in spreadsheet-friendly format.\n"
            ),
        )
    archive.seek(0)
    return archive


async def send_user_list(reply_fn):
    """Legacy: just sends a quick summary text (used by /users cmd)."""
    users = db_query("SELECT uid, username, first_name, balance, banned, joined_at FROM users ORDER BY joined_at DESC")
    if not users:
        await reply_fn("📭 No users found.")
        return
    total_balance = sum(u["balance"] for u in users)
    total_banned  = sum(1 for u in users if u["banned"])
    lines = [
        "👥 <b>User Summary</b>",
        f"Total: <b>{len(users)}</b> | Banned: <b>{total_banned}</b> | Balance Pool: <b>{format_currency(total_balance)}</b>"
    ]
    await reply_fn("\n".join(lines), parse_mode="HTML")

# ─── DOCUMENT HANDLER ────────────────────────────────────────────────────────
async def document_handler(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    uid   = update.effective_user.id
    state = ctx.user_data.get("state", "")
    if not (is_admin(uid) and state == "add_number_file"):
        return

    await delete_incoming_message(update)
    doc  = update.message.document
    name = (doc.file_name or "").lower()
    if not any(name.endswith(e) for e in (".txt", ".csv", ".xlsx")):
        await update.message.reply_text(
            "❌ Only <b>.txt</b>, <b>.csv</b>, or <b>.xlsx</b> files are supported.",
            parse_mode="HTML"
        )
        return
    if doc.file_size and doc.file_size > MAX_NUMBER_UPLOAD_BYTES:
        await update.message.reply_text(
            f"❌ File size cannot exceed {MAX_NUMBER_UPLOAD_BYTES // (1024 * 1024)} MB.",
            parse_mode="HTML",
        )
        return

    country_id   = ctx.user_data.get("country_id")
    country_name = ctx.user_data.get("country_name", "")
    wait_msg     = await update.message.reply_text("⏳ Processing file...")

    try:
        raw = bytes(await (await doc.get_file()).download_as_bytearray())
        if name.endswith(".txt"):
            numbers = parse_txt(raw)
        elif name.endswith(".csv"):
            numbers = parse_csv(raw)
        else:
            numbers = parse_excel(raw)

        numbers = normalize_unique_numbers(numbers)
        if not numbers:
            await wait_msg.edit_text("⚠️ No numbers found in the file.")
            return
        if len(numbers) > MAX_NUMBERS_PER_UPLOAD:
            await wait_msg.edit_text(
                f"❌ A single upload may contain at most {MAX_NUMBERS_PER_UPLOAD:,} unique numbers."
            )
            return

        count = db_insert_many(
            "INSERT OR IGNORE INTO numbers (country_id, number) VALUES (?, ?)",
            [(country_id, n) for n in numbers]
        )
        await wait_msg.edit_text(
            f"✅ <b>{count}</b> numbers added to <b>{country_name}</b>!\n"
            f"📄 File: <code>{doc.file_name}</code>",
            parse_mode="HTML"
        )
        await update.message.reply_text("🌍 Country Management:", reply_markup=country_mgmt_keyboard())
    except Exception as e:
        logger.exception("File parse error")
        await wait_msg.edit_text(f"❌ An error occurred:\n<code>{e}</code>", parse_mode="HTML")

    ctx.user_data.clear()

# ─── TEXT HANDLER ─────────────────────────────────────────────────────────────
async def text_handler(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    await delete_incoming_message(update)
    text  = resolve_button_text(update.message.text.strip())
    uid   = update.effective_user.id
    state = ctx.user_data.get("state", "")

    if is_banned(uid):
        await update.message.reply_text("🚫 You have been banned.")
        return

    if not await enforce_force_join_message(update, ctx):
        return

    # ── NAVIGATION ALWAYS WINS ────────────────────────────────────────────────
    # Any reply-keyboard navigation button must clear whatever input state is
    # active before falling through to the normal routing below.  Without this
    # block, states like set_min_withdraw intercept every text message and show
    # "Enter a valid amount…" even when the user presses a menu button.
    _NAV_BTNS = {
        BTN_BACK_ADMIN, BTN_COUNTRY_MGMT, BTN_USER_MGMT, BTN_BROADCAST,
        BTN_LINKS, BTN_STATS, BTN_PANELS, BTN_ADD_COUNTRY, BTN_ADD_NUMBER,
        BTN_COUNTRY_PRICE, BTN_NUM_PER_USER, BTN_SERVICE_MANAGE, BTN_SERVICE,
        BTN_ADD_SERVICE, BTN_BACK_COUNTRY_MGMT, BTN_RESET_NUMBER,
        BTN_USER_LIST, BTN_WITHDRAWALS,
        BTN_ADD_ADMIN, BTN_REMOVE_ADMIN, BTN_ADD_BALANCE, BTN_REFERRAL_REWARD,
        BTN_BOARD_CURRENCY,
        BTN_WITHDRAW_METHODS, BTN_NUMBER_VALID_TIME,
        BTN_SUPPORT_LINK, BTN_OTP_LINK, BTN_GET_NUMBER_LINK,
        BTN_CHANNEL_LINK, BTN_FORCE_JOIN, BTN_OTP_GROUP_CHAT, BTN_OTP_DEMO_SEND,
        BTN_PANEL_ADD, BTN_LAST_MSGS,
        BTN_BACK_PANELS, BTN_BACK_USER_MGMT,
        BTN_GET_NUMBER, BTN_AVAIL, BTN_LIVE_TRAFFIC, BTN_BALANCE,
        BTN_LEADERBOARD, BTN_SETTINGS, BTN_REFER_EARN, BTN_SUPPORT,
    }
    _nav_labels = {button_label(b) for b in _NAV_BTNS}
    _is_nav = (
        text in _nav_labels
        or any(
                text.startswith(f"{button_label(b)} [")
                or (b == BTN_BOARD_CURRENCY and text.startswith(f"{b} ["))
                for b in (
                    BTN_WITHDRAW_TOGGLE,
                    BTN_MIN_WITHDRAW,
                    BTN_FORCE_JOIN,
                    BTN_OTP_GROUP_CHAT,
                    BTN_BOARD_CURRENCY,
                )
        )
    )
    if state and _is_nav:
        ctx.user_data.clear()
        state = ""

    # Navigation buttons must always win over an active input wizard.  Without
    # this early route, a reply-keyboard click such as Service Management can
    # be consumed by the previous Service Map/Country/Price state first.
    if is_admin(uid):
        if text == BTN_SERVICE_MANAGE or text == BTN_SERVICE:
            ctx.user_data.clear()
            ctx.user_data["state"] = "service_manage_mode"
            await update.message.reply_text(
                service_manage_text(),
                parse_mode="HTML",
            )
            return

        if text == BTN_ADD_SERVICE:
            ctx.user_data.clear()
            ctx.user_data["state"] = "service_manage_mode"
            await update.message.reply_text(
                service_manage_text(),
                parse_mode="HTML",
            )
            return

    # ── COUNTRY MANAGEMENT (text-based) ───────────────────────────────────────
    if state == "country_mgmt_mode" and is_admin(uid):
        if text in (BTN_BACK_ADMIN, BTN_COUNTRY_MGMT, BTN_ADD_NUMBER,
                    BTN_COUNTRY_PRICE, BTN_NUM_PER_USER, BTN_RESET_NUMBER,
                    BTN_BROADCAST, BTN_USER_MGMT):
            pass
        else:
            cname = _country_delete_name(text)
            if cname is None:
                # Keep the original Telegram text and custom-emoji entities so
                # the same premium emoji can be rendered later in the user panel.
                cname = update.message.text.strip()
                emoji_entities = _message_custom_emoji_entities(update.message)
                # Clean up rows left behind by the old soft-delete behavior so
                # a country can be added again with exactly the same name.
                _purge_inactive_country_by_name(cname)
                try:
                    db_execute(
                        "INSERT INTO countries (name, emoji_entities) VALUES (?, ?)",
                        (cname, emoji_entities),
                    )
                    extra = f"✅ <b>{_html.escape(cname)}</b> has been added!"
                except sqlite3.IntegrityError:
                    if emoji_entities:
                        db_execute(
                            "UPDATE countries SET emoji_entities=? "
                            "WHERE name=? AND active=1",
                            (emoji_entities, cname),
                        )
                    extra = f"⚠️ <b>{_html.escape(cname)}</b> already exists."
                await update.message.reply_text(
                    country_list_text(extra),
                    parse_mode="HTML",
                )
                return

            row = _find_country_by_input(cname)
            if row:
                _delete_country_permanently(row["id"])
                extra = (
                    f"✅ <b>{_html.escape(copyable_country_name(row))}</b> "
                    "has been permanently deleted!"
                )
            else:
                extra = f"❌ Country <b>{_html.escape(cname)}</b> not found."
            await update.message.reply_text(
                country_list_text(extra),
                parse_mode="HTML",
            )
            return

    # ── ADD WITHDRAW METHOD ───────────────────────────────────────────────────
    if state == "add_withdraw_method" and is_admin(uid):
        name = text.strip()
        if not name:
            await update.message.reply_text("❌ Name cannot be empty.", reply_markup=cancel_inline())
            return
        emoji_entities = _message_custom_emoji_entities(update.message)
        new_method = _normalize_withdraw_method({
            "name": name,
            "emoji_entities": emoji_entities,
        })
        methods = get_withdraw_methods()
        if any(
            name.casefold() in {
                withdraw_method_name(method).casefold(),
                withdraw_method_button_label(method).casefold(),
            }
            for method in methods
        ):
            await update.message.reply_text(
                f"⚠️ <b>{name}</b> already exists.",
                parse_mode="HTML", reply_markup=cancel_inline()
            )
            return
        methods.append(new_method)
        set_withdraw_methods(methods)
        ctx.user_data.clear()
        await update.message.reply_text(
            f"✅ {withdraw_method_html(new_method)} added as a withdraw method.",
            parse_mode="HTML", reply_markup=user_mgmt_keyboard()
        )
        return

    # ── SET MINIMUM WITHDRAW ──────────────────────────────────────────────────
    if state == "set_min_withdraw" and is_admin(uid):
        try:
            min_wd = parse_currency_input(text, allow_zero=True)
        except ValueError:
            await update.message.reply_text("❌ Enter a valid amount (e.g. <code>5</code> or <code>0</code> to remove limit)", parse_mode="HTML")
            return
        set_setting("min_withdraw", str(min_wd))
        ctx.user_data.clear()
        status = f"<b>{format_currency(min_wd)}</b>" if min_wd > 0 else "<b>No limit</b>"
        await update.message.reply_text(
            f"✅ <b>Minimum Withdraw Updated!</b>\n\n"
            f"💵 Minimum withdraw amount: {status}",
            parse_mode="HTML", reply_markup=user_mgmt_keyboard()
        )
        return

    # ── SET ASSIGNED NUMBER VALID TIME ────────────────────────────────────────
    if state == "set_number_valid_time" and is_admin(uid):
        try:
            if not re.fullmatch(r"\d+", text):
                raise ValueError
            valid_minutes = int(text)
            if not (
                MIN_NUMBER_VALID_TIME_MINUTES
                <= valid_minutes
                <= MAX_NUMBER_VALID_TIME_MINUTES
            ):
                raise ValueError
        except ValueError:
            await update.message.reply_text(
                "❌ Enter a whole number of minutes from "
                f"<code>{MIN_NUMBER_VALID_TIME_MINUTES}</code> to "
                f"<code>{MAX_NUMBER_VALID_TIME_MINUTES}</code>.",
                parse_mode="HTML",
                reply_markup=cancel_inline(),
            )
            return

        set_setting("number_valid_time_minutes", str(valid_minutes))
        ctx.user_data.clear()
        await update.message.reply_text(
            f"✅ <b>Number Valid Time Updated</b>\n\n"
            f"Assigned numbers stay valid for <b>{valid_minutes} minutes</b>.",
            parse_mode="HTML",
            reply_markup=user_mgmt_keyboard(),
        )
        return

    # ── SET REFERRAL REWARD ────────────────────────────────────────────────────
    if state == "set_referral_reward" and is_admin(uid):
        try:
            reward = parse_currency_input(text, allow_zero=True)
        except ValueError:
            await update.message.reply_text("❌ Enter a valid amount (e.g. <code>5</code> or <code>0</code> to disable)", parse_mode="HTML")
            return
        set_setting("referral_qualified_reward", str(reward))
        ctx.user_data.clear()
        status = f"<b>{format_currency(reward)}</b> per referral" if reward > 0 else "<b>Disabled</b> (0)"
        await update.message.reply_text(
            f"✅ <b>Referral Reward Updated!</b>\n\n"
            f"💎 Each qualified referral earns: {status}\n\n"
            f"Reward is credited after the referred user receives "
            f"{referral_qualification_otps()} OTPs.",
            parse_mode="HTML",
            reply_markup=referral_settings_markup()
        )
        return

    # ── SET REFERRAL QUALIFICATION THRESHOLD ───────────────────────────────────
    if state == "set_referral_qualification_otps" and is_admin(uid):
        try:
            qualification = int(text)
            if qualification < 1 or qualification > 100_000:
                raise ValueError
        except ValueError:
            await update.message.reply_text(
                "❌ Enter a whole number between <code>1</code> and "
                "<code>100000</code>.",
                parse_mode="HTML",
            )
            return
        set_setting("referral_qualification_otps", str(qualification))
        ctx.user_data.clear()
        await update.message.reply_text(
            f"✅ <b>Qualification Rule Updated!</b>\n\n"
            f"🎯 A referred user becomes active after "
            f"<b>{qualification} OTPs</b>.",
            parse_mode="HTML",
            reply_markup=referral_settings_markup(),
        )
        return

    # ── SET REFERRED USER OTP COMMISSION ───────────────────────────────────────
    if state == "set_referral_commission_rate" and is_admin(uid):
        try:
            commission_percent = float(text)
            if (
                commission_percent < 0
                or commission_percent > 100
                or not math.isfinite(commission_percent)
            ):
                raise ValueError
        except ValueError:
            await update.message.reply_text(
                "❌ Enter a percentage between <code>0</code> and "
                "<code>100</code> (example: <code>10</code>).",
                parse_mode="HTML",
            )
            return
        set_setting(
            "referral_otp_commission_rate",
            str(commission_percent / 100),
        )
        ctx.user_data.clear()
        await update.message.reply_text(
            f"✅ <b>User Commission Updated!</b>\n\n"
            f"💸 Referred users now receive "
            f"<b>{commission_percent:.2f}%</b> commission on every OTP reward.",
            parse_mode="HTML",
            reply_markup=referral_settings_markup(),
        )
        return

    # ── SET SUPPORT LINK ──────────────────────────────────────────────────────
    if state == "set_support_link" and is_admin(uid):
        link = text.strip()
        if not (link.startswith("http://") or link.startswith("https://") or link.startswith("t.me/")):
            await update.message.reply_text("❌ Enter a valid link (e.g. <code>https://t.me/group</code>)", parse_mode="HTML")
            return
        set_setting("support_link", link)
        ctx.user_data.clear()
        await update.message.reply_text(
            f"✅ <b>Support Link Updated!</b>\n\n🔗 <code>{link}</code>",
            parse_mode="HTML", reply_markup=links_keyboard()
        )
        return

    # ── SET OTP LINK ──────────────────────────────────────────────────────────
    if state == "set_otp_link" and is_admin(uid):
        link = text.strip()
        if not (link.startswith("http://") or link.startswith("https://") or link.startswith("t.me/")):
            await update.message.reply_text("❌ Enter a valid link (e.g. <code>https://t.me/group</code>)", parse_mode="HTML")
            return
        set_setting("otp_link", link)
        ctx.user_data.clear()
        await update.message.reply_text(
            f"✅ <b>OTP Link Updated!</b>\n\n🔗 <code>{link}</code>",
            parse_mode="HTML", reply_markup=links_keyboard()
        )
        return

    # ── SET GET NUMBER LINK ───────────────────────────────────────────────────
    if state == "set_get_number_link" and is_admin(uid):
        link = text.strip()
        if not (link.startswith("http://") or link.startswith("https://") or link.startswith("t.me/")):
            await update.message.reply_text(
                "❌ Enter a valid link (e.g. <code>https://t.me/yourbot</code>)",
                parse_mode="HTML",
            )
            return
        set_setting("get_number_link", link)
        ctx.user_data.clear()
        await update.message.reply_text(
            f"✅ <b>Get Number Link Updated!</b>\n\n🔗 <code>{_html.escape(link)}</code>",
            parse_mode="HTML", reply_markup=links_keyboard()
        )
        return

    # ── SET CHANNEL LINK ──────────────────────────────────────────────────────
    if state == "set_channel_link" and is_admin(uid):
        link = text.strip()
        if not (link.startswith("http://") or link.startswith("https://") or link.startswith("t.me/")):
            await update.message.reply_text(
                "❌ Enter a valid link (e.g. <code>https://t.me/yourchannel</code>)",
                parse_mode="HTML",
            )
            return
        set_setting("channel_link", link)
        ctx.user_data.clear()
        await update.message.reply_text(
            f"✅ <b>Channel Link Updated!</b>\n\n🔗 <code>{_html.escape(link)}</code>",
            parse_mode="HTML", reply_markup=links_keyboard()
        )
        return

    # ── ADD FORCE-JOIN CHANNEL ────────────────────────────────────────────────
    if state == "force_join_add_channel" and is_admin(uid):
        parts = [part.strip() for part in text.split("|")]
        if len(parts) == 1:
            value = parts[0].strip()
            if value.startswith(("http://", "https://", "t.me/")):
                if value.startswith("t.me/"):
                    value = f"https://{value}"
                username = value.rstrip("/").rsplit("/", 1)[-1]
                if not re.fullmatch(r"[A-Za-z0-9_]{5,32}", username):
                    await update.message.reply_text(
                        "❌ একটি public channel username বা channel link দিন।",
                        reply_markup=cancel_inline()
                    )
                    return
                chat_id = f"@{username}"
                invite_link = value
            else:
                username = value.lstrip("@")
                if not re.fullmatch(r"[A-Za-z0-9_]{5,32}", username):
                    await update.message.reply_text(
                        "❌ শুধু channel username দিন, যেমন "
                        "<code>@mychannel</code>।",
                        parse_mode="HTML", reply_markup=cancel_inline()
                    )
                    return
                chat_id = f"@{username}"
                invite_link = f"https://t.me/{username}"
            title = ""
        elif len(parts) in (2, 3):
            chat_id, invite_link = parts[0], parts[1]
            title = parts[2] if len(parts) == 3 else ""
        else:
            await update.message.reply_text(
                "❌ এই format-এ পাঠান:\n"
                "<code>@channelusername</code>\n"
                "অথবা\n"
                "<code>@channel | https://t.me/channel | Channel Name</code>",
                parse_mode="HTML", reply_markup=cancel_inline()
            )
            return

        if not (
            chat_id.startswith("@")
            or chat_id.lstrip("-").isdigit()
        ):
            await update.message.reply_text(
                "❌ Chat ID অবশ্যই <code>@channelusername</code> "
                "অথবা numeric channel ID হতে হবে।",
                parse_mode="HTML", reply_markup=cancel_inline()
            )
            return
        if invite_link.startswith("t.me/"):
            invite_link = f"https://{invite_link}"
        if not invite_link.startswith(("http://", "https://")):
            await update.message.reply_text(
                "❌ Valid Telegram invite link দিন।",
                reply_markup=cancel_inline()
            )
            return

        try:
            chat = await ctx.bot.get_chat(chat_id)
        except Exception as exc:
            logger.warning("Force-join channel validation failed: %s", exc)
            await update.message.reply_text(
                "❌ Channel পাওয়া যায়নি। Chat ID/link ঠিক আছে এবং বটটি "
                "channel-এর Admin কি না নিশ্চিত করুন।",
                parse_mode="HTML", reply_markup=cancel_inline()
            )
            return

        channels = get_force_join_channels()
        if any(channel["chat_id"] == chat_id for channel in channels):
            await update.message.reply_text(
                "⚠️ এই channel আগেই সেট করা আছে।",
                reply_markup=cancel_inline()
            )
            return

        channel_title = title or getattr(chat, "title", None) or chat_id
        channels.append({
            "chat_id": chat_id,
            "invite_link": invite_link,
            "title": channel_title,
        })
        set_force_join_channels(channels)
        if len(channels) == 1:
            set_setting("force_join_enabled", "1")
        ctx.user_data.clear()
        await update.message.reply_text(
            force_join_settings_text("✅ Force-join channel added and activated."),
            parse_mode="HTML",
            reply_markup=force_join_settings_markup(),
        )
        return

    # ── SET OTP GROUP CHAT IDS ─────────────────────────────────────────────────
    if state == "set_otp_group_id" and is_admin(uid):
        raw_value = text.strip()
        current_group_ids = get_otp_group_ids()
        lowered = raw_value.casefold()

        if lowered in {"clear", "clear all", "remove all", "none"}:
            set_otp_group_ids([])
            await update.message.reply_text(
                otp_group_settings_text("✅ সব OTP group সরানো হয়েছে."),
                parse_mode="HTML",
                reply_markup=links_keyboard(),
            )
            return

        if lowered.startswith(("remove ", "delete ")):
            removal_text = raw_value.split(maxsplit=1)[1]
            removal_values = [
                item.strip()
                for item in re.split(r"[,;\n]+", removal_text)
                if item.strip()
            ]
            invalid = [
                item for item in removal_values
                if _normalize_otp_group_id(item) is None
            ]
            if invalid:
                await update.message.reply_text(
                    "❌ সরানোর জন্য সঠিক Chat ID বা @username দিন।",
                    parse_mode="HTML",
                )
                return
            removal_set = set(
                _normalize_otp_group_id(item) for item in removal_values
            )
            updated_group_ids = [
                group_id
                for group_id in current_group_ids
                if group_id not in removal_set
            ]
            if len(updated_group_ids) == len(current_group_ids):
                await update.message.reply_text(
                    "❌ এই group তালিকায় পাওয়া যায়নি।\n\n"
                    + otp_group_settings_text(),
                    parse_mode="HTML",
                    reply_markup=cancel_inline(),
                )
                return
            set_otp_group_ids(updated_group_ids)
            ctx.user_data.clear()
            await update.message.reply_text(
                otp_group_settings_text("✅ Group সরানো হয়েছে."),
                parse_mode="HTML",
                reply_markup=links_keyboard(),
            )
            return

        candidate_values = [
            item.strip()
            for item in re.split(r"[,;\n]+", raw_value)
            if item.strip()
        ]
        normalized_candidates = [
            _normalize_otp_group_id(item) for item in candidate_values
        ]
        if (
            not candidate_values
            or any(group_id is None for group_id in normalized_candidates)
        ):
            await update.message.reply_text(
                "❌ Chat ID বা @username সঠিকভাবে দিন। একাধিক হলে কমা "
                "বা আলাদা লাইন ব্যবহার করুন।\n"
                "উদাহরণ: <code>-1001234567890</code> অথবা "
                "<code>@mygroupname</code>",
                parse_mode="HTML",
            )
            return

        merged_group_ids = current_group_ids[:]
        for group_id in normalized_candidates:
            if group_id not in merged_group_ids:
                merged_group_ids.append(group_id)
        if len(merged_group_ids) > MAX_OTP_GROUPS:
            await update.message.reply_text(
                f"❌ সর্বোচ্চ {MAX_OTP_GROUPS}টি OTP group রাখা যাবে।",
                parse_mode="HTML",
            )
            return

        set_otp_group_ids(merged_group_ids)
        ctx.user_data.clear()
        await update.message.reply_text(
            otp_group_settings_text(
                f"✅ {len(normalized_candidates)}টি group যোগ হয়েছে।"
            )
            + "\n\nএখন থেকে প্যানেলের সব নতুন OTP এই groupগুলোতে পাঠানো হবে।",
            parse_mode="HTML", reply_markup=links_keyboard()
        )
        return

    # ── SET NUMBER PER USER ────────────────────────────────────────────────────
    if state == "set_num_per_user" and is_admin(uid):
        try:
            n = int(text)
            if n < 1 or n > MAX_NUMBERS_PER_USER_REQUEST:
                raise ValueError
        except ValueError:
            await update.message.reply_text(
                f"❌ 1 থেকে {MAX_NUMBERS_PER_USER_REQUEST}-এর মধ্যে সংখ্যা দিন।",
                parse_mode="HTML",
            )
            return
        set_setting("num_per_user", str(n))
        ctx.user_data.clear()
        await update.message.reply_text(
            f"✅ <b>Updated!</b>\n\n"
            f"🔢 Users will now receive <b>{n}</b> number(s) per request.",
            parse_mode="HTML", reply_markup=country_mgmt_keyboard()
        )
        return

    # ── ADD BALANCE: enter UID ─────────────────────────────────────────────────
    if state == "addbal_uid" and is_admin(uid):
        try:
            target_uid = int(text)
        except ValueError:
            await update.message.reply_text("❌ Please enter a valid User ID (numbers only).", reply_markup=cancel_inline())
            return
        user_row = db_query(
            """
            SELECT uid, first_name, username, balance, banned, otp_count, joined_at
            FROM users
            WHERE uid=?
            """,
            (target_uid,),
        )
        if not user_row:
            await update.message.reply_text("❌ User not found.", reply_markup=cancel_inline())
            return
        ctx.user_data["addbal_target_uid"]  = target_uid
        ctx.user_data["addbal_target_name"] = user_row[0]["first_name"] or str(target_uid)
        ctx.user_data["addbal_current_bal"] = user_row[0]["balance"]
        ctx.user_data["state"] = "addbal_amount"

        profile = user_row[0]
        total_invited, qualified_referrals, referral_earnings = get_referral_stats(target_uid)
        withdrawal_summary = db_query(
            """
            SELECT status, COUNT(*) AS count, COALESCE(SUM(amount), 0) AS total
            FROM withdrawal_requests
            WHERE uid=?
            GROUP BY status
            """,
            (target_uid,),
        )
        withdrawal_totals = {
            str(row["status"] or "unknown"): (
                int(row["count"] or 0),
                float(row["total"] or 0),
            )
            for row in withdrawal_summary
        }
        total_withdrawals = sum(item[0] for item in withdrawal_totals.values())
        total_withdrawn = sum(item[1] for item in withdrawal_totals.values())
        approved_count, approved_total = withdrawal_totals.get("approved", (0, 0.0))
        pending_count, pending_total = withdrawal_totals.get("pending", (0, 0.0))
        rejected_count, rejected_total = withdrawal_totals.get("rejected", (0, 0.0))

        recent_withdrawals = db_query(
            """
            SELECT id, amount, status, wallet, created_at
            FROM withdrawal_requests
            WHERE uid=?
            ORDER BY id DESC
            LIMIT 3
            """,
            (target_uid,),
        )
        history_lines = []
        for withdrawal in recent_withdrawals:
            status_label = str(withdrawal["status"] or "unknown").title()
            created_at = str(withdrawal["created_at"] or "")[:16]
            wallet = withdraw_wallet_html(withdrawal["wallet"] or "—")
            history_lines.append(
                f"  #{withdrawal['id']} — <b>{status_label}</b> — "
                f"{format_currency(withdrawal['amount'])} — {created_at}\n"
                f"    {wallet}"
            )
        history_text = "\n".join(history_lines) if history_lines else "  None"

        uname = f"@{_html.escape(str(profile['username']))}" if profile["username"] else "—"
        joined_at = _html.escape(str(profile["joined_at"] or "Unknown"))
        account_status = "Banned" if profile["banned"] else "Active"
        await update.message.reply_text(
            f"👤 <b>{_html.escape(str(profile['first_name'] or target_uid))}</b> {uname}\n"
            f"🆔 <code>{target_uid}</code>\n"
            f"📌 Status: <b>{account_status}</b>\n"
            f"📅 Joined: <code>{joined_at}</code>\n"
            f"💰 Current Balance: <b>{format_currency(profile['balance'])}</b>\n"
            f"📲 OTP Count: <b>{int(profile['otp_count'] or 0)}</b>\n\n"
            f"👥 Total Referrals: <b>{total_invited}</b>\n"
            f"✅ Qualified Referrals: <b>{qualified_referrals}</b>\n"
            f"💵 Referral Earnings: <b>{format_currency(referral_earnings, 4)}</b>\n\n"
            f"📤 Withdraw Requests: <b>{total_withdrawals}</b> "
            f"({format_currency(total_withdrawn)})\n"
            f"✅ Approved: <b>{approved_count}</b> ({format_currency(approved_total)})\n"
            f"⏳ Pending: <b>{pending_count}</b> ({format_currency(pending_total)})\n"
            f"❌ Rejected: <b>{rejected_count}</b> ({format_currency(rejected_total)})\n\n"
            f"📜 <b>Recent Withdrawals</b>\n{history_text}\n\n"
            f"Enter amount in {board_currency()} to add "
            f"(use a negative amount to deduct, e.g. <code>-5</code>):",
            parse_mode="HTML", reply_markup=cancel_inline()
        )
        details_zip = build_add_balance_user_zip(
            profile,
            total_invited,
            qualified_referrals,
            referral_earnings,
            withdrawal_totals,
            recent_withdrawals,
        )
        await update.message.reply_document(
            document=details_zip,
            filename=f"user_{target_uid}_details.zip",
            caption=(
                f"📦 <b>User Details ZIP</b>\n"
                f"🆔 UID: <code>{target_uid}</code>\n"
                f"📜 Recent withdrawals included: <b>last 3 only</b>"
            ),
            parse_mode="HTML",
        )
        return

    # ── ADD BALANCE: enter amount ──────────────────────────────────────────────
    if state == "addbal_amount" and is_admin(uid):
        try:
            entered_amount = Decimal(text.strip())
            if not entered_amount.is_finite():
                raise ValueError
            amount = float(currency_input_to_usdt(entered_amount))
            if not math.isfinite(amount):
                raise ValueError
        except ValueError:
            await update.message.reply_text("❌ Enter a valid number (e.g. <code>10</code> or <code>-5</code>)", parse_mode="HTML")
            return
        target_uid  = ctx.user_data.get("addbal_target_uid")
        target_name = ctx.user_data.get("addbal_target_name", "?")
        current_row = db_query("SELECT balance FROM users WHERE uid=?", (target_uid,))
        if not current_row:
            ctx.user_data.clear()
            await update.message.reply_text(
                "❌ User no longer exists.",
                reply_markup=user_mgmt_keyboard(),
            )
            return
        current_bal = float(current_row[0]["balance"] or 0)
        new_bal = adjust_user_balance(target_uid, amount)
        if new_bal is None:
            if current_bal + amount < 0:
                await update.message.reply_text(
                    f"⚠️ Balance would go negative ({format_currency(current_bal + amount)}). Adjust the amount.",
                    parse_mode="HTML"
                )
            else:
                await update.message.reply_text(
                    "⚠️ Balance was changed by another action. Please enter the amount again.",
                    reply_markup=cancel_inline(),
                )
            return
        if new_bal < 0:
            await update.message.reply_text(
                f"⚠️ Balance would go negative ({format_currency(new_bal)}). Adjust the amount.",
                parse_mode="HTML"
            )
            return
        action = "added to" if amount >= 0 else "deducted from"
        ctx.user_data.clear()
        await update.message.reply_text(
            f"✅ <b>{format_currency(abs(amount))}</b> {action} <b>{target_name}</b>'s balance!\n\n"
            f"💰 New Balance: <b>{format_currency(new_bal)}</b>",
            parse_mode="HTML", reply_markup=user_mgmt_keyboard()
        )
        return

    # ── ADD ADMIN: enter UID ───────────────────────────────────────────────────
    if state == "add_admin_uid" and is_admin(uid):
        try:
            new_admin_uid = int(text)
        except ValueError:
            await update.message.reply_text("❌ Please enter a valid User ID.", reply_markup=cancel_inline())
            return
        if new_admin_uid in SUPER_ADMINS:
            await update.message.reply_text("⚠️ This user is already a permanent super-admin.", reply_markup=cancel_inline())
            return
        user_row = db_query("SELECT first_name, username FROM users WHERE uid=?", (new_admin_uid,))
        if not user_row:
            await update.message.reply_text("❌ User not found. They must have used /start first.", reply_markup=cancel_inline())
            return
        try:
            db_execute("INSERT INTO admins (uid, added_by) VALUES (?, ?)", (new_admin_uid, uid))
            name  = user_row[0]["first_name"] or str(new_admin_uid)
            uname = f"@{user_row[0]['username']}" if user_row[0]["username"] else ""
            msg   = f"✅ <b>{name}</b> {uname} is now an admin!"
        except sqlite3.IntegrityError:
            msg = "⚠️ This user is already an admin."
        ctx.user_data.clear()
        await update.message.reply_text(msg, parse_mode="HTML", reply_markup=user_mgmt_keyboard())
        try:
            await ctx.bot.send_message(
                chat_id=new_admin_uid,
                text="🛡 You have been granted <b>Admin</b> access!",
                parse_mode="HTML", reply_markup=admin_keyboard()
            )
        except Exception:
            pass
        return

    # ── REMOVE ADMIN: enter UID ───────────────────────────────────────────────
    if state == "remove_admin_uid" and is_admin(uid):
        try:
            target_uid = int(text)
        except ValueError:
            await update.message.reply_text("❌ Please enter a valid User ID.", reply_markup=cancel_inline())
            return
        if target_uid in SUPER_ADMINS:
            await update.message.reply_text("❌ Cannot remove a permanent super-admin.", reply_markup=cancel_inline())
            return
        admin_row = db_query("SELECT a.uid, u.first_name, u.username FROM admins a JOIN users u ON u.uid=a.uid WHERE a.uid=?", (target_uid,))
        if not admin_row:
            await update.message.reply_text("❌ This user is not an admin.", reply_markup=cancel_inline())
            return
        name  = admin_row[0]["first_name"] or str(target_uid)
        uname = f"@{admin_row[0]['username']}" if admin_row[0]["username"] else ""
        await update.message.reply_text(
            f"⚠️ Remove admin role from this user?\n\n"
            f"👤 <b>{name}</b> {uname}\n🆔 <code>{target_uid}</code>",
            parse_mode="HTML",
            reply_markup=InlineKeyboardMarkup([
                [InlineKeyboardButton("✅ Yes, Remove Admin", callback_data=f"rem_admin_{target_uid}")],
                [InlineKeyboardButton("❌ Cancel", callback_data="cancel_input")]
            ])
        )
        return

    # ── WITHDRAW: enter wallet number ──────────────────────────────────────────
    if state == "withdraw_wallet" and not is_admin(uid):
        wallet_num = text.strip()
        if not wallet_num:
            await update.message.reply_text("❌ Wallet number cannot be empty.", reply_markup=cancel_inline())
            return
        user_row = db_query("SELECT balance FROM users WHERE uid=?", (uid,))
        bal = user_row[0]["balance"] if user_row else 0.0
        wtype = ctx.user_data.get(
            "withdraw_wallet_method",
            ctx.user_data.get("withdraw_wallet_type", ""),
        )
        ctx.user_data["withdraw_wallet"] = wallet_num
        ctx.user_data["state"] = "withdraw_amount"
        await update.message.reply_text(
            f"💸 <b>Withdraw Balance</b>\n\n"
            f"💳 Wallet type: <b>{withdraw_method_html(wtype)}</b>\n"
            f"🔢 Number: <code>{_html.escape(wallet_num)}</code>\n"
            f"💰 Available: <b>{format_currency(bal)}</b>\n\n"
            f"Enter the amount you want to withdraw in {board_currency()}:",
            parse_mode="HTML", reply_markup=cancel_inline()
        )
        return

    # ── WITHDRAW: enter amount ─────────────────────────────────────────────────
    if state == "withdraw_amount" and not is_admin(uid):
        try:
            amount = parse_currency_input(text)
        except ValueError:
            await update.message.reply_text("❌ Enter a valid amount greater than 0.", reply_markup=cancel_inline())
            return
        min_wd = minimum_withdraw_usdt()
        if min_wd > 0 and amount < min_wd:
            await update.message.reply_text(
                f"❌ Minimum withdraw amount is <b>{format_currency(min_wd)}</b>.\n"
                f"Please enter at least <b>{format_currency(min_wd)}</b>.",
                parse_mode="HTML", reply_markup=cancel_inline()
            )
            return
        user_row = db_query("SELECT balance FROM users WHERE uid=?", (uid,))
        balance  = user_row[0]["balance"] if user_row else 0.0
        if amount > balance:
            await update.message.reply_text(
                f"❌ Insufficient balance.\n💰 Your balance: <b>{format_currency(balance)}</b>",
                parse_mode="HTML", reply_markup=cancel_inline()
            )
            return
        wtype  = ctx.user_data.get(
            "withdraw_wallet_method",
            ctx.user_data.get("withdraw_wallet_type", ""),
        )
        wallet = ctx.user_data.get("withdraw_wallet", "—")
        method_name = withdraw_method_name(wtype) or str(wtype or "")
        wallet_full = f"{method_name} — {wallet}" if method_name else wallet
        rid = create_withdrawal_request(uid, amount, wallet_full)
        if rid is None:
            await update.message.reply_text(
                "⚠️ Balance changed while submitting the request. "
                "Please try again.",
                reply_markup=user_keyboard(),
            )
            ctx.user_data.clear()
            return
        new_bal_row = db_query("SELECT balance FROM users WHERE uid=?", (uid,))
        new_bal = float(new_bal_row[0]["balance"]) if new_bal_row else 0.0
        user_row2 = db_query("SELECT first_name, username FROM users WHERE uid=?", (uid,))
        fname = user_row2[0]["first_name"] if user_row2 else "?"
        uname = f"@{user_row2[0]['username']}" if user_row2 and user_row2[0]["username"] else ""
        ctx.user_data.clear()
        await update.message.reply_text(
            f"✅ Withdrawal request submitted!\n\n"
            f"💳 Wallet: {withdraw_wallet_html(wallet_full)}\n"
            f"💸 Amount: <b>{format_currency(amount)}</b>\n"
            f"💰 Remaining Balance: <b>{format_currency(new_bal)}</b>\n"
            f"⏳ Status: <b>Pending</b>\n\n"
            f"You will be notified when admin processes it.",
            parse_mode="HTML", reply_markup=user_keyboard()
        )
        wd_copy_markup = InlineKeyboardMarkup([[
            InlineKeyboardButton(
                "📋 Copy Wallet",
                copy_text=CopyTextButton(text=withdraw_wallet_value(wallet_full))
            )
        ]])
        await notify_admin(
            ctx.bot,
            f"📤 <b>New Withdrawal Request</b>\n\n"
            f"👤 {_html.escape(str(fname))} {_html.escape(str(uname))}\n"
            f"🆔 <code>{uid}</code>\n"
            f"💳 Wallet: {withdraw_wallet_html(wallet_full)}\n"
            f"💸 Amount: <b>{format_currency(amount)}</b>\n"
            f"🔖 Request ID: <b>#{rid}</b>",
            reply_markup=wd_copy_markup
        )
        return

    # ── WAITING STATES ────────────────────────────────────────────────────────

    if state == "select_country_for_number" and is_admin(uid):
        countries = ctx.user_data.get("country_list", [])
        chosen = None
        for c in countries:
            if text.casefold() in {
                str(c["name"]).casefold(),
                copyable_country_name(c).casefold(),
            }:
                chosen = c
                break
        if not chosen:
            list_text = "\n".join(
                f"  <code>{copyable_country_name(c)}</code>" for c in countries
            )
            await update.message.reply_text(
                f"❌ Country not found.\n\nTap a name to copy it:\n\n{list_text}",
                parse_mode="HTML"
            )
            return
        ctx.user_data["state"]        = "add_number_file"
        ctx.user_data["country_id"]   = chosen["id"]
        ctx.user_data["country_name"] = chosen["name"]
        ctx.user_data.pop("country_list", None)
        await update.message.reply_text(
            f"📞 <b>{chosen['name']}</b> selected!\n\n"
            f"Now send the numbers file:\n"
            f"  📄 <b>.txt</b> — one number per line\n"
            f"  📊 <b>.csv</b> — numbers in any column\n"
            f"  📗 <b>.xlsx</b> — Excel file",
            parse_mode="HTML", reply_markup=cancel_inline()
        )
        return

    if state == "add_number_file" and is_admin(uid):
        await update.message.reply_text(
            "📎 Please send a <b>.txt</b>, <b>.csv</b>, or <b>.xlsx</b> file.",
            parse_mode="HTML"
        )
        return

    if state == "cp_select_country" and is_admin(uid):
        cp_countries = ctx.user_data.get("cp_countries", [])
        chosen = None
        for c in cp_countries:
            if text.casefold() in {
                str(c["name"]).casefold(),
                copyable_country_name(c).casefold(),
            }:
                chosen = c
                break
        if not chosen:
            lines = "\n".join(
                f"  {'🟢' if c['price'] > 0 else '⚪'} <code>{c['name']}</code> — {format_currency_price(c['price'])}"
                for c in cp_countries
            )
            await update.message.reply_text(
                f"❌ Country not found.\n\nTap a name to copy it:\n\n{lines}",
                parse_mode="HTML"
            )
            return
        ctx.user_data["state"]              = "set_country_price"
        ctx.user_data["price_country_id"]   = chosen["id"]
        ctx.user_data["price_country_name"] = chosen["name"]
        ctx.user_data.pop("cp_countries", None)
        await update.message.reply_text(
            f"💰 <b>{chosen['name']}</b>\n\nCurrent price: {format_currency_price(chosen['price'])}\n\n"
            f"Enter new price in {board_currency()}:\nExample: <code>5.50</code>",
            parse_mode="HTML", reply_markup=cancel_inline()
        )
        return

    if state == "set_country_price" and is_admin(uid):
        country_id   = ctx.user_data.get("price_country_id")
        country_name = ctx.user_data.get("price_country_name", "")
        try:
            price = float(text)
            if price < 0:
                raise ValueError
            price = float(currency_input_to_usdt(price))
            if not math.isfinite(price):
                raise ValueError
        except (InvalidOperation, OverflowError, ValueError):
            await update.message.reply_text("❌ Enter a valid price (e.g. <code>5.50</code>)", parse_mode="HTML")
            return
        db_execute("UPDATE countries SET price=? WHERE id=?", (price, country_id))
        # Service-country mappings cache the OTP amount separately. Keep those
        # cached values synchronized so the user panel reflects the new country
        # price immediately instead of showing the previous amount.
        db_execute(
            "UPDATE service_countries SET amount=? WHERE country_id=?",
            (price, country_id),
        )
        ctx.user_data.clear()
        await update.message.reply_text(
            f"✅ Price for <b>{country_name}</b> set to <b>{format_currency_price(price)}</b> per number.",
            parse_mode="HTML"
        )
        countries = db_query("SELECT id, name, price FROM countries WHERE active=1 ORDER BY name")
        lines = "\n".join(
            f"  {'🟢' if c['price'] > 0 else '⚪'} <code>{c['name']}</code> — {format_currency_price(c['price'])}"
            for c in countries
        )
        await update.message.reply_text(
            f"💰 <b>Country Price</b>\n\n"
            f"🟢 = Price set | ⚪ = No price\n\n{lines}\n\n"
            f"✏️ Type a country name to update its price.",
            parse_mode="HTML",
        )
        return

    # ── RESET NUMBER: country selection ───────────────────────────────────────
    if state == "reset_number_select" and is_admin(uid):
        row = _find_country_by_input(text)
        if not row:
            await update.message.reply_text(
                "❌ Country not found. সঠিক নাম টাইপ করুন।",
                parse_mode="HTML", reply_markup=cancel_inline()
            )
            return
        country = row[0]
        total = db_query(
            "SELECT COUNT(*) AS c FROM numbers WHERE country_id=?", (country["id"],)
        )[0]["c"]
        ctx.user_data["rstn_country_id"]   = country["id"]
        ctx.user_data["rstn_country_name"] = country["name"]
        await update.message.reply_text(
            f"⚠️ <b>নিশ্চিত করুন</b>\n\n"
            f"Country: <b>{country['name']}</b>\n"
            f"মোট নম্বর: <b>{total:,}</b>\n\n"
            f"এই country-র সব নম্বর স্থায়ীভাবে মুছে যাবে।",
            parse_mode="HTML",
            reply_markup=InlineKeyboardMarkup([
                [InlineKeyboardButton("✅ হ্যাঁ, মুছুন", callback_data=f"rstn_confirm_{country['id']}")],
                [InlineKeyboardButton("❌ বাতিল",         callback_data="rstn_cancel")],
            ])
        )
        return

    # ── SERVICE MANAGEMENT ────────────────────────────────────────────────────
    if state == "service_manage_mode" and is_admin(uid):
        if text in _service_map_menu_texts() or text in (
            BTN_BACK_ADMIN, BTN_COUNTRY_MGMT, BTN_USER_MGMT,
        ):
            ctx.user_data.clear()
        else:
            lowered = text.casefold()

            # delete / remove service
            delete_prefix = None
            for prefix in ("delete service ", "delete ", "remove service ", "remove "):
                if lowered.startswith(prefix):
                    delete_prefix = prefix
                    break

            if delete_prefix:
                service_name = text[len(delete_prefix):].strip()
                service = _find_service_by_input(service_name)
                if not service:
                    await update.message.reply_text(
                        f"❌ Service <b>{_html.escape(service_name)}</b> পাওয়া যায়নি।",
                        parse_mode="HTML",
                    )
                    return
                db_execute(
                    "DELETE FROM service_countries WHERE service_id=?",
                    (service["id"],),
                )
                db_execute("UPDATE services SET active=0 WHERE id=?", (service["id"],))
                ctx.user_data.clear()
                ctx.user_data["state"] = "service_manage_mode"
                await update.message.reply_text(
                    service_manage_text(
                        f"✅ Service <b>{_html.escape(service['name'])}</b> ডিলিট করা হয়েছে।"
                    ),
                    parse_mode="HTML",
                )
                return

            # unmap service country
            is_unmap = lowered.startswith("unmap ")
            raw_mapping = text[6:].strip() if is_unmap else text
            service, country, service_name = _resolve_service_country(
                raw_mapping, create_service=not is_unmap
            )

            # plain service name — add/update service only
            if not is_unmap and not service and raw_mapping.strip():
                service_name = " ".join(raw_mapping.strip().split())
                emoji_entities = _normalized_message_custom_emoji_entities(
                    update.message,
                    text_limit=service_name,
                )
                service = _find_service_by_input(service_name, active_only=False)
                if service:
                    if not service["active"]:
                        db_execute("UPDATE services SET active=1 WHERE id=?", (service["id"],))
                    if emoji_entities:
                        db_execute(
                            "UPDATE services SET name=?, emoji_entities=? WHERE id=?",
                            (service_name, emoji_entities, service["id"]),
                        )
                        service = db_query(
                            "SELECT id, name, active, emoji_entities FROM services "
                            "WHERE id=?",
                            (service["id"],),
                        )[0]
                        extra = (
                            f"✅ Service <b>{service_display_html(service)}</b>-এর "
                            "animated emoji সংরক্ষণ করা হয়েছে।"
                        )
                    else:
                        extra = (
                            f"⚠️ Service <b>{service_display_html(service)}</b> "
                            "আগে থেকেই আছে।"
                        )
                else:
                    try:
                        db_execute(
                            "INSERT INTO services (name, emoji_entities) VALUES (?, ?)",
                            (service_name, emoji_entities),
                        )
                        extra = f"✅ Service <b>{_html.escape(service_name)}</b> যোগ করা হয়েছে।"
                    except sqlite3.IntegrityError:
                        extra = f"⚠️ Service <b>{_html.escape(service_name)}</b> আগে থেকেই আছে।"
                ctx.user_data.clear()
                ctx.user_data["state"] = "service_manage_mode"
                await update.message.reply_text(
                    service_manage_text(extra),
                    parse_mode="HTML",
                )
                return

            if service and country:
                if is_unmap:
                    removed = db_execute(
                        "DELETE FROM service_countries WHERE service_id=? AND country_id=?",
                        (service["id"], country["id"])
                    )
                    if removed:
                        extra = (
                            f"✅ <b>{_html.escape(country['name'])}</b> unmap করা হয়েছে "
                            f"<b>{_html.escape(service['name'])}</b> থেকে।"
                        )
                    else:
                        extra = (
                            f"⚠️ <b>{_html.escape(country['name'])}</b> আগে থেকেই "
                            f"<b>{_html.escape(service['name'])}</b>-এর সঙ্গে map করা ছিল না।"
                        )
                else:
                    emoji_entities = _normalized_message_custom_emoji_entities(
                        update.message,
                        text_limit=service_name or "",
                    )
                    if emoji_entities:
                        db_execute(
                            "UPDATE services SET name=?, emoji_entities=? WHERE id=?",
                            (service_name, emoji_entities, service["id"]),
                        )
                        service = db_query(
                            "SELECT id, name, active, emoji_entities FROM services "
                            "WHERE id=?",
                            (service["id"],),
                        )[0]
                    amount = float(country["price"] or 0.0)
                    db_execute(
                        "INSERT OR REPLACE INTO service_countries "
                        "(service_id, country_id, amount) VALUES (?, ?, ?)",
                        (service["id"], country["id"], amount)
                    )
                    extra = (
                        f"✅ <b>{_html.escape(country['name'])}</b> map করা হয়েছে "
                        f"<b>{_html.escape(service['name'])}</b>-এর সঙ্গে।\n"
                        f"💰 OTP Bonus: <b>{format_currency_price(amount)}</b>"
                    )
                ctx.user_data.clear()
                ctx.user_data["state"] = "service_manage_mode"
                await update.message.reply_text(
                    service_manage_text(extra),
                    parse_mode="HTML",
                )
                return
            elif text.strip():
                await update.message.reply_text(
                    "❌ Service বা country পাওয়া যায়নি।\n\n"
                    "এই ফরম্যাটে লিখুন:\n"
                    "➕ <code>Service</code> — নতুন Service যোগ\n"
                    "➕ <code>Service Country</code> — Map\n"
                    "➖ <code>delete Service</code> — Service ডিলিট\n"
                    "➖ <code>unmap Service Country</code>\n\n"
                    "Country Management-এ দেশটি আগে যোগ করা আছে কি না দেখুন।",
                    parse_mode="HTML",
                )
                return

    # broadcast state is now handled by broadcast_receive_handler (any message type)

    # ── ADMIN BUTTONS ─────────────────────────────────────────────────────────
    if is_admin(uid):

        if text == BTN_COUNTRY_MGMT:
            ctx.user_data.clear()
            await update.message.reply_text("🌍 <b>Country Management</b>", parse_mode="HTML", reply_markup=country_mgmt_keyboard())
            return

        if text == BTN_BACK_ADMIN:
            ctx.user_data.clear()
            await update.message.reply_text("🛠 <b>Admin Panel</b>", parse_mode="HTML", reply_markup=admin_keyboard())
            return

        if text == BTN_SETTINGS:
            ctx.user_data.clear()
            await update.message.reply_text(
                admin_settings_text(),
                parse_mode="HTML",
                reply_markup=admin_settings_markup(),
            )
            return

        if text == BTN_LEADERBOARD:
            ctx.user_data.clear()
            await update.message.reply_text(
                order_leaderboard_text(uid, admin_view=True),
                parse_mode="HTML",
                reply_markup=leaderboard_markup(admin_view=True),
            )
            return

        if text == BTN_USER_MGMT:
            ctx.user_data.clear()
            await update.message.reply_text("👥 <b>User Management</b>", parse_mode="HTML", reply_markup=user_mgmt_keyboard())
            return

        if text == BTN_USER_LIST:
            ctx.user_data.clear()
            users_check = db_query("SELECT COUNT(*) as cnt FROM users")
            if not users_check or users_check[0]["cnt"] == 0:
                await update.message.reply_text("📭 No users found.", reply_markup=user_mgmt_keyboard())
                return
            wait_msg = await update.message.reply_text("⏳ Generating user data files...")
            archive, total = await asyncio.to_thread(build_user_data_zip)
            total_bal = db_query("SELECT SUM(balance) as s FROM users")[0]["s"] or 0
            from datetime import datetime
            fname = f"user_data_{datetime.now().strftime('%Y%m%d_%H%M')}.zip"
            await wait_msg.delete()
            await update.message.reply_document(
                document=archive,
                filename=fname,
                caption=(
                    f"<b>User List Export ZIP</b>\n"
                    f"👥 Total: <b>{total}</b> users\n"
                    f"💰 Total Balance: <b>{format_currency(total_bal)}</b>\n"
                    f"📦 Contains: Excel, users.json, numbers.json"
                ),
                parse_mode="HTML",
                reply_markup=InlineKeyboardMarkup([[
                    InlineKeyboardButton("🗑 Zero All Balances", callback_data="zero_all_bal_confirm")
                ]])
            )
            return

        if text == BTN_WITHDRAWALS:
            ctx.user_data.clear()
            requests = db_query(
                "SELECT wr.id, wr.uid, wr.amount, wr.wallet, wr.created_at, u.first_name, u.username "
                "FROM withdrawal_requests wr JOIN users u ON u.uid=wr.uid "
                "WHERE wr.status='pending' ORDER BY wr.created_at ASC"
            )
            if not requests:
                await update.message.reply_text("📭 No pending withdrawal requests.", reply_markup=user_mgmt_keyboard())
                return
            await update.message.reply_text(
                f"📤 <b>Pending Withdrawals</b> ({len(requests)} request{'s' if len(requests)>1 else ''})\n\n"
                f"Click a request to Approve or Reject:",
                parse_mode="HTML"
            )
            for r in requests:
                name  = r["first_name"] or "?"
                uname = f"@{r['username']}" if r["username"] else ""
                date  = r["created_at"][:10] if r["created_at"] else ""
                wallet_val = r["wallet"] or ""
                wallet_str = (
                    f"\n👛 Wallet: {withdraw_wallet_html(wallet_val)}"
                    if wallet_val else ""
                )
                btns = [[
                    InlineKeyboardButton("✅ Approve", callback_data=f"wr_approve_{r['id']}"),
                    InlineKeyboardButton("❌ Reject",  callback_data=f"wr_reject_{r['id']}")
                ]]
                if wallet_val:
                    btns.append([InlineKeyboardButton(
                        f"📋 Copy Wallet",
                        copy_text=CopyTextButton(text=withdraw_wallet_value(wallet_val))
                    )])
                await update.message.reply_text(
                    f"🔖 <b>Request #{r['id']}</b>\n"
                    f"👤 {_html.escape(str(name))} {_html.escape(str(uname))} | "
                    f"🆔 <code>{r['uid']}</code>\n"
                    f"💸 <b>{format_currency(r['amount'])}</b> | 📅 {date}{wallet_str}",
                    parse_mode="HTML",
                    reply_markup=InlineKeyboardMarkup(btns)
                )
            return

        if text == BTN_ADD_BALANCE:
            ctx.user_data.clear()
            ctx.user_data["state"] = "addbal_uid"
            await update.message.reply_text(
                "💰 <b>Add / Deduct Balance</b>\n\nEnter the User ID:",
                parse_mode="HTML", reply_markup=cancel_inline()
            )
            return

        if BTN_WITHDRAW_TOGGLE in text:
            current = get_setting("withdraw_enabled", "1")
            new_val = "0" if current == "1" else "1"
            set_setting("withdraw_enabled", new_val)
            status = "✅ ON" if new_val == "1" else "🔴 OFF"
            await update.message.reply_text(
                f"💸 <b>Withdraw Status Updated</b>\n\n"
                f"Status: <b>{status}</b>\n\n"
                f"{'Users can now withdraw their balance.' if new_val == '1' else 'Withdrawals are now disabled for all users.'}",
                parse_mode="HTML", reply_markup=user_mgmt_keyboard()
            )
            return

        if (
            text.startswith(f"{button_label(BTN_BOARD_CURRENCY)} [")
            or text.startswith(f"{BTN_BOARD_CURRENCY} [")
        ):
            new_currency = "BDT" if board_currency() == "USDT" else "USDT"
            set_setting(BOARD_CURRENCY_SETTING, new_currency)
            await update.message.reply_text(
                f"✅ <b>Board Currency Updated</b>\n\n"
                f"Current currency: <b>{new_currency}</b>\n"
                f"1 USDT = <b>৳{USD_TO_BDT}</b>\n"
                "This changes displayed amounts only; stored balances remain unchanged.",
                parse_mode="HTML",
                reply_markup=user_mgmt_keyboard(),
            )
            return

        if text == BTN_WITHDRAW_METHODS:
            ctx.user_data.clear()
            await update.message.reply_text(
                withdraw_methods_panel_text(),
                parse_mode="HTML",
                reply_markup=withdraw_methods_panel_markup()
            )
            return

        if BTN_MIN_WITHDRAW in text:
            ctx.user_data.clear()
            ctx.user_data["state"] = "set_min_withdraw"
            current_min = minimum_withdraw_usdt()
            cur_label   = format_currency(current_min) if current_min > 0 else "Not set"
            await update.message.reply_text(
                f"💵 <b>Minimum Withdraw Amount</b>\n\n"
                f"📌 Current minimum: <b>{cur_label}</b>\n\n"
                f"Enter the new minimum withdraw amount:\n"
                f"  • Example: <code>5</code> {board_currency()} minimum\n"
                f"  • Enter <code>0</code> to remove the minimum limit",
                parse_mode="HTML", reply_markup=cancel_inline()
            )
            return

        if text == BTN_NUMBER_VALID_TIME:
            ctx.user_data.clear()
            current_minutes = configured_number_valid_time_minutes()
            ctx.user_data["state"] = "set_number_valid_time"
            await update.message.reply_text(
                f"⏱ <b>Number Valid Time</b>\n\n"
                f"Current duration: <b>{current_minutes} minutes</b>\n\n"
                f"Enter the new duration in minutes "
                f"(whole number from {MIN_NUMBER_VALID_TIME_MINUTES} to "
                f"{MAX_NUMBER_VALID_TIME_MINUTES}).\n"
                f"Example: <code>10</code> = 10 minutes.",
                parse_mode="HTML",
                reply_markup=cancel_inline(),
            )
            return

        if text == BTN_REFERRAL_REWARD:
            ctx.user_data.clear()
            await update.message.reply_text(
                referral_settings_text(),
                parse_mode="HTML",
                reply_markup=referral_settings_markup(),
            )
            return

        if text == BTN_ADD_ADMIN:
            ctx.user_data.clear()
            ctx.user_data["state"] = "add_admin_uid"
            admins = db_query("SELECT a.uid, u.first_name, u.username FROM admins a JOIN users u ON u.uid=a.uid")
            admin_list = ""
            if admins:
                admin_list = "\n\n<b>Current Admins:</b>\n" + "\n".join(
                    f"  • {a['first_name'] or '?'} (<code>{a['uid']}</code>)" for a in admins
                )
            await update.message.reply_text(
                f"🛡 <b>Add Admin</b>{admin_list}\n\nEnter the User ID of the new admin:",
                parse_mode="HTML", reply_markup=cancel_inline()
            )
            return

        if text == BTN_REMOVE_ADMIN:
            ctx.user_data.clear()
            admins = db_query(
                "SELECT a.uid, u.first_name, u.username FROM admins a JOIN users u ON u.uid=a.uid"
            )
            if not admins:
                await update.message.reply_text("📭 No sub-admins found.", reply_markup=user_mgmt_keyboard())
                return
            ctx.user_data["state"] = "remove_admin_uid"
            admin_list = "\n".join(
                f"  • <b>{a['first_name'] or '?'}</b> (<code>{a['uid']}</code>)"
                + (f" @{a['username']}" if a["username"] else "")
                for a in admins
            )
            await update.message.reply_text(
                f"🚫 <b>Remove Admin</b>\n\n<b>Current Admins:</b>\n{admin_list}\n\n"
                f"Enter the User ID to remove from admin:",
                parse_mode="HTML", reply_markup=cancel_inline()
            )
            return

        if text == BTN_ADD_COUNTRY:
            ctx.user_data.clear()
            ctx.user_data["state"] = "country_mgmt_mode"
            countries = get_country_manager_countries()
            await update.message.reply_text(
                country_list_text(),
                parse_mode="HTML",
            )
            return

        if text == BTN_ADD_NUMBER:
            ctx.user_data.clear()
            countries = get_add_number_countries()
            if not countries:
                await update.message.reply_text("⚠️ No countries yet. Add one first.", reply_markup=country_mgmt_keyboard())
                return
            ctx.user_data["state"] = "select_country_for_number"
            ctx.user_data["country_list"] = countries
            await update.message.reply_text(
                add_number_countries_text(countries)
                + "\n\nকপি করা দেশের নাম লিখে পাঠান। তারপর numbers file পাঠান।",
                parse_mode="HTML",
            )
            return

        if text == BTN_COUNTRY_PRICE:
            ctx.user_data.clear()
            countries = db_query(
                "SELECT id, name, price, emoji_entities FROM countries "
                "WHERE active=1 ORDER BY name"
            )
            if not countries:
                await update.message.reply_text("⚠️ No countries yet.", reply_markup=country_mgmt_keyboard())
                return
            ctx.user_data["state"]        = "cp_select_country"
            ctx.user_data["cp_countries"] = [
                {
                    "id": c["id"],
                    "name": c["name"],
                    "price": c["price"],
                    "emoji_entities": c["emoji_entities"],
                }
                for c in countries
            ]
            lines = "\n".join(
                f"  {'🟢' if c['price'] > 0 else '⚪'} <code>{c['name']}</code> — {format_currency_price(c['price'])}"
                for c in countries
            )
            await update.message.reply_text(
                f"💰 <b>Country Price</b>\n\n"
                f"🟢 = Price set | ⚪ = No price\n\n{lines}\n\n"
                f"✏️ Type a country name to update its price.",
                parse_mode="HTML",
            )
            return

        if text == BTN_NUM_PER_USER:
            ctx.user_data.clear()
            current = get_setting("num_per_user", "1")
            ctx.user_data["state"] = "set_num_per_user"
            await update.message.reply_text(
                f"🔢 <b>Number Per User</b>\n\n"
                f"Current setting: <b>{current}</b> number(s) per request\n\n"
                f"Enter the new number (e.g. <code>1</code>, <code>2</code>, <code>3</code>):",
                parse_mode="HTML", reply_markup=cancel_inline()
            )
            return

        if text == BTN_RESET_NUMBER:
            ctx.user_data.clear()
            countries = db_query(
                """SELECT c.id, c.name,
                          COUNT(n.id) AS total,
                          COALESCE(SUM(CASE WHEN n.used=0 THEN 1 ELSE 0 END), 0) AS available,
                          COALESCE(SUM(CASE WHEN n.used=1 THEN 1 ELSE 0 END), 0) AS used
                   FROM countries c
                   LEFT JOIN numbers n ON n.country_id = c.id
                   WHERE c.active = 1
                   GROUP BY c.id, c.name
                   ORDER BY c.name COLLATE NOCASE"""
            )
            if not countries:
                await update.message.reply_text("⚠️ No countries found.", reply_markup=country_mgmt_keyboard())
                return
            await update.message.reply_text(
                f"🗑 <b>Reset Number</b>\n\n"
                f"যে country-র নম্বর মুছতে চান সেটি বেছে নিন:\n"
                f"প্রতি বাটনে মোট নম্বরের সংখ্যা দেখানো আছে।\n\n"
                f"⚠️ সব নম্বর মুছে যাবে (used + available)।",
                parse_mode="HTML",
                reply_markup=reset_number_country_markup(countries)
            )
            return

        # ── SERVICE MAP ────────────────────────────────────────────────────────
        if text in (BTN_SERVICE_MANAGE, BTN_SERVICE):
            ctx.user_data.clear()
            ctx.user_data["state"] = "service_manage_mode"
            await update.message.reply_text(
                service_manage_text(),
                parse_mode="HTML",
            )
            return

        if text == BTN_ADD_SERVICE:
            ctx.user_data.clear()
            ctx.user_data["state"] = "service_manage_mode"
            await update.message.reply_text(
                service_manage_text(), parse_mode="HTML",
            )
            return

        if text == BTN_BACK_COUNTRY_MGMT:
            ctx.user_data.clear()
            await update.message.reply_text("🌍 <b>Country Management</b>", parse_mode="HTML", reply_markup=country_mgmt_keyboard())
            return

        if text == BTN_LINKS:
            ctx.user_data.clear()
            await update.message.reply_text("🔗 <b>Links</b>", parse_mode="HTML", reply_markup=links_keyboard())
            return

        if text == BTN_STATS:
            ctx.user_data.clear()
            total_users     = db_query("SELECT COUNT(*) AS c FROM users")[0]["c"]
            banned_users    = db_query("SELECT COUNT(*) AS c FROM users WHERE banned=1")[0]["c"]
            # Only numbers belonging to active countries are inventory.
            # This prevents orphaned rows left by older soft-delete flows
            # from appearing as available numbers in the admin statistics.
            total_numbers   = db_query(
                """SELECT COUNT(*) AS c
                   FROM numbers n
                   JOIN countries c ON c.id=n.country_id
                   WHERE c.active=1"""
            )[0]["c"]
            used_numbers    = db_query(
                """SELECT COUNT(*) AS c
                   FROM numbers n
                   JOIN countries c ON c.id=n.country_id
                   WHERE c.active=1 AND n.used=1"""
            )[0]["c"]
            unused_numbers  = total_numbers - used_numbers
            total_countries = db_query("SELECT COUNT(*) AS c FROM countries WHERE active=1")[0]["c"]
            pending_wr      = db_query("SELECT COUNT(*) AS c FROM withdrawal_requests WHERE status='pending'")[0]["c"]
            total_wr        = db_query("SELECT COUNT(*) AS c FROM withdrawal_requests")[0]["c"]
            total_admins    = db_query("SELECT COUNT(*) AS c FROM admins")[0]["c"]
            country_inventory = get_country_manager_countries()
            country_lines = []
            for country in country_inventory:
                country_lines.append(
                    f"  • {country_display_html(country)} — "
                    f"Total: <b>{int(country['total'] or 0):,}</b> | "
                    f"Used: <b>{int(country['used'] or 0):,}</b> | "
                    f"Available: <b>{int(country['available'] or 0):,}</b>"
                )
            country_inventory_text = "\n".join(country_lines) or "  • No countries found."
            msg = (
                "📊 <b>Bot Statistics</b>\n\n"
                "👥 <b>Users</b>\n"
                f"  • Total: <b>{total_users}</b>\n"
                f"  • Banned: <b>{banned_users}</b>\n\n"
                "📞 <b>Numbers</b>\n"
                f"  • Total: <b>{total_numbers}</b>\n"
                f"  • Used: <b>{used_numbers}</b>\n"
                f"  • Available: <b>{unused_numbers}</b>\n\n"
                "🌍 <b>Countries</b>\n"
                f"  • Active: <b>{total_countries}</b>\n\n"
                "📦 <b>Country-wise Number Status</b>\n"
                f"{country_inventory_text}\n\n"
                "💸 <b>Withdrawals</b>\n"
                f"  • Pending: <b>{pending_wr}</b>\n"
                f"  • Total: <b>{total_wr}</b>\n\n"
                "🛡 <b>Admins</b>\n"
                f"  • Total: <b>{total_admins + len(SUPER_ADMINS)}</b>"
            )
            await update.message.reply_text(msg, parse_mode="HTML", reply_markup=admin_keyboard())
            return

        if text == BTN_SUPPORT_LINK:
            ctx.user_data.clear()
            current = get_setting("support_link", "https://t.me/sxsupportgroup")
            ctx.user_data["state"] = "set_support_link"
            await update.message.reply_text(
                f"🔗 <b>Support Link</b>\n\n"
                f"Current: <code>{current}</code>\n\n"
                f"Enter the new support link:",
                parse_mode="HTML", reply_markup=cancel_inline()
            )
            return

        if text == BTN_OTP_LINK:
            ctx.user_data.clear()
            current = get_setting("otp_link", "https://t.me/sxotp99")
            ctx.user_data["state"] = "set_otp_link"
            await update.message.reply_text(
                f"📲 <b>OTP Link</b>\n\n"
                f"Current: <code>{current}</code>\n\n"
                f"Enter the new OTP link:",
                parse_mode="HTML", reply_markup=cancel_inline()
            )
            return

        if text == BTN_GET_NUMBER_LINK:
            ctx.user_data.clear()
            current = get_setting("get_number_link", get_setting("otp_link", "https://t.me/sxotp99"))
            ctx.user_data["state"] = "set_get_number_link"
            await update.message.reply_text(
                f"📱 <b>Get Number Link</b>\n\n"
                f"Current: <code>{_html.escape(current)}</code>\n\n"
                f"Enter the new Get Number link:",
                parse_mode="HTML", reply_markup=cancel_inline()
            )
            return

        if text == BTN_CHANNEL_LINK:
            ctx.user_data.clear()
            current = get_setting("channel_link", get_setting("support_link", "https://t.me/sxsupportgroup"))
            ctx.user_data["state"] = "set_channel_link"
            await update.message.reply_text(
                f"📢 <b>Channel Link</b>\n\n"
                f"Current: <code>{_html.escape(current)}</code>\n\n"
                f"Enter the new Channel link:",
                parse_mode="HTML", reply_markup=cancel_inline()
            )
            return

        if text.startswith(button_label(BTN_FORCE_JOIN)):
            ctx.user_data.clear()
            await update.message.reply_text(
                force_join_settings_text(),
                parse_mode="HTML",
                reply_markup=force_join_settings_markup(),
            )
            return

        if BTN_OTP_GROUP_CHAT in text:
            ctx.user_data.clear()
            ctx.user_data["state"] = "set_otp_group_id"
            await update.message.reply_text(
                otp_group_settings_text(),
                parse_mode="HTML", reply_markup=cancel_inline()
            )
            return

        if BTN_OTP_DEMO_SEND in text:
            otp_group_ids = get_otp_group_ids()
            if not otp_group_ids:
                await update.message.reply_text(
                    "❌ <b>OTP Group সেট করা নেই!</b>\n\n"
                    "আগে <b>OTP Group Chat</b> বাটন থেকে গ্রুপ ID সেট করুন।",
                    parse_mode="HTML", reply_markup=links_keyboard()
                )
                return
            demo_number = "221771234020"
            demo_user_id = str(uid or "7476095122")
            demo_messages = [
                ("WhatsApp", "186433", "Username: 1864332583 Password: AxfpDQ2m Do not share this information."),
                ("WhatsApp", "566676", "<#> Verification code 566676\nWz09uzhCZ0v"),
            ]

            # Preview the exact body a user receives when an OTP arrives.
            demo_user_text, demo_user_kb = _format_user_otp_msg(
                demo_number,
                "Senegal 🇸🇳",
                None,
                0.0010,
                0.0010,
                "566676",
                "<#> Verification code 566676\nWz09uzhCZ0v",
                sender="WhatsApp",
            )

            group_sent_count = 0
            user_preview_sent = False
            for otp_group_id in otp_group_ids:
                group_ok = False
                for demo_service, service_otp, service_full_msg in demo_messages:
                    demo_text, demo_kb = _format_otp_group_msg(
                        number=demo_number,
                        sender=demo_service,
                        otp_code=service_otp,
                        full_message=service_full_msg,
                        user_id=demo_user_id,
                        country_name="Senegal",
                    )
                    try:
                        await ctx.bot.send_message(
                            chat_id=otp_group_id,
                            text=demo_text,
                            parse_mode="HTML",
                            reply_markup=demo_kb
                        )
                        group_ok = True
                    except Exception as e:
                        logger.warning(
                            "Demo OTP group send error for %s: %s",
                            otp_group_id,
                            e,
                        )
                if group_ok:
                    group_sent_count += 1

            try:
                await ctx.bot.send_message(
                    chat_id=uid,
                    text=demo_user_text,
                    parse_mode="HTML",
                    reply_markup=demo_user_kb,
                )
                user_preview_sent = True
            except Exception as e:
                logger.warning(f"Demo OTP user preview send error: {e}")

            if group_sent_count or user_preview_sent:
                await update.message.reply_text(
                    f"✅ <b>Demo OTP Sent!</b>\n\n"
                    f"📢 Group demo: {group_sent_count}/{len(otp_group_ids)} groups ✅\n"
                    f"👤 User-panel preview: {'✅' if user_preview_sent else '❌'}\n"
                    f"🔐 OTP Buttons: <b>5 service demos</b>",
                    parse_mode="HTML", reply_markup=links_keyboard()
                )
            else:
                await update.message.reply_text(
                    f"❌ <b>Demo Send Failed!</b>\n\n"
                    f"গ্রুপ বা ইউজার-প্যানেল—কোনোটিতেই ডেমো পাঠানো যায়নি।\n\n"
                    f"💡 বটকে গ্রুপের Admin করা আছে কিনা চেক করুন।",
                    parse_mode="HTML", reply_markup=links_keyboard()
                )
            return

        if text == BTN_BROADCAST:
            ctx.user_data["state"] = "broadcast_wait"
            await update.message.reply_text(
                "📢 <b>Broadcast</b>\n\n"
                "Send the message you want to broadcast to all users.\n\n"
                "✅ <b>Supported types:</b>\n"
                "  • Text (with bold, italic, links etc.)\n"
                "  • 📷 Photo\n"
                "  • 🎥 Video\n"
                "  • 🎞 GIF / Animation\n"
                "  • 🎵 Audio / Voice\n"
                "  • 📄 Document / File\n"
                "  • 😀 Sticker (normal + premium)\n"
                "  • 💎 Premium emoji in text",
                parse_mode="HTML", reply_markup=cancel_inline()
            )
            return

    # ── USER BUTTONS ──────────────────────────────────────────────────────────

    if text == BTN_LIVE_TRAFFIC:
        admin_view = is_admin(uid)
        if not admin_view and get_setting("live_traffic_user_enabled", "1") != "1":
            await update.message.reply_text(
                "🔒 <b>Live Traffic</b>\n\n"
                "এই feature এখন user panel-এর জন্য বন্ধ আছে।",
                parse_mode="HTML",
                reply_markup=user_keyboard(),
            )
            return
        await update.message.reply_text(
            live_traffic_text(),
            parse_mode="HTML",
            reply_markup=live_traffic_markup(admin_view=admin_view),
        )
        return

    if text == BTN_LEADERBOARD:
        if not leaderboard_is_enabled():
            await update.message.reply_text(
                "🔒 <b>Leaderboard</b>\n\n"
                "এই feature এখন user panel-এর জন্য বন্ধ আছে।",
                parse_mode="HTML",
                reply_markup=user_keyboard(),
            )
            return
        await update.message.reply_text(
            order_leaderboard_text(uid),
            parse_mode="HTML",
            reply_markup=leaderboard_markup(),
        )
        return

    if text == BTN_GET_NUMBER:
        services = get_number_services()
        if not services:
            await update.message.reply_text(
                "❌ No service is available at the moment.",
                reply_markup=user_keyboard()
            )
            return
        await update.message.reply_text(
            GET_NUMBER_SERVICE_PROMPT,
            parse_mode="HTML",
            reply_markup=number_services_markup(services)
        )
        return

    if text == BTN_AVAIL:
        await update.message.reply_text(
            available_country_text(),
            parse_mode="HTML", reply_markup=user_keyboard()
        )
        return

    if text == BTN_SUPPORT:
        link = get_setting("support_link", "https://t.me/sxsupportgroup")
        await update.message.reply_text(
            "🆘 <b>Support</b>\n\nClick the button below to join our support group:",
            parse_mode="HTML",
            reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🆘 Join Support Group", url=link)]])
        )
        return

    if text == BTN_BALANCE:
        row = db_query("SELECT balance FROM users WHERE uid=?", (uid,))
        bal = row[0]["balance"] if row else 0.0
        min_withdraw = minimum_withdraw_usdt()
        withdraw_status = (
            "✅ ON" if get_setting("withdraw_enabled", "1") == "1" else "🔴 OFF"
        )
        await update.message.reply_text(
            f"💰 <b>My Balance</b>\n\n"
            f"💵 Current Balance: <b>{format_currency(bal)}</b> {_per_otp_premium_emoji_html()}\n"
            f"💵 minimum withdraw : <b>{format_currency(min_withdraw)}</b> "
            f"{_per_otp_premium_emoji_html()}\n"
            f"💸 Withdraw option: <b>{withdraw_status}</b>",
            parse_mode="HTML", reply_markup=balance_inline()
        )
        return

    if text in (BTN_MY_REFERRAL, BTN_REFER_EARN):
        referral_text, referral_markup = await build_referral_panel(ctx.bot, uid)
        await update.message.reply_text(
            referral_text,
            parse_mode="HTML",
            reply_markup=referral_markup,
        )
        return

    if text == BTN_WITHDRAW:
        if get_setting("withdraw_enabled", "1") != "1":
            await update.message.reply_text(
                "🔴 <b>Withdraw is currently disabled.</b>\n\nPlease try again later.",
                parse_mode="HTML", reply_markup=user_keyboard()
            )
            return
        rows = db_query("SELECT balance FROM users WHERE uid=?", (uid,))
        bal  = rows[0]["balance"] if rows else 0.0
        if bal <= 0:
            await update.message.reply_text("❌ You have no balance to withdraw.", reply_markup=user_keyboard())
            return
        ctx.user_data["state"] = "withdraw_wallet_type"
        await update.message.reply_text(
            f"💸 <b>Withdraw Balance</b>\n\n"
            f"💰 Available: <b>{format_currency(bal)}</b>\n\n"
            f"Select your wallet type:",
            parse_mode="HTML",
            reply_markup=build_wtype_markup(bal)
        )
        return

    # ── PANELS BUTTON ─────────────────────────────────────────────────────────
    if text == BTN_PANELS and is_admin(uid):
        ctx.user_data.clear()
        await update.message.reply_text(
            panels_list_text(), parse_mode="HTML", reply_markup=panels_keyboard()
        )
        return

    # ── LAST MSGS BUTTON ──────────────────────────────────────────────────────
    if text == BTN_LAST_MSGS and is_admin(uid):
        ctx.user_data.clear()
        panels = db_query("SELECT * FROM panels WHERE active=1")
        if not panels:
            await update.message.reply_text("📭 No active panels.", reply_markup=admin_keyboard())
            return
        if len(panels) == 1:
            panel = panels[0]
            sms_rows = await asyncio.to_thread(
                panel_fetch_sms, panel, 1, True
            )
            if sms_rows is None:
                await update.message.reply_text(
                    f"⚠️ Panel <b>{panel['name']}</b> session expired!", parse_mode="HTML"
                )
            elif not sms_rows:
                await update.message.reply_text(
                    f"📭 <b>{panel['name']}</b> — No messages found today.", parse_mode="HTML"
                )
            else:
                await update.message.reply_text(
                    format_last_sms(panel['name'], sms_rows), parse_mode="HTML"
                )
        else:
            btns = [[InlineKeyboardButton(f"📡 {p['name']}", callback_data=f"panel_lastmsgs_{p['id']}")] for p in panels]
            await update.message.reply_text(
                "📋 <b>Last Message</b> — কোন panel?",
                parse_mode="HTML", reply_markup=InlineKeyboardMarkup(btns)
            )
        return

    # ── ADD PANEL → choose panel type directly ────────────────────────────────
    if text == BTN_PANEL_ADD and is_admin(uid):
        ctx.user_data.clear()
        await update.message.reply_text(
            "📡 <b>Panel টাইপ বেছে নিন</b>\n\n"
            "🔐 <b>Captcha Panel</b> — Username/Password দিয়ে cookie-based login\n"
            "🌐 <b>Non-Captcha Panel</b> — একই web login, শুধু captcha ছাড়া\n"
            "🔌 <b>API Panel</b> — API URL ও Key দিয়ে সরাসরি data fetch",
            parse_mode="HTML",
            reply_markup=InlineKeyboardMarkup([
                [InlineKeyboardButton("🔐 Captcha Panel", callback_data="panel_type_captcha")],
                [InlineKeyboardButton("🌐 Non-Captcha Panel", callback_data="panel_type_non_captcha")],
                [InlineKeyboardButton("🔌 API Panel",     callback_data="panel_type_api")],
                [InlineKeyboardButton("❌ Cancel",        callback_data="cancel_input")],
            ])
        )
        return

    # ── PANEL NAME TAP → open that panel's actions ────────────────────────────
    if is_admin(uid):
        all_panels = db_query("SELECT id, name, active FROM panels ORDER BY id")
        for p in all_panels:
            icon = "🟢" if p["active"] else "🔴"
            if text == f"{icon} {p['name']}":
                ctx.user_data.clear()
                last_ts = db_query("SELECT last_seen_ts FROM panels WHERE id=?", (p["id"],))
                ts_str = (last_ts[0]["last_seen_ts"] or "scan হয়নি") if last_ts else "scan হয়নি"
                status = "🟢 Active" if p["active"] else "🔴 Paused"
                await update.message.reply_text(
                    f"📡 <b>{p['name']}</b>\n"
                    f"স্ট্যাটাস: {status}\n"
                    f"Last scan: <code>{ts_str}</code>\n\n"
                    f"কী করতে চান?",
                    parse_mode="HTML",
                    reply_markup=panel_action_markup(p["id"], p["active"])
                )
                return

    if state == "panel_add_name" and is_admin(uid):
        ctx.user_data["panel_name"] = text.strip()
        ctx.user_data["state"] = "panel_add_login_url"
        await update.message.reply_text(
            "Step 2/12 — Login URL পাঠান:\n"
            "উদাহরণ: <code>http://168.119.13.175/ints/login</code>",
            parse_mode="HTML", reply_markup=cancel_inline()
        )
        return

    if state == "panel_add_login_url" and is_admin(uid):
        link = text.strip()
        if not link.startswith("http"):
            await update.message.reply_text("❌ Valid URL দিন (http দিয়ে শুরু)।", reply_markup=cancel_inline())
            return
        ctx.user_data["panel_login_url"] = link
        ctx.user_data["state"] = "panel_add_username"
        await update.message.reply_text(
            "Step 3/12 — Username পাঠান:", parse_mode="HTML", reply_markup=cancel_inline()
        )
        return

    if state == "panel_add_username" and is_admin(uid):
        ctx.user_data["panel_username"] = text.strip()
        ctx.user_data["state"] = "panel_add_password"
        await update.message.reply_text(
            "Step 4/12 — Password পাঠান:", parse_mode="HTML", reply_markup=cancel_inline()
        )
        return

    if state == "panel_add_password" and is_admin(uid):
        ctx.user_data["panel_password"] = text.strip()
        ctx.user_data["state"] = "panel_add_stats_url"
        await update.message.reply_text(
            "Step 5/12 — SMS data পেইজের লিঙ্ক পাঠান:\n"
            "উদাহরণ: <code>http://168.119.13.175/ints/agent/SMSCDRStats</code>",
            parse_mode="HTML", reply_markup=cancel_inline()
        )
        return

    if state == "panel_add_stats_url" and is_admin(uid):
        stats_url = text.strip()
        if not stats_url.startswith("http"):
            await update.message.reply_text("❌ Valid URL দিন।", reply_markup=cancel_inline())
            return
        ctx.user_data["panel_stats_url"] = stats_url
        ctx.user_data["state"] = "panel_add_num_col_idx"
        await update.message.reply_text(
            "Step 6/9 — <b>Number</b> কোন column number-এ আছে?\n"
            "উদাহরণ: <code>3</code>",
            parse_mode="HTML", reply_markup=cancel_inline()
        )
        return

    if state == "panel_add_num_col_idx" and is_admin(uid):
        if not text.strip().isdigit() or int(text.strip()) < 1:
            await update.message.reply_text("❌ 1 বা তার বেশি column number লিখুন।", reply_markup=cancel_inline())
            return
        # User-facing column numbers start at 1; store zero-based indexes.
        ctx.user_data["panel_num_col_idx"] = int(text.strip()) - 1
        ctx.user_data["state"] = "panel_add_sender_col_idx"
        await update.message.reply_text(
            "Step 7/9 — <b>CLI</b> কোন column number-এ আছে?\n"
            "উদাহরণ: <code>4</code>",
            parse_mode="HTML", reply_markup=cancel_inline()
        )
        return

    if state == "panel_add_sender_col_idx" and is_admin(uid):
        if not text.strip().isdigit() or int(text.strip()) < 1:
            await update.message.reply_text("❌ 1 বা তার বেশি column number লিখুন।", reply_markup=cancel_inline())
            return
        ctx.user_data["panel_sender_col_idx"] = int(text.strip()) - 1
        ctx.user_data["state"] = "panel_add_msg_col_idx"
        await update.message.reply_text(
            "Step 8/9 — <b>SMS</b> কোন column number-এ আছে?\n"
            "উদাহরণ: <code>6</code>",
            parse_mode="HTML", reply_markup=cancel_inline()
        )
        return

    if state == "panel_add_msg_col_idx" and is_admin(uid):
        if not text.strip().isdigit() or int(text.strip()) < 1:
            await update.message.reply_text("❌ 1 বা তার বেশি column number লিখুন।", reply_markup=cancel_inline())
            return
        ctx.user_data["panel_msg_col_idx"] = int(text.strip()) - 1
        ctx.user_data["state"] = "panel_add_scan_interval"
        await update.message.reply_text(
            "Step 9/9 — ⏱ <b>Scan Interval</b>\n\n"
            "এই panel কত সেকেন্ড পর পর ডেটা লোড করবে?\n\n"
            "উদাহরণ: <code>30</code> = ৩০ সেকেন্ড পরপর\n"
            "         <code>60</code> = ১ মিনিট পরপর\n"
            "         <code>120</code> = ২ মিনিট পরপর\n\n"
            "⚠️ minimum 3 সেকেন্ড",
            parse_mode="HTML", reply_markup=cancel_inline()
        )
        return

    if state == "panel_add_scan_interval" and is_admin(uid):
        raw = text.strip()
        if not raw.isdigit() or int(raw) < 3:
            await update.message.reply_text(
                "❌ কমপক্ষে <b>3</b> সেকেন্ড দিন।\nউদাহরণ: <code>3</code>",
                parse_mode="HTML", reply_markup=cancel_inline()
            )
            return
        ctx.user_data["panel_scan_interval"] = int(raw)

        # collect all wizard data
        name            = ctx.user_data.get("panel_name", "")
        login_url       = ctx.user_data.get("panel_login_url", "")
        username        = ctx.user_data.get("panel_username", "")
        password        = ctx.user_data.get("panel_password", "")
        stats_url       = ctx.user_data.get("panel_stats_url", "")
        num_col_name    = "Number"
        num_col_idx     = ctx.user_data.get("panel_num_col_idx", 2)
        sender_col_name = "CLI"
        sender_col_idx  = ctx.user_data.get("panel_sender_col_idx", 3)
        msg_col_name    = "SMS"
        msg_col_idx     = ctx.user_data.get("panel_msg_col_idx", 5)
        scan_interval   = ctx.user_data.get("panel_scan_interval", 60)
        panel_type      = ctx.user_data.get("panel_type", "captcha")
        ctx.user_data.clear()

        wait_msg = await update.message.reply_text(
            "🔄 <b>Logging in...</b> অপেক্ষা করুন।", parse_mode="HTML"
        )
        session_result = await asyncio.to_thread(
            panel_login_session,
            login_url,
            username,
            password,
            stats_url,
            panel_type,
        )
        if not session_result:
            await wait_msg.edit_text(
                "❌ <b>Login ব্যর্থ হয়েছে!</b>\n\n"
                "Username/Password, Login URL, SMS URL এবং panel-এর form format "
                "চেক করুন। JavaScript panel হলে browser login-ও চেষ্টা করা হয়েছে। "
                "Login হলেও SMS page access না হলে panel save হবে না।",
                parse_mode="HTML"
            )
            await update.message.reply_text("📡 Panels", reply_markup=panels_keyboard())
            return
        cookies, browser_state = session_result

        db_execute(
            "INSERT INTO panels "
            "(name, login_url, username, password, stats_url, cookies, browser_state, "
            "number_col_name, number_col_idx, sender_col_name, sender_col_idx, "
            "message_col_name, message_col_idx, scan_interval, panel_type) "
            "VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)",
            (name, login_url, username, password, stats_url, json.dumps(cookies),
             browser_state,
             num_col_name, num_col_idx, sender_col_name, sender_col_idx,
              msg_col_name, msg_col_idx, scan_interval, panel_type)
        )

        # human-friendly interval label
        if scan_interval >= 60 and scan_interval % 60 == 0:
            interval_label = f"{scan_interval // 60} মিনিট"
        elif scan_interval >= 60:
            interval_label = f"{scan_interval // 60}m {scan_interval % 60}s"
        else:
            interval_label = f"{scan_interval} সেকেন্ড"

        await wait_msg.edit_text(
            f"✅ <b>Panel যোগ হয়েছে!</b>\n\n"
            f"📡 Name: <b>{name}</b>\n"
            f"👤 Username: <b>{username}</b>\n"
            f"🔢 Number column: <b>{num_col_name}</b> (column {num_col_idx + 1})\n"
            f"📨 Sender column: <b>{sender_col_name}</b> (column {sender_col_idx + 1})\n"
            f"💬 Message column: <b>{msg_col_name}</b> (column {msg_col_idx + 1})\n"
            f"⏱ Scan interval: <b>{interval_label}</b>\n"
            f"🟢 Session সংরক্ষিত হয়েছে।\n\n"
            f"API এখন প্রতি <b>{scan_interval} seconds</b> পরপর "
            f"fresh data check করবে।",
            parse_mode="HTML"
        )
        await update.message.reply_text(panels_list_text(), parse_mode="HTML", reply_markup=panels_keyboard())
        return

    # ── BACK TO PANELS ────────────────────────────────────────────────────────
    if text == BTN_BACK_PANELS and is_admin(uid):
        ctx.user_data.clear()
        await update.message.reply_text(panels_list_text(), parse_mode="HTML", reply_markup=panels_keyboard())
        return

    # ── PANEL NAME TAP (from mobile keyboard) ─────────────────────────────────
    if is_admin(uid):
        all_panels = db_query("SELECT id, name, active FROM panels ORDER BY id")
        for p in all_panels:
            icon = "🟢" if p["active"] else "🔴"
            if text == f"{icon} {p['name']}":
                ctx.user_data.clear()
                last_ts = db_query("SELECT last_seen_ts FROM panels WHERE id=?", (p["id"],))
                ts_str = (last_ts[0]["last_seen_ts"] or "scan হয়নি") if last_ts else "scan হয়নি"
                status = "🟢 Active" if p["active"] else "🔴 Paused"
                await update.message.reply_text(
                    f"📡 <b>{p['name']}</b>\n"
                    f"স্ট্যাটাস: {status}\n"
                    f"Last scan: <code>{ts_str}</code>\n\n"
                    f"কী করতে চান?",
                    parse_mode="HTML",
                    reply_markup=panel_action_markup(p["id"], p["active"])
                )
                return

    # ── API PANEL WIZARD ──────────────────────────────────────────────────────
    if state == "panel_api_add_name" and is_admin(uid):
        name = text.strip()
        if not name:
            await update.message.reply_text(
                "❌ Panel-এর নাম খালি রাখা যাবে না।",
                reply_markup=cancel_inline(),
            )
            return
        ctx.user_data["panel_name"] = name
        ctx.user_data["state"] = "panel_api_add_url"
        await update.message.reply_text(
            "Step 2/7 — API URL পাঠান:\n"
            "উদাহরণ: <code>https://api.example.com/sms/list</code>",
            parse_mode="HTML", reply_markup=cancel_inline()
        )
        return

    if state == "panel_api_add_url" and is_admin(uid):
        link = text.strip()
        parsed = urlparse(link)
        if parsed.scheme not in {"http", "https"} or not parsed.netloc:
            await update.message.reply_text(
                "❌ Valid http:// অথবা https:// URL দিন।",
                reply_markup=cancel_inline(),
            )
            return
        ctx.user_data["panel_stats_url"] = link
        ctx.user_data["state"] = "panel_api_add_key"
        await update.message.reply_text(
            "Step 3/4 — API token / key পাঠান:\n"
            "Token না থাকলে <code>none</code> লিখুন।\n\n"
            "Auth format নিজে থেকে detect করার চেষ্টা করবে।",
            parse_mode="HTML",
            reply_markup=cancel_inline(),
        )
        return

    if state == "panel_api_add_method" and is_admin(uid):
        await update.message.reply_text(
            "GET অথবা POST button ব্যবহার করে method নির্বাচন করুন।",
            reply_markup=cancel_inline(),
        )
        return

    if state == "panel_api_add_key" and is_admin(uid):
        raw_key = text.strip()
        ctx.user_data["panel_api_key"] = "" if raw_key.lower() == "none" else raw_key
        ctx.user_data["state"] = "panel_api_add_interval"
        await update.message.reply_text(
            "Step 4/4 — ⏱ <b>Refresh interval</b>\n\n"
            "কত সেকেন্ড পরপর API scan হবে? minimum <code>3</code> seconds দিন।\n"
            "আপনি যে interval লিখবেন, bot সেই interval-এই API check করবে।\n"
            "উদাহরণ: <code>3</code>, <code>30</code> অথবা <code>60</code>",
            parse_mode="HTML",
            reply_markup=cancel_inline(),
        )
        return

    if state == "panel_api_add_auth_name" and is_admin(uid):
        auth_name = text.strip()
        if not auth_name or any(char in auth_name for char in "\r\n"):
            await update.message.reply_text(
                "❌ একটি valid header বা parameter name দিন।",
                reply_markup=cancel_inline(),
            )
            return
        ctx.user_data["panel_api_auth_name"] = auth_name
        ctx.user_data["state"] = "panel_api_add_mapping"
        await update.message.reply_text(
            "Step 6/7 — <b>JSON Mapping (Optional)</b>\n\n"
            "Default field না হলে এক লাইনে mapping দিন:\n"
            "<code>rows=data.items;number=phone;sender=from;message=body;time=created_at;range=country</code>\n\n"
            "Auto-detect ব্যবহার করতে <code>none</code> লিখুন।",
            parse_mode="HTML",
            reply_markup=cancel_inline(),
        )
        return

    if state == "panel_api_add_mapping" and is_admin(uid):
        mapping = _parse_api_mapping(text)
        ctx.user_data.update(mapping)
        ctx.user_data["state"] = "panel_api_add_interval"
        await update.message.reply_text(
            "Step 7/7 — ⏱ <b>Scan Interval</b>\n\n"
            "কত সেকেন্ড পরপর data load করবে?\n"
            "আপনি যে interval লিখবেন, bot সেই interval-এই API check করবে।\n"
            "উদাহরণ: <code>3</code> = প্রতি ৩ সেকেন্ডে check\n\n"
            "⚠️ minimum 3 সেকেন্ড",
            parse_mode="HTML",
            reply_markup=cancel_inline(),
        )
        return

    if state == "panel_api_add_interval" and is_admin(uid):
        raw = text.strip()
        if not raw.isdigit() or not 3 <= int(raw) <= 86400:
            await update.message.reply_text(
                "❌ Refresh interval <b>3 থেকে 86400 seconds</b>-এর মধ্যে দিন।\n"
                "উদাহরণ: <code>3</code>, <code>30</code> অথবা <code>60</code>",
                parse_mode="HTML", reply_markup=cancel_inline()
            )
            return
        scan_interval = int(raw)
        name      = ctx.user_data.get("panel_name", "")
        stats_url = ctx.user_data.get("panel_stats_url", "")
        api_key   = ctx.user_data.get("panel_api_key", "")
        # The fetcher discovers safe GET auth and common JSON field names at
        # runtime, so the admin does not have to guess provider-specific
        # header/query/mapping options.
        api_method = "GET"
        api_auth_type = "auto"
        api_auth_name = ""
        api_rows_path = ""
        api_number_field = ""
        api_sender_field = ""
        api_message_field = ""
        api_timestamp_field = ""
        api_range_field = ""
        ctx.user_data.clear()

        db_execute(
            "INSERT INTO panels "
            "(name, login_url, username, password, stats_url, api_key, "
            "scan_interval, panel_type, active, api_method, api_auth_type, "
            "api_auth_name, api_rows_path, api_number_field, api_sender_field, "
            "api_message_field, api_timestamp_field, api_range_field) "
            "VALUES (?, '', '', '', ?, ?, ?, 'api', 1, ?, ?, ?, ?, ?, ?, ?, ?, ?)",
            (
                name, stats_url, api_key, scan_interval, api_method,
                api_auth_type, api_auth_name, api_rows_path, api_number_field,
                api_sender_field, api_message_field, api_timestamp_field,
                api_range_field,
            )
        )

        if scan_interval >= 60 and scan_interval % 60 == 0:
            interval_label = f"{scan_interval // 60} মিনিট"
        elif scan_interval >= 60:
            interval_label = f"{scan_interval // 60}m {scan_interval % 60}s"
        else:
            interval_label = f"{scan_interval} সেকেন্ড"

        await update.message.reply_text(
            f"✅ <b>API Panel যোগ হয়েছে!</b>\n\n"
            f"🔌 Name: <b>{_html.escape(name)}</b>\n"
            f"🔗 API URL: <b>{_html.escape(stats_url)}</b>\n"
            f"🔑 API Key: {'✅ সেট' if api_key else '⚠️ নেই'}\n"
            f"📤 Method: <b>{api_method}</b> · Auth: <b>{api_auth_type}</b>\n"
            f"⏱ Scan interval: <b>{interval_label}</b>\n\n"
            f"বট এখন থেকে প্রতি <b>{interval_label}</b> পরপর স্বয়ংক্রিয়ভাবে SMS চেক করবে।",
            parse_mode="HTML", reply_markup=panels_keyboard()
        )
        await update.message.reply_text(panels_list_text(), parse_mode="HTML", reply_markup=panels_keyboard())
        return

    # ── EDIT COLUMNS WIZARD ───────────────────────────────────────────────────
    if state == "panel_editcols_num_idx" and is_admin(uid):
        if not text.strip().isdigit() or int(text.strip()) < 1:
            await update.message.reply_text("❌ 1 বা তার বেশি column number লিখুন।", reply_markup=cancel_inline())
            return
        ctx.user_data["ec_num_idx"] = int(text.strip()) - 1
        ctx.user_data["state"] = "panel_editcols_sender_idx"
        await update.message.reply_text(
            "Step 2/3 — CLI কোন column number-এ?\n"
            "উদাহরণ: <code>3</code>",
            parse_mode="HTML", reply_markup=cancel_inline()
        )
        return

    if state == "panel_editcols_sender_idx" and is_admin(uid):
        if not text.strip().isdigit() or int(text.strip()) < 1:
            await update.message.reply_text("❌ 1 বা তার বেশি column number লিখুন।", reply_markup=cancel_inline())
            return
        ctx.user_data["ec_sender_idx"] = int(text.strip()) - 1
        ctx.user_data["state"] = "panel_editcols_msg_idx"
        await update.message.reply_text(
            "Step 3/3 — SMS কোন column number-এ?\n"
            "উদাহরণ: <code>5</code>",
            parse_mode="HTML", reply_markup=cancel_inline()
        )
        return

    if state == "panel_editcols_msg_idx" and is_admin(uid):
        if not text.strip().isdigit() or int(text.strip()) < 1:
            await update.message.reply_text("❌ 1 বা তার বেশি column number লিখুন।", reply_markup=cancel_inline())
            return
        pid         = ctx.user_data.get("ec_panel_id")
        num_idx     = ctx.user_data.get("ec_num_idx", 2)
        sender_idx  = ctx.user_data.get("ec_sender_idx", 3)
        msg_idx     = int(text.strip()) - 1
        ctx.user_data.clear()
        if pid:
            db_execute(
                "UPDATE panels SET number_col_idx=?, sender_col_idx=?, message_col_idx=? WHERE id=?",
                (num_idx, sender_idx, msg_idx, pid)
            )
            await update.message.reply_text(
                f"✅ Column config আপডেট হয়েছে!\n\n"
                f"📞 Number column: <b>{num_idx + 1}</b>\n"
                f"👤 CLI column: <b>{sender_idx + 1}</b>\n"
                f"💬 SMS column: <b>{msg_idx + 1}</b>",
                parse_mode="HTML", reply_markup=panels_keyboard()
            )
        return

    # ── PER-PANEL SCAN INTERVAL SET ───────────────────────────────────────────
    if state == "panel_set_pinterval" and is_admin(uid):
        try:
            secs = int(text.strip())
            if secs < 3:
                raise ValueError
        except ValueError:
            await update.message.reply_text("❌ কমপক্ষে 3 সেকেন্ড দিন।", reply_markup=cancel_inline())
            return
        pid        = ctx.user_data.get("pi_panel_id")
        panel_name = ctx.user_data.get("pi_panel_name", "")
        panel_type = ctx.user_data.get("pi_panel_type", "")
        ctx.user_data.clear()
        if pid:
            db_execute("UPDATE panels SET scan_interval=? WHERE id=?", (secs, pid))
            message = (
                f"✅ <b>{panel_name}</b>-এর scan interval "
                f"<b>{secs} সেকেন্ড</b> এ সেট হয়েছে।"
            )
            if panel_type == "api":
                message += (
                    f"\nএখন bot প্রতি <b>{secs} seconds</b> পরপর API check করবে।"
                )
            await update.message.reply_text(
                message,
                parse_mode="HTML", reply_markup=panels_keyboard()
            )
        return

    if is_admin(uid):
        await update.message.reply_text(
            "⚠️ এই message-এর জন্য কোনো action মেলেনি। নিচের menu থেকে একটি option বেছে নিন।",
            reply_markup=admin_keyboard(),
        )
    else:
        await update.message.reply_text(
            "⚠️ এই message-এর জন্য কোনো action মেলেনি। নিচের menu ব্যবহার করুন।",
            reply_markup=user_keyboard(),
        )


# ─── CALLBACK HANDLER ────────────────────────────────────────────────────────
async def callback_handler(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()
    data  = query.data
    uid   = query.from_user.id

    # ── FORCE-JOIN SETTINGS / USER CHECK ─────────────────────────────────────
    if data == "forcejoin_check":
        missing = await missing_force_join_channels(ctx.bot, uid)
        if missing:
            await query.edit_message_text(
                force_join_user_text(missing),
                parse_mode="HTML",
                reply_markup=force_join_user_markup(missing),
            )
        else:
            await query.edit_message_text(
                "✅ <b>Membership verified!</b>",
                parse_mode="HTML",
            )
            await ctx.bot.send_message(
                chat_id=uid,
                text=USER_PANEL_WELCOME_TEXT,
                parse_mode="HTML",
                reply_markup=user_keyboard(),
            )
        return

    if data == "fj_add" and is_admin(uid):
        ctx.user_data.clear()
        ctx.user_data["state"] = "force_join_add_channel"
        await ctx.bot.send_message(
            chat_id=uid,
            text=(
                "➕ <b>Add Force-Join Channel</b>\n\n"
                "শুধু channel username পাঠান:\n"
                "<code>@channelusername</code>\n"
                "অথবা <code>channelusername</code>\n\n"
                "চাইলে এই full format-ও ব্যবহার করতে পারেন:\n"
                "<code>@channel | https://t.me/channel | Channel Name</code>\n\n"
                "Private channel হলে @username-এর বদলে numeric Chat ID দিন:\n"
                "<code>-1001234567890 | https://t.me/+invite | Private Channel</code>"
            ),
            parse_mode="HTML",
            reply_markup=cancel_inline(),
        )
        return

    if data == "fj_toggle" and is_admin(uid):
        channels = get_force_join_channels()
        if not channels:
            await ctx.bot.send_message(
                chat_id=uid,
                text="❌ আগে অন্তত একটি channel add করুন।",
                reply_markup=force_join_settings_markup(),
            )
            return
        new_value = "0" if force_join_is_enabled() else "1"
        set_setting("force_join_enabled", new_value)
        status_text = "✅ চালু হয়েছে" if new_value == "1" else "🔴 বন্ধ হয়েছে"
        await ctx.bot.send_message(
            chat_id=uid,
            text=force_join_settings_text(f"✅ Force Join {status_text}."),
            parse_mode="HTML",
            reply_markup=force_join_settings_markup(),
        )
        return

    if data.startswith("fj_remove_") and is_admin(uid):
        try:
            index = int(data.rsplit("_", 1)[1])
        except ValueError:
            await query.answer("Invalid channel.", show_alert=True)
            return
        channels = get_force_join_channels()
        if index < 0 or index >= len(channels):
            await query.answer("Channel not found.", show_alert=True)
            return
        removed = channels.pop(index)
        set_force_join_channels(channels)
        if not channels:
            set_setting("force_join_enabled", "0")
        await ctx.bot.send_message(
            chat_id=uid,
            text=force_join_settings_text(
                f"🗑 Removed <b>{_html.escape(removed['title'])}</b>."
            ),
            parse_mode="HTML",
            reply_markup=force_join_settings_markup(),
        )
        return

    if data == "fj_back" and is_admin(uid):
        ctx.user_data.clear()
        await ctx.bot.send_message(
            chat_id=uid,
            text="🔗 <b>Links</b>",
            parse_mode="HTML",
            reply_markup=links_keyboard(),
        )
        return

    if not await enforce_force_join_callback(query, ctx):
        return

    # ── ADMIN FEATURE SETTINGS ─────────────────────────────────────────────────
    if data.startswith("settings_"):
        if not is_admin(uid):
            await query.edit_message_text("❌ Only admins can change these settings.")
            return
        if data == "settings_back":
            await query.edit_message_text(
                "🛠 <b>Admin Panel</b>",
                parse_mode="HTML",
            )
            await ctx.bot.send_message(
                chat_id=uid,
                text="🛠 <b>Admin Panel</b>",
                parse_mode="HTML",
                reply_markup=admin_keyboard(),
            )
            return
        if data == "settings_panel":
            await query.edit_message_text(
                admin_settings_text(),
                parse_mode="HTML",
                reply_markup=admin_settings_markup(),
            )
            return
        if data == "settings_toggle_leaderboard":
            new_value = "0" if leaderboard_is_enabled() else "1"
            set_setting("leaderboard_enabled", new_value)
            status = "ON" if new_value == "1" else "OFF"
            await query.edit_message_text(
                admin_settings_text(f"✅ Leaderboard is now {status}."),
                parse_mode="HTML",
                reply_markup=admin_settings_markup(),
            )
            return
        if data == "settings_toggle_traffic":
            current = get_setting("live_traffic_user_enabled", "1") == "1"
            new_value = "0" if current else "1"
            set_setting("live_traffic_user_enabled", new_value)
            status = "ON" if new_value == "1" else "OFF"
            await query.edit_message_text(
                admin_settings_text(f"✅ User Live Traffic is now {status}."),
                parse_mode="HTML",
                reply_markup=admin_settings_markup(),
            )
            return
        if data == "settings_open_leaderboard":
            await query.edit_message_text(
                order_leaderboard_text(uid, admin_view=True),
                parse_mode="HTML",
                reply_markup=leaderboard_markup(admin_view=True),
            )
            return
        if data == "settings_open_referrals":
            referral_text, referral_markup = build_top_referrals_panel(
                uid, admin_view=True
            )
            await query.edit_message_text(
                referral_text,
                parse_mode="HTML",
                reply_markup=referral_markup,
            )
            return
        if data == "settings_open_traffic":
            await query.edit_message_text(
                live_traffic_text(),
                parse_mode="HTML",
                reply_markup=live_traffic_markup(admin_view=True),
            )
            return
        await query.answer("Unknown setting.", show_alert=True)
        return

    # ── ORDER LEADERBOARD ──────────────────────────────────────────────────────
    if data in ("leaderboard_refresh", "leaderboard_find_rank"):
        admin_view = is_admin(uid)
        if not admin_view and not leaderboard_is_enabled():
            await query.edit_message_text(
                "🔒 <b>Leaderboard</b>\n\n"
                "This feature is currently disabled for the user panel.",
                parse_mode="HTML",
            )
            return
        await query.edit_message_text(
            order_leaderboard_text(
                uid,
                admin_view=admin_view,
                include_rank=(data == "leaderboard_find_rank"),
            ),
            parse_mode="HTML",
            reply_markup=leaderboard_markup(admin_view=admin_view),
        )
        return

    # ── USER REFERRAL VIEWS ───────────────────────────────────────────────────
    if data == "top_referrals":
        admin_view = is_admin(uid)
        if not admin_view and not leaderboard_is_enabled():
            await query.edit_message_text(
                "🔒 <b>Referral Leaderboard</b>\n\n"
                "This feature is currently disabled for the user panel.",
                parse_mode="HTML",
            )
            return
        top_text, top_markup = build_top_referrals_panel(
            uid, admin_view=admin_view
        )
        await query.edit_message_text(
            top_text,
            parse_mode="HTML",
            reply_markup=top_markup,
        )
        return

    if data == "referral_panel":
        referral_text, referral_markup = await build_referral_panel(
            ctx.bot, uid
        )
        await query.edit_message_text(
            referral_text,
            parse_mode="HTML",
            reply_markup=referral_markup,
        )
        return

    # ── REFERRAL SETTINGS ─────────────────────────────────────────────────────
    if data == "refcfg_back" and is_admin(uid):
        ctx.user_data.clear()
        await query.edit_message_text(
            "👥 <b>User Management</b>",
            parse_mode="HTML",
        )
        await ctx.bot.send_message(
            chat_id=uid,
            text="👥 <b>User Management</b>",
            parse_mode="HTML",
            reply_markup=user_mgmt_keyboard(),
        )
        return

    if data in {"refcfg_reward", "refcfg_otps", "refcfg_commission"} and is_admin(uid):
        ctx.user_data.clear()
        if data == "refcfg_reward":
            ctx.user_data["state"] = "set_referral_reward"
            await query.edit_message_text(
                f"🔥 <b>Per Referral Reward</b>\n\n"
                f"Current value: <b>{format_currency(referral_qualified_reward())}</b>\n\n"
                f"Enter the reward in {board_currency()} per qualified referral.\n"
                f"Example: <code>{'13' if board_currency() == 'BDT' else '0.10'}</code>\n"
                "Enter <code>0</code> to disable the reward.",
                parse_mode="HTML",
                reply_markup=cancel_inline(),
            )
        elif data == "refcfg_otps":
            ctx.user_data["state"] = "set_referral_qualification_otps"
            await query.edit_message_text(
                f"🎯 <b>Qualification OTPs</b>\n\n"
                f"Current threshold: <b>{referral_qualification_otps()} OTPs</b>\n\n"
                "Enter how many successfully delivered OTPs a referred user "
                "must receive before the referral becomes active.\n"
                "Example: <code>50</code>",
                parse_mode="HTML",
                reply_markup=cancel_inline(),
            )
        else:
            ctx.user_data["state"] = "set_referral_commission_rate"
            await query.edit_message_text(
                f"💸 <b>Qualified Referrer Commission</b>\n\n"
                f"Current rate: <b>{referral_otp_commission_rate() * 100:.2f}%</b>\n\n"
                "Enter the percentage of every OTP reward paid to the "
                "qualified referrer.\n"
                "Example: <code>10</code> = 10%",
                parse_mode="HTML",
                reply_markup=cancel_inline(),
            )
        return

    # ── LIVE TRAFFIC ─────────────────────────────────────────────────────────
    if data in ("traffic_refresh", "traffic_toggle_users"):
        admin_view = is_admin(uid)
        if data == "traffic_toggle_users":
            if not admin_view:
                await query.answer("Only admins can change this setting.", show_alert=True)
                return
            current = get_setting("live_traffic_user_enabled", "1") == "1"
            set_setting("live_traffic_user_enabled", "0" if current else "1")
            status = "ON" if not current else "OFF"
            await query.edit_message_text(
                admin_settings_text(f"✅ User Live Traffic is now {status}."),
                parse_mode="HTML",
                reply_markup=admin_settings_markup(),
            )
            return

        if not admin_view and get_setting("live_traffic_user_enabled", "1") != "1":
            await query.edit_message_text(
                "🔒 <b>Live Traffic</b>\n\n"
                "This feature is currently disabled for the user panel.",
                parse_mode="HTML",
            )
            return
        await query.edit_message_text(
            live_traffic_text(),
            parse_mode="HTML",
            reply_markup=live_traffic_markup(admin_view=admin_view),
        )
        return

    # ── PANEL TYPE SELECTION ──────────────────────────────────────────────────
    if data == "panel_type_captcha" and is_admin(uid):
        ctx.user_data.clear()
        ctx.user_data["state"] = "panel_add_name"
        ctx.user_data["panel_type"] = "captcha"
        await query.answer("Captcha Panel")
        await ctx.bot.send_message(
            chat_id=uid,
            text="🔐 <b>Captcha Panel যোগ করুন</b>\n\n"
                 "Step 1/12 — Panel-এর নাম দিন:\n"
                 "উদাহরণ: <code>MyFlexPanel</code>",
            parse_mode="HTML", reply_markup=cancel_inline()
        )
        return

    if data == "panel_type_non_captcha" and is_admin(uid):
        ctx.user_data.clear()
        ctx.user_data["state"] = "panel_add_name"
        ctx.user_data["panel_type"] = "non_captcha"
        await query.answer("Non-Captcha Panel")
        await ctx.bot.send_message(
            chat_id=uid,
            text="🌐 <b>Non-Captcha Panel যোগ করুন</b>\n\n"
                 "Step 1/12 — Panel-এর নাম দিন:\n"
                 "উদাহরণ: <code>SharkSMS</code>",
            parse_mode="HTML", reply_markup=cancel_inline()
        )
        return

    if data == "panel_type_api" and is_admin(uid):
        ctx.user_data.clear()
        ctx.user_data["state"] = "panel_api_add_name"
        ctx.user_data["panel_type"] = "api"
        await query.answer("API Panel")
        await ctx.bot.send_message(
            chat_id=uid,
            text="🔌 <b>API Panel যোগ করুন</b>\n\n"
                 "Step 1/4 — Panel-এর নাম দিন:\n"
                 "উদাহরণ: <code>MyAPIPanel</code>",
            parse_mode="HTML", reply_markup=cancel_inline()
        )
        return

    if data in {"api_method_get", "api_method_post"} and is_admin(uid):
        ctx.user_data["panel_api_method"] = data.rsplit("_", 1)[1].upper()
        ctx.user_data["state"] = "panel_api_add_key"
        await query.answer(ctx.user_data["panel_api_method"])
        await ctx.bot.send_message(
            chat_id=uid,
            text=(
                "Step 4/7 — API Key / Token পাঠান:\n"
                "Key না থাকলে <code>none</code> লিখুন।"
            ),
            parse_mode="HTML",
            reply_markup=cancel_inline(),
        )
        return

    if data.startswith("api_auth_") and is_admin(uid):
        auth_type = data[len("api_auth_"):]
        allowed = {
            "auto", "bearer", "raw", "token", "x_auth_token", "x_api_key",
            "api_key_header", "basic", "custom_header", "custom_query",
            "token_query", "post_form", "post_json", "none",
        }
        if auth_type not in allowed:
            await query.answer("Unsupported auth mode.", show_alert=True)
            return
        if auth_type == "raw":
            auth_type = "raw_authorization"
        ctx.user_data["panel_api_auth_type"] = auth_type
        ctx.user_data["panel_api_auth_name"] = ""
        await query.answer("Authentication selected")
        if auth_type in {"custom_header", "custom_query"}:
            ctx.user_data["state"] = "panel_api_add_auth_name"
            await ctx.bot.send_message(
                chat_id=uid,
                text=(
                    "Step 6/7 — এই key কোন header/parameter name-এ যাবে?\n"
                    "উদাহরণ: <code>X-Access-Token</code>, "
                    "<code>access_token</code>"
                ),
                parse_mode="HTML",
                reply_markup=cancel_inline(),
            )
        else:
            ctx.user_data["state"] = "panel_api_add_mapping"
            await ctx.bot.send_message(
                chat_id=uid,
                text=(
                    "Step 6/7 — <b>JSON Mapping (Optional)</b>\n\n"
                    "Default field না হলে এক লাইনে mapping দিন:\n"
                    "<code>rows=data.items;number=phone;sender=from;"
                    "message=body;time=created_at;range=country</code>\n\n"
                    "Auto-detect ব্যবহার করতে <code>none</code> লিখুন।"
                ),
                parse_mode="HTML",
                reply_markup=cancel_inline(),
            )
        return

    if data == "service_manage_open" and is_admin(uid):
        ctx.user_data.clear()
        ctx.user_data["state"] = "service_manage_mode"
        await query.answer("Service Management")
        await ctx.bot.send_message(
            chat_id=uid,
            text=service_manage_text(),
            parse_mode="HTML",
        )
        return

    if data == "service_map_back" and is_admin(uid):
        await query.answer("Service Management")
        ctx.user_data["state"] = "service_manage_mode"
        await ctx.bot.send_message(
            chat_id=uid,
            text=service_manage_text(),
            parse_mode="HTML",
        )
        return

    if data.startswith("service_map_copy_") and is_admin(uid):
        try:
            service_id = int(data.rsplit("_", 1)[1])
        except ValueError:
            await query.answer("Invalid service.", show_alert=True)
            return
        service = db_query(
            "SELECT id, name, emoji_entities FROM services WHERE id=? AND active=1",
            (service_id,),
        )
        if not service:
            await query.answer("Service not found.", show_alert=True)
            return
        await query.answer("Use the Copy button below.", show_alert=True)
        await ctx.bot.send_message(
            chat_id=uid,
            text=f"📋 <b>{service_display_html(service[0])}</b>",
            parse_mode="HTML",
            reply_markup=InlineKeyboardMarkup([[
                InlineKeyboardButton(
                    "📋 Copy Service Name",
                    copy_text=CopyTextButton(text=copyable_service_name(service[0])),
                )
            ]]),
        )
        return

    if data.startswith("service_map_service_") and is_admin(uid):
        try:
            service_id = int(data.rsplit("_", 1)[1])
        except ValueError:
            await query.answer("Invalid service.", show_alert=True)
            return
        service = db_query(
            "SELECT id, name, emoji_entities FROM services WHERE id=? AND active=1",
            (service_id,),
        )
        if not service:
            await query.answer("Service not found.", show_alert=True)
            return
        ctx.user_data["state"] = "service_manage_mode"
        await query.answer("Select a country to map.")
        await ctx.bot.send_message(
            chat_id=uid,
            text=(
                f"🗺️ <b>{service_display_html(service[0])}</b>\n\n"
                "একটি country বেছে নিন। ✅ মানে আগে থেকেই mapped, "
                "➕ মানে এখনো mapped নয়।"
            ),
            parse_mode="HTML",
            reply_markup=service_map_country_markup(service_id),
        )
        return

    if data.startswith("service_map_country_") and is_admin(uid):
        parts = data.split("_")
        if len(parts) != 5:
            await query.answer("Invalid mapping.", show_alert=True)
            return
        try:
            service_id = int(parts[3])
            country_id = int(parts[4])
        except ValueError:
            await query.answer("Invalid mapping.", show_alert=True)
            return

        service = db_query(
            "SELECT id, name, emoji_entities FROM services WHERE id=? AND active=1",
            (service_id,),
        )
        country = db_query(
            """
            SELECT id, name, price, emoji_entities
            FROM countries
            WHERE id=? AND active=1
            """,
            (country_id,),
        )
        if not service or not country:
            await query.answer("Service or country not found.", show_alert=True)
            return

        amount = float(country[0]["price"] or 0.0)
        existing = db_query(
            "SELECT id FROM service_countries WHERE service_id=? AND country_id=?",
            (service_id, country_id),
        )
        db_execute(
            """
            INSERT OR REPLACE INTO service_countries
                (service_id, country_id, amount)
            VALUES (?, ?, ?)
            """,
            (service_id, country_id, amount),
        )
        await query.answer("Mapped successfully.")
        await ctx.bot.send_message(
            chat_id=uid,
            text=(
                f"{'🔄' if existing else '✅'} "
                f"<b>{country_display_html(country[0])}</b> "
                f"map করা হয়েছে <b>{service_display_html(service[0])}</b>-এর সঙ্গে।\n"
                f"💰 OTP Price: <b>{format_currency_price(amount)}</b>"
            ),
            parse_mode="HTML",
            reply_markup=service_map_country_markup(service_id),
        )
        return

    if data.startswith("addnum_country_") and is_admin(uid):
        try:
            country_id = int(data.rsplit("_", 1)[1])
        except ValueError:
            await query.answer("Invalid country.", show_alert=True)
            return
        rows = db_query(
            "SELECT id, name, emoji_entities FROM countries "
            "WHERE id=? AND active=1",
            (country_id,),
        )
        if not rows:
            await query.answer("Country not found.", show_alert=True)
            return
        country = rows[0]
        ctx.user_data.clear()
        ctx.user_data["state"] = "add_number_file"
        ctx.user_data["country_id"] = country["id"]
        ctx.user_data["country_name"] = country["name"]
        await query.edit_message_text(
            f"📞 <b>{country_display_html(country)}</b> selected!\n\n"
            f"Now send the numbers file:\n"
            f"  📄 <b>.txt</b> — one number per line\n"
            f"  📊 <b>.csv</b> — numbers in any column\n"
            f"  📗 <b>.xlsx</b> — Excel file",
            parse_mode="HTML",
            reply_markup=cancel_inline(),
        )
        return

    if data == "cancel_input":
        ctx.user_data.clear()
        await query.edit_message_text("❌ Cancelled.")
        kb    = admin_keyboard() if is_admin(uid) else user_keyboard()
        panel = "🛠 <b>Admin Panel</b>" if is_admin(uid) else "🏠 Main Menu"
        await ctx.bot.send_message(chat_id=uid, text=panel, parse_mode="HTML", reply_markup=kb)
        return

    if data in ("custom_noop", "noop"):
        return

    if data == "noop":
        return

    # ── BALANCE SUB-PANEL ─────────────────────────────────────────────────────
    if data == "bal_back":
        row = db_query("SELECT balance FROM users WHERE uid=?", (uid,))
        bal       = row[0]["balance"]        if row else 0.0
        withdraw_status = (
            "✅ ON" if get_setting("withdraw_enabled", "1") == "1" else "🔴 OFF"
        )
        total_invited, qualified_referrals, referral_earnings = get_referral_stats(uid)
        reward_val = referral_qualified_reward()
        qualification = referral_qualification_otps()
        commission = referral_otp_commission_rate() * 100
        bot_info   = await ctx.bot.get_me()
        ref_link   = f"https://t.me/{bot_info.username}?start=ref_{uid}"
        await query.edit_message_text(
            f"💰 <b>My Balance</b>\n\n"
            f"💵 Balance: <b>{format_currency(bal)}</b>\n"
            f"💸 Withdraw option: <b>{withdraw_status}</b>\n\n"
            f"🎁 <b>REFERRAL BONUS</b>\n"
            f"🔗 Your link:\n<code>{ref_link}</code>\n\n"
            f"🔥 {format_currency(reward_val)} per successful referral\n"
            f"📍 Credited after referred user receives {qualification} OTPs.\n"
            f"💸 You earn {commission:.2f}% from the qualifying OTP and every OTP after it.\n\n"
            f"💬 Total Invited: <b>{total_invited}</b>\n"
            f"✅ Qualified: <b>{qualified_referrals}</b>\n"
            f"💰 Referral Earnings: <b>{format_currency(referral_earnings, 4)}</b>",
            parse_mode="HTML", reply_markup=balance_inline()
        )
        return

    if data == "bal_withdraw":
        if get_setting("withdraw_enabled", "1") != "1":
            await query.answer("🔴 Withdraw is currently disabled. Try later.", show_alert=True)
            return
        rows = db_query("SELECT balance FROM users WHERE uid=?", (uid,))
        bal = rows[0]["balance"] if rows else 0.0
        if bal <= 0:
            await query.answer("❌ You have no balance to withdraw.", show_alert=True)
            return
        ctx.user_data["state"] = "withdraw_wallet_type"
        await query.edit_message_text(
            f"💸 <b>Withdraw Balance</b>\n\n"
            f"💰 Available: <b>{format_currency(bal)}</b>\n\n"
            f"Select your wallet type:",
            parse_mode="HTML",
            reply_markup=build_wtype_markup(bal)
        )
        return

    if data.startswith("wtype_"):
        try:
            method_index = int(data.split("_", 1)[1])
        except (IndexError, ValueError):
            await query.answer("Invalid wallet method.", show_alert=True)
            return
        methods = get_withdraw_methods()
        if method_index < 0 or method_index >= len(methods):
            await query.answer("Wallet method not found.", show_alert=True)
            return
        wtype = methods[method_index]
        rows = db_query("SELECT balance FROM users WHERE uid=?", (uid,))
        bal  = rows[0]["balance"] if rows else 0.0
        ctx.user_data["withdraw_wallet_method"] = wtype
        ctx.user_data["withdraw_wallet_type"] = withdraw_method_name(wtype)
        ctx.user_data["state"] = "withdraw_wallet"
        await query.edit_message_text(
            f"💸 <b>Withdraw Balance</b>\n\n"
            f"💳 Wallet type: <b>{withdraw_method_html(wtype)}</b>\n"
            f"💰 Available: <b>{format_currency(bal)}</b>\n\n"
            f"Enter your {withdraw_method_html(wtype)} wallet number:",
            parse_mode="HTML", reply_markup=cancel_inline()
        )
        return

    # ── WITHDRAW METHODS MANAGEMENT (admin) ───────────────────────────────────
    if data == "wm_add" and is_admin(uid):
        ctx.user_data.clear()
        ctx.user_data["state"] = "add_withdraw_method"
        await query.answer()
        await ctx.bot.send_message(
            chat_id=uid,
            text=(
                "💳 <b>Add Withdraw Method</b>\n\n"
                "Enter the name of the new method:\n"
                "  • Example: <code>Rocket</code>, <code>USDT TRC20</code>\n\n"
                "Name will appear exactly as you type it.\n"
                "Telegram custom/animated emoji দিতে চাইলে method name-এর "
                "সঙ্গে একই message-এ emoji পাঠান—সেটি method-এর সঙ্গে save হবে।"
            ),
            parse_mode="HTML", reply_markup=cancel_inline()
        )
        return

    if data.startswith("wm_remove_") and is_admin(uid):
        try:
            method_index = int(data[len("wm_remove_"):])
        except ValueError:
            await query.answer("Invalid wallet method.", show_alert=True)
            return
        methods = get_withdraw_methods()
        if method_index < 0 or method_index >= len(methods):
            await query.answer("Wallet method not found.", show_alert=True)
            return
        name = methods.pop(method_index)
        set_withdraw_methods(methods)
        await query.answer(f"✅ Removed: {name}")
        try:
            await query.edit_message_text(
                withdraw_methods_panel_text(),
                parse_mode="HTML",
                reply_markup=withdraw_methods_panel_markup()
            )
        except Exception:
            pass
        return

    # ── ZERO ALL BALANCES ─────────────────────────────────────────────────────
    if data == "zero_all_bal_confirm" and is_admin(uid):
        total_bal = db_query("SELECT SUM(balance) as s FROM users")[0]["s"] or 0
        count     = db_query("SELECT COUNT(*) as c FROM users WHERE balance > 0")[0]["c"] or 0
        try:
            await query.edit_message_reply_markup(reply_markup=None)
        except Exception:
            pass
        await ctx.bot.send_message(
            chat_id=uid,
            text=(
                f"⚠️ <b>Zero All Balances?</b>\n\n"
                f"This will set balance to {format_currency(0)} for <b>{count}</b> users.\n"
                f"Total amount to be cleared: <b>{format_currency(total_bal)}</b>\n\n"
                f"✅ Users will NOT be removed from the bot.\n"
                f"❗ This action cannot be undone."
            ),
            parse_mode="HTML",
            reply_markup=InlineKeyboardMarkup([[
                InlineKeyboardButton("✅ Yes, Zero All", callback_data="zero_all_bal_do"),
                InlineKeyboardButton("❌ Cancel",        callback_data="zero_all_bal_cancel")
            ]])
        )
        return

    if data == "zero_all_bal_do" and is_admin(uid):
        affected = db_query("SELECT COUNT(*) as c FROM users WHERE balance > 0")[0]["c"] or 0
        db_execute("UPDATE users SET balance = 0.0", ())
        await query.edit_message_text(
            f"✅ <b>Done!</b>\n\n"
            f"💰 Balances zeroed for <b>{affected}</b> users.\n"
            f"👥 All users remain in the bot.",
            parse_mode="HTML"
        )
        await ctx.bot.send_message(chat_id=uid, text="👥 User Management", reply_markup=user_mgmt_keyboard())
        return

    if data == "zero_all_bal_cancel" and is_admin(uid):
        await query.edit_message_text("❌ Cancelled. No balances were changed.")
        await ctx.bot.send_message(chat_id=uid, text="👥 User Management", reply_markup=user_mgmt_keyboard())
        return

    # ── WITHDRAWAL REQUESTS ───────────────────────────────────────────────────
    if data.startswith("wr_approve_") and is_admin(uid):
        req_id  = int(data.split("_")[2])
        req_row = db_query("SELECT uid, amount, wallet, status FROM withdrawal_requests WHERE id=?", (req_id,))
        if not req_row or req_row[0]["status"] != "pending":
            await query.edit_message_text("⚠️ Request already processed or not found.")
            return
        req_uid     = req_row[0]["uid"]
        amount      = req_row[0]["amount"]
        wallet_info = req_row[0]["wallet"] or "—"
        db_execute("UPDATE withdrawal_requests SET status='approved' WHERE id=?", (req_id,))
        user_bal = db_query("SELECT balance FROM users WHERE uid=?", (req_uid,))
        cur_bal  = user_bal[0]["balance"] if user_bal else 0
        await query.edit_message_text(
            f"✅ <b>Withdrawal Approved</b>\n\n"
            f"🔖 Request #{req_id}\n"
            f"💳 Wallet: {withdraw_wallet_html(wallet_info)}\n"
            f"💸 Amount: <b>{format_currency(amount)}</b>\n"
            f"👤 User: <code>{req_uid}</code>",
            parse_mode="HTML"
        )
        try:
            await ctx.bot.send_message(
                chat_id=req_uid,
                text=f"✅ <b>Withdrawal Approved!</b>\n\n"
                     f"💳 Wallet: {withdraw_wallet_html(wallet_info)}\n"
                     f"💸 Amount: <b>{format_currency(amount)}</b>\n"
                     f"💰 Current Balance: <b>{format_currency(cur_bal)}</b>",
                parse_mode="HTML"
            )
        except Exception:
            pass
        return

    if data.startswith("wr_reject_") and is_admin(uid):
        try:
            req_id = int(data.split("_")[2])
        except (IndexError, ValueError):
            await query.edit_message_text("⚠️ Invalid withdrawal request.")
            return
        rejected = reject_withdrawal_request(req_id)
        if rejected is None:
            await query.edit_message_text("⚠️ Request already processed or not found.")
            return
        req_uid     = rejected["uid"]
        amount      = rejected["amount"]
        wallet_info = rejected["wallet"] or "—"
        user_bal = db_query("SELECT balance FROM users WHERE uid=?", (req_uid,))
        refunded_bal = float(user_bal[0]["balance"]) if user_bal else 0.0
        await query.edit_message_text(
            f"❌ <b>Withdrawal Rejected</b>\n\n"
            f"🔖 Request #{req_id}\n"
            f"💳 Wallet: {withdraw_wallet_html(wallet_info)}\n"
            f"💸 Amount: <b>{format_currency(amount)}</b>\n"
            f"↩️ Refunded Balance: <b>{format_currency(amount)}</b>\n"
            f"💰 Current Balance: <b>{format_currency(refunded_bal)}</b>\n"
            f"👤 User: <code>{req_uid}</code>",
            parse_mode="HTML"
        )
        try:
            await ctx.bot.send_message(
                chat_id=req_uid,
                text=f"❌ <b>Withdrawal Rejected</b>\n\n"
                     f"💸 Amount: <b>{format_currency(amount)}</b>\n"
                     f"↩️ The amount has been returned to your balance.\n"
                     f"💰 Current Balance: <b>{format_currency(refunded_bal)}</b>\n"
                     f"⚠️ Please contact support for more info.",
                parse_mode="HTML"
            )
        except Exception:
            pass
        return

    # ── RESET NUMBER CALLBACKS ────────────────────────────────────────────────
    if data.startswith("rstn_country_") and is_admin(uid):
        try:
            country_id = int(data.rsplit("_", 1)[1])
        except ValueError:
            await query.answer("Invalid country.", show_alert=True)
            return
        country = db_query(
            "SELECT id, name, emoji_entities FROM countries WHERE id=? AND active=1",
            (country_id,),
        )
        if not country:
            await query.answer("Country not found.", show_alert=True)
            return
        selected = country[0]
        total = db_query(
            "SELECT COUNT(*) AS c FROM numbers WHERE country_id=?",
            (country_id,),
        )[0]["c"]
        ctx.user_data["rstn_country_name"] = selected["name"]
        await query.edit_message_text(
            f"⚠️ <b>নিশ্চিত করুন</b>\n\n"
            f"Country: <b>{country_display_html(selected)}</b>\n"
            f"মোট নম্বর: <b>{int(total):,}</b>\n\n"
            f"এই country-র সব নম্বর স্থায়ীভাবে মুছে যাবে।",
            parse_mode="HTML",
            reply_markup=InlineKeyboardMarkup([
                [InlineKeyboardButton(
                    "✅ হ্যাঁ, মুছুন",
                    callback_data=f"rstn_confirm_{country_id}",
                )],
                [InlineKeyboardButton("❌ বাতিল", callback_data="rstn_cancel")],
            ]),
        )
        return

    if data.startswith("rstn_confirm_") and is_admin(uid):
        country_id   = int(data.split("_")[2])
        country_name = ctx.user_data.get("rstn_country_name", str(country_id))
        deleted = db_execute("DELETE FROM numbers WHERE country_id=?", (country_id,))
        ctx.user_data.clear()
        await query.edit_message_text(
            f"✅ <b>{country_name}</b> — <b>{max(deleted, 0):,}</b>টি নম্বর মুছে ফেলা হয়েছে।",
            parse_mode="HTML"
        )
        await ctx.bot.send_message(
            chat_id=uid,
            text=f"🌍 Country Management",
            reply_markup=country_mgmt_keyboard()
        )
        return

    if data == "rstn_cancel" and is_admin(uid):
        ctx.user_data.clear()
        await query.edit_message_text("❌ বাতিল করা হয়েছে।")
        await ctx.bot.send_message(
            chat_id=uid,
            text="🌍 Country Management",
            reply_markup=country_mgmt_keyboard()
        )
        return

    # ── REMOVE ADMIN ──────────────────────────────────────────────────────────
    if data.startswith("rem_admin_") and is_admin(uid):
        target_uid = int(data.split("_")[2])
        if target_uid in SUPER_ADMINS:
            await query.answer("Cannot remove a permanent super-admin.", show_alert=True)
            return
        user_row = db_query("SELECT first_name, username FROM users WHERE uid=?", (target_uid,))
        name  = user_row[0]["first_name"] if user_row else str(target_uid)
        uname = f"@{user_row[0]['username']}" if user_row and user_row[0]["username"] else ""
        db_execute("DELETE FROM admins WHERE uid=?", (target_uid,))
        ctx.user_data.clear()
        await query.edit_message_text(
            f"✅ <b>{name}</b> {uname} (<code>{target_uid}</code>) has been removed from admin.",
            parse_mode="HTML"
        )
        await ctx.bot.send_message(chat_id=uid, text="👥 User Management", reply_markup=user_mgmt_keyboard())
        try:
            await ctx.bot.send_message(
                chat_id=target_uid,
                text="⚠️ Your <b>Admin</b> access has been revoked.",
                parse_mode="HTML", reply_markup=user_keyboard()
            )
        except Exception:
            pass
        return

    # ── PANEL INLINE CALLBACKS ────────────────────────────────────────────────
    if data.startswith("panel_toggle_") and is_admin(uid):
        pid = int(data.split("_")[2])
        row = db_query("SELECT id, name, active FROM panels WHERE id=?", (pid,))
        if not row:
            await query.answer("Panel not found.", show_alert=True)
            return
        new_active = 0 if row[0]["active"] else 1
        db_execute("UPDATE panels SET active=? WHERE id=?", (new_active, pid))
        status = "🟢 চালু" if new_active else "🔴 বন্ধ"
        await query.answer(f"{row[0]['name']} {status}", show_alert=True)
        try:
            await query.edit_message_reply_markup(
                reply_markup=panel_action_markup(pid, new_active)
            )
        except Exception:
            pass
        await ctx.bot.send_message(chat_id=uid, text=panels_list_text(), parse_mode="HTML",
                                   reply_markup=panels_keyboard())
        return

    if data.startswith("panel_del_") and is_admin(uid):
        pid = int(data.split("_")[2])
        row = db_query("SELECT name FROM panels WHERE id=?", (pid,))
        if not row:
            await query.answer("Panel not found.", show_alert=True)
            return
        name = row[0]["name"]
        await query.edit_message_text(
            f"⚠️ <b>{name}</b> মুছে ফেলবেন?",
            parse_mode="HTML",
            reply_markup=InlineKeyboardMarkup([
                [InlineKeyboardButton("✅ হ্যাঁ, মুছুন", callback_data=f"panel_delconfirm_{pid}"),
                 InlineKeyboardButton("❌ না", callback_data="panel_delcancel")]
            ])
        )
        return

    if data.startswith("panel_delconfirm_") and is_admin(uid):
        pid = int(data.split("_")[2])
        row = db_query("SELECT id, name, stats_url FROM panels WHERE id=?", (pid,))
        name = row[0]["name"] if row else "?"
        panel_key = _panel_sms_cache_key(row[0]) if row else pid
        db_execute("DELETE FROM panels WHERE id=?", (pid,))
        _forget_panel_runtime_state(panel_key)
        await query.edit_message_text(f"✅ Panel <b>{name}</b> মুছে ফেলা হয়েছে।", parse_mode="HTML")
        await ctx.bot.send_message(chat_id=uid, text=panels_list_text(), parse_mode="HTML",
                                   reply_markup=panels_keyboard())
        return

    if data == "panel_delcancel" and is_admin(uid):
        await query.edit_message_text("❌ বাতিল।")
        return

    if data.startswith("panel_info_") and is_admin(uid):
        pid = int(data.split("_")[2])
        row = db_query("SELECT * FROM panels WHERE id=?", (pid,))
        if not row:
            await query.answer("Panel not found.", show_alert=True)
            return
        p = row[0]
        last_ts  = p["last_seen_ts"] or "এখনো scan হয়নি"
        status   = "🟢 Active" if p["active"] else "🔴 Paused"
        panel_type = _panel_type(p)
        session  = (
            "🔌 API configured"
            if panel_type == "api"
            else ("✅ আছে" if p["cookies"] else "❌ নেই")
        )
        num_idx  = p["number_col_idx"]  if p["number_col_idx"]  is not None else 2
        snd_idx  = p["sender_col_idx"]  if p["sender_col_idx"]  is not None else 3
        msg_idx  = p["message_col_idx"] if p["message_col_idx"] is not None else 5
        api_info = (
            f"📤 Method: <b>{_html.escape(str(p['api_method'] or 'GET'))}</b>\n"
            f"🔑 Auth: <b>{_html.escape(str(p['api_auth_type'] or 'auto'))}</b>\n"
            if panel_type == "api" else ""
        )
        await query.answer("ℹ️ নিচে বিস্তারিত দেখুন।")
        await ctx.bot.send_message(
            chat_id=uid,
            text=(
                f"📡 <b>{_html.escape(str(p['name']))}</b>\n"
                f"🔐 Type: <b>{panel_type.upper()}</b>\n"
                f"👤 Username: <code>{_html.escape(str(p['username'] or '—'))}</code>\n"
                f"🔗 Login URL: <code>{_html.escape(str(p['login_url'] or '—'))}</code>\n"
                f"📊 Stats URL: <code>{_html.escape(str(p['stats_url'] or '—'))}</code>\n"
                + api_info
                + f"স্ট্যাটাস: {status}\n"
                + f"Session: {session}\n"
                + f"Last scan: <code>{last_ts}</code>\n\n"
                + f"<b>Column Config:</b>\n"
                + f"📞 Number  → index <b>{num_idx}</b> ({p['number_col_name'] or 'Number'})\n"
                + f"👤 Sender  → index <b>{snd_idx}</b> ({p['sender_col_name'] or 'CLI'})\n"
                + f"💬 Message → index <b>{msg_idx}</b> ({p['message_col_name'] or 'Message'})\n\n"
                + f"Column index ভুল হলে 📊 Raw Data দিয়ে দেখুন, তারপর ✏️ Edit Columns দিয়ে ঠিক করুন।"
            ),
            parse_mode="HTML"
        )
        return

    if data.startswith("panel_lastmsgs_") and is_admin(uid):
        pid = int(data.split("_")[2])
        row = db_query("SELECT * FROM panels WHERE id=?", (pid,))
        if not row:
            await query.answer("Panel not found.", show_alert=True)
            return
        panel = row[0]
        await query.edit_message_text("🔄 Fetching...", parse_mode="HTML")
        sms_rows = await asyncio.to_thread(
            panel_fetch_sms, panel, 1, True
        )
        if sms_rows is None:
            panel_type = _panel_type(panel)
            error_text = (
                "API authorization failed — API key/header যাচাই করুন।"
                if panel_type == "api"
                else "session expired — আবার login করুন।"
            )
            await query.edit_message_text(
                f"⚠️ <b>{panel['name']}</b> {error_text}", parse_mode="HTML"
            )
        elif not sms_rows:
            await query.edit_message_text(
                f"📭 <b>{panel['name']}</b> — আজকে কোনো message নেই।", parse_mode="HTML"
            )
        else:
            await query.edit_message_text(
                format_last_sms(panel['name'], sms_rows), parse_mode="HTML"
            )
        return

    # ── PANEL RAW DATA ────────────────────────────────────────────────────────
    if data.startswith("panel_rawdata_") and is_admin(uid):
        pid = int(data.split("_")[2])
        row = db_query("SELECT * FROM panels WHERE id=?", (pid,))
        if not row:
            await query.answer("Panel not found.", show_alert=True)
            return
        panel = row[0]
        await query.edit_message_text("🔄 Raw data লোড হচ্ছে...", parse_mode="HTML")
        raw = await asyncio.to_thread(panel_fetch_raw_row, panel)
        if raw is None:
            await query.edit_message_text("❌ Session expired. Panel টি re-login করুন।", parse_mode="HTML")
            return
        if not raw:
            await query.edit_message_text("📭 কোনো data নেই।", parse_mode="HTML")
            return
        num_idx = panel["number_col_idx"] if panel["number_col_idx"] is not None else 2
        snd_idx = panel["sender_col_idx"] if panel["sender_col_idx"] is not None else 3
        msg_idx = panel["message_col_idx"] if panel["message_col_idx"] is not None else 5
        lines = [
            f"📊 <b>Raw Data — {_html.escape(str(panel['name']))}</b>\n"
            "(প্রথম row-এর সব field)\n"
        ]
        if isinstance(raw, dict):
            for key, val in list(raw.items())[:100]:
                lines.append(
                    f"<b>{_html.escape(str(key))}</b>: "
                    f"<code>{_html.escape(str(val)[:160])}</code>"
                )
        else:
            for i, val in enumerate(raw[:100]):
                tag = ""
                if i == num_idx: tag = "  ← 📞 current Number"
                elif i == snd_idx: tag = "  ← 👤 current Sender"
                elif i == msg_idx: tag = "  ← 💬 current Message"
                lines.append(
                    f"[{i}]: <code>{_html.escape(str(val)[:160])}</code>{tag}"
                )
        lines.append(f"\n✏️ ভুল index থাকলে <b>Edit Columns</b> দিয়ে ঠিক করুন।")
        await query.edit_message_text(
            "\n".join(lines), parse_mode="HTML",
            reply_markup=InlineKeyboardMarkup([[
                InlineKeyboardButton("✏️ Edit Columns", callback_data=f"panel_editcols_{pid}")
            ]])
        )
        return

    # ── PANEL SCAN INTERVAL ───────────────────────────────────────────────────
    if data.startswith("panel_interval_") and is_admin(uid):
        pid = int(data.split("_")[2])
        row = db_query(
            "SELECT id, name, scan_interval, panel_type FROM panels WHERE id=?",
            (pid,),
        )
        if not row:
            await query.answer("Panel not found.", show_alert=True)
            return
        p = row[0]
        current_interval = p["scan_interval"] if p["scan_interval"] else 60
        ctx.user_data.clear()
        ctx.user_data["state"]        = "panel_set_pinterval"
        ctx.user_data["pi_panel_id"]  = pid
        ctx.user_data["pi_panel_name"] = p["name"]
        ctx.user_data["pi_panel_type"] = _panel_type(p)
        await query.answer()
        await ctx.bot.send_message(
            chat_id=uid,
            text=(
                f"⏱ <b>Scan Interval — {p['name']}</b>\n\n"
                f"বর্তমান: <b>{current_interval} সেকেন্ড</b>\n\n"
                f"এই panel-এর জন্য নতুন interval লিখুন (সেকেন্ডে, minimum 3):\n"
                f"উদাহরণ: <code>3</code>"
                + (
                    "\nAPI panel-এ আপনি যে interval লিখবেন, bot সেই interval-এই "
                    "request করবে।"
                    if _panel_type(p) == "api" else ""
                )
            ),
            parse_mode="HTML", reply_markup=cancel_inline()
        )
        return

    # ── PANEL EDIT COLUMNS ────────────────────────────────────────────────────
    if data.startswith("panel_editcols_") and is_admin(uid):
        pid = int(data.split("_")[2])
        row = db_query("SELECT id, name, number_col_idx, sender_col_idx, message_col_idx FROM panels WHERE id=?", (pid,))
        if not row:
            await query.answer("Panel not found.", show_alert=True)
            return
        p = row[0]
        ctx.user_data.clear()
        ctx.user_data["state"]       = "panel_editcols_num_idx"
        ctx.user_data["ec_panel_id"] = pid
        await query.answer()
        await ctx.bot.send_message(
            chat_id=uid,
            text=(
                f"✏️ <b>Edit Columns — {p['name']}</b>\n\n"
                f"বর্তমান: Number={p['number_col_idx']}, "
                f"Sender={p['sender_col_idx']}, "
                f"Message={p['message_col_idx']}\n\n"
                f"Step 1/3 — Number column index লিখুন:\n"
                f"উদাহরণ: <code>2</code>"
            ),
            parse_mode="HTML", reply_markup=cancel_inline()
        )
        return

    # ── GET NUMBER (User) ─────────────────────────────────────────────────────
    def _gn_number_keyboard(
        rows_given,
        service_id: int,
        cid: int,
        remove_country_code: bool = False,
    ) -> InlineKeyboardMarkup:
        otp_url = get_setting("otp_link", "https://t.me/sxotp99")
        num_btns = [
            [InlineKeyboardButton(
                _number_button_text(r["number"], remove_country_code),
                copy_text=CopyTextButton(
                    text=_number_button_text(r["number"], remove_country_code)
                ),
                style=INLINE_SUCCESS,
            )]
            for r in rows_given
        ]
        change_number_callback = (
            f"gn_change_{service_id}_{cid}_no_cc"
            if remove_country_code
            else f"gn_change_{service_id}_{cid}"
        )
        action_btns = [
            [InlineKeyboardButton(
                "Add CC" if remove_country_code else "Remove CC",
                callback_data=(
                    f"gn_cc_add_{service_id}_{cid}"
                    if remove_country_code
                    else f"gn_cc_remove_{service_id}_{cid}"
                ),
                icon_custom_emoji_id=(
                    "6068905891531332936"
                    if remove_country_code
                    else "6068768181994921479"
                ),
            )],
            [InlineKeyboardButton(
                "Change Number",
                callback_data=change_number_callback,
                icon_custom_emoji_id="6068707416797618717",
            )],
            [InlineKeyboardButton(
                "Change Country",
                callback_data=f"gn_countries_{service_id}",
                icon_custom_emoji_id="6068649679552257644",
            )],
            [InlineKeyboardButton(
                "GET OTP",
                url=otp_url,
                icon_custom_emoji_id="6068705166234755288",
            )],
        ]
        return InlineKeyboardMarkup(num_btns + action_btns)

    def _gn_service_list_markup() -> tuple:
        rows_s = get_number_services()
        if not rows_s:
            return None, None
        return rows_s, number_services_markup(rows_s)

    def _gn_country_list_markup(service_id: int) -> tuple:
        rows_c = get_number_countries(service_id)
        if not rows_c:
            return None, None
        btns = []
        for i in range(0, len(rows_c), 2):
            btns.append([
                InlineKeyboardButton(
                    country_button_name(country),
                    callback_data=f"gncountry_{service_id}_{country['id']}",
                    icon_custom_emoji_id=country_icon_custom_emoji_id(country),
                )
                for country in rows_c[i:i + 2]
            ])
        btns.append([
            InlineKeyboardButton(
                "Back to Services",
                callback_data="gn_services_back",
                icon_custom_emoji_id=GET_NUMBER_BACK_EMOJI_ID,
            )
        ])
        return rows_c, InlineKeyboardMarkup(btns)

    if data.startswith("gnsvc_"):
        service_id = int(data.split("_")[1])
        service = db_query("SELECT id, name, emoji_entities FROM services WHERE id=? AND active=1", (service_id,))
        _, markup = _gn_country_list_markup(service_id)
        if not service or not markup:
            await query.edit_message_text(
                "❌ এই service-এর কোনো country-তে number available নেই।",
                parse_mode="HTML"
            )
        else:
            await query.edit_message_text(
                f"📱 <b>{service_display_html(service[0])}</b>\n\nSelect a country:",
                parse_mode="HTML",
                reply_markup=markup
            )
        return

    if data.startswith("gncountry_"):
        _, service_id_raw, country_id_raw = data.split("_", 2)
        service_id = int(service_id_raw)
        country_id = int(country_id_raw)
        num_per_user = configured_numbers_per_user()
        valid_country = db_query(
            """
            SELECT c.id FROM service_countries sc
            JOIN countries c ON c.id=sc.country_id AND c.active=1
            WHERE sc.service_id=? AND c.id=?
            """,
            (service_id, country_id),
        )
        rows = (
            claim_available_numbers(uid, country_id, num_per_user)
            if valid_country else []
        )
        if rows:
            await query.edit_message_text(
                number_assigned_text(rows, service_id, country_id),
                parse_mode="HTML",
                reply_markup=_gn_number_keyboard(rows, service_id, country_id)
            )
        else:
            await query.edit_message_text(
                "❌ No numbers available for this country.",
                parse_mode="HTML",
                reply_markup=InlineKeyboardMarkup([
                    [InlineKeyboardButton("Change Country", callback_data=f"gn_countries_{service_id}")],
                    [InlineKeyboardButton("GET OTP", url=get_setting("otp_link", "https://t.me/sxotp99"))],
                ])
            )
        return

    if data.startswith("gn_cc_"):
        parts = data.split("_")
        if len(parts) != 5 or parts[2] not in {"add", "remove"}:
            await query.answer("Invalid number format.", show_alert=True)
            return
        try:
            service_id = int(parts[3])
            country_id = int(parts[4])
        except ValueError:
            await query.answer("Invalid number selection.", show_alert=True)
            return

        rows = _current_assigned_number_rows(uid, country_id)
        if not rows:
            await query.answer(
                "এই number card-এর assignment আর পাওয়া যাচ্ছে না।",
                show_alert=True,
            )
            return

        remove_country_code = parts[2] == "remove"
        await query.edit_message_reply_markup(
            reply_markup=_gn_number_keyboard(
                rows,
                service_id,
                country_id,
                remove_country_code=remove_country_code,
            )
        )
        await query.answer(
            "Country code removed." if remove_country_code else "Country code added."
        )
        return

    if data.startswith("gn_countries_"):
        service_id = int(data.split("_")[2])
        _, markup = _gn_country_list_markup(service_id)
        if not markup:
            await query.edit_message_text(
                "❌ এই service-এর কোনো country-তে number available নেই。",
                parse_mode="HTML"
            )
        else:
            await query.edit_message_text(
                "📱 <b>Change Country</b>\n\nSelect a country:",
                parse_mode="HTML",
                reply_markup=markup
            )
        return

    if data == "gn_services_back":
        _, markup = _gn_service_list_markup()
        if not markup:
            await query.edit_message_text(
                "❌ No numbers available at the moment.",
                parse_mode="HTML"
            )
        else:
            await query.edit_message_text(
                GET_NUMBER_SERVICE_PROMPT,
                parse_mode="HTML",
                reply_markup=markup
            )
        return

    if data == "gn_countries":
        _, markup = _gn_service_list_markup()
        if not markup:
            await query.edit_message_text("❌ No numbers available at the moment.", parse_mode="HTML")
        else:
            await query.edit_message_text(
                GET_NUMBER_SERVICE_PROMPT,
                parse_mode="HTML",
                reply_markup=markup,
            )
        return

    if data.startswith("gn_cc_remove_") or data.startswith("gn_cc_add_"):
        parts = data.split("_")
        if len(parts) != 5:
            await query.answer("Invalid number display option.", show_alert=True)
            return

        try:
            service_id = int(parts[3])
            country_id = int(parts[4])
        except ValueError:
            await query.answer("Invalid number selection.", show_alert=True)
            return

        rows = _current_assigned_number_rows(uid, country_id)
        if not rows:
            await query.answer("Assigned number not found.", show_alert=True)
            return

        remove_country_code = data.startswith("gn_cc_remove_")
        await query.answer(
            "Country code removed." if remove_country_code else "Country code added."
        )
        await query.edit_message_reply_markup(
            reply_markup=_gn_number_keyboard(
                rows,
                service_id,
                country_id,
                remove_country_code=remove_country_code,
            )
        )
        return

    if data.startswith("gn_change_"):
        parts = data.split("_")
        remove_country_code = False
        if len(parts) == 6 and parts[4] == "no" and parts[5] == "cc":
            service_id = int(parts[2])
            country_id = int(parts[3])
            remove_country_code = True
        elif len(parts) == 4:
            service_id = int(parts[2])
            country_id = int(parts[3])
        elif len(parts) == 3:
            service_id = 0
            country_id = int(parts[2])
        else:
            await query.answer("Invalid number selection.", show_alert=True)
            return
        num_per_user = configured_numbers_per_user()
        rows = claim_available_numbers(
            uid,
            country_id,
            num_per_user,
            bypass_cooldown=True,
        )
        if rows:
            await query.edit_message_text(
                number_assigned_text(rows, service_id, country_id),
                parse_mode="HTML",
                reply_markup=_gn_number_keyboard(
                    rows,
                    service_id,
                    country_id,
                    remove_country_code=remove_country_code,
                )
            )
        else:
            await query.edit_message_text(
                "❌ No more numbers available for this country.",
                parse_mode="HTML",
                reply_markup=InlineKeyboardMarkup([
                    [InlineKeyboardButton(
                        "Change Country",
                        callback_data=f"gn_countries_{service_id}" if service_id else "gn_countries"
                    )],
                    [InlineKeyboardButton("GET OTP",           url=get_setting("otp_link", "https://t.me/sxotp99"))],
                ])
            )
        return

    if data.startswith("gn_"):
        country_id = int(data[3:])
        num_per_user = configured_numbers_per_user()
        rows = claim_available_numbers(uid, country_id, num_per_user)
        if rows:
            await query.edit_message_text(
                number_assigned_text(rows, 0, country_id),
                parse_mode="HTML",
                reply_markup=_gn_number_keyboard(rows, 0, country_id)
            )
        else:
            await query.edit_message_text(
                "❌ No numbers available for this country.",
                parse_mode="HTML",
                reply_markup=InlineKeyboardMarkup([
                    [InlineKeyboardButton("Change Country", callback_data="gn_countries")],
                    [InlineKeyboardButton("GET OTP",        url=get_setting("otp_link", "https://t.me/sxotp99"))],
                ])
            )
        return


# ─── BROADCAST HANDLER (any message type) ────────────────────────────────────
class _BroadcastRateLimiter:
    """Reserve steady send slots and apply a shared Telegram 429 backoff."""

    def __init__(self, rate_per_second: float):
        self._interval = 1.0 / max(1.0, rate_per_second)
        self._lock = asyncio.Lock()
        self._next_slot = 0.0
        self._blocked_until = 0.0

    async def acquire(self):
        loop = asyncio.get_running_loop()
        while True:
            async with self._lock:
                now = loop.time()
                slot = max(now, self._next_slot, self._blocked_until)
                self._next_slot = slot + self._interval
                wait_for = slot - now
            if wait_for > 0:
                await asyncio.sleep(wait_for)
            # A different worker may have received a 429 while this request
            # was waiting. Re-check so already-reserved slots do not punch
            # through the shared backoff window.
            async with self._lock:
                if slot < self._blocked_until:
                    continue
            return

    async def backoff(self, seconds: float):
        loop = asyncio.get_running_loop()
        delay = max(1.0, min(float(seconds), 60.0))
        async with self._lock:
            blocked_until = loop.time() + delay
            self._blocked_until = max(self._blocked_until, blocked_until)
            # Drop already-reserved slots. Continuing a queued burst after a
            # 429 would immediately trigger another 429.
            self._next_slot = self._blocked_until


async def broadcast_receive_handler(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    if not (is_admin(uid) and ctx.user_data.get("state") == "broadcast_wait"):
        return
    if not update.message:
        return

    msg = update.message
    ctx.user_data.clear()

    users = db_query("SELECT uid FROM users WHERE banned=0")
    if not users:
        await msg.reply_text("⚠️ No users found.", reply_markup=admin_keyboard())
        return

    total = len(users)
    progress_msg = await msg.reply_text(
        f"📢 Broadcasting to <b>{total}</b> users...\n⏳ 0/{total} (0%)",
        parse_mode="HTML"
    )

    sent = blocked = failed = done = 0
    progress_lock = asyncio.Lock()
    last_progress_done = 0
    rate_limiter = _BroadcastRateLimiter(BROADCAST_RATE_PER_SECOND)

    async def send_one(target_uid: int):
        nonlocal sent, blocked, failed
        for attempt in range(BROADCAST_RETRY_ATTEMPTS):
            try:
                await rate_limiter.acquire()
                await ctx.bot.copy_message(
                    chat_id=target_uid,
                    from_chat_id=msg.chat_id,
                    message_id=msg.message_id
                )
                sent += 1
                return
            except Exception as e:
                err = str(e).lower()
                if any(x in err for x in ("blocked", "deactivated", "not found",
                                           "chat not found", "forbidden", "kicked",
                                           "user is deactivated", "bot was blocked")):
                    blocked += 1
                    return

                retry_after = getattr(e, "retry_after", None)
                if attempt < BROADCAST_RETRY_ATTEMPTS - 1:
                    try:
                        delay = float(retry_after or (2 ** attempt))
                    except (TypeError, ValueError):
                        delay = float(2 ** attempt)
                    if retry_after is not None or "429" in err or "retry after" in err:
                        await rate_limiter.backoff(delay)
                    else:
                        await asyncio.sleep(max(0.5, min(delay, 30.0)))
                    continue

                failed += 1
                logger.warning("Broadcast failed uid=%s: %s", target_uid, e)

    async def update_progress():
        nonlocal last_progress_done
        async with progress_lock:
            if done == total or (
                done - last_progress_done >= BROADCAST_PROGRESS_STEP
            ):
                last_progress_done = done
                pct = int(done / total * 100)
                try:
                    await progress_msg.edit_text(
                        f"📢 Broadcasting...\n⏳ {done}/{total} ({pct}%)",
                        parse_mode="HTML"
                    )
                except Exception:
                    pass

    async def worker(queue):
        nonlocal done
        while True:
            target_uid = await queue.get()
            try:
                await send_one(target_uid)
                done += 1
                await update_progress()
            finally:
                queue.task_done()

    uid_list = [u["uid"] for u in users]
    queue = asyncio.Queue()
    for target_uid in uid_list:
        queue.put_nowait(target_uid)

    workers = [
        asyncio.create_task(worker(queue))
        for _ in range(min(BROADCAST_WORKERS, total))
    ]
    await queue.join()
    for task in workers:
        task.cancel()
    await asyncio.gather(*workers, return_exceptions=True)

    await progress_msg.edit_text(
        f"✅ <b>Broadcast Complete!</b>\n\n"
        f"✔️ Sent: <b>{sent}</b>\n"
        f"🚫 Blocked/Inactive: <b>{blocked}</b>\n"
        f"❌ Failed: <b>{failed}</b>\n"
        f"👥 Total: <b>{total}</b>",
        parse_mode="HTML"
    )
    await delete_incoming_message(update)
    await ctx.bot.send_message(chat_id=uid, text="🛠 Admin Panel",
                               reply_markup=admin_keyboard())
    raise ApplicationHandlerStop

# ─── PANEL HELPERS ────────────────────────────────────────────────────────────
class _PanelLoginFormParser(HTMLParser):
    """Collect ordinary HTML login forms without adding a browser dependency."""

    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.forms = []
        self._form = None

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if tag.lower() == "form":
            self._form = {
                "action": attrs.get("action") or "",
                "method": (attrs.get("method") or "POST").upper(),
                "fields": {},
            }
            self.forms.append(self._form)
            return
        if tag.lower() != "input" or self._form is None:
            return
        name = (attrs.get("name") or "").strip()
        input_type = (attrs.get("type") or "text").casefold()
        if name and input_type not in {"submit", "button", "image", "reset"}:
            self._form["fields"][name] = attrs.get("value") or ""

    def handle_endtag(self, tag):
        if tag.lower() == "form":
            self._form = None


def _panel_login_candidates(login_url: str, html: str):
    """Return form/action/data candidates for a standard web login."""
    parser = _PanelLoginFormParser()
    try:
        parser.feed(html or "")
    except Exception:
        parser.forms = []

    user_names = (
        "username", "user_name", "user", "email", "login", "account",
    )
    password_names = ("password", "pass", "passwd", "user_password")
    candidates = []
    for form in parser.forms:
        fields = dict(form["fields"])
        normalized = {_api_key_name(name): name for name in fields}
        user_field = next(
            (normalized[_api_key_name(name)] for name in user_names
             if _api_key_name(name) in normalized),
            next(
                (
                    field_name for normalized_name, field_name in normalized.items()
                    if any(
                        marker in normalized_name
                        for marker in ("user", "login", "email", "account")
                    )
                ),
                "username",
            ),
        )
        password_field = next(
            (normalized[_api_key_name(name)] for name in password_names
             if _api_key_name(name) in normalized),
            next(
                (
                    field_name for normalized_name, field_name in normalized.items()
                    if any(
                        marker in normalized_name
                        for marker in ("pass", "pwd", "secret")
                    )
                ),
                "password",
            ),
        )
        action = urljoin(login_url, form["action"] or login_url)
        fields[user_field] = "__PANEL_USERNAME__"
        fields[password_field] = "__PANEL_PASSWORD__"
        candidates.append((form["method"], action, fields))

    if not candidates:
        # Some small panels render the form with JavaScript but still accept
        # the conventional username/password POST contract.
        candidates.extend([
            ("POST", login_url, {
                "username": "__PANEL_USERNAME__",
                "password": "__PANEL_PASSWORD__",
            }),
            ("POST", urljoin(login_url, "signin"), {
                "username": "__PANEL_USERNAME__",
                "password": "__PANEL_PASSWORD__",
            }),
        ])
    return candidates


def _panel_login_response_ok(response, session, cookies_before=None, login_url=None) -> bool:
    """Recognize successful HTML or JSON login responses without false success."""
    if getattr(response, "status_code", 0) >= 400:
        return False
    body = (getattr(response, "text", "") or "")
    lowered = body.casefold()
    try:
        payload = response.json()
    except ValueError:
        payload = None
    if isinstance(payload, dict):
        if payload.get("success") is False or payload.get("authenticated") is False:
            return False
        if (
            payload.get("success") is True
            or payload.get("authenticated") is True
            or payload.get("access_token")
            or payload.get("token")
        ):
            return True
    if any(marker in lowered for marker in (
        "invalid username", "invalid password", "invalid credentials",
        "incorrect password", "incorrect credentials", "login failed",
        "authentication failed", "invalid user",
    )):
        return False
    if any(marker in lowered for marker in (
        "dashboard", "smscdr", "cdr reports", "logout", "sign out",
    )):
        return True
    # Check for the credential form only after success markers.  Some panels
    # keep a hidden login modal on every authenticated page.
    if (
        'name="password"' in lowered
        or "name='password'" in lowered
        or 'type="password"' in lowered
        or "type='password'" in lowered
    ):
        return False
    if cookies_before is not None and dict(session.cookies) != dict(cookies_before):
        return True
    if login_url and getattr(response, "url", ""):
        response_path = urlparse(response.url).path.casefold().rstrip("/")
        login_path = urlparse(login_url).path.casefold().rstrip("/")
        if response_path and response_path != login_path and not any(
            marker in response_path for marker in ("/login", "/signin", "/auth")
        ):
            return True
    return False


def panel_do_web_login(login_url: str, username: str, password: str):
    """Login to a non-captcha web panel and return its session cookies."""
    try:
        session = requests.Session()
        session.headers.update({
            "User-Agent": (
                "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                "AppleWebKit/537.36 (KHTML, like Gecko) "
                "Chrome/131.0.0.0 Safari/537.36"
            ),
            "Accept": (
                "text/html,application/xhtml+xml,application/xml;"
                "q=0.9,image/avif,image/webp,*/*;q=0.8"
            ),
            "Accept-Language": "en-US,en;q=0.9",
        })
        page = session.get(login_url, timeout=15)
        page.raise_for_status()
        candidates = _panel_login_candidates(login_url, page.text)
        for method, action, fields in candidates:
            cookies_before = dict(session.cookies)
            payload = {
                key: (
                    username if value == "__PANEL_USERNAME__"
                    else password if value == "__PANEL_PASSWORD__"
                    else value
                )
                for key, value in fields.items()
            }
            request_method = method if method in {"GET", "POST"} else "POST"
            request_args = {
                "headers": {
                    "Referer": login_url,
                    "Origin": (
                        f"{urlparse(login_url).scheme}://"
                        f"{urlparse(login_url).netloc}"
                    ),
                },
                "timeout": 15,
                "allow_redirects": True,
            }
            # HTML forms using GET put their fields in the query string;
            # requests with ``data=`` silently send the wrong shape for them.
            request_args["params" if request_method == "GET" else "data"] = payload
            response = session.request(request_method, action, **request_args)
            if _panel_login_response_ok(
                response, session, cookies_before=cookies_before, login_url=login_url
            ):
                return {cookie.name: cookie.value for cookie in session.cookies}
        logger.warning("Non-captcha panel login did not return an authenticated session")
        return None
    except Exception as exc:
        logger.warning("Non-captcha panel login error: %s", type(exc).__name__)
        return None


def _panel_browser_executable():
    """Return the first available Chromium executable for JS-rendered panels."""
    for candidate in _BROWSER_EXECUTABLE_CANDIDATES:
        if candidate and os.path.isfile(candidate) and os.access(candidate, os.X_OK):
            return candidate
    return None


def _browser_visible_locator(page, selectors):
    """Return the first visible locator from a list of CSS selectors."""
    for selector in selectors:
        try:
            locator = page.locator(selector)
            for index in range(min(locator.count(), 5)):
                item = locator.nth(index)
                if item.is_visible(timeout=500):
                    return item
        except Exception:
            continue
    return None


def _browser_fill_login_fields(page, username: str, password: str):
    """Fill common login controls without depending on a provider's HTML names."""
    user_input = _browser_visible_locator(page, [
        'input[autocomplete="username"]',
        'input[name*="user" i]',
        'input[name*="email" i]',
        'input[id*="user" i]',
        'input[id*="email" i]',
        'input[placeholder*="user" i]',
        'input[placeholder*="email" i]',
        'input:not([type="hidden"]):not([type="password"]):not([type="submit"]):not([type="button"])',
    ])
    password_input = _browser_visible_locator(page, [
        'input[autocomplete="current-password"]',
        'input[type="password"]',
        'input[name*="pass" i]',
        'input[id*="pass" i]',
        'input[placeholder*="pass" i]',
    ])
    if user_input is None or password_input is None:
        return False
    user_input.fill(str(username))
    password_input.fill(str(password))

    # Handle simple arithmetic captchas used by many older panels. Human or
    # third-party challenge pages are intentionally not bypassed.
    try:
        body_text = page.locator("body").inner_text(timeout=1000)
    except Exception:
        body_text = ""
    arithmetic = re.search(r"(?<!\d)(\d+)\s*\+\s*(\d+)(?!\d)", body_text)
    if arithmetic:
        answer = str(int(arithmetic.group(1)) + int(arithmetic.group(2)))
        captcha_input = _browser_visible_locator(page, [
            'input[name*="capt" i]',
            'input[id*="capt" i]',
            'input[placeholder*="capt" i]',
            'input[name*="answer" i]',
            'input[id*="answer" i]',
        ])
        if captcha_input is not None:
            captcha_input.fill(answer)
    elif re.search(r"(recaptcha|hcaptcha|cloudflare turnstile)", body_text, re.I):
        logger.warning("Panel login requires a human verification challenge")
        return False
    return True


def _browser_page_requires_login(page):
    """Detect a client-rendered login screen after navigation."""
    try:
        current_url = str(page.url or "").casefold()
        password_input = _browser_visible_locator(page, [
            'input[type="password"]',
            'input[name*="pass" i]',
            'input[id*="pass" i]',
        ])
        if password_input is not None:
            return True
        return any(marker in urlparse(current_url).path for marker in (
            "/login", "/signin", "/auth"
        ))
    except Exception:
        return True


def _browser_wait_after_action(page):
    """Allow SPA route changes and API-driven rendering to settle."""
    try:
        page.wait_for_load_state("networkidle", timeout=10000)
    except PlaywrightTimeoutError:
        pass
    try:
        page.wait_for_timeout(1200)
    except Exception:
        pass


def panel_do_browser_login(login_url: str, username: str, password: str,
                           stats_url: str):
    """Login through a provider-approved browser flow and return state + cookies."""
    executable = _panel_browser_executable()
    if not executable:
        logger.warning("No Chromium executable is available for browser panel login")
        return None
    try:
        with sync_playwright() as playwright:
            browser = playwright.chromium.launch(
                executable_path=executable,
                headless=True,
                args=["--no-sandbox", "--disable-dev-shm-usage"],
            )
            context = browser.new_context(
                user_agent=(
                    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                    "AppleWebKit/537.36 (KHTML, like Gecko) "
                    "Chrome/131.0.0.0 Safari/537.36"
                ),
                viewport={"width": 1365, "height": 900},
            )
            page = context.new_page()
            page.goto(login_url, wait_until="domcontentloaded", timeout=30000)
            _browser_wait_after_action(page)
            if not _browser_fill_login_fields(page, username, password):
                browser.close()
                return None

            submit = _browser_visible_locator(page, [
                'button:has-text("Login")',
                'button:has-text("Sign in")',
                'button:has-text("Log in")',
                'input[type="submit"]',
                'button[type="submit"]',
            ])
            if submit is not None:
                submit.click(timeout=5000)
            else:
                page.locator('input[type="password"]').first.press("Enter")
            _browser_wait_after_action(page)

            if stats_url:
                page.goto(stats_url, wait_until="domcontentloaded", timeout=30000)
                _browser_wait_after_action(page)
            if _browser_page_requires_login(page):
                logger.warning(
                    "Browser panel login did not reach an authenticated page: %s",
                    page.url,
                )
                browser.close()
                return None

            state = context.storage_state()
            cookies = {
                cookie["name"]: cookie["value"]
                for cookie in state.get("cookies", [])
                if cookie.get("name")
            }
            browser.close()
            return cookies, json.dumps(state, ensure_ascii=False)
    except Exception as exc:
        logger.warning("Browser panel login error: %s", type(exc).__name__)
        return None


def panel_login_session(login_url: str, username: str, password: str,
                        stats_url: str, panel_type: str):
    """Try the lightweight HTTP adapter, then fall back to a JS browser."""
    login_fn = panel_do_login if panel_type == "captcha" else panel_do_web_login
    cookies = login_fn(login_url, username, password)
    if cookies:
        if panel_type == "captcha" or panel_verify_web_session(stats_url, cookies):
            return cookies, None

    browser_result = panel_do_browser_login(
        login_url, username, password, stats_url
    )
    if browser_result:
        return browser_result
    return None


def _browser_state_cookies(state):
    return {
        cookie["name"]: cookie["value"]
        for cookie in state.get("cookies", [])
        if cookie.get("name")
    }


def _persist_browser_state(panel, state):
    """Persist refreshed browser storage without exposing it in Telegram."""
    panel_id = panel.get("id")
    if panel_id is None:
        return
    cookies = _browser_state_cookies(state)
    db_execute(
        "UPDATE panels SET cookies=?, browser_state=? WHERE id=?",
        (json.dumps(cookies), json.dumps(state, ensure_ascii=False), panel_id),
    )


def panel_browser_fetch_rows(panel_row):
    """Render a JS panel and return visible table rows, or None if logged out."""
    panel = _panel_as_dict(panel_row)
    raw_state = panel.get("browser_state")
    stats_url = str(panel.get("stats_url") or "").strip()
    executable = _panel_browser_executable()
    if not raw_state or not stats_url or not executable:
        return None
    try:
        state = json.loads(raw_state)
        with sync_playwright() as playwright:
            browser = playwright.chromium.launch(
                executable_path=executable,
                headless=True,
                args=["--no-sandbox", "--disable-dev-shm-usage"],
            )
            context = browser.new_context(
                storage_state=state,
                user_agent=(
                    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                    "AppleWebKit/537.36 (KHTML, like Gecko) "
                    "Chrome/131.0.0.0 Safari/537.36"
                ),
                viewport={"width": 1365, "height": 900},
            )
            page = context.new_page()
            page.goto(stats_url, wait_until="domcontentloaded", timeout=30000)
            _browser_wait_after_action(page)
            if _browser_page_requires_login(page):
                browser.close()
                return None

            rows = page.locator("table tbody tr").evaluate_all(
                """rows => rows.map(row =>
                    Array.from(row.querySelectorAll("td"))
                        .map(cell => (cell.innerText || "").trim())
                ).filter(row => row.length)"""
            )
            refreshed_state = context.storage_state()
            _persist_browser_state(panel, refreshed_state)
            browser.close()
            return rows
    except Exception as exc:
        logger.warning(
            "Browser panel fetch error (panel=%s): %s",
            panel.get("name", "?"),
            type(exc).__name__,
        )
        return []


def panel_browser_keepalive(panel_row) -> bool:
    """Touch a saved browser session and persist rotated cookies/storage."""
    panel = _panel_as_dict(panel_row)
    raw_state = panel.get("browser_state")
    stats_url = str(panel.get("stats_url") or "").strip()
    executable = _panel_browser_executable()
    if not raw_state or not stats_url or not executable:
        return False
    try:
        state = json.loads(raw_state)
        with sync_playwright() as playwright:
            browser = playwright.chromium.launch(
                executable_path=executable,
                headless=True,
                args=["--no-sandbox", "--disable-dev-shm-usage"],
            )
            context = browser.new_context(storage_state=state)
            page = context.new_page()
            page.goto(stats_url, wait_until="domcontentloaded", timeout=30000)
            _browser_wait_after_action(page)
            if _browser_page_requires_login(page):
                browser.close()
                return False
            _persist_browser_state(panel, context.storage_state())
            browser.close()
            return True
    except Exception as exc:
        logger.warning(
            "Browser panel keep-alive error (panel=%s): %s",
            panel.get("name", "?"),
            type(exc).__name__,
        )
        return False


def _web_rows_to_sms_results(panel, rows):
    """Map rendered HTML table rows using the same user-selected columns."""
    num_idx = panel["number_col_idx"] if panel["number_col_idx"] is not None else 2
    snd_idx = panel["sender_col_idx"] if panel["sender_col_idx"] is not None else 3
    msg_idx = panel["message_col_idx"] if panel["message_col_idx"] is not None else 5
    min_len = max(num_idx, snd_idx, msg_idx) + 1
    results = []
    for row_index, row in enumerate(rows or []):
        if not isinstance(row, list) or len(row) < min_len:
            continue
        vals = [_strip_html(value) for value in row]
        ts = vals[0] if vals else ""
        rng = vals[1] if len(vals) > 1 else ""
        number = vals[num_idx] if vals[num_idx] else ""
        sender = vals[snd_idx] if vals[snd_idx] else ""
        message = vals[msg_idx] if vals[msg_idx] else ""
        if not ts:
            ts = f"{len(rows) - row_index:012d}"
        if number:
            results.append({
                "ts": ts,
                "range": rng,
                "number": number,
                "sender": sender,
                "message": message,
            })
    results.sort(key=lambda item: item["ts"], reverse=True)
    return results


def panel_verify_web_session(stats_url: str, cookies: dict) -> bool:
    """Verify a newly created web session against the configured SMS page."""
    if not stats_url or not isinstance(cookies, dict) or not cookies:
        return False
    try:
        session = requests.Session()
        session.headers.update({
            "User-Agent": (
                "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                "AppleWebKit/537.36 (KHTML, like Gecko) "
                "Chrome/131.0.0.0 Safari/537.36"
            ),
        })
        for key, value in cookies.items():
            session.cookies.set(key, value)
        response = session.get(stats_url, timeout=15)
        return (
            response.status_code < 400
            and not _panel_session_expired(response)
        )
    except requests.RequestException:
        return False


def panel_do_login(login_url: str, username: str, password: str):
    """
    Login to panel once. Returns cookies dict on success, None on failure.
    Solves the math captcha automatically.
    """
    try:
        s = requests.Session()
        s.headers.update({
            "User-Agent": (
                "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                "AppleWebKit/537.36 (KHTML, like Gecko) "
                "Chrome/131.0.0.0 Safari/537.36"
            ),
            "Accept": (
                "text/html,application/xhtml+xml,application/xml;"
                "q=0.9,image/avif,image/webp,*/*;q=0.8"
            ),
            "Accept-Language": "en-US,en;q=0.9",
        })
        r = s.get(login_url, timeout=15)
        r.raise_for_status()
        q = re.search(r"What is (\d+) \+ (\d+)", r.text)
        if not q:
            logger.warning("Panel login page did not contain the math captcha")
            return None
        ans = int(q.group(1)) + int(q.group(2))
        base = login_url.rsplit("/", 1)[0]
        signin_url = base + "/signin"
        parsed_login_url = urlparse(login_url)
        origin = f"{parsed_login_url.scheme}://{parsed_login_url.netloc}"
        r2 = s.post(
            signin_url,
            data={"username": username, "password": password, "capt": ans},
            headers={
                "Referer": login_url,
                "Origin": origin,
            },
            timeout=15,
            allow_redirects=True,
        )
        if r2.status_code >= 400:
            logger.warning(
                "Panel login request rejected (status=%s, url=%s)",
                r2.status_code,
                r2.url,
            )
            return None

        body = (r2.text or "").casefold()
        login_form_visible = (
            'name="username"' in body and 'name="password"' in body
        )
        invalid_credentials = any(
            marker in body
            for marker in (
                "username/password invalid",
                "invalid username",
                "invalid password",
                "incorrect username",
                "incorrect password",
            )
        )
        if (
            not login_form_visible
            and not invalid_credentials
            and (
                "dashboard" in body
                or "agent panel" in body
                or "smscdrstats" in body
                or "/login" not in r2.url.casefold()
            )
        ):
            return {c.name: c.value for c in s.cookies}
        return None
    except Exception as e:
        logger.warning(f"Panel login error: {e}")
        return None

def _panel_as_dict(panel_row):
    """Normalize sqlite rows and dictionaries for session maintenance helpers."""
    if hasattr(panel_row, "get"):
        return panel_row
    return {key: panel_row[key] for key in panel_row.keys()}

def _panel_session_expired(response) -> bool:
    """Recognize both explicit auth failures and redirects to a login page."""
    body = (getattr(response, "text", "") or "").casefold()
    final_url = str(getattr(response, "url", "") or "").casefold()
    if getattr(response, "status_code", 0) in (401, 403):
        return True
    # Authenticated pages often contain a harmless "Login" navigation label.
    # Only treat the body as a login page when an actual credential form is
    # present, or when the final URL clearly redirected to an auth endpoint.
    if any(marker in body for marker in (
        "dashboard", "smscdr", "cdr reports", "logout", "sign out",
    )):
        return False
    has_password_field = (
        'name="password"' in body
        or "name='password'" in body
        or 'type="password"' in body
        or "type='password'" in body
    )
    return has_password_field or any(
        marker in final_url for marker in ("/login", "/signin", "/auth")
    )

def _panel_relogin_notice_allowed(panel_key) -> bool:
    """Rate-limit admin warnings while still retrying login in the background."""
    now = time.monotonic()
    with _panel_sms_cache_lock:
        last_notice = _panel_relogin_notice_at.get(panel_key, 0)
        if now - last_notice < _PANEL_RELOGIN_NOTICE_COOLDOWN:
            return False
        _panel_relogin_notice_at[panel_key] = now
        return True

def panel_auto_relogin(panel_row):
    """
    Re-authenticate a cookie-based web panel with its stored credentials.
    Returns fresh cookies on success, otherwise None.
    """
    panel = _panel_as_dict(panel_row)
    panel_type = _panel_type(panel)
    if panel_type not in {"captcha", "non_captcha"}:
        return None

    login_url = (panel.get("login_url") or "").strip()
    username = panel.get("username") or ""
    password = panel.get("password") or ""
    if not login_url or not username or not password:
        logger.warning("Panel %s cannot auto-login: credentials are incomplete",
                       panel.get("name", "?"))
        return None

    # Prevent two scheduled jobs from logging into the same service at once.
    with _panel_relogin_lock:
        session_result = panel_login_session(
            login_url,
            username,
            password,
            str(panel.get("stats_url") or ""),
            panel_type,
        )
        if not session_result:
            logger.warning("Panel %s automatic re-login failed",
                           panel.get("name", "?"))
            return None
        cookies, browser_state = session_result

        panel_id = panel.get("id")
        if panel_id is not None:
            db_execute(
                "UPDATE panels SET cookies=?, browser_state=?, active=1 WHERE id=?",
                (json.dumps(cookies), browser_state, panel_id)
            )

        panel_key = _panel_sms_cache_key(panel)
        with _panel_sms_cache_lock:
            _panel_sms_cache.pop(panel_key, None)
            _panel_relogin_notice_at.pop(panel_key, None)
        logger.info("Panel %s automatically re-logged in successfully",
                    panel.get("name", "?"))
        return cookies

def panel_keepalive(panel_row) -> bool:
    """
    Touch a cookie-based web panel regularly so an idle overnight session is less
    likely to expire. If the touch lands on the login page, re-login immediately.
    """
    panel = _panel_as_dict(panel_row)
    if not _is_web_panel(panel):
        return True

    stats_url = (panel.get("stats_url") or "").strip()
    if not stats_url:
        return False

    if panel.get("browser_state"):
        if panel_browser_keepalive(panel):
            return True
        return bool(panel_auto_relogin(panel))

    try:
        cookies = json.loads(panel.get("cookies") or "{}")
        session = requests.Session()
        session.headers.update({
            "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                          "AppleWebKit/537.36"
        })
        for key, value in cookies.items():
            session.cookies.set(key, value)
        response = session.get(stats_url, timeout=15)
        if _panel_session_expired(response):
            return bool(panel_auto_relogin(panel))
        # Some panels rotate cookies while an authenticated page is touched.
        # Persist new values so future keep-alives and scans use fresh cookies.
        refreshed_cookies = session.cookies.get_dict()
        panel_id = panel.get("id")
        if panel_id is not None and refreshed_cookies and refreshed_cookies != cookies:
            try:
                db_execute(
                    "UPDATE panels SET cookies=? WHERE id=?",
                    (json.dumps(refreshed_cookies), panel_id),
                )
            except Exception as exc:
                logger.warning(
                    "Could not persist refreshed cookies for panel %s: %s",
                    panel.get("name", "?"),
                    type(exc).__name__,
                )
        return True
    except Exception as exc:
        logger.warning("Panel keep-alive error (panel=%s): %s",
                       panel.get("name", "?"), exc)
        # A transport error can happen while the panel is rotating its
        # session.  Give the stored credentials one immediate recovery try
        # instead of waiting for the next keep-alive.
        return bool(panel_auto_relogin(panel))

def panel_fetch_raw_row(panel_row):
    """
    Fetch the very first raw row from aaData so admin can inspect column indices.
    Returns list (the row) on success, None if session expired, [] if no data.
    """
    if not hasattr(panel_row, "get"):
        panel_row = {key: panel_row[key] for key in panel_row.keys()}
    if _panel_type(panel_row) == "api":
        stats_url = str(panel_row.get("stats_url") or "").strip()
        if not stats_url:
            return []
        try:
            for request_kwargs in _api_request_attempts(panel_row):
                request_kwargs = dict(request_kwargs)
                request_kwargs["url"] = stats_url
                response = _api_request_with_limits(
                    _panel_sms_cache_key(panel_row), request_kwargs
                )
                if response.status_code == 429:
                    delay = _api_mark_throttled(
                        _panel_sms_cache_key(panel_row), response
                    )
                    _api_set_last_error(
                        panel_row,
                        f"Provider rate limit (HTTP 429); retrying in {delay}s",
                    )
                    return []
                if _api_response_is_auth_error(response):
                    continue
                response.raise_for_status()
                if len(response.content) > API_MAX_RESPONSE_BYTES:
                    return []
                payload = response.json()
                rows = _api_path_value(
                    payload, panel_row.get("api_rows_path")
                )
                if not isinstance(rows, list):
                    rows = _api_payload_rows(payload)
                return rows[0] if rows else []
            return None
        except Exception as exc:
            logger.warning(
                "API raw row error (panel=%s, type=%s)",
                panel_row.get("name", "?"),
                type(exc).__name__,
            )
            return []
    if panel_row.get("browser_state"):
        browser_rows = panel_browser_fetch_rows(panel_row)
        if browser_rows is None:
            refreshed = panel_auto_relogin(panel_row)
            if not refreshed:
                return None
            refreshed_rows = db_query(
                "SELECT * FROM panels WHERE id=?",
                (panel_row.get("id"),),
            )
            browser_rows = (
                panel_browser_fetch_rows(refreshed_rows[0])
                if refreshed_rows else None
            )
            if browser_rows is None:
                return None
        return browser_rows[0] if browser_rows else []
    try:
        cookies = json.loads(panel_row["cookies"]) if panel_row["cookies"] else {}
        s = requests.Session()
        s.headers.update({"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36"})
        for k, v in cookies.items():
            s.cookies.set(k, v)
        stats_url = panel_row["stats_url"]
        r = s.get(stats_url, timeout=15)
        if _panel_session_expired(r):
            refreshed_cookies = panel_auto_relogin(panel_row)
            if not refreshed_cookies:
                return None  # session expired and automatic re-login failed
            s = requests.Session()
            s.headers.update({"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36"})
            for k, v in refreshed_cookies.items():
                s.cookies.set(k, v)
            r = s.get(stats_url, timeout=15)
            if _panel_session_expired(r):
                return None
        ajax_match = (
            re.search(r'"sAjaxSource"\s*:\s*"([^"]+)"', r.text)
            or re.search(r'AjaxSource"?\s*:\s*"([^"]+)"', r.text)
            or re.search(r'"ajax"\s*:\s*"([^"]+)"', r.text)
            or re.search(r"'sAjaxSource'\s*:\s*'([^']+)'", r.text)
            or re.search(r"'ajax'\s*:\s*'([^']+)'", r.text)
        )
        if not ajax_match:
            return []
        data_url = urljoin(
            stats_url,
            _html.unescape(ajax_match.group(1)).replace("\\/", "/"),
        )
        r2 = s.get(data_url, headers={
            "Referer": stats_url,
            "X-Requested-With": "XMLHttpRequest",
            "Accept": "application/json, text/javascript, */*"
        }, timeout=15)
        rows = r2.json().get("aaData", [])
        return rows[0] if rows else []
    except Exception as e:
        logger.warning(f"Panel raw row error: {e}")
        return []

def format_last_sms(panel_name: str, sms_rows: list) -> str:
    """Format the latest SMS rows for display. All user-supplied text is HTML-escaped."""
    divider = "─" * 30
    lines = [f"📋 <b>Last Message · {_html.escape(panel_name)}</b>\n{divider}"]
    for s in sms_rows[:1]:
        number  = _html.escape(str(s.get("number",  "") or ""))
        ts      = _html.escape(str(s.get("ts",      "") or ""))
        sender  = _html.escape(str(s.get("sender",  "") or ""))
        message = _html.escape(str(s.get("message", "") or ""))
        lines.append(
            f"\n📞 <b>নম্বর:</b> <code>{number or '—'}</code>\n"
            f"📅 <b>তারিখ:</b> {ts or '—'}\n"
            f"👤 <b>CLI:</b> {_html.escape(sender) if sender else '—'}\n"
            f"💬 <b>SMS:</b>\n<pre>{message or '—'}</pre>\n"
            f"{divider}"
        )
    return "\n".join(lines)

def _strip_html(text: str) -> str:
    """Remove HTML tags and decode HTML entities from a string."""
    text = re.sub(r'<[^>]+>', '', str(text))
    text = _html.unescape(text)
    return text.strip()

def _country_flag(code: str) -> str:
    """Generate flag emoji from 2-letter country code."""
    code = code.strip().upper()
    if len(code) >= 2 and code[:2].isalpha():
        return (
            chr(0x1F1E6 + ord(code[0]) - ord('A')) +
            chr(0x1F1E6 + ord(code[1]) - ord('A'))
        )
    return "🌐"

def _premium_flag_html(flag: str) -> str:
    """Render a regional flag with the configured animated custom emoji pack."""
    custom_id = _flag_custom_emoji_id(flag)
    if custom_id:
        return (
            f'<tg-emoji emoji-id="{_html.escape(custom_id, quote=True)}">'
            f"{_html.escape(flag)}</tg-emoji>"
        )
    return _html.escape(flag)


SERVICE_SHORT_NAMES = {
    "facebook": "FB",
    "whatsapp": "WA",
    "telegram": "TG",
    "instagram": "IG",
    "tik": "TT",
    "google": "GO",
    "gmail": "GM",
    "tiktok": "TT",
    "twitter": "TW",
    "x": "X",
}


def _service_short_name(name: str) -> str:
    """Return a compact two-character service label for OTP group messages."""
    clean = re.sub(r"[^A-Za-z0-9]+", " ", str(name or "")).strip().casefold()
    if not clean:
        return "—"
    first_word = clean.split()[0]
    if first_word in SERVICE_SHORT_NAMES:
        return SERVICE_SHORT_NAMES[first_word]
    letters = re.sub(r"[^A-Za-z]", "", clean)
    return (letters[:2] or "—").upper()


def _service_group_html(sender: str) -> str:
    """Render the saved service emoji, or only the two-letter fallback name."""
    raw_label = str(sender or "").strip()
    service = _find_service_by_input(raw_label) if raw_label else None
    if service:
        short_name = _service_short_name(copyable_service_name(service))
        logo = service_logo_html(service, fallback="")
        if service_icon_custom_emoji_id(service):
            return logo
        return _html.escape(short_name)
    mapping_key = _service_mapping_key(raw_label)
    builtin_id = SERVICE_CUSTOM_EMOJI_IDS.get(mapping_key)
    if builtin_id:
        glyph = SERVICE_CUSTOM_EMOJI_FALLBACKS.get(mapping_key, "🔔")
        return (
            f'<tg-emoji emoji-id="{_html.escape(builtin_id, quote=True)}">'
            f"{_html.escape(glyph)}</tg-emoji>"
        )
    return _html.escape(_service_short_name(raw_label))


def _country_group_html(number: str, iso2: str) -> str:
    """Render a phone country's saved premium flag for the OTP group line."""
    clean_number = re.sub(r"\D", "", str(number or ""))
    countries = db_query(
        "SELECT id, name, emoji_entities FROM countries WHERE active=1"
    )

    # Prefer the exact inventory number, which is authoritative when the same
    # dial code is shared by multiple countries.
    exact_country_id = None
    if clean_number:
        for row in db_query("SELECT country_id, number FROM numbers"):
            row_number = re.sub(r"\D", "", str(row["number"] or ""))
            if row_number == clean_number:
                exact_country_id = row["country_id"]
                break

    country = next(
        (
            row for row in countries
            if exact_country_id is not None and row["id"] == exact_country_id
        ),
        None,
    )

    # If the number is no longer in inventory, use the country whose saved
    # name contains the detected ISO short name (for example "MM").
    if country is None and iso2:
        country = next(
            (
                row for row in countries
                if re.search(
                    rf"(?<![A-Za-z]){re.escape(iso2)}(?![A-Za-z])",
                    copyable_country_name(row),
                    re.IGNORECASE,
                )
            ),
            None,
        )

    if country:
        raw = country["emoji_entities"]
        try:
            entities = json.loads(raw) if isinstance(raw, str) else raw
        except (TypeError, ValueError):
            entities = None
        if isinstance(entities, list):
            name = str(country["name"])
            for entity in entities:
                if not isinstance(entity, dict):
                    continue
                emoji_id = str(entity.get("id") or "")
                if not emoji_id:
                    continue
                start_units = int(entity.get("offset", 0))
                end_units = start_units + int(entity.get("length", 0))
                start = _utf16_index(name, start_units)
                end = _utf16_index(name, end_units)
                glyph = name[start:end] or _country_flag(iso2)
                return (
                    f'<tg-emoji emoji-id="{_html.escape(emoji_id, quote=True)}">'
                    f"{_html.escape(glyph)}</tg-emoji>"
                )

    return _premium_flag_html(_country_flag(iso2))

def _extract_otp(message: str) -> str | None:
    """Try to extract OTP/verification code from SMS message text."""
    patterns = [
        r'(?:OTP|code|kode|verification|verify|confirm|passcode|password|PIN|token)[^\d]{0,10}(\d{4,8})',
        r'(\d{4,8})(?:\s+is\s+your|\s+ist\s+dein|\s+es\s+tu)',
        r'\b([0-9]{4,8})\b',
    ]
    for pattern in patterns:
        match = re.search(pattern, message, re.IGNORECASE)
        if match:
            return match.group(1)
    return None

def panel_fetch_sms(panel_row, limit=None, force_refresh=False):
    """
    Fetch SMS rows from panel.
    For captcha panels: cookie-based session fetch from SMSCDRStats page.
    For api panels: Bearer-token GET request to stats_url.
    Returns list of dicts with keys: ts, range, number, sender, message
    Returns None if session expired (captcha) or auth failed (api).
    """
    # Rows returned by db_query are sqlite3.Row objects.  They support
    # bracket access but not dict.get(), while API callers may pass a dict.
    # Normalize once so both panel types work from the panel menu callbacks.
    if not hasattr(panel_row, "get"):
        panel_row = {key: panel_row[key] for key in panel_row.keys()}
    panel_type = _panel_type(panel_row)
    panel_key = _panel_sms_cache_key(panel_row)
    cache_ttl = _API_SMS_CACHE_TTL if panel_type == "api" else _CAPTCHA_SMS_CACHE_TTL
    stale_rows = _panel_sms_stale(panel_key) or _panel_persisted_latest(panel_row)
    if not force_refresh:
        cached_rows = _panel_sms_cached(panel_key, cache_ttl)
        if cached_rows is not None:
            return cached_rows[:limit] if limit else cached_rows

    # ── API Panel ─────────────────────────────────────────────────────────────
    if panel_type == "api":
        r = None
        try:
            api_key = str(panel_row.get("api_key") or "").strip()
            stats_url = str(panel_row.get("stats_url") or "").strip()
            parsed_url = urlparse(stats_url)
            if (
                not stats_url
                or parsed_url.scheme not in {"http", "https"}
                or not parsed_url.netloc
            ):
                logger.warning(
                    "API panel %s has an invalid URL",
                    panel_row.get("name", "?"),
                )
                return _panel_sms_store(panel_key, stale_rows, limit)

            attempts = _api_request_attempts(panel_row)
            if not attempts:
                _api_mark_failure(panel_key)
                _api_set_last_error(panel_row, "Invalid authentication configuration")
                return None

            data = None
            auth_failed = False
            throttled_response = None
            for attempt_index, request_kwargs in enumerate(attempts):
                request_kwargs = dict(request_kwargs)
                request_kwargs["url"] = stats_url
                candidate = _api_request_with_limits(panel_key, request_kwargs)
                r = candidate
                if _api_response_is_auth_error(candidate):
                    auth_failed = True
                    continue
                if candidate.status_code == 429:
                    throttled_response = candidate
                    if (
                        str(panel_row.get("api_auth_type") or "auto").casefold()
                        == "auto"
                        and attempt_index < len(attempts) - 1
                    ):
                        continue
                    break
                # Some providers return a transient/server-style error for an
                # unsupported auth format instead of 401/403.  In auto mode,
                # keep trying the remaining formats so a later valid format
                # (for example ?token=...) can succeed.
                if (
                    candidate.status_code >= 500
                    and attempt_index < len(attempts) - 1
                ):
                    continue
                candidate.raise_for_status()
                if len(candidate.content) > API_MAX_RESPONSE_BYTES:
                    raise ValueError(
                        f"API response exceeds {API_MAX_RESPONSE_BYTES // 1024} KB"
                    )
                data = candidate.json()
                auth_failed = False
                _api_remember_auto_auth(panel_row, attempt_index)
                break

            if data is None:
                if throttled_response is not None:
                    delay = _api_mark_throttled(panel_key, throttled_response)
                    _api_set_last_error(
                        panel_row,
                        f"Provider rate limit (HTTP 429); retrying in {delay}s",
                    )
                    return _panel_sms_store(panel_key, stale_rows, limit)
                if auth_failed:
                    _api_mark_failure(panel_key)
                    _api_set_last_error(panel_row, "Authentication failed")
                    return None
                return _panel_sms_store(panel_key, [], limit)

            rows = _api_path_value(data, panel_row.get("api_rows_path"))
            if not isinstance(rows, list):
                rows = _api_payload_rows(data)
            rows = rows[:API_MAX_ROWS]
            num_idx = panel_row["number_col_idx"]  if panel_row["number_col_idx"]  is not None else 2
            snd_idx = panel_row["sender_col_idx"]  if panel_row["sender_col_idx"]  is not None else 3
            msg_idx = panel_row["message_col_idx"] if panel_row["message_col_idx"] is not None else 5
            min_len = max(num_idx, snd_idx, msg_idx) + 1
            field_map = {
                "number": panel_row.get("api_number_field"),
                "sender": panel_row.get("api_sender_field"),
                "message": panel_row.get("api_message_field"),
                "timestamp": panel_row.get("api_timestamp_field"),
                "range": panel_row.get("api_range_field"),
            }
            results = []
            for row_index, row in enumerate(rows):
                vals = _api_row_values(
                    row, num_idx, snd_idx, msg_idx, field_map
                )
                if not vals or len(vals) < min_len:
                    continue
                ts      = _strip_html(vals[0])       if vals[0]         else ""
                rng     = _strip_html(vals[1])       if len(vals) > 1   else ""
                number  = _strip_html(vals[num_idx]) if vals[num_idx]   else ""
                sender  = _strip_html(vals[snd_idx]) if vals[snd_idx]   else ""
                message = _strip_html(vals[msg_idx]) if vals[msg_idx]   else ""
                # Some providers omit a timestamp entirely.  Keep those rows
                # visible instead of dropping the whole panel response; the
                # stable row order still gives the scanner a usable cursor.
                if not ts:
                    ts = f"{len(rows) - row_index:012d}"
                if not number:
                    continue
                results.append({"ts": ts, "range": rng, "number": number, "sender": sender, "message": message})
            results.sort(key=lambda x: x["ts"], reverse=True)
            _api_clear_failure(panel_key)
            _api_set_last_error(panel_row, None)
            _persist_panel_latest_sms(panel_row, results)
            return _panel_sms_store(panel_key, results, limit)
        except requests.RequestException as e:
            logger.warning(
                "API Panel request error (panel=%s, status=%s, type=%s)",
                panel_row.get("name", "?"),
                getattr(r, "status_code", "?"),
                type(e).__name__,
            )
            _api_mark_failure(panel_key)
            status = getattr(r, "status_code", None)
            _api_set_last_error(
                panel_row,
                f"HTTP request failed ({status})" if status else "Network request failed",
            )
            return _panel_sms_store(panel_key, stale_rows, limit)
        except Exception as e:
            logger.warning(
                "API Panel fetch error (panel=%s, type=%s)",
                panel_row.get("name", "?"),
                type(e).__name__,
            )
            _api_mark_failure(panel_key)
            diagnostic = str(e) if isinstance(e, ValueError) else type(e).__name__
            _api_set_last_error(panel_row, diagnostic)
            return _panel_sms_store(panel_key, stale_rows, limit)

    # ── Web Panel (captcha or non-captcha, cookie-based) ──────────────────────
    try:
        if panel_row.get("browser_state"):
            browser_rows = panel_browser_fetch_rows(panel_row)
            if browser_rows is None:
                refreshed = panel_auto_relogin(panel_row)
                if not refreshed:
                    return None
                refreshed_rows = db_query(
                    "SELECT * FROM panels WHERE id=?",
                    (panel_row.get("id"),),
                )
                browser_rows = (
                    panel_browser_fetch_rows(refreshed_rows[0])
                    if refreshed_rows else None
                )
                if browser_rows is None:
                    return None
            results = _web_rows_to_sms_results(panel_row, browser_rows)
            _persist_panel_latest_sms(panel_row, results)
            return _panel_sms_store(panel_key, results, limit)

        cookies = json.loads(panel_row["cookies"]) if panel_row["cookies"] else {}
        sess = requests.Session()
        sess.headers.update({"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36"})
        for k, v in cookies.items():
            sess.cookies.set(k, v)

        stats_url = panel_row["stats_url"]
        r = sess.get(stats_url, timeout=15)

        # Session expiry check. Re-login and retry once before reporting failure.
        if _panel_session_expired(r):
            refreshed_cookies = panel_auto_relogin(panel_row)
            if not refreshed_cookies:
                return None  # session expired and automatic re-login failed
            sess = requests.Session()
            sess.headers.update({
                "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                              "AppleWebKit/537.36"
            })
            for k, v in refreshed_cookies.items():
                sess.cookies.set(k, v)
            r = sess.get(stats_url, timeout=15)
            if _panel_session_expired(r):
                return None

        # Try multiple patterns for AjaxSource URL
        ajax_match = (
            re.search(r'"sAjaxSource"\s*:\s*"([^"]+)"', r.text) or
            re.search(r'AjaxSource"?\s*:\s*"([^"]+)"', r.text) or
            re.search(r'"ajax"\s*:\s*"([^"]+)"', r.text) or
            re.search(r"'sAjaxSource'\s*:\s*'([^']+)'", r.text) or
            re.search(r"'ajax'\s*:\s*'([^']+)'", r.text)
        )
        if not ajax_match:
            logger.warning(f"Panel {panel_row['name']}: AjaxSource not found in page")
            return _panel_sms_store(panel_key, [], limit)

        ajax_path = _html.unescape(ajax_match.group(1)).replace("\\/", "/")
        # Build absolute URL: if already absolute keep it, otherwise join with base
        data_url = urljoin(stats_url, ajax_path)

        r2 = sess.get(data_url, headers={
            "Referer": stats_url,
            "X-Requested-With": "XMLHttpRequest",
            "Accept": "application/json, text/javascript, */*"
        }, timeout=15)
        r2.raise_for_status()

        # dynamic column indices per panel config
        num_idx = panel_row["number_col_idx"]  if panel_row["number_col_idx"]  is not None else 2
        snd_idx = panel_row["sender_col_idx"]  if panel_row["sender_col_idx"]  is not None else 3
        msg_idx = panel_row["message_col_idx"] if panel_row["message_col_idx"] is not None else 5
        min_len = max(num_idx, snd_idx, msg_idx) + 1

        data = r2.json()
        # Support direct DataTables payloads and nested provider envelopes.
        rows = data.get("aaData") or data.get("data") or []
        if not isinstance(rows, list):
            rows = _api_payload_rows(data)
        results = []
        field_map = {
            "number": panel_row.get("number_col_name"),
            "sender": panel_row.get("sender_col_name"),
            "message": panel_row.get("message_col_name"),
        }
        for row_index, row in enumerate(rows):
            if not isinstance(row, (list, dict)):
                continue
            # Dict rows must be matched by field name; relying on insertion
            # order is why many valid "Last SMS" rows previously disappeared.
            vals = _api_row_values(
                row, num_idx, snd_idx, msg_idx, field_map
            )
            if len(vals) < min_len:
                continue
            ts      = _strip_html(vals[0])      if vals[0]         else ""
            rng     = _strip_html(vals[1])      if len(vals) > 1   else ""
            number  = _strip_html(vals[num_idx]) if vals[num_idx]  else ""
            sender  = _strip_html(vals[snd_idx]) if vals[snd_idx]  else ""
            message = _strip_html(vals[msg_idx]) if vals[msg_idx]  else ""
            if not ts:
                ts = f"{len(rows) - row_index:012d}"
            if not number:
                continue
            results.append({"ts": ts, "range": rng, "number": number, "sender": sender, "message": message})

        results.sort(key=lambda x: x["ts"], reverse=True)
        _persist_panel_latest_sms(panel_row, results)
        return _panel_sms_store(panel_key, results, limit)
    except Exception as e:
        logger.warning(f"Panel fetch SMS error (panel={panel_row.get('name','?')}): {e}")
        return _panel_sms_store(panel_key, stale_rows, limit)

def panels_list_text() -> str:
    panels = db_query(
        "SELECT id, name, active, login_url, username, scan_interval, "
        "panel_type, api_last_error, added_at FROM panels ORDER BY id"
    )
    lines = ["📡 <b>Panels</b>\n"]
    if not panels:
        lines.append("📭 No panels added yet.\nPress <b>➕ Add Panel</b> to add one.")
    else:
        for p in panels:
            status   = "🟢 Active" if p["active"] else "🔴 Paused"
            interval = p["scan_interval"] if p["scan_interval"] else 60
            ptype    = _panel_type(p).upper().replace("_", "-")
            type_icon = (
                "🔐" if ptype == "CAPTCHA"
                else "🌐" if ptype == "NON-CAPTCHA"
                else "🔌"
            )
            lines.append(f"<b>{p['name']}</b>  {status}  {type_icon} {ptype}")
            lines.append(f"  👤 {p['username']}")
            lines.append(f"  🔗 {p['login_url']}")
            lines.append(f"  ⏱ Scan interval: <b>{interval}s</b>")
            if ptype == "API" and p["api_last_error"]:
                lines.append(
                    f"  ⚠️ Last API error: <code>"
                    f"{_html.escape(str(p['api_last_error']))}</code>"
                )
            lines.append("")
    return "\n".join(lines)

def panel_action_markup(panel_id: int, active: int):
    """Inline action buttons for a single panel (shown when its name is tapped)."""
    toggle_label = "⏸ Pause" if active else "▶️ Resume"
    return InlineKeyboardMarkup([
        [
            InlineKeyboardButton("ℹ️ Info",       callback_data=f"panel_info_{panel_id}"),
            InlineKeyboardButton(toggle_label,    callback_data=f"panel_toggle_{panel_id}"),
            InlineKeyboardButton("🗑 Delete",     callback_data=f"panel_del_{panel_id}"),
        ],
        [
            InlineKeyboardButton("📋 Last Message", callback_data=f"panel_lastmsgs_{panel_id}"),
            InlineKeyboardButton("📊 Raw Data",    callback_data=f"panel_rawdata_{panel_id}"),
        ],
        [
            InlineKeyboardButton("✏️ Edit Columns",  callback_data=f"panel_editcols_{panel_id}"),
            InlineKeyboardButton("⏱ Scan Interval", callback_data=f"panel_interval_{panel_id}"),
        ],
    ])

# ─── PHONE PREFIX → COUNTRY MAPPING ──────────────────────────────────────────
_PHONE_PREFIX_MAP = {
    "1": "US", "7": "RU", "20": "EG", "27": "ZA", "30": "GR", "31": "NL",
    "32": "BE", "33": "FR", "34": "ES", "36": "HU", "39": "IT", "40": "RO",
    "41": "CH", "43": "AT", "44": "GB", "45": "DK", "46": "SE", "47": "NO",
    "48": "PL", "49": "DE", "51": "PE", "52": "MX", "53": "CU", "54": "AR",
    "55": "BR", "56": "CL", "57": "CO", "58": "VE", "60": "MY", "61": "AU",
    "62": "ID", "63": "PH", "64": "NZ", "65": "SG", "66": "TH", "81": "JP",
    "82": "KR", "84": "VN", "86": "CN", "90": "TR", "91": "IN", "92": "PK",
    "93": "AF", "94": "LK", "95": "MM", "98": "IR", "212": "MA", "213": "DZ",
    "216": "TN", "218": "LY", "220": "GM", "221": "SN", "222": "MR",
    "223": "ML", "224": "GN", "225": "CI", "226": "BF", "227": "NE",
    "228": "TG", "229": "BJ", "230": "MU", "231": "LR", "232": "SL",
    "233": "GH", "234": "NG", "235": "TD", "236": "CF", "237": "CM",
    "238": "CV", "240": "GQ", "241": "GA", "242": "CG", "243": "CD",
    "244": "AO", "245": "GW", "248": "SC", "249": "SD", "250": "RW",
    "251": "ET", "252": "SO", "253": "DJ", "254": "KE", "255": "TZ",
    "256": "UG", "257": "BI", "258": "MZ", "260": "ZM", "261": "MG",
    "263": "ZW", "264": "NA", "265": "MW", "266": "LS", "267": "BW",
    "268": "SZ", "269": "KM", "291": "ER", "297": "AW", "298": "FO",
    "299": "GL", "350": "GI", "351": "PT", "352": "LU", "353": "IE",
    "354": "IS", "355": "AL", "356": "MT", "357": "CY", "358": "FI",
    "359": "BG", "370": "LT", "371": "LV", "372": "EE", "373": "MD",
    "374": "AM", "375": "BY", "376": "AD", "380": "UA", "381": "RS",
    "385": "HR", "386": "SI", "387": "BA", "389": "MK", "420": "CZ",
    "421": "SK", "501": "BZ", "502": "GT", "503": "SV", "504": "HN",
    "505": "NI", "506": "CR", "507": "PA", "509": "HT", "591": "BO",
    "592": "GY", "593": "EC", "595": "PY", "597": "SR", "598": "UY",
    "670": "TL", "673": "BN", "675": "PG", "676": "TO", "677": "SB",
    "678": "VU", "679": "FJ", "685": "WS", "686": "KI", "687": "NC",
    "689": "PF", "850": "KP", "852": "HK", "853": "MO", "855": "KH",
    "856": "LA", "880": "BD", "886": "TW", "960": "MV", "961": "LB",
    "962": "JO", "963": "SY", "964": "IQ", "965": "KW", "966": "SA",
    "967": "YE", "968": "OM", "970": "PS", "971": "AE", "972": "IL",
    "973": "BH", "974": "QA", "975": "BT", "976": "MN", "977": "NP",
    "992": "TJ", "993": "TM", "994": "AZ", "995": "GE", "996": "KG",
    "998": "UZ",
}

def _phone_to_iso2(number: str):
    """Return ISO alpha-2 country code and dial-code string from a phone number."""
    clean = number.lstrip("+").strip()
    for length in (3, 2, 1):
        prefix = clean[:length]
        if prefix in _PHONE_PREFIX_MAP:
            return _PHONE_PREFIX_MAP[prefix], prefix
    return None, None

_ISO2_TO_COUNTRY_NAME = {
    "AF": "Afghanistan", "AL": "Albania", "DZ": "Algeria", "AD": "Andorra",
    "AO": "Angola", "AR": "Argentina", "AM": "Armenia", "AU": "Australia",
    "AT": "Austria", "AZ": "Azerbaijan", "BH": "Bahrain", "BD": "Bangladesh",
    "BY": "Belarus", "BE": "Belgium", "BZ": "Belize", "BJ": "Benin",
    "BT": "Bhutan", "BO": "Bolivia", "BA": "Bosnia and Herzegovina", "BW": "Botswana",
    "BR": "Brazil", "BN": "Brunei", "BG": "Bulgaria", "BF": "Burkina Faso",
    "BI": "Burundi", "KH": "Cambodia", "CM": "Cameroon", "CA": "Canada",
    "CV": "Cape Verde", "CF": "Central African Republic", "TD": "Chad", "CL": "Chile",
    "CN": "China", "CO": "Colombia", "KM": "Comoros", "CG": "Congo",
    "CD": "DR Congo", "CR": "Costa Rica", "CI": "Ivory Coast", "HR": "Croatia",
    "CU": "Cuba", "CY": "Cyprus", "CZ": "Czech Republic", "DK": "Denmark",
    "DJ": "Djibouti", "EC": "Ecuador", "EG": "Egypt", "SV": "El Salvador",
    "GQ": "Equatorial Guinea", "ER": "Eritrea", "EE": "Estonia", "SZ": "Eswatini",
    "ET": "Ethiopia", "FJ": "Fiji", "FI": "Finland", "FR": "France",
    "GA": "Gabon", "GM": "Gambia", "GE": "Georgia", "DE": "Germany",
    "GH": "Ghana", "GR": "Greece", "GT": "Guatemala", "GN": "Guinea",
    "GW": "Guinea-Bissau", "GY": "Guyana", "HT": "Haiti", "HN": "Honduras",
    "HK": "Hong Kong", "HU": "Hungary", "IS": "Iceland", "IN": "India",
    "ID": "Indonesia", "IR": "Iran", "IQ": "Iraq", "IE": "Ireland",
    "IL": "Israel", "IT": "Italy", "JM": "Jamaica", "JP": "Japan",
    "JO": "Jordan", "KZ": "Kazakhstan", "KE": "Kenya", "KW": "Kuwait",
    "KG": "Kyrgyzstan", "LA": "Laos", "LV": "Latvia", "LB": "Lebanon",
    "LS": "Lesotho", "LR": "Liberia", "LY": "Libya", "LT": "Lithuania",
    "LU": "Luxembourg", "MO": "Macau", "MG": "Madagascar", "MW": "Malawi",
    "MY": "Malaysia", "MV": "Maldives", "ML": "Mali", "MT": "Malta",
    "MR": "Mauritania", "MU": "Mauritius", "MX": "Mexico", "MD": "Moldova",
    "MC": "Monaco", "MN": "Mongolia", "ME": "Montenegro", "MA": "Morocco",
    "MZ": "Mozambique", "MM": "Myanmar", "NA": "Namibia", "NP": "Nepal",
    "NL": "Netherlands", "NZ": "New Zealand", "NI": "Nicaragua", "NE": "Niger",
    "NG": "Nigeria", "MK": "North Macedonia", "NO": "Norway", "OM": "Oman",
    "PK": "Pakistan", "PS": "Palestine", "PA": "Panama", "PG": "Papua New Guinea",
    "PY": "Paraguay", "PE": "Peru", "PH": "Philippines", "PL": "Poland",
    "PT": "Portugal", "QA": "Qatar", "RO": "Romania", "RU": "Russia",
    "RW": "Rwanda", "SA": "Saudi Arabia", "SN": "Senegal", "RS": "Serbia",
    "SC": "Seychelles", "SL": "Sierra Leone", "SG": "Singapore", "SK": "Slovakia",
    "SI": "Slovenia", "SO": "Somalia", "ZA": "South Africa", "KR": "South Korea",
    "SS": "South Sudan", "ES": "Spain", "LK": "Sri Lanka", "SD": "Sudan",
    "SR": "Suriname", "SE": "Sweden", "CH": "Switzerland", "SY": "Syria",
    "TW": "Taiwan", "TJ": "Tajikistan", "TZ": "Tanzania", "TH": "Thailand",
    "TL": "Timor-Leste", "TG": "Togo", "TN": "Tunisia", "TR": "Turkey",
    "TM": "Turkmenistan", "UG": "Uganda", "UA": "Ukraine", "AE": "United Arab Emirates",
    "GB": "United Kingdom", "US": "United States", "UY": "Uruguay", "UZ": "Uzbekistan",
    "VE": "Venezuela", "VN": "Vietnam", "YE": "Yemen", "ZM": "Zambia", "ZW": "Zimbabwe"
}

def _mask_otp_number(clean_number: str, dial_code: str = "") -> str:
    """Mask phone number matching screenshot: 221****020 (dial code + **** + last 3 digits)."""
    clean = re.sub(r"\D", "", str(clean_number or ""))
    if not clean:
        return "—"
    if dial_code and clean.startswith(dial_code) and len(clean) > len(dial_code) + 2:
        last3 = clean[-3:]
        return f"{dial_code}****{last3}"
    if len(clean) >= 7:
        prefix = clean[:3]
        last3 = clean[-3:]
        return f"{prefix}****{last3}"
    if len(clean) > 4:
        return f"{clean[:2]}****{clean[-2:]}"
    return clean

def _format_otp_country_display(iso2: str, db_country_name: str = "") -> str:
    flag = _country_flag(iso2) if iso2 else "🌐"
    if db_country_name:
        clean_name = re.sub(r"[\U0001F1E6-\U0001F1FF]{2}", "", db_country_name).strip()
        if clean_name:
            return f"{flag} {clean_name}"
    name = _ISO2_TO_COUNTRY_NAME.get(iso2, iso2 or "Unknown")
    return f"{flag} {name}"

def _format_otp_group_msg(
    number: str,
    sender: str = "",
    otp_code: str = "",
    full_message: str = "",
    user_id = None,
    country_name: str = "",
) -> tuple:
    """Format OTP message for group/channel:

    𝗢𝗧𝗣 𝗭𝗢𝗡𝗘
    🔔 OTP Received Successfully

    👤 User ID: 7476095122
    📞 Number: 221****020
    🌍 Country: 🇸🇳 Senegal

    📩 Full Message:
    <blockquote>Username: 1864332583 Password: AxfpDQ2m Do not share this information.</blockquote>

    Buttons:
    [ 📱 Number ] [ 📢 Channel ]
    """
    clean = re.sub(r"\D", "", str(number or ""))
    iso2, dial_code = _phone_to_iso2(clean)
    if not iso2:
        iso2, dial_code = "SN", "221"

    masked_num = _mask_otp_number(clean, dial_code)
    country_display = _format_otp_country_display(iso2, country_name)

    saved_prefix = get_setting("otp_group_prefix", "").strip()
    if not saved_prefix or saved_prefix == "ConfirmSMS—OTP":
        prefix = "𝗢𝗧𝗣 𝗭𝗢𝗡𝗘"
    else:
        prefix = saved_prefix
    channel_url = get_setting(
        "channel_link",
        get_setting("support_link", "https://t.me/sxsupportgroup"),
    )
    get_number_url = get_setting(
        "get_number_link",
        get_setting("otp_link", "https://t.me/OtpZoneAZ_Bot"),
    )

    display_uid = str(user_id) if user_id else "7476095122"
    msg_content = str(full_message or otp_code or "No message content").strip()

    lines = [
        f"<b>{_html.escape(prefix)}</b>",
        "🔔 <b>OTP Received Successfully</b>",
        "",
        f"👤 User ID: {_html.escape(str(display_uid))}",
        f"📞 Number: {_html.escape(masked_num)}",
        f"🌍 Country: {country_display}",
        "",
        "📩 <b>Full Message:</b>",
        f"<blockquote>{_html.escape(msg_content)}</blockquote>",
    ]
    text = "\n".join(lines)

    rows = [[
        InlineKeyboardButton(
            "📱 Number",
            url=get_number_url,
            style=INLINE_SUCCESS,
        ),
        InlineKeyboardButton(
            "📢 Channel",
            url=channel_url,
            style=INLINE_DANGER,
        ),
    ]]
    markup = InlineKeyboardMarkup(rows)
    return text, markup


def _user_otp_country_flag_html(
    country_name: str,
    country_emoji_entities,
    iso2: str,
) -> str:
    """Use the saved country flag emoji, falling back to the phone prefix."""
    name = str(country_name or "")
    entities = country_emoji_entities
    if isinstance(entities, str):
        try:
            entities = json.loads(entities)
        except (TypeError, ValueError):
            entities = None

    if isinstance(entities, list):
        for entity in entities:
            if not isinstance(entity, dict):
                continue
            start_units = int(entity.get("offset", 0))
            end_units = start_units + int(entity.get("length", 0))
            glyph = name[
                _utf16_index(name, start_units):
                _utf16_index(name, end_units)
            ]
            if not re.fullmatch(r"[\U0001F1E6-\U0001F1FF]{2}", glyph):
                continue
            emoji_id = str(entity.get("id") or "")
            custom_id = _flag_custom_emoji_id(glyph) or emoji_id
            if custom_id:
                return (
                    f'<tg-emoji emoji-id="{_html.escape(custom_id, quote=True)}">'
                    f"{_html.escape(glyph)}</tg-emoji>"
                )
            return _premium_flag_html(glyph)

    flag_match = re.search(r"[\U0001F1E6-\U0001F1FF]{2}", name)
    flag = flag_match.group(0) if flag_match else _country_flag(iso2)
    return _premium_flag_html(flag)


def _user_otp_service_html(sender: str) -> str:
    """Render the service emoji, when available, followed by its short name."""
    raw_sender = str(sender or "").strip()
    service = _find_service_by_input(raw_sender) if raw_sender else None
    service_name = (
        copyable_service_name(service) if service else raw_sender
    )
    short_name = _service_short_name(service_name)

    if service:
        logo_html = service_logo_html(service, fallback="")
    else:
        logo_html = _service_group_html(raw_sender) if raw_sender else ""

    if "<tg-emoji" in logo_html:
        return f"{logo_html} {_html.escape(short_name)}"
    return _html.escape(short_name)


def _format_user_otp_msg(
    number: str,
    country_name: str,
    country_emoji_entities,
    otp_bonus: float,
    balance: float,
    otp_code: str,
    full_message: str,
    sender: str = "",
) -> tuple:
    """Build the two-line OTP message and its two copy buttons."""
    clean_number = str(number or "").lstrip("+").strip()
    iso2, _dial_code = _phone_to_iso2(clean_number)
    country_short_name = iso2 or "UN"
    country_flag = _user_otp_country_flag_html(
        country_name,
        country_emoji_entities,
        country_short_name,
    )
    service_text = _user_otp_service_html(sender)
    otp_value = str(otp_code or "—")
    full_value = str(full_message or otp_value)
    # Telegram CopyTextButton accepts up to 256 characters.
    full_copy_value = full_value[:256]

    text = (
        f"<b>{country_flag} {_html.escape(country_short_name)} "
        f"{service_text} <code>{_html.escape(clean_number)}</code></b>\n"
        f'<tg-emoji emoji-id="{PER_OTP_PREMIUM_EMOJI_ID}">💵</tg-emoji> '
        f"<b>Per OTP:</b> {format_currency(otp_bonus, 4)} "
        f'<tg-emoji emoji-id="{PER_OTP_TRAILING_EMOJI_ID}">✅</tg-emoji>'
    )
    markup = InlineKeyboardMarkup([
        [
            InlineKeyboardButton(
                "𝗢𝗧𝗣",
                copy_text=CopyTextButton(text=otp_value[:256]),
                icon_custom_emoji_id=PER_OTP_PREMIUM_EMOJI_ID,
            ),
            InlineKeyboardButton(
                "𝗦𝗠𝗦",
                copy_text=CopyTextButton(text=full_copy_value),
                icon_custom_emoji_id=FULL_MESSAGE_BUTTON_EMOJI_ID,
            ),
        ],
    ])
    return text, markup


def _referral_custom_emoji(name: str, fallback: str) -> str:
    """Render one of the supplied referral notification emoji IDs."""
    emoji_id = REFERRAL_NOTIFICATION_EMOJIS[name]
    return f'<tg-emoji emoji-id="{emoji_id}">{fallback}</tg-emoji>'


def _format_referral_bonus_msg(
    referred_first_name: str,
    commission: float,
    referrer_balance: float,
) -> str:
    """Build the recurring qualified-referral commission notification."""
    first_name = _html.escape(str(referred_first_name or "User"))
    return "\n".join([
        f"{_referral_custom_emoji('bonus', '🎁')} "
        "<b>Referral Bonus (L1)</b>",
        f"{_referral_custom_emoji('otp_success', '✅')} "
        f"<b>{first_name}</b> OTP success",
        f"{_referral_custom_emoji('amount', '💸')} "
        f"<b>+{format_currency(commission, 4)}</b>",
        f"{_referral_custom_emoji('balance', '💰')} "
        f"Balance: <b>{format_currency(referrer_balance, 4)}</b>",
        f"{_referral_custom_emoji('more_earn_left', '🔥')} "
        "<b>More Refer More Earn</b> "
        f"{_referral_custom_emoji('more_earn_right', '✨')}",
    ])


def _format_referral_qualified_msg(
    referred_first_name: str,
    referred_username: str,
    credited_amount: float,
    referrer_balance: float,
    qualification_otps: int,
) -> str:
    """Build the one-time notification sent when a referral becomes active."""
    first_name = _html.escape(str(referred_first_name or "User"))
    username = str(referred_username or "").strip().lstrip("@")
    username_line = (
        f" <code>@{_html.escape(username)}</code>" if username else ""
    )
    return "\n".join([
        f"{_referral_custom_emoji('bonus', '🎁')} "
        "<b>আপনার refer টি qualified হয়েছে</b>",
        f"{_referral_custom_emoji('otp_success', '✅')} "
        f"<b>{first_name}</b>{username_line} "
        f"({qualification_otps} OTP success)",
        f"{_referral_custom_emoji('amount', '💸')} "
        f"<b>+{format_currency(credited_amount, 4)}</b>",
        f"{_referral_custom_emoji('balance', '💰')} "
        f"Balance: <b>{format_currency(referrer_balance, 4)}</b>",
        f"{_referral_custom_emoji('more_earn_left', '🔥')} "
        "<b>More Refer More Earn</b> "
        f"{_referral_custom_emoji('more_earn_right', '✨')}",
    ])


# ─── PANEL BACKGROUND SCAN JOB ────────────────────────────────────────────────
import datetime as _dt

async def _notify_panel_admins(context, text: str):
    """Send one panel-maintenance notice to every permanent admin."""
    for admin_uid in SUPER_ADMINS:
        try:
            await context.bot.send_message(
                chat_id=admin_uid,
                text=text,
                parse_mode="HTML",
            )
        except Exception:
            pass


async def _send_otp_with_retry(
    context,
    chat_id,
    text,
    reply_markup,
    attempts=3,
    label="OTP",
):
    """Send an OTP message with bounded retries for transient Telegram errors."""
    for attempt in range(attempts):
        try:
            await context.bot.send_message(
                chat_id=chat_id,
                text=text,
                parse_mode="HTML",
                reply_markup=reply_markup,
            )
            return True
        except Exception as exc:
            error_text = str(exc).casefold()
            permanent_failure = any(
                marker in error_text
                for marker in (
                    "blocked", "deactivated", "chat not found", "forbidden",
                    "bot was blocked", "user is deactivated", "can't parse entities",
                    "message is too long",
                )
            )
            if permanent_failure:
                logger.warning("%s delivery permanently failed: %s", label, exc)
                return False
            if attempt == attempts - 1:
                logger.error(
                    "%s delivery failed after %s attempts: %s",
                    label,
                    attempts,
                    exc,
                )
                return False
            retry_after = getattr(exc, "retry_after", None)
            try:
                delay = max(0.5, min(float(retry_after or 1.0), 10.0))
            except (TypeError, ValueError):
                delay = 1.0
            await asyncio.sleep(delay)
    return False


async def _send_otp_group_message(context, chat_id, text, reply_markup, attempts=3):
    return await _send_otp_with_retry(
        context, chat_id, text, reply_markup, attempts, label="OTP group"
    )


async def _otp_group_worker():
    """Forward group OTPs at a safe rate without blocking user delivery."""
    global _otp_group_queue
    last_sent_at = 0.0
    while True:
        context, chat_id, text, reply_markup = await _otp_group_queue.get()
        try:
            loop = asyncio.get_running_loop()
            wait_for = OTP_GROUP_MIN_INTERVAL - (loop.time() - last_sent_at)
            if wait_for > 0:
                await asyncio.sleep(wait_for)
            # Do not retry immediately: each retry is another group message
            # and can itself trigger Telegram's group flood control.
            await _send_otp_group_message(
                context,
                chat_id,
                text,
                reply_markup,
                attempts=1,
            )
            last_sent_at = loop.time()
        except asyncio.CancelledError:
            raise
        except Exception:
            logger.exception("Queued OTP group delivery failed")
        finally:
            _otp_group_queue.task_done()


async def enqueue_otp_group_message(context, chat_id, text, reply_markup):
    """Queue a group forward and return immediately to the scanner."""
    global _otp_group_queue, _otp_group_worker_task
    if not chat_id:
        return
    if _otp_group_queue is None:
        _otp_group_queue = asyncio.Queue(maxsize=OTP_GROUP_QUEUE_MAXSIZE)
    if _otp_group_worker_task is None or _otp_group_worker_task.done():
        _otp_group_worker_task = asyncio.create_task(_otp_group_worker())
    try:
        _otp_group_queue.put_nowait((context, chat_id, text, reply_markup))
    except asyncio.QueueFull:
        # Direct user delivery must remain available even if the group backlog
        # is larger than Telegram can drain in a reasonable period.
        logger.warning("OTP group queue full; dropping group forward only")


async def _send_otp_user_message(context, chat_id, text, reply_markup, attempts=3):
    global _otp_user_rate_lock, _otp_user_last_sent_at
    if _otp_user_rate_lock is None:
        _otp_user_rate_lock = asyncio.Lock()
    async with _otp_user_rate_lock:
        loop = asyncio.get_running_loop()
        min_interval = 1 / OTP_USER_MESSAGES_PER_SECOND
        wait_for = min_interval - (loop.time() - _otp_user_last_sent_at)
        if wait_for > 0:
            await asyncio.sleep(wait_for)
        _otp_user_last_sent_at = loop.time()
    return await _send_otp_with_retry(
        context, chat_id, text, reply_markup, attempts, label="OTP user"
    )


def _sms_cursor_key(sms) -> str:
    """Disambiguate SMS rows that share the same panel timestamp."""
    payload = "\x1f".join(
        str(sms.get(field, "") or "")
        for field in ("ts", "number", "sender", "message")
    )
    return hashlib.sha256(payload.encode("utf-8", "replace")).hexdigest()


def _traffic_country_snapshot(number: str, iso2: str):
    """Capture country display data before an assigned number is removed."""
    clean_number = re.sub(r"\D", "", str(number or ""))
    rows = db_query(
        """
        SELECT c.name, c.emoji_entities
        FROM numbers n
        JOIN countries c ON c.id=n.country_id
        WHERE n.number=? OR n.number=?
        LIMIT 1
        """,
        (clean_number, "+" + clean_number),
    )
    if rows:
        return rows[0]["name"], rows[0]["emoji_entities"]

    if iso2:
        for country in db_query(
            "SELECT name, emoji_entities FROM countries WHERE active=1"
        ):
            if re.search(
                rf"(?<![A-Za-z]){re.escape(iso2)}(?![A-Za-z])",
                copyable_country_name(country),
                re.IGNORECASE,
            ):
                return country["name"], country["emoji_entities"]
    return None, None


def record_live_traffic_event(panel_id, sms):
    """Persist one newly discovered panel SMS for the rolling traffic view."""
    sender = " ".join(str(sms.get("sender") or "").split()) or "Unknown"
    message = str(sms.get("message") or "")
    number = str(sms.get("number") or "")
    timestamp = str(sms.get("ts") or "")
    event_key = hashlib.sha256(
        "|".join((str(panel_id), timestamp, number, sender, message)).encode(
            "utf-8", "replace"
        )
    ).hexdigest()

    service = _find_service_by_input(sender, active_only=False)
    if service:
        # Keep the fallback glyph in the stored name so its saved Telegram
        # entity offsets remain valid for the traffic report.
        service_name = str(service["name"]) or sender
        service_emoji_entities = service["emoji_entities"]
    else:
        service_name = sender
        service_emoji_entities = None

    iso2, _ = _phone_to_iso2(number)
    country_name, country_emoji_entities = _traffic_country_snapshot(number, iso2)
    occurred_at = _dt.datetime.now(_dt.timezone.utc).replace(
        tzinfo=None
    ).isoformat(timespec="seconds")

    inserted = db_execute(
        """
        INSERT OR IGNORE INTO traffic_events
            (event_key, occurred_at, service_name, service_emoji_entities,
             iso2, country_name, country_emoji_entities)
        VALUES (?, ?, ?, ?, ?, ?, ?)
        """,
        (
            event_key,
            occurred_at,
            service_name,
            service_emoji_entities,
            iso2 or "",
            country_name,
            country_emoji_entities,
        ),
    )
    # Keep the JSON backup and in-memory database bounded while preserving a
    # small buffer beyond the one-hour reporting window.
    db_execute(
        "DELETE FROM traffic_events "
        "WHERE datetime(replace(occurred_at, 'T', ' ')) "
        "< datetime('now', '-2 hours')"
    )
    return inserted > 0


def _traffic_service_html(row) -> str:
    """Render a service name with its saved custom animated emoji when present."""
    name = str(row["service_name"] or "Unknown").strip() or "Unknown"
    service = _find_service_by_input(name, active_only=False)
    service_like = service or {
        "name": name,
        "emoji_entities": row["service_emoji_entities"],
    }
    snapshot_service = {
        "name": name,
        "emoji_entities": row["service_emoji_entities"],
    }
    logo = _saved_service_logo_html(snapshot_service)
    if logo is None:
        logo = service_logo_html(service_like, fallback="💠")
    label = copyable_service_name(service_like)
    return f"{logo} <b>{_html.escape(label)}</b>"


def _traffic_country_html(row) -> str:
    """Render the country flag from the rolling event snapshot."""
    name = str(row["country_name"] or "").strip()
    iso2 = str(row["iso2"] or "").strip().upper()
    if name:
        rendered = country_name_html(name, row["country_emoji_entities"])
        if re.search(r"[\U0001F1E6-\U0001F1FF]{2}", name):
            return rendered
        if iso2:
            return f"{_premium_flag_html(_country_flag(iso2))} {rendered}"
        return rendered
    if iso2:
        return f"{_premium_flag_html(_country_flag(iso2))} <b>{_html.escape(iso2)}</b>"
    return "🌐 <b>Unknown</b>"


def _traffic_country_service_html(row) -> str:
    """Render a ranked traffic entry as country plus service."""
    country = _traffic_country_html(row)
    service = {
        "name": str(row["service_name"] or "").strip() or "Unknown",
        "emoji_entities": row["service_emoji_entities"],
    }
    service_name = copyable_service_name(service) or "Unknown"
    return f"{country} <b>{_html.escape(service_name)}</b>"


def live_traffic_text() -> str:
    """Build the rolling country and active-service report for 30 minutes."""
    cutoff = (
        _dt.datetime.now(_dt.timezone.utc).replace(tzinfo=None)
        - _dt.timedelta(minutes=30)
    ).isoformat(timespec="seconds")
    total_rows = db_query(
        "SELECT COUNT(*) AS total FROM traffic_events WHERE occurred_at>=?",
        (cutoff,),
    )
    total = int(total_rows[0]["total"] or 0) if total_rows else 0
    traffic_rows = db_query(
        """
        SELECT iso2, country_name, country_emoji_entities,
               service_name, service_emoji_entities, COUNT(*) AS total
        FROM traffic_events
        WHERE occurred_at>=?
        GROUP BY iso2, country_name, country_emoji_entities,
                 service_name, service_emoji_entities
        ORDER BY total DESC, country_name COLLATE NOCASE,
                 service_name COLLATE NOCASE
        """,
        (cutoff,),
    )

    # A country can receive OTPs for several services. Aggregate country
    # traffic independently so the same country is not repeated once per
    # service in the Top Countries section.
    country_totals = {}
    for row in traffic_rows:
        country_key = (
            str(row["iso2"] or "").strip().upper()
            or str(row["country_name"] or "").strip().casefold()
            or "unknown"
        )
        country = country_totals.setdefault(
            country_key,
            {
                "iso2": row["iso2"],
                "country_name": row["country_name"],
                "country_emoji_entities": row["country_emoji_entities"],
                "total": 0,
            },
        )
        country["total"] += int(row["total"] or 0)
        if not country["country_name"] and row["country_name"]:
            country["country_name"] = row["country_name"]
        if not country["country_emoji_entities"] and row["country_emoji_entities"]:
            country["country_emoji_entities"] = row["country_emoji_entities"]

    # Keep every service that received at least one OTP in the window. Merge
    # snapshots by service name so a service is never listed twice if its
    # saved emoji was updated while traffic was being recorded.
    service_totals = {}
    for row in traffic_rows:
        service_name = str(row["service_name"] or "Unknown").strip() or "Unknown"
        service_key = service_name.casefold()
        service = service_totals.setdefault(
            service_key,
            {
                "service_name": service_name,
                "service_emoji_entities": row["service_emoji_entities"],
                "total": 0,
            },
        )
        service["total"] += int(row["total"] or 0)
        if not service["service_emoji_entities"] and row["service_emoji_entities"]:
            service["service_emoji_entities"] = row["service_emoji_entities"]

    top_countries = sorted(
        country_totals.values(),
        key=lambda row: (
            -int(row["total"]),
            str(row["country_name"] or row["iso2"] or "").casefold(),
        ),
    )[:5]
    active_services = sorted(
        service_totals.values(),
        key=lambda row: (
            -int(row["total"]),
            str(row["service_name"]).casefold(),
        ),
    )
    results_sent = "100%" if total else "0%"
    lines = [
        '<tg-emoji emoji-id="6276077203876745608">📈</tg-emoji> '
        "<b>Live Traffic</b>",
        "",
        "🕒 <b>Window:</b> Last 30 minutes",
        f"📊 <b>Results Sent:</b> {results_sent}",
        (
            f"🏆 <b>Top Country:</b> "
            f"{_traffic_country_html(top_countries[0])} 🔥"
            if top_countries
            else "🏆 <b>Top Country:</b> —"
        ),
        "",
        "🔺 <b>Active Services:</b>",
    ]
    if active_services:
        for rank, row in enumerate(active_services, start=1):
            percent = (int(row["total"]) * 100 / total) if total else 0
            lines.append(
                f"{rank}. {_traffic_service_html(row)} — "
                f"<b>{percent:.1f}%</b>"
            )
    else:
        lines.append("No active services in the last 30 minutes.")

    lines.extend([
        "",
        '<tg-emoji emoji-id="5447410659077661506">🌍</tg-emoji> '
        "<b>Top Countries:</b>",
    ])
    if top_countries:
        for rank, row in enumerate(top_countries, start=1):
            percent = (int(row["total"]) * 100 / total) if total else 0
            hot = " 🔥" if rank == 1 else ""
            lines.append(
                f"{rank}. {_traffic_country_html(row)}{hot} — "
                f"<b>{percent:.1f}%</b>"
            )
    else:
        lines.append("No traffic in the last 30 minutes.")
    return "\n".join(lines)


def live_traffic_markup(admin_view: bool = False):
    """Add refresh for everyone and user-visibility control for admins."""
    rows = [[InlineKeyboardButton(
        "Refresh",
        callback_data="traffic_refresh",
        icon_custom_emoji_id="6068649679552257644",
    )]]
    if admin_view:
        visible = get_setting("live_traffic_user_enabled", "1") == "1"
        label = "👥 Hide from Users" if visible else "👥 Show to Users"
        rows.append([
            InlineKeyboardButton("⚙️ Back to Settings", callback_data="settings_panel")
        ])
    return InlineKeyboardMarkup(rows)


async def panel_scan_job(context):
    """Master job (runs every 3s). Each panel is scanned according to its own interval."""
    # Keep OTP group country flags on the same animated sponsor pack even when
    # no user has opened the country menu yet.
    await refresh_flag_emoji_pack(context.bot)
    panels = db_query("SELECT * FROM panels WHERE active=1")
    # Keep persisted timestamps naive for backward compatibility with the
    # existing SQLite data while avoiding the deprecated utcnow() call.
    now = _dt.datetime.now(_dt.timezone.utc).replace(tzinfo=None)
    for panel in panels:
        try:
            # Per-panel interval check
            interval_secs = max(3, int(panel["scan_interval"] or 60))
            panel_type = _panel_type(panel)
            last_scanned  = panel["last_scanned_at"]
            if last_scanned:
                try:
                    last_dt = _dt.datetime.fromisoformat(last_scanned)
                    if (now - last_dt).total_seconds() < interval_secs:
                        continue  # not yet due
                except Exception:
                    pass

            # Mark scanned time before fetching
            db_execute(
                "UPDATE panels SET last_scanned_at=? WHERE id=?",
                (now.isoformat(timespec="seconds"), panel["id"])
            )

            rows = await asyncio.to_thread(panel_fetch_sms, panel)
            if rows is None:
                panel_type = _panel_type(panel)
                panel_key = _panel_sms_cache_key(panel)
                if panel_type in {"captcha", "non_captcha"}:
                    # panel_fetch_sms already tried automatic re-login. Keep the
                    # panel active so the next scan/keep-alive can retry.
                    if _panel_relogin_notice_allowed(panel_key):
                        await _notify_panel_admins(
                            context,
                            f"⚠️ <b>Panel Auto Re-login Failed</b>\n\n"
                            f"📡 Panel: <b>{panel['name']}</b>\n"
                            f"সেশন শেষ হয়েছে, কিন্তু স্বয়ংক্রিয় login সফল হয়নি।\n"
                            f"বট পরের চেকে আবার চেষ্টা করবে।",
                        )
                else:
                    # API panels cannot refresh a token automatically, but a
                    # temporary 401/403 or provider outage must not permanently
                    # stop the scanner. Keep the panel active and retry on the
                    # next scheduled scan.
                    if _panel_relogin_notice_allowed(panel_key):
                        await _notify_panel_admins(
                            context,
                            f"⚠️ <b>Panel Authorization Failed</b>\n\n"
                            f"📡 Panel: <b>{panel['name']}</b>\n"
                            f"API key বা authorization যাচাই করুন।\n"
                            f"বট panel বন্ধ করছে না; পরের scan-এ আবার চেষ্টা করবে।",
                        )
                continue

            last_ts = panel["last_seen_ts"] or ""
            last_key = panel["last_seen_key"] or ""
            new_last_ts = last_ts
            new_last_key = last_key
            otp_group_ids = get_otp_group_ids()
            # Process oldest pending messages first. This prevents a burst of
            # SMS rows from being delivered newest-first.
            pending_sms = sorted(
                (
                    sms for sms in rows
                    if (
                        sms["ts"] > last_ts
                        or (
                            sms["ts"] == last_ts
                            and _sms_cursor_key(sms) > last_key
                        )
                    )
                ),
                key=lambda sms: (sms["ts"], _sms_cursor_key(sms)),
            )
            for sms in pending_sms:
                sms_key = _sms_cursor_key(sms)

                # Record panel traffic once per unique SMS before delivery.
                is_new_sms = record_live_traffic_event(panel["id"], sms)

                num_clean = sms["number"].lstrip("+").strip()
                # Only deliver OTP while the assigned number is still valid.
                matched = db_query(
                    """SELECT n.assigned_uid, c.price, c.name AS country_name,
                              c.emoji_entities AS country_emoji_entities,
                              u.referred_by
                       FROM numbers n
                       JOIN countries c ON c.id = n.country_id
                       JOIN users u ON u.uid = n.assigned_uid
                       WHERE (n.number=? OR n.number=?)
                         AND n.assigned_uid IS NOT NULL
                         AND (n.assigned_at IS NULL
                               OR (julianday('now') - julianday(n.assigned_at)) * 1440 <= ?)
                       ORDER BY n.id
                       LIMIT 1""",
                    (
                        num_clean,
                        "+" + num_clean,
                        configured_number_valid_time_minutes(),
                    )
                )

                assigned_uid_grp = matched[0]["assigned_uid"] if matched else None
                country_name_grp = matched[0]["country_name"] if matched else ""
                if not assigned_uid_grp:
                    num_row = db_query(
                        "SELECT assigned_uid, country_id FROM numbers WHERE number=? OR number=?",
                        (num_clean, "+" + num_clean)
                    )
                    if num_row and num_row[0]["assigned_uid"]:
                        assigned_uid_grp = num_row[0]["assigned_uid"]
                    if num_row and num_row[0]["country_id"] and not country_name_grp:
                        c_row = db_query("SELECT name FROM countries WHERE id=?", (num_row[0]["country_id"],))
                        if c_row:
                            country_name_grp = c_row[0]["name"]

                # ── Send to OTP Group ─────────────────────────────────────
                if otp_group_ids and is_new_sms:
                    otp_code_grp = _extract_otp(sms.get("message", "")) or ""
                    group_text, group_kb = _format_otp_group_msg(
                        number=sms["number"],
                        sender=sms.get("sender", ""),
                        otp_code=otp_code_grp,
                        full_message=sms.get("message", ""),
                        user_id=assigned_uid_grp,
                        country_name=country_name_grp,
                    )
                    for otp_group_id in otp_group_ids:
                        await enqueue_otp_group_message(
                            context,
                            otp_group_id,
                            group_text,
                            group_kb,
                        )
                    try:
                        from firebase_sync import log_otp_event_to_firebase
                        log_otp_event_to_firebase({
                            "number": sms["number"],
                            "sender": sms.get("sender", ""),
                            "otp_code": otp_code_grp,
                            "message": sms.get("message", ""),
                            "user_id": assigned_uid_grp,
                            "country": country_name_grp,
                        })
                    except Exception:
                        pass
                if not matched:
                    if (sms["ts"], sms_key) > (new_last_ts, new_last_key):
                        new_last_ts = sms["ts"]
                        new_last_key = sms_key
                    continue

                delivery_failed = False
                for m in matched:
                    target_uid   = m["assigned_uid"]
                    otp_bonus    = float(m["price"] or 0.0)
                    referrer_uid = m["referred_by"]
                    country_name = m["country_name"] or ""
                    country_emoji_entities = m["country_emoji_entities"]

                    # Calculate the user's own reward before delivery, but do
                    # not mutate the database until Telegram confirms the OTP.
                    # The referred user receives only the OTP's own reward.
                    # Any referral credit is handled atomically for the
                    # referrer after successful delivery.
                    user_otp_credit = otp_bonus
                    bal_row = db_query(
                        "SELECT balance FROM users WHERE uid=?", (target_uid,)
                    )
                    current_balance = (
                        float(bal_row[0]["balance"]) if bal_row else 0.0
                    )
                    new_balance = current_balance + user_otp_credit

                    # Build the user-facing OTP card
                    number_clean = sms["number"].lstrip("+").strip()
                    otp_code     = _extract_otp(sms["message"])
                    msg_text, otp_markup = _format_user_otp_msg(
                        number_clean,
                        country_name,
                        country_emoji_entities,
                        otp_bonus,
                        new_balance,
                        otp_code or "",
                        sms.get("message", ""),
                        sender=sms.get("sender", ""),
                    )

                    user_delivered = await _send_otp_user_message(
                        context,
                        target_uid,
                        msg_text,
                        otp_markup,
                    )
                    if not user_delivered:
                        delivery_failed = True
                        logger.warning(
                            "OTP delivery failed; keeping SMS cursor unchanged "
                            "(panel_id=%s, user_id=%s, number=%s)",
                            panel["id"],
                            target_uid,
                            num_clean,
                        )
                        break

                    # The OTP is now paid exactly once, after successful
                    # delivery. This transaction also handles qualification
                    # and ensures recurring commission goes to the referrer.
                    reward_result = record_otp_rewards_after_delivery(
                        target_uid,
                        user_otp_credit,
                        referrer_uid,
                    )
                    if reward_result is None:
                        delivery_failed = True
                        logger.warning(
                            "OTP reward skipped because user %s no longer exists",
                            target_uid,
                        )
                        break

                    if (sms["ts"], sms_key) > (new_last_ts, new_last_key):
                        new_last_ts = sms["ts"]
                        new_last_key = sms_key

                    # ── Notify the referrer about qualification and recurring bonus
                    notification_uid = reward_result["referrer_uid"]
                    notification_balance = reward_result["referrer_balance"]
                    if notification_uid and notification_balance is not None:
                        try:
                            if reward_result["became_qualified"]:
                                await context.bot.send_message(
                                    chat_id=notification_uid,
                                    text=_format_referral_qualified_msg(
                                        reward_result["first_name"],
                                        reward_result["username"],
                                        reward_result["referral_credit"],
                                        notification_balance,
                                        reward_result["otp_count"],
                                    ),
                                    parse_mode="HTML",
                                )
                            elif reward_result["commission"] > 0:
                                await context.bot.send_message(
                                    chat_id=notification_uid,
                                    text=_format_referral_bonus_msg(
                                        reward_result["first_name"],
                                        reward_result["commission"],
                                        notification_balance,
                                    ),
                                    parse_mode="HTML",
                                )
                        except Exception:
                            logger.warning(
                                "Referral notification failed for referrer %s",
                                notification_uid,
                                exc_info=True,
                            )

                    # A number that has completed a user request must never
                    # return to the available inventory or be reused.
                    db_execute(
                        "DELETE FROM numbers "
                        "WHERE assigned_uid=? AND (number=? OR number=?)",
                        (target_uid, num_clean, "+" + num_clean),
                    )

                if delivery_failed:
                    break

            if (new_last_ts, new_last_key) != (last_ts, last_key):
                db_execute(
                    "UPDATE panels SET last_seen_ts=?, last_seen_key=? WHERE id=?",
                    (new_last_ts, new_last_key, panel["id"]),
                )
        except Exception as e:
            logger.warning(f"Panel scan error (panel_id={panel['id']}): {e}")

async def panel_session_keepalive_job(context):
    """
    Touch every active web panel every minute. This prevents an
    overnight idle timeout where possible and triggers automatic re-login
    immediately when the panel returns its login page.
    """
    panels = db_query(
        "SELECT * FROM panels WHERE active=1"
    )
    for panel in panels:
        try:
            if not await asyncio.to_thread(panel_keepalive, panel):
                panel_key = _panel_sms_cache_key(panel)
                if _panel_relogin_notice_allowed(panel_key):
                    await _notify_panel_admins(
                        context,
                        f"⚠️ <b>Panel Session Maintenance Failed</b>\n\n"
                        f"📡 Panel: <b>{panel['name']}</b>\n"
                        f"সেশন সক্রিয় রাখা যায়নি। বট স্বয়ংক্রিয়ভাবে আবার চেষ্টা করবে।",
                    )
        except Exception as exc:
            logger.warning(
                "Panel keep-alive job error (panel_id=%s): %s",
                panel["id"],
                exc,
            )


async def panel_utc_rollover_job(context):
    """Refresh every active panel once per UTC calendar day.

    Loading the panel page/data endpoint at the new UTC date lets panels that
    rotate their report date at midnight start serving the new day's SMS.
    Web panels get a fresh login and one retry whenever that refresh
    reports an expired session or otherwise fails.
    """
    utc_today = _dt.datetime.now(_dt.timezone.utc).date().isoformat()
    panels = db_query("SELECT * FROM panels WHERE active=1")

    for panel in panels:
        panel_id = panel["id"]
        rollover_key = f"panel_utc_rollover_date:{panel_id}"
        if get_setting(rollover_key) == utc_today:
            continue

        panel_key = _panel_sms_cache_key(panel)
        panel_type = _panel_type(panel)
        try:
            with _panel_sms_cache_lock:
                _panel_sms_cache.pop(panel_key, None)

            refresh_ok = True
            if panel_type in {"captcha", "non_captcha"}:
                refresh_ok = await asyncio.to_thread(panel_keepalive, panel)

            rows = (
                await asyncio.to_thread(panel_fetch_sms, panel, 1)
                if refresh_ok else None
            )
            if rows is None and panel_type in {"captcha", "non_captcha"}:
                logger.warning(
                    "UTC date refresh failed for panel %s; forcing re-login",
                    panel["name"],
                )
                refreshed_cookies = await asyncio.to_thread(panel_auto_relogin, panel)
                if refreshed_cookies:
                    rows = await asyncio.to_thread(panel_fetch_sms, panel, 1)

            if rows is None:
                if _panel_relogin_notice_allowed(panel_key):
                    await _notify_panel_admins(
                        context,
                        f"⚠️ <b>UTC Date Refresh Failed</b>\n\n"
                        f"📡 Panel: <b>{_html.escape(panel['name'])}</b>\n"
                        f"নতুন UTC দিনের ডেটা নিতে পারিনি। বট লগইন করে আবার চেষ্টা করবে।",
                    )
                continue

            set_setting(rollover_key, utc_today)
            logger.info(
                "Panel %s refreshed for UTC date %s",
                panel["name"],
                utc_today,
            )
        except Exception as exc:
            logger.warning(
                "UTC date refresh error (panel_id=%s): %s",
                panel_id,
                exc,
            )


# ─── PERIODIC NUMBER EXPIRY JOB ──────────────────────────────────────────────
async def number_expiry_job(context):
    """Remove assigned numbers after their configured validity window."""
    expired = db_query(
        """SELECT n.id, n.assigned_uid, n.number
           FROM numbers n
           WHERE n.used=1
             AND n.assigned_uid IS NOT NULL
             AND n.assigned_at IS NOT NULL
              AND (julianday('now') - julianday(n.assigned_at)) * 1440 > ?""",
        (configured_number_valid_time_minutes(),),
    )
    for row in expired:
        # Never return a user-assigned number to the available inventory.
        db_execute(
            "DELETE FROM numbers WHERE id=?",
            (row["id"],)
        )

# ─── DAILY USER DATA BACKUP JOB ───────────────────────────────────────────────
async def daily_user_backup_job(context):
    """Send each super-admin the workbook and both JSON database files daily.

    The JSON files contain the complete bot state, including operational
    settings. Keep the resulting backup private. Delivery is tracked per
    admin so a restart does not resend a successful backup.
    """
    today = _dt.datetime.now(_dt.timezone.utc).date().isoformat()
    users = db_query("SELECT COUNT(*) AS cnt FROM users")
    total_users = int(users[0]["cnt"]) if users else 0

    for admin_uid in SUPER_ADMINS:
        setting_key = f"daily_user_backup_date:{admin_uid}"
        if get_setting(setting_key) == today:
            continue

        try:
            excel_buf, total = await asyncio.to_thread(build_user_excel)
            total_balance_row = db_query("SELECT SUM(balance) AS s FROM users")
            total_balance = float(total_balance_row[0]["s"] or 0) if total_balance_row else 0.0
            # Package the sanitized user workbook together with a consistent
            # snapshot of both active JSON database files.
            archive = io.BytesIO()
            with zipfile.ZipFile(archive, "w", compression=zipfile.ZIP_DEFLATED) as zf:
                excel_buf.seek(0)
                zf.writestr(
                    f"users_{today.replace('-', '')}.xlsx",
                    excel_buf.read(),
                )
                json_files = await asyncio.to_thread(build_json_database_files)
                zf.writestr("users.json", json_files["users.json"])
                zf.writestr("numbers.json", json_files["numbers.json"])
                zf.writestr(
                    "README.txt",
                    (
                        "Daily bot backup.\n"
                        "Contains the user workbook and a consistent snapshot of users.json and numbers.json.\n"
                        "Restore both JSON files together with the bot to preserve all users and bot state.\n"
                        "The database may contain panel credentials, API keys, cookies, and other "
                        "operational data. Keep this ZIP private.\n"
                    ),
                )
            archive.seek(0)
            filename = f"users_backup_{today.replace('-', '')}.zip"
            await context.bot.send_document(
                chat_id=admin_uid,
                document=archive,
                filename=filename,
                caption=(
                    f"<b>Daily User Data Backup ZIP</b>\n"
                    f"📅 Date: <b>{today}</b>\n"
                    f"👥 Users: <b>{total}</b>\n"
                    f"💰 Total Balance: <b>{format_currency(total_balance)}</b>"
                ),
                parse_mode="HTML",
            )
            set_setting(setting_key, today)
        except Exception as exc:
            logger.warning(
                "Daily user backup delivery failed for admin %s: %s",
                admin_uid,
                exc,
            )


async def telegram_error_handler(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Log update failures and keep the admin-facing bot usable."""
    error_text = str(context.error or "").casefold()
    if "message is not modified" in error_text:
        # Telegram raises this when a refresh button is tapped while the
        # message and markup are already identical. It is a successful no-op,
        # not an update failure that should be shown to the user.
        callback_query = getattr(update, "callback_query", None)
        if callback_query is not None:
            try:
                await callback_query.answer()
            except Exception:
                pass
        return
    logger.exception(
        "Unhandled Telegram update error",
        exc_info=context.error,
    )
    message = getattr(update, "effective_message", None)
    if message is not None:
        try:
            await message.reply_text(
                "❌ এই ধাপে একটি সমস্যা হয়েছে। আবার চেষ্টা করুন।"
            )
        except Exception:
            logger.exception("Could not send the Telegram error notice")


def leaderboard_is_enabled() -> bool:
    """Return whether leaderboard views are enabled for ordinary users."""
    return get_setting("leaderboard_enabled", "1") == "1"


def leaderboard_week_start(reference=None):
    """Return the most recent Friday 00:00 UTC, including today if Friday."""
    now = reference or _dt.datetime.now(_dt.timezone.utc)
    if now.tzinfo is None:
        now = now.replace(tzinfo=_dt.timezone.utc)
    else:
        now = now.astimezone(_dt.timezone.utc)
    days_since_friday = (now.weekday() - 4) % 7
    friday = now.date() - _dt.timedelta(days=days_since_friday)
    return _dt.datetime.combine(
        friday,
        _dt.time.min,
        tzinfo=_dt.timezone.utc,
    )


def leaderboard_active_period():
    start = leaderboard_week_start()
    end = start + _dt.timedelta(days=7)
    return (
        start.strftime("%Y-%m-%d %H:%M:%S"),
        end.strftime("%Y-%m-%d %H:%M:%S"),
    )


def initialize_weekly_leaderboard_report_state():
    """Start weekly reporting from the current UTC week's opening boundary."""
    if get_setting(WEEKLY_LEADERBOARD_LAST_END_KEY):
        return
    current_start = leaderboard_week_start().strftime("%Y-%m-%d %H:%M:%S")
    set_setting(WEEKLY_LEADERBOARD_LAST_END_KEY, current_start)


def leaderboard_event_timestamp():
    """Return a sortable UTC timestamp for a leaderboard event."""
    return _dt.datetime.now(_dt.timezone.utc).strftime("%Y-%m-%d %H:%M:%S")


def leaderboard_week_start_key(timestamp: str):
    parsed = _dt.datetime.strptime(
        timestamp, "%Y-%m-%d %H:%M:%S"
    ).replace(tzinfo=_dt.timezone.utc)
    return leaderboard_week_start(parsed).strftime("%Y-%m-%d %H:%M:%S")


def weekly_otp_leaderboard_rows(start_at: str, end_at: str, limit: int = 10):
    return db_query(
        """
        SELECT u.uid, u.first_name, u.username,
               weekly.otp_count AS weekly_otp_count,
               COALESCE(u.balance, 0) AS balance
        FROM leaderboard_weekly_counts AS weekly
        JOIN users AS u ON u.uid=weekly.uid
        WHERE weekly.week_start >= ? AND weekly.week_start < ?
        ORDER BY weekly.otp_count DESC, COALESCE(u.balance, 0) DESC,
                 COALESCE(u.joined_at, '') ASC, u.uid ASC
        LIMIT ?
        """,
        (start_at, end_at, limit),
    )


def weekly_referral_leaderboard_rows(
    start_at: str,
    end_at: str,
    limit: int = 10,
):
    return db_query(
        """
        SELECT referrer.uid, referrer.first_name, referrer.username,
               COALESCE(referrer.balance, 0) AS balance,
               COALESCE(referrer.referral_earnings, 0) AS referral_earnings,
               referral_counts.total_invited,
               referral_counts.valid_referrals
        FROM users AS referrer
        JOIN (
            SELECT e.uid,
                   COUNT(e.id) AS total_invited,
                   SUM(
                       CASE WHEN EXISTS (
                           SELECT 1
                           FROM leaderboard_events AS qualified
                           WHERE qualified.event_type='qualified_referral'
                             AND qualified.uid=e.uid
                             AND qualified.related_uid=e.related_uid
                             AND qualified.occurred_at >= e.occurred_at
                             AND qualified.occurred_at < ?
                       ) THEN 1 ELSE 0 END
                   ) AS valid_referrals
            FROM leaderboard_events AS e
            JOIN users AS invited ON invited.uid=e.related_uid
            WHERE e.event_type='referral'
              AND e.occurred_at >= ? AND e.occurred_at < ?
            GROUP BY e.uid
        ) AS referral_counts ON referral_counts.uid=referrer.uid
        ORDER BY referral_counts.valid_referrals DESC,
                 referral_counts.total_invited DESC,
                 COALESCE(referrer.referral_earnings, 0) DESC,
                 COALESCE(referrer.balance, 0) DESC,
                 COALESCE(referrer.joined_at, '') ASC, referrer.uid ASC
        LIMIT ?
        """,
        (end_at, start_at, end_at, limit),
    )


def _build_weekly_leaderboard_excel(
    title: str,
    start_at: str,
    end_at: str,
    headers: list[str],
    rows: list[list],
    column_widths: list[int],
) -> io.BytesIO:
    workbook = openpyxl.Workbook()
    worksheet = workbook.active
    worksheet.title = title[:31]
    worksheet.merge_cells(
        start_row=1,
        start_column=1,
        end_row=1,
        end_column=len(headers),
    )
    title_cell = worksheet.cell(row=1, column=1, value=title)
    title_cell.font = openpyxl.styles.Font(bold=True, size=14, color="FFFFFF")
    title_cell.fill = openpyxl.styles.PatternFill("solid", fgColor="1F4E78")
    worksheet.cell(
        row=2,
        column=1,
        value=f"UTC period: {start_at} (inclusive) to {end_at} (exclusive)",
    )
    worksheet.merge_cells(
        start_row=2,
        start_column=1,
        end_row=2,
        end_column=len(headers),
    )

    header_row = 4
    for column, header in enumerate(headers, 1):
        cell = worksheet.cell(row=header_row, column=column, value=header)
        cell.font = openpyxl.styles.Font(bold=True, color="FFFFFF")
        cell.fill = openpyxl.styles.PatternFill("solid", fgColor="4472C4")

    if rows:
        for row_index, values in enumerate(rows, header_row + 1):
            for column, value in enumerate(values, 1):
                worksheet.cell(row=row_index, column=column, value=value)
    else:
        worksheet.cell(
            row=header_row + 1,
            column=1,
            value="No leaderboard activity in this UTC week.",
        )
        worksheet.merge_cells(
            start_row=header_row + 1,
            start_column=1,
            end_row=header_row + 1,
            end_column=len(headers),
        )

    worksheet.freeze_panes = f"A{header_row + 1}"
    worksheet.auto_filter.ref = (
        f"A{header_row}:{openpyxl.utils.get_column_letter(len(headers))}"
        f"{header_row + len(rows)}"
        if rows else f"A{header_row}:{openpyxl.utils.get_column_letter(len(headers))}{header_row}"
    )
    for column, width in enumerate(column_widths, 1):
        worksheet.column_dimensions[
            openpyxl.utils.get_column_letter(column)
        ].width = width

    output = io.BytesIO()
    workbook.save(output)
    output.seek(0)
    return output


def build_weekly_leaderboard_excels(start_at: str, end_at: str):
    """Build separate OTP and referral top-10 workbooks for one UTC week."""
    otp_rows = weekly_otp_leaderboard_rows(start_at, end_at)
    referral_rows = weekly_referral_leaderboard_rows(start_at, end_at)

    otp_data = [
        [
            rank,
            int(row["uid"]),
            int(row["uid"]),
            str(row["first_name"] or row["username"] or "User"),
            int(row["weekly_otp_count"] or 0),
            round(float(row["balance"] or 0), 2),
        ]
        for rank, row in enumerate(otp_rows, 1)
    ]
    referral_data = [
        [
            rank,
            int(row["uid"]),
            int(row["uid"]),
            str(row["first_name"] or row["username"] or "User"),
            int(row["total_invited"] or 0),
            int(row["valid_referrals"] or 0),
            round(float(row["referral_earnings"] or 0), 4),
            round(float(row["balance"] or 0), 2),
        ]
        for rank, row in enumerate(referral_rows, 1)
    ]

    otp_workbook = _build_weekly_leaderboard_excel(
        "Weekly OTP Leaderboard",
        start_at,
        end_at,
        [
            "Rank", "UID", "Telegram UID", "Name",
            "Total OTP / Orders", "Total Balance (USDT)",
        ],
        otp_data,
        [10, 18, 18, 24, 22, 24],
    )
    referral_workbook = _build_weekly_leaderboard_excel(
        "Weekly Referral Leaderboard",
        start_at,
        end_at,
        [
            "Rank", "UID", "Telegram UID", "Name",
            "Total Referrals", "Valid Referrals",
            "Referral Earnings (USDT)", "Total Balance (USDT)",
        ],
        referral_data,
        [10, 18, 18, 24, 20, 18, 26, 24],
    )
    return otp_workbook, referral_workbook, len(otp_data), len(referral_data)


def _leaderboard_display_name(name: str, admin_view: bool = False) -> str:
    """Escape names and lightly mask them on public leaderboards."""
    name = str(name or "User").strip() or "User"
    if not admin_view:
        visible = [character for character in name if not character.isspace()]
        if len(visible) <= 1:
            name = visible[0] + "•••" if visible else "User"
        else:
            name = f"{visible[0]}••••{visible[-1]}"
    return _html.escape(name)


def _leaderboard_identity(row, admin_view: bool = False) -> str:
    name = _leaderboard_display_name(
        row["first_name"] or row["username"] or "User",
        admin_view=admin_view,
    )
    if admin_view:
        return f"{name} <code>({int(row['uid'])})</code>"
    return name


def order_leaderboard_text(
    uid: int,
    admin_view: bool = False,
    include_rank: bool = False,
) -> str:
    """Render the current UTC-week leaderboard and optionally caller's rank."""
    week_start, week_end = leaderboard_active_period()
    rows = weekly_otp_leaderboard_rows(week_start, week_end)
    lines = [
        "🏆 <b>WEEKLY TOP 10 USERS LEADERBOARD</b>",
        "━━━━━━━━━━━━━━━━━━",
        f"UTC period: <code>{week_start}</code> – <code>{week_end}</code>",
        "Rankings are based on successfully delivered OTPs/orders.",
        "",
    ]
    if rows:
        medals = ("🥇", "🥈", "🥉")
        for index, row in enumerate(rows, 1):
            medal = medals[index - 1] if index <= len(medals) else f"<b>{index}.</b>"
            lines.append(
                f"{medal} {_leaderboard_identity(row, admin_view)}\n"
                f"   📦 Orders: <b>{int(row['weekly_otp_count'] or 0)}</b> "
                f"| 💰 Balance: <b>{format_currency(row['balance'])}</b>"
            )
    else:
        lines.append("📭 No successful OTPs/orders yet this UTC week.")

    if include_rank:
        profile_rows = db_query(
            """
            SELECT u.uid, COALESCE(weekly.otp_count, 0) AS otp_count,
                   COALESCE(u.balance, 0) AS balance, u.joined_at
            FROM users AS u
            LEFT JOIN (
                SELECT uid, otp_count
                FROM leaderboard_weekly_counts
                WHERE week_start=?
            ) AS weekly ON weekly.uid=u.uid
            WHERE u.uid=?
            """,
            (week_start, uid),
        )
        profile = profile_rows[0] if profile_rows else None
        count = int(profile["otp_count"] or 0) if profile else 0
        balance = float(profile["balance"] or 0) if profile else 0.0
        lines.extend(["", "━━━━━━━━━━━━━━━━━━", "🔎 <b>Find My Rank</b>"])
        lines.append(f"📦 Your completed orders: <b>{count}</b>")
        lines.append(f"💰 Your balance: <b>{format_currency(balance)}</b>")

        if count < LEADERBOARD_MIN_ORDERS:
            lines.extend([
                "",
                f"⛔ You need at least "
                f"<b>{LEADERBOARD_MIN_ORDERS} completed orders/received OTPs</b> "
                "to qualify for a rank.",
                f"You have <b>{count}/{LEADERBOARD_MIN_ORDERS}</b> so far. "
                f"Your rank will appear after you reach {LEADERBOARD_MIN_ORDERS}.",
            ])
        else:
            rank_rows = db_query(
                """
                SELECT COUNT(*) + 1 AS rank
                FROM leaderboard_weekly_counts AS weekly
                JOIN users AS u ON u.uid=weekly.uid
                WHERE weekly.week_start=?
                  AND weekly.otp_count >= ?
                  AND (
                    weekly.otp_count > ?
                    OR (weekly.otp_count = ? AND COALESCE(u.balance, 0) > ?)
                    OR (
                        weekly.otp_count = ?
                        AND COALESCE(u.balance, 0) = ?
                        AND COALESCE(u.joined_at, '') < COALESCE(?, '')
                    )
                    OR (
                        weekly.otp_count = ?
                        AND COALESCE(u.balance, 0) = ?
                        AND COALESCE(u.joined_at, '') = COALESCE(?, '')
                        AND u.uid < ?
                    )
                  )
                """,
                (
                    week_start,
                    LEADERBOARD_MIN_ORDERS,
                    count, count, balance, count, balance, profile["joined_at"],
                    count, balance, profile["joined_at"], uid,
                ),
            )
            rank = int(rank_rows[0]["rank"]) if rank_rows else 1
            lines.append(f"🏅 Your rank: <b>#{rank}</b>")

    return "\n".join(lines)


def leaderboard_markup(admin_view: bool = False):
    rows = [
        [InlineKeyboardButton("🔄 Refresh", callback_data="leaderboard_refresh")],
        [InlineKeyboardButton("🔎 Find My Rank", callback_data="leaderboard_find_rank")],
    ]
    if admin_view:
        rows.append([
            InlineKeyboardButton("⚙️ Back to Settings", callback_data="settings_panel")
        ])
    return InlineKeyboardMarkup(rows)


def admin_settings_text(extra_message: str = "") -> str:
    leaderboard_status = "✅ ON" if leaderboard_is_enabled() else "🔴 OFF"
    traffic_status = (
        "✅ ON" if get_setting("live_traffic_user_enabled", "1") == "1"
        else "🔴 OFF"
    )
    lines = [
        "⚙️ <b>Admin Settings</b>",
        "",
        f"🏆 User leaderboards: <b>{leaderboard_status}</b>",
        "Controls the OTP and referral leaderboards in user-facing panels.",
        f"📡 User Live Traffic: <b>{traffic_status}</b>",
        "Controls whether ordinary users can open Live Traffic.",
    ]
    if extra_message:
        lines.extend(["", extra_message])
    return "\n".join(lines)


def admin_settings_markup():
    leaderboard_status = "ON" if leaderboard_is_enabled() else "OFF"
    traffic_status = (
        "ON" if get_setting("live_traffic_user_enabled", "1") == "1" else "OFF"
    )
    return InlineKeyboardMarkup([
        [InlineKeyboardButton(
            f"🏆 Leaderboard: {leaderboard_status}",
            callback_data="settings_toggle_leaderboard",
        )],
        [InlineKeyboardButton(
            f"📡 Live Traffic: {traffic_status}",
            callback_data="settings_toggle_traffic",
        )],
        [InlineKeyboardButton(
            "📊 View OTP Leaderboard",
            callback_data="settings_open_leaderboard",
        )],
        [InlineKeyboardButton(
            "👥 View Referral Leaderboard",
            callback_data="settings_open_referrals",
        )],
        [InlineKeyboardButton(
            "🌐 Open Live Traffic",
            callback_data="settings_open_traffic",
        )],
        [InlineKeyboardButton(
            "⬅️ Back to Admin Panel",
            callback_data="settings_back",
        )],
    ])


async def weekly_leaderboard_report_job(context):
    """Export each completed Friday-to-Friday leaderboard week to every admin.

    This check runs frequently, but the persisted report-end marker makes it
    idempotent and lets a running bot retry transient Telegram delivery errors.
    """
    latest_completed_boundary = leaderboard_week_start()
    last_end_raw = get_setting(WEEKLY_LEADERBOARD_LAST_END_KEY)
    if not last_end_raw:
        initialize_weekly_leaderboard_report_state()
        return

    try:
        period_start = _dt.datetime.strptime(
            last_end_raw, "%Y-%m-%d %H:%M:%S"
        ).replace(tzinfo=_dt.timezone.utc)
    except (TypeError, ValueError):
        logger.warning(
            "Invalid weekly leaderboard report marker %r; resetting to this "
            "UTC week's boundary.",
            last_end_raw,
        )
        initialize_weekly_leaderboard_report_state()
        return

    if period_start >= latest_completed_boundary:
        return

    admin_rows = db_query("SELECT uid FROM admins")
    admin_uids = set(SUPER_ADMINS)
    admin_uids.update(int(row["uid"]) for row in admin_rows)
    admin_uids = sorted(admin_uids)

    while period_start < latest_completed_boundary:
        period_end = period_start + _dt.timedelta(days=7)
        start_at = period_start.strftime("%Y-%m-%d %H:%M:%S")
        end_at = period_end.strftime("%Y-%m-%d %H:%M:%S")
        otp_file, referral_file, otp_total, referral_total = (
            build_weekly_leaderboard_excels(start_at, end_at)
        )
        week_label = (
            f"{period_start.strftime('%Y-%m-%d')} to "
            f"{period_end.strftime('%Y-%m-%d')} UTC"
        )
        week_key = period_end.strftime("%Y%m%d")

        for admin_uid in admin_uids:
            for kind, file_buffer, filename, total, caption in (
                (
                    "otp",
                    otp_file,
                    f"weekly_otp_leaderboard_{week_key}.xlsx",
                    otp_total,
                    f"Weekly OTP leaderboard | {week_label} | Top {otp_total}",
                ),
                (
                    "referrals",
                    referral_file,
                    f"weekly_referral_leaderboard_{week_key}.xlsx",
                    referral_total,
                    f"Weekly referral leaderboard | {week_label} | "
                    f"Top {referral_total}",
                ),
            ):
                delivery_key = (
                    f"weekly_leaderboard_delivery:{week_key}:"
                    f"{admin_uid}:{kind}"
                )
                if get_setting(delivery_key):
                    continue
                try:
                    file_buffer.seek(0)
                    await context.bot.send_document(
                        chat_id=admin_uid,
                        document=file_buffer,
                        filename=filename,
                        caption=caption,
                    )
                    set_setting(delivery_key, "sent")
                except Exception as exc:
                    error_text = str(exc).casefold()
                    permanent_failure = any(
                        marker in error_text
                        for marker in (
                            "blocked", "deactivated", "chat not found",
                            "forbidden", "bot was blocked",
                        )
                    )
                    logger.warning(
                        "Weekly %s leaderboard delivery failed for admin %s: %s",
                        kind,
                        admin_uid,
                        exc,
                    )
                    if permanent_failure:
                        set_setting(delivery_key, "failed")
                        continue
                    # Keep this week's events and retry the unsent file.
                    return

        # Save the completed boundary before pruning old event rows. If the
        # process stops between these operations, a later week safely prunes
        # the leftover rows without sending this report twice.
        set_setting(WEEKLY_LEADERBOARD_LAST_END_KEY, end_at)
        db_execute(
            "DELETE FROM leaderboard_events WHERE occurred_at < ?",
            (end_at,),
        )
        db_execute(
            "DELETE FROM leaderboard_weekly_counts WHERE week_start < ?",
            (end_at,),
        )
        db_execute(
            "DELETE FROM settings WHERE key LIKE "
            "'weekly_leaderboard_delivery:%'"
        )
        period_start = period_end


# ─── MAIN ─────────────────────────────────────────────────────────────────────
def main():
    if not BOT_TOKEN:
        raise RuntimeError(
            "BOT_TOKEN is not configured. Add the bot token to the runtime "
            "secret/environment before starting the bot."
        )
    init_db()
    initialize_weekly_leaderboard_report_state()
    logger.info("Bot starting...")
    request = HTTPXRequest(
        connection_pool_size=32,
        connect_timeout=30.0,
        read_timeout=30.0,
        write_timeout=30.0,
        pool_timeout=30.0,
    )
    app = (
        Application.builder()
        .token(BOT_TOKEN)
        .request(request)
        .concurrent_updates(32)
        .build()
    )
    app.add_handler(CommandHandler("start", start))
    app.add_handler(CommandHandler("userpanel", userpanel_cmd))
    app.add_handler(CommandHandler("users", users_cmd))
    app.add_handler(CallbackQueryHandler(callback_handler))
    # Group 0: broadcast handler intercepts when admin is in broadcast_wait state.
    # It raises ApplicationHandlerStop only when it actually handles a broadcast,
    # otherwise returns and lets group 1 handlers run normally.
    app.add_handler(MessageHandler(
        filters.ALL & ~filters.COMMAND & ~filters.UpdateType.EDITED_MESSAGE,
        broadcast_receive_handler
    ), group=0)
    # Group 1: normal message handlers — run when broadcast_receive_handler passes through
    app.add_handler(MessageHandler(filters.Document.ALL, document_handler), group=1)
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, text_handler), group=1)
    app.add_error_handler(telegram_error_handler)

    # Schedule periodic panel SMS scan (master job runs every 3s;
    # each panel is scanned according to its own scan_interval setting)
    app.job_queue.run_repeating(panel_scan_job, interval=3, first=3)

    # Keep captcha sessions alive overnight and automatically re-login when
    # the panel invalidates the stored session cookie.
    app.job_queue.run_repeating(
        panel_session_keepalive_job,
        interval=_PANEL_KEEPALIVE_INTERVAL,
        first=15,
    )
    # Detect UTC 00:00 without relying on the scheduler firing at the exact
    # second, then refresh each panel once for the new UTC calendar date.
    app.job_queue.run_repeating(
        panel_utc_rollover_job,
        interval=_PANEL_UTC_ROLLOVER_CHECK_INTERVAL,
        first=5,
    )

    # Schedule number expiry check every 60 seconds
    app.job_queue.run_repeating(number_expiry_job, interval=60, first=60)

    # Export the previous UTC week's OTP and referral leaderboards each Friday.
    app.job_queue.run_repeating(
        weekly_leaderboard_report_job,
        interval=30,
        first=10,
        name="weekly-leaderboard-report",
    )

    # Check hourly; the per-admin date marker guarantees one successful
    # delivery per UTC day even if the bot restarts around midnight.
    app.job_queue.run_repeating(daily_user_backup_job, interval=3600, first=10)

    logger.info("Bot is running.")
    app.run_polling(
        allowed_updates=Update.ALL_TYPES,
        bootstrap_retries=-1,
        timeout=30,
        drop_pending_updates=True,
    )

if __name__ == "__main__":
    main()