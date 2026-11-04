"""
Firebase Realtime Database & Firestore Integration for Telegram Bot
Handles seamless cloud synchronization of:
- Users & Balances
- Settings & Custom Links
- Numbers & Country Inventory
- Live Traffic & OTP Events
- Withdrawal Requests
"""

import os
import json
import logging
import threading
import time

logger = logging.getLogger("firebase_sync")

_firebase_app = None
_firebase_rtdb = None
_firebase_firestore = None
_firebase_initialized = False
_firebase_lock = threading.Lock()

CREDENTIALS_FILE = os.getenv("FIREBASE_CREDENTIALS_FILE", "firebase_service_account.json")
DATABASE_URL = os.getenv("FIREBASE_DATABASE_URL", "https://otp-group-8bf7e-default-rtdb.firebaseio.com")


def get_firebase_credentials():
    """Retrieve service account credentials from file or environment variable."""
    env_json = os.getenv("FIREBASE_SERVICE_ACCOUNT_JSON")
    if env_json:
        try:
            return json.loads(env_json)
        except Exception as e:
            logger.warning(f"Failed to parse FIREBASE_SERVICE_ACCOUNT_JSON: {e}")

    env_b64 = os.getenv("FIREBASE_SERVICE_ACCOUNT_B64")
    if env_b64:
        try:
            import base64
            decoded = base64.b64decode(env_b64).decode("utf-8")
            return json.loads(decoded)
        except Exception as e:
            logger.warning(f"Failed to parse FIREBASE_SERVICE_ACCOUNT_B64: {e}")

    if os.path.exists(CREDENTIALS_FILE):
        try:
            with open(CREDENTIALS_FILE, "r", encoding="utf-8") as f:
                return json.load(f)
        except Exception as e:
            logger.warning(f"Failed to read {CREDENTIALS_FILE}: {e}")

    return None


def init_firebase():
    """Initialize Firebase Admin SDK with Realtime Database and Firestore."""
    global _firebase_app, _firebase_rtdb, _firebase_firestore, _firebase_initialized

    with _firebase_lock:
        if _firebase_initialized:
            return True

        cred_dict = get_firebase_credentials()
        if not cred_dict:
            logger.info("Firebase credentials not found. Cloud sync will remain inactive.")
            return False

        try:
            import firebase_admin
            from firebase_admin import credentials, db, firestore

            if not firebase_admin._apps:
                cred = credentials.Certificate(cred_dict)
                _firebase_app = firebase_admin.initialize_app(cred, {
                    "databaseURL": DATABASE_URL,
                    "projectId": cred_dict.get("project_id", "otp-group-8bf7e"),
                    "storageBucket": f"{cred_dict.get('project_id', 'otp-group-8bf7e')}.firebasestorage.app"
                })
            else:
                _firebase_app = firebase_admin.get_app()

            try:
                _firebase_rtdb = db.reference()
            except Exception as e:
                logger.warning(f"Firebase RTDB init warning: {e}")

            try:
                _firebase_firestore = firestore.client()
            except Exception as e:
                logger.warning(f"Firebase Firestore init warning: {e}")

            _firebase_initialized = True
            logger.info("Firebase successfully connected to otp-group-8bf7e!")
            return True

        except ImportError:
            logger.warning("firebase-admin package not installed. Run: pip install firebase-admin")
            return False
        except Exception as e:
            logger.exception(f"Error initializing Firebase: {e}")
            return False


def is_firebase_active() -> bool:
    if not _firebase_initialized:
        init_firebase()
    return _firebase_initialized


def sync_database_to_firebase(users_payload: dict, numbers_payload: dict):
    """Synchronize the current state to Firebase Realtime Database in background."""
    if not is_firebase_active():
        return

    def _worker():
        try:
            from firebase_admin import db

            ref = db.reference("bot_data")
            update_data = {
                "last_updated": int(time.time()),
                "version": users_payload.get("version", 1),
            }

            tables = users_payload.get("tables", {})
            for table_name, rows in tables.items():
                # Store list or dict of rows
                if rows is not None:
                    update_data[table_name] = rows

            # Numbers list
            num_rows = numbers_payload.get("numbers", [])
            if num_rows:
                update_data["numbers_count"] = len(num_rows)
                # Keep top or clean inventory in RTDB
                update_data["numbers"] = num_rows[:5000]

            ref.update(update_data)
            logger.info("Database snapshot successfully synced to Firebase.")
        except Exception as e:
            logger.warning(f"Failed to sync database to Firebase: {e}")

    threading.Thread(target=_worker, name="firebase-db-sync", daemon=True).start()


def restore_database_from_firebase():
    """Pull backup data from Firebase if local memory/file database is empty."""
    if not is_firebase_active():
        return None

    try:
        from firebase_admin import db
        ref = db.reference("bot_data")
        data = ref.get()
        if data and isinstance(data, dict):
            logger.info(f"Retrieved cloud backup from Firebase (keys: {list(data.keys())})")
            return data
    except Exception as e:
        logger.warning(f"Failed to pull data from Firebase: {e}")

    return None


def log_otp_event_to_firebase(event_data: dict):
    """Log an incoming OTP event directly into Firebase Realtime Database."""
    if not is_firebase_active():
        return

    def _worker():
        try:
            from firebase_admin import db
            ref = db.reference("otp_events")
            event_id = str(int(time.time() * 1000))
            clean_event = dict(event_data)
            clean_event["timestamp"] = int(time.time())
            ref.child(event_id).set(clean_event)
            logger.info(f"OTP event {event_id} logged to Firebase.")
        except Exception as e:
            logger.warning(f"Failed to log OTP event to Firebase: {e}")

    threading.Thread(target=_worker, name="firebase-otp-logger", daemon=True).start()
