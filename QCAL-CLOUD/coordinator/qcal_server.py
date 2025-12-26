"""Coordinator utilities for QCAL-CLOUD.

This module exposes helper functions for managing the SQLite persistence layer
and tracking active nodes. The actual FastAPI application lives in
``dashboard_api.py`` but imports the primitives defined here.
"""
from __future__ import annotations

import json
import sqlite3
import threading
import time
from contextlib import contextmanager
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterable, Iterator, List, Optional

DATA_DIR = Path(__file__).with_suffix("").parent / "data" / "validation_logs"
DATA_DIR.mkdir(parents=True, exist_ok=True)
DB_PATH = DATA_DIR / "qcal_results.db"
JSONL_PATH = DATA_DIR / "certificates.jsonl"


@dataclass
class ValidationRecord:
    node_id: str
    timestamp: float
    precision: int
    evac_frequency: float
    relative_error: Optional[float]
    payload: dict


_DB_LOCK = threading.Lock()


def _ensure_schema(conn: sqlite3.Connection) -> None:
    conn.execute(
        """
        CREATE TABLE IF NOT EXISTS validations (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            node_id TEXT NOT NULL,
            timestamp REAL NOT NULL,
            precision INTEGER,
            evac_frequency REAL,
            relative_error REAL,
            payload TEXT NOT NULL
        )
        """
    )
    conn.commit()


def get_connection() -> sqlite3.Connection:
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    _ensure_schema(conn)
    return conn


@contextmanager
def db_cursor() -> Iterator[sqlite3.Cursor]:
    with _DB_LOCK:
        conn = get_connection()
        try:
            cursor = conn.cursor()
            yield cursor
            conn.commit()
        finally:
            conn.close()


def persist_certificate(record: ValidationRecord) -> None:
    payload_json = json.dumps(record.payload)
    with db_cursor() as cursor:
        cursor.execute(
            """
            INSERT INTO validations (node_id, timestamp, precision, evac_frequency, relative_error, payload)
            VALUES (?, ?, ?, ?, ?, ?)
            """,
            (
                record.node_id,
                record.timestamp,
                record.precision,
                record.evac_frequency,
                record.relative_error,
                payload_json,
            ),
        )

    with JSONL_PATH.open("a", encoding="utf-8") as handle:
        handle.write(payload_json + "\n")


def latest_validations(limit: int = 25) -> List[Dict[str, object]]:
    with db_cursor() as cursor:
        cursor.execute(
            """
            SELECT node_id, timestamp, precision, evac_frequency, relative_error, payload
            FROM validations
            ORDER BY timestamp DESC
            LIMIT ?
            """,
            (limit,),
        )
        rows = cursor.fetchall()

    return [
        {
            "node_id": row["node_id"],
            "timestamp": row["timestamp"],
            "precision": row["precision"],
            "evac_frequency": row["evac_frequency"],
            "relative_error": row["relative_error"],
            "payload": json.loads(row["payload"]),
        }
        for row in rows
    ]


def compute_global_metrics(window: int = 50) -> Dict[str, float]:
    records = latest_validations(limit=window)
    if not records:
        return {"coherence_error": float("nan"), "count": 0}

    errors = [r["relative_error"] for r in records if r["relative_error"] is not None]
    if not errors:
        return {"coherence_error": float("nan"), "count": len(records)}

    mean_error = sum(errors) / len(errors)
    return {"coherence_error": mean_error, "count": len(records)}


def prune_old_entries(ttl_hours: float = 24.0) -> None:
    cutoff = time.time() - ttl_hours * 3600
    with db_cursor() as cursor:
        cursor.execute("DELETE FROM validations WHERE timestamp < ?", (cutoff,))


def iter_jsonl(path: Path = JSONL_PATH) -> Iterable[dict]:
    if not path.exists():
        return []
    with path.open("r", encoding="utf-8") as handle:
        for line in handle:
            try:
                yield json.loads(line)
            except json.JSONDecodeError:
                continue
