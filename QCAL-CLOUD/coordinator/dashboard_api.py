"""FastAPI application exposing QCAL-CLOUD coordination endpoints."""
from __future__ import annotations

import asyncio
import json
import logging
import math
import time
from pathlib import Path
from typing import Any, Dict, List

from fastapi import FastAPI, HTTPException, WebSocket, WebSocketDisconnect
from fastapi.responses import JSONResponse
from fastapi.middleware.cors import CORSMiddleware

from .qcal_server import (
    ValidationRecord,
    compute_global_metrics,
    iter_jsonl,
    latest_validations,
    persist_certificate,
    prune_old_entries,
)

LOGGER = logging.getLogger("qcal_dashboard")
app = FastAPI(title="QCAL-CLOUD Coordinator")

app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)


class ConnectionManager:
    def __init__(self) -> None:
        self.active_connections: List[WebSocket] = []
        self.lock = asyncio.Lock()

    async def connect(self, websocket: WebSocket) -> None:
        await websocket.accept()
        async with self.lock:
            self.active_connections.append(websocket)
        LOGGER.info("WebSocket client connected (%d active)", len(self.active_connections))

    async def disconnect(self, websocket: WebSocket) -> None:
        async with self.lock:
            if websocket in self.active_connections:
                self.active_connections.remove(websocket)
        LOGGER.info("WebSocket client disconnected (%d active)", len(self.active_connections))

    async def broadcast(self, message: Dict[str, Any]) -> None:
        payload = json.dumps(message)
        stale_connections: List[WebSocket] = []
        async with self.lock:
            for connection in self.active_connections:
                try:
                    await connection.send_text(payload)
                except Exception:
                    stale_connections.append(connection)
        for connection in stale_connections:
            await self.disconnect(connection)


manager = ConnectionManager()


def _extract_relative_error(payload: Dict[str, Any]) -> float | None:
    try:
        validation = payload["validation"]
        stdout = validation.get("stdout", "")
        for line in stdout.splitlines()[::-1]:
            if "Relative error" in line:
                try:
                    return float(line.split(":")[-1].strip())
                except ValueError:
                    continue
        return None
    except Exception:
        return None


@app.post("/api/upload")
async def upload_certificate(payload: Dict[str, Any]) -> JSONResponse:
    if "node_id" not in payload:
        raise HTTPException(status_code=400, detail="Missing node_id")

    relative_error = _extract_relative_error(payload)
    record = ValidationRecord(
        node_id=payload["node_id"],
        timestamp=float(payload.get("timestamp", time.time())),
        precision=int(payload.get("precision", 0)),
        evac_frequency=float(payload.get("evac_frequency", math.nan)),
        relative_error=relative_error,
        payload=payload,
    )

    persist_certificate(record)
    await manager.broadcast({"event": "validation", "data": payload})

    return JSONResponse({"status": "ok", "relative_error": relative_error})


@app.get("/api/status")
async def status() -> JSONResponse:
    prune_old_entries()
    latest = latest_validations(limit=50)
    metrics = compute_global_metrics()
    return JSONResponse({"latest": latest, "metrics": metrics})


@app.get("/api/datasets")
async def datasets() -> JSONResponse:
    dataset_dir = Path(__file__).resolve().parents[1] / "datasets"
    datasets: List[Dict[str, Any]] = []
    for path in dataset_dir.glob("*.*"):
        if path.name == "dataset_card.md":
            continue
        datasets.append({
            "name": path.name,
            "size": path.stat().st_size,
            "updated": path.stat().st_mtime,
        })
    return JSONResponse({"datasets": datasets})


@app.websocket("/ws/live")
async def websocket_endpoint(websocket: WebSocket) -> None:
    await manager.connect(websocket)
    try:
        while True:
            await websocket.receive_text()
    except WebSocketDisconnect:
        await manager.disconnect(websocket)


@app.get("/api/history")
async def history(limit: int = 100) -> JSONResponse:
    events = list(iter_jsonl())[-limit:]
    return JSONResponse({"events": events})


@app.on_event("startup")
async def on_startup() -> None:
    logging.basicConfig(level=logging.INFO)
    LOGGER.info("QCAL-CLOUD coordinator started")


@app.get("/")
async def root() -> Dict[str, str]:
    return {"message": "QCAL-CLOUD coordinator operational"}
