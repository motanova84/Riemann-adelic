"""QCAL-CLOUD node worker.

This module orchestrates periodic execution of the local validation scripts and
pushes signed result artefacts to the coordinator service. The implementation is
explicitly asynchronous so that the same process can stream heartbeats over a
WebSocket while uploading JSON certificates via REST.
"""
from __future__ import annotations

import argparse
import asyncio
import json
import logging
import platform
import socket
import subprocess
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, Optional

import httpx

try:
    import websockets
except ImportError:  # pragma: no cover - optional dependency for lightweight nodes
    websockets = None  # type: ignore


LOGGER = logging.getLogger("qcal_worker")
DEFAULT_CONFIG_PATH = Path(__file__).with_name("config.json")
OUTPUT_DIR = Path(__file__).with_name("output")


@dataclass
class WorkerConfig:
    """Minimal configuration shared by voluntary nodes and CI runners."""

    node_id: str
    api_base: str
    websocket_url: Optional[str]
    poll_interval: float
    precision: int
    evac_frequency: float
    validate_script: str = "validate_v5_coronacion.py"
    evac_script: str = "Evac_Rpsi"

    @staticmethod
    def from_mapping(data: Dict[str, Any]) -> "WorkerConfig":
        return WorkerConfig(
            node_id=data["node_id"],
            api_base=data["api_base"],
            websocket_url=data.get("websocket_url"),
            poll_interval=float(data.get("poll_interval", 900.0)),
            precision=int(data.get("precision", 25)),
            evac_frequency=float(data.get("evac_frequency", 1.0)),
            validate_script=data.get("validate_script", "validate_v5_coronacion.py"),
            evac_script=data.get("evac_script", "Evac_Rpsi"),
        )


async def run_subprocess(command: list[str], cwd: Path) -> subprocess.CompletedProcess[str]:
    """Run a subprocess asynchronously while streaming stdout/stderr."""

    LOGGER.info("Launching %s", " ".join(command))
    process = await asyncio.create_subprocess_exec(
        *command,
        cwd=str(cwd),
        stdout=asyncio.subprocess.PIPE,
        stderr=asyncio.subprocess.PIPE,
        text=True,
    )
    stdout, stderr = await process.communicate()

    if stdout:
        LOGGER.debug("%s stdout:\n%s", command[0], stdout)
    if stderr:
        LOGGER.warning("%s stderr:\n%s", command[0], stderr)

    return subprocess.CompletedProcess(command, process.returncode, stdout, stderr)


def build_certificate(config: WorkerConfig, validation: subprocess.CompletedProcess[str], evac: subprocess.CompletedProcess[str]) -> Dict[str, Any]:
    """Compose a JSON serialisable certificate for coordinator ingestion."""

    timestamp = time.time()
    certificate: Dict[str, Any] = {
        "node_id": config.node_id,
        "hostname": socket.gethostname(),
        "platform": platform.platform(),
        "timestamp": timestamp,
        "precision": config.precision,
        "evac_frequency": config.evac_frequency,
        "validation": {
            "command": validation.args,
            "returncode": validation.returncode,
            "stdout": validation.stdout,
            "stderr": validation.stderr,
        },
        "evac_rpsi": {
            "command": evac.args,
            "returncode": evac.returncode,
            "stdout": evac.stdout,
            "stderr": evac.stderr,
        },
    }
    return certificate


async def upload_certificate(config: WorkerConfig, payload: Dict[str, Any]) -> None:
    """Send the aggregated payload to the coordinator REST endpoint."""

    url = f"{config.api_base.rstrip('/')}/api/upload"
    async with httpx.AsyncClient(timeout=30) as client:
        response = await client.post(url, json=payload)
        response.raise_for_status()
        LOGGER.info("Uploaded certificate to %s (status %s)", url, response.status_code)


async def websocket_heartbeat(config: WorkerConfig) -> None:
    """Send heartbeat pings if a WebSocket endpoint is configured."""

    if websockets is None or not config.websocket_url:
        return

    while True:
        try:
            async with websockets.connect(config.websocket_url) as ws:  # type: ignore[attr-defined]
                LOGGER.info("Connected to coordinator WebSocket")
                while True:
                    heartbeat = json.dumps({
                        "node_id": config.node_id,
                        "timestamp": time.time(),
                        "status": "idle",
                    })
                    await ws.send(heartbeat)
                    await asyncio.sleep(config.poll_interval)
        except Exception as exc:  # pragma: no cover - network failure paths
            LOGGER.error("WebSocket heartbeat failed: %s", exc)
            await asyncio.sleep(min(config.poll_interval, 60.0))


async def run_cycle(config: WorkerConfig) -> None:
    repo_root = Path(__file__).resolve().parents[2]
    LOGGER.info("Using repository root at %s", repo_root)

    validation_cmd = [
        "python",
        config.validate_script,
        "--precision",
        str(config.precision),
    ]

    evac_cmd = [
        "python",
        "-m",
        config.evac_script,
        "--frequency",
        str(config.evac_frequency),
    ]

    validation = await run_subprocess(validation_cmd, repo_root)
    evac = await run_subprocess(evac_cmd, repo_root)

    OUTPUT_DIR.mkdir(exist_ok=True)
    output_path = OUTPUT_DIR / f"certificate_{int(time.time())}.json"
    certificate = build_certificate(config, validation, evac)
    output_path.write_text(json.dumps(certificate, indent=2))
    LOGGER.info("Stored local certificate at %s", output_path)

    await upload_certificate(config, certificate)


async def worker_loop(config: WorkerConfig) -> None:
    LOGGER.info("Starting QCAL worker with poll interval %.1fs", config.poll_interval)
    while True:
        await run_cycle(config)
        await asyncio.sleep(config.poll_interval)


def load_config(path: Path) -> WorkerConfig:
    data = json.loads(path.read_text())
    return WorkerConfig.from_mapping(data)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Run the QCAL worker")
    parser.add_argument("--config", type=Path, default=DEFAULT_CONFIG_PATH)
    parser.add_argument(
        "--once",
        action="store_true",
        help="Run a single validation cycle instead of looping",
    )
    parser.add_argument(
        "--verbose",
        action="store_true",
        help="Enable verbose logging",
    )
    return parser.parse_args()


async def main_async(config: WorkerConfig, run_once: bool) -> None:
    if config.websocket_url and websockets is not None:
        asyncio.create_task(websocket_heartbeat(config))

    if run_once:
        await run_cycle(config)
    else:
        await worker_loop(config)


def configure_logging(verbose: bool) -> None:
    level = logging.DEBUG if verbose else logging.INFO
    logging.basicConfig(level=level, format="%(asctime)s [%(levelname)s] %(name)s: %(message)s")


def main() -> None:
    args = parse_args()
    configure_logging(args.verbose)

    config_path: Path = args.config
    if not config_path.exists():
        raise FileNotFoundError(f"Config file {config_path} does not exist")

    config = load_config(config_path)

    try:
        asyncio.run(main_async(config, run_once=args.once))
    except KeyboardInterrupt:
        LOGGER.info("Interrupted by user")


if __name__ == "__main__":
    main()
