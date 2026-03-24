#!/usr/bin/env python3
"""
AURA-CHECK — Noesis Guardian Skill
====================================

Health check skill for MCP servers triggered when QCAL coherence drops
below the threshold Ψ < 0.888.  Reads the server registry from config.json
(Trinity Protocol) and probes each server entry using the configured command.

Author: José Manuel Mota Burruezo (JMMB Ψ ✧)
System: QCAL-SABIO ∞³
Frequency: f₀ = 141.7001 Hz
"""

import json
import os
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List

# Coherence threshold below which Aura-Check is triggered
PSI_THRESHOLD: float = 0.888

# Timeout for each server probe (seconds)
PROBE_TIMEOUT: int = 5

# Default path to the Trinity MCP hub config
_DEFAULT_CONFIG = Path(__file__).parent.parent.parent / "config.json"


class AuraCheck:
    """
    Aura-Check skill for the Noesis Guardian.

    Reads the MCP server registry from config.json and performs a lightweight
    reachability probe for each server entry.  Results are collected and
    returned as a structured report that the Guardian can log or surface.

    Usage::

        checker = AuraCheck()
        report = checker.run()
        if not report["all_healthy"]:
            # handle degraded servers …
    """

    def __init__(self, config_path: str | None = None) -> None:
        """
        Initialise the Aura-Check skill.

        Args:
            config_path: Absolute path to the MCP hub config.json.
                         Defaults to ``<repo_root>/config.json``.
        """
        self.config_path = Path(config_path) if config_path else _DEFAULT_CONFIG
        self.repo_root = self.config_path.parent

    # ------------------------------------------------------------------
    # Public API
    # ------------------------------------------------------------------

    def should_trigger(self, psi: float) -> bool:
        """
        Return True when coherence Ψ falls below the threshold.

        Args:
            psi: Current global QCAL coherence value.

        Returns:
            bool: True if Aura-Check should run.
        """
        return psi < PSI_THRESHOLD

    def run(self, psi: float | None = None) -> Dict[str, Any]:
        """
        Execute the MCP server health check.

        Args:
            psi: Optional coherence value.  If provided and above threshold,
                 the check is skipped and a ``skipped`` report is returned.

        Returns:
            dict: Health report with keys:
                - ``timestamp``: ISO-8601 timestamp (UTC).
                - ``psi``: Coherence value supplied (or None).
                - ``triggered_by_threshold``: Whether Ψ < 0.888.
                - ``servers``: List of per-server probe results.
                - ``all_healthy``: True only if every server probe succeeded.
                - ``skipped``: True when the check was bypassed.
        """
        now = datetime.now(timezone.utc).isoformat()

        if psi is not None and not self.should_trigger(psi):
            return {
                "timestamp": now,
                "psi": psi,
                "triggered_by_threshold": False,
                "servers": [],
                "all_healthy": True,
                "skipped": True,
            }

        servers = self._load_servers()
        results = [self._probe(entry) for entry in servers]
        all_healthy = all(r["reachable"] for r in results)

        return {
            "timestamp": now,
            "psi": psi,
            "triggered_by_threshold": psi is None or self.should_trigger(psi),
            "servers": results,
            "all_healthy": all_healthy,
            "skipped": False,
        }

    # ------------------------------------------------------------------
    # Internal helpers
    # ------------------------------------------------------------------

    def _load_servers(self) -> List[Dict[str, Any]]:
        """
        Load the server list from config.json.

        Returns:
            List of server descriptor dicts from ``mcpServers``.
        """
        if not self.config_path.exists():
            return []

        try:
            with self.config_path.open(encoding="utf-8") as fh:
                data = json.load(fh)
        except (json.JSONDecodeError, OSError):
            return []

        mcp_servers = data.get("mcpServers", {})
        entries: List[Dict[str, Any]] = []
        for name, cfg in mcp_servers.items():
            # Skip comment-style keys (start with underscore)
            if name.startswith("_"):
                continue
            entries.append({"name": name, **cfg})
        return entries

    def _probe(self, server: Dict[str, Any]) -> Dict[str, Any]:
        """
        Probe a single MCP server entry.

        For Python/node servers we attempt to run the command with ``--version``
        (or ``--help``) to verify the binary is reachable.  The actual server
        process is NOT started.

        Args:
            server: Server descriptor from config.json.

        Returns:
            dict: Probe result with keys ``name``, ``reachable``, ``detail``.
        """
        name = server.get("name", "unknown")
        command = server.get("command", "")
        args = server.get("args", [])
        cwd_rel = server.get("cwd", ".")
        env_overlay = server.get("env", {})

        # Resolve working directory relative to the repo root
        cwd = str(self.repo_root / cwd_rel.lstrip("./"))

        # Build probe command: check the binary exists and is executable
        if command in ("python", "python3", "node"):
            probe_cmd = [command, "--version"]
        elif command == "npx":
            probe_cmd = ["npx", "--version"]
        else:
            probe_cmd = [command, "--version"]

        env = {**os.environ, **env_overlay}

        try:
            result = subprocess.run(
                probe_cmd,
                capture_output=True,
                text=True,
                timeout=PROBE_TIMEOUT,
                env=env,
                shell=False,
            )
            reachable = result.returncode == 0
            detail = (result.stdout or result.stderr).strip()[:200]
        except FileNotFoundError:
            reachable = False
            detail = f"Binary not found: {command}"
        except subprocess.TimeoutExpired:
            reachable = False
            detail = f"Probe timed out after {PROBE_TIMEOUT}s"
        except (OSError, PermissionError, ValueError) as exc:
            reachable = False
            detail = str(exc)[:200]

        return {
            "name": name,
            "command": command,
            "reachable": reachable,
            "detail": detail,
        }


def run_aura_check(psi: float | None = None, config_path: str | None = None) -> Dict[str, Any]:
    """
    Convenience entry point for running Aura-Check.

    Args:
        psi: Current global coherence value.  Pass None to always run.
        config_path: Path to the MCP hub config.json (optional).

    Returns:
        Health report dict (see :meth:`AuraCheck.run`).
    """
    checker = AuraCheck(config_path=config_path)
    report = checker.run(psi=psi)

    # Pretty-print summary to stdout
    if report.get("skipped"):
        print(f"⏭  Aura-Check skipped (Ψ={psi:.4f} ≥ {PSI_THRESHOLD})")
    else:
        status_icon = "✅" if report["all_healthy"] else "⚠️"
        psi_str = f"Ψ={psi:.4f}" if psi is not None else "Ψ=unset"
        print(f"{status_icon} Aura-Check [{psi_str}] — {report['timestamp']}")
        for srv in report["servers"]:
            icon = "✅" if srv["reachable"] else "❌"
            print(f"   {icon} {srv['name']}: {srv['detail']}")

    return report


if __name__ == "__main__":
    # CLI usage: python hook_aura_check.py [psi_value]
    psi_arg: float | None = None
    if len(sys.argv) > 1:
        try:
            psi_arg = float(sys.argv[1])
        except ValueError:
            print(f"Invalid Ψ value: {sys.argv[1]}", file=sys.stderr)
            sys.exit(1)

    result = run_aura_check(psi=psi_arg)
    sys.exit(0 if result.get("all_healthy") else 1)
