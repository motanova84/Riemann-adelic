#!/usr/bin/env python3
"""
NOESIS Guardian Core — Central Monitoring and Alert System

Orchestrates all spectral monitoring hooks and provides alert capabilities
for structural incoherence detection in the Riemann operator.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
DOI: 10.5281/zenodo.17379721
QCAL: f₀=141.7001 Hz, C=244.36
"""

from __future__ import annotations

import json
import sys
from datetime import datetime
from pathlib import Path
from typing import Any

from noesis_guardian.modules.hook_spectral_heat import SpectralHeat


class Notifier:
    """
    Alert notification system for spectral anomalies.

    Provides methods for reporting and logging spectral incoherence
    detected by the Guardian monitoring system.
    """

    LOG_DIR = Path(__file__).parent.parent / "logs" / "guardian"

    @classmethod
    def _ensure_log_dir(cls) -> None:
        """Ensure the log directory exists."""
        cls.LOG_DIR.mkdir(parents=True, exist_ok=True)

    @classmethod
    def alert(cls, message: str, data: dict[str, Any] | None = None) -> None:
        """
        Send an alert about spectral anomaly.

        Args:
            message: Alert message describing the anomaly
            data: Additional data about the anomaly
        """
        cls._ensure_log_dir()

        timestamp = datetime.now().isoformat()
        alert_entry = {
            "timestamp": timestamp,
            "type": "spectral_alert",
            "message": message,
            "data": data
        }

        # Print to stderr for immediate visibility
        print(f"🚨 GUARDIAN ALERT: {message}", file=sys.stderr)
        if data:
            print(f"   Data: {json.dumps(data, indent=2)}", file=sys.stderr)

        # Log to file
        log_file = cls.LOG_DIR / f"alerts_{datetime.now().strftime('%Y%m%d')}.json"

        alerts = []
        if log_file.exists():
            try:
                with open(log_file) as f:
                    alerts = json.load(f)
            except (json.JSONDecodeError, IOError):
                alerts = []

        alerts.append(alert_entry)

        with open(log_file, "w") as f:
            json.dump(alerts, f, indent=2)

    @classmethod
    def info(cls, message: str, data: dict[str, Any] | None = None) -> None:
        """
        Log an informational message.

        Args:
            message: Info message
            data: Additional data
        """
        timestamp = datetime.now().isoformat()
        print(f"ℹ️  GUARDIAN INFO [{timestamp}]: {message}")
        if data:
            print(f"   {json.dumps(data, indent=2)}")

    @classmethod
    def success(cls, message: str, data: dict[str, Any] | None = None) -> None:
        """
        Log a success message.

        Args:
            message: Success message
            data: Additional data
        """
        timestamp = datetime.now().isoformat()
        print(f"✅ GUARDIAN SUCCESS [{timestamp}]: {message}")
        if data:
            print(f"   {json.dumps(data, indent=2)}")


class GuardianCore:
    """
    Central coordinator for NOESIS Guardian monitoring.

    Runs all spectral hooks and aggregates results into a unified
    monitoring report with alerts for any detected anomalies.
    """

    QCAL_FREQUENCY = 141.7001
    QCAL_COHERENCE = 244.36

    @classmethod
    def run_all_hooks(cls) -> dict[str, Any]:
        """
        Execute all monitoring hooks and compile results.

        Returns:
            Comprehensive monitoring report with all hook results
        """
        timestamp = datetime.now().isoformat()

        entry = {
            "timestamp": timestamp,
            "guardian": "NOESIS",
            "version": "1.0.0",
            "qcal": {
                "base_frequency": cls.QCAL_FREQUENCY,
                "coherence": cls.QCAL_COHERENCE
            },
            "hooks": {},
            "alerts": [],
            "status": "initializing"
        }

        # --- Hook B: Spectral Heat ---
        Notifier.info("Running Hook B: Spectral Heat Analysis...")
        spectral_report = SpectralHeat.run()
        entry["hooks"]["spectral_heat"] = spectral_report
        entry["spectral_heat"] = spectral_report  # For backward compatibility

        if not spectral_report.get("hilbert_polya_ok", True):
            alert_msg = "⚠️ Anomalía espectral profunda detectada"
            Notifier.alert(alert_msg, spectral_report)
            entry["alerts"].append({
                "hook": "spectral_heat",
                "message": alert_msg,
                "severity": "critical"
            })

        if spectral_report.get("status") == "missing_data":
            Notifier.alert("Missing spectral data files", spectral_report)
            entry["alerts"].append({
                "hook": "spectral_heat",
                "message": "Missing data files",
                "severity": "error"
            })

        # --- Determine overall status ---
        if entry["alerts"]:
            critical = any(a.get("severity") == "critical" for a in entry["alerts"])
            entry["status"] = "critical" if critical else "warning"
        elif spectral_report.get("status") == "ok":
            entry["status"] = "coherent"
            Notifier.success("All hooks passed - spectral coherence verified")
        else:
            entry["status"] = "unknown"

        return entry

    @classmethod
    def save_report(cls, report: dict[str, Any], output_path: Path | None = None) -> Path:
        """
        Save monitoring report to file.

        Args:
            report: The monitoring report to save
            output_path: Optional custom output path

        Returns:
            Path to the saved report file
        """
        if output_path is None:
            reports_dir = Path(__file__).parent.parent / "data" / "guardian_reports"
            reports_dir.mkdir(parents=True, exist_ok=True)
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            output_path = reports_dir / f"guardian_report_{timestamp}.json"

        with open(output_path, "w") as f:
            json.dump(report, f, indent=2)

        return output_path


def run_guardian() -> dict[str, Any]:
    """
    Main entry point for running the Guardian monitoring system.

    Returns:
        Complete monitoring report
    """
    Notifier.info("NOESIS Guardian starting...")
    Notifier.info(f"QCAL Parameters: f₀={GuardianCore.QCAL_FREQUENCY} Hz, C={GuardianCore.QCAL_COHERENCE}")

    report = GuardianCore.run_all_hooks()

    if report["status"] == "coherent":
        Notifier.success("Guardian validation complete - all systems coherent")
    else:
        Notifier.alert(f"Guardian status: {report['status']}", report.get("alerts"))

    return report


if __name__ == "__main__":
    report = run_guardian()
    print("\n" + "=" * 60)
    print("NOESIS GUARDIAN REPORT")
    print("=" * 60)
    print(json.dumps(report, indent=2))

    if report["status"] not in ("coherent", "ok"):
        sys.exit(1)
