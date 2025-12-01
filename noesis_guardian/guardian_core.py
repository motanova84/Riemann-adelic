#!/usr/bin/env python3
"""
Guardian Core - Central Orchestration for Noesis Guardian
----------------------------------------------------------

This module provides the central coordination for all monitoring hooks,
alert notification, and spectral integrity validation.

Usage:
    from noesis_guardian.guardian_core import GuardianCore

    guardian = GuardianCore()
    report = guardian.run_all_hooks()

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
"""

import json
import logging
from datetime import datetime
from pathlib import Path
from typing import Any, Callable, Dict, Optional

from .modules.hook_schatten_paley import SchattenPaley


# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s - %(name)s - %(levelname)s - %(message)s"
)
logger = logging.getLogger("NoesisGuardian")


# Status constants for hook results
class Status:
    """Status constants for Guardian hook results."""
    OK = "ok"
    ANOMALY = "⚠️ anomaly"
    MISSING_DATA = "missing_data"
    ERROR = "error"


class Notifier:
    """
    Alert notification system for Guardian events.

    Handles alerting when monitoring hooks detect anomalies
    or when system integrity is compromised.
    """

    @staticmethod
    def alert(message: str, data: Optional[Dict[str, Any]] = None) -> None:
        """
        Emit an alert notification.

        In production, this can be extended to send emails,
        Slack messages, or trigger other notification systems.

        Args:
            message: Alert message
            data: Optional additional data to include
        """
        logger.warning(f"🚨 ALERT: {message}")
        if data:
            logger.warning(f"   Data: {json.dumps(data, indent=2)}")

    @staticmethod
    def info(message: str) -> None:
        """
        Log an informational message.

        Args:
            message: Info message
        """
        logger.info(f"ℹ️  {message}")

    @staticmethod
    def success(message: str) -> None:
        """
        Log a success message.

        Args:
            message: Success message
        """
        logger.info(f"✅ {message}")


class GuardianCore:
    """
    Central orchestration for the Noesis Guardian system.

    This class manages all monitoring hooks and coordinates
    their execution to ensure spectral operator integrity.

    Attributes:
        hooks: Dictionary of registered monitoring hooks
        last_report: Last execution report
    """

    def __init__(self) -> None:
        """Initialize GuardianCore with default hooks."""
        self.hooks: Dict[str, Callable[[], Dict[str, Any]]] = {}
        self.last_report: Optional[Dict[str, Any]] = None

        # Register default hooks
        self._register_default_hooks()

    def _register_default_hooks(self) -> None:
        """Register the default set of monitoring hooks."""
        self.register_hook("schatten_paley", SchattenPaley.run)

    def register_hook(
        self, name: str, hook_func: Callable[[], Dict[str, Any]]
    ) -> None:
        """
        Register a new monitoring hook.

        Args:
            name: Unique identifier for the hook
            hook_func: Callable that returns a status dictionary
        """
        self.hooks[name] = hook_func
        Notifier.info(f"Registered hook: {name}")

    def run_hook(self, name: str) -> Dict[str, Any]:
        """
        Execute a specific hook by name.

        Args:
            name: Name of the hook to run

        Returns:
            Hook execution result dictionary

        Raises:
            KeyError: If hook name not found
        """
        if name not in self.hooks:
            raise KeyError(f"Hook '{name}' not registered")

        Notifier.info(f"Running hook: {name}")
        result = self.hooks[name]()

        if result.get("status") not in (Status.OK, Status.MISSING_DATA):
            Notifier.alert(
                f"⚠️ Anomaly in {name} functional invariants", result
            )

        return result

    def run_all_hooks(self) -> Dict[str, Any]:
        """
        Execute all registered monitoring hooks.

        Returns:
            Complete execution report with all hook results
        """
        timestamp = datetime.now().isoformat()
        report: Dict[str, Any] = {
            "timestamp": timestamp,
            "hooks": {},
            "overall_status": Status.OK,
            "anomalies": [],
        }

        for name in self.hooks:
            try:
                result = self.run_hook(name)
                report["hooks"][name] = result

                if result.get("status") not in (Status.OK, Status.MISSING_DATA):
                    report["overall_status"] = Status.ANOMALY
                    report["anomalies"].append({
                        "hook": name,
                        "status": result.get("status"),
                        "message": result.get("message"),
                    })
            except Exception as e:
                error_result = {
                    "status": Status.ERROR,
                    "message": str(e),
                }
                report["hooks"][name] = error_result
                report["overall_status"] = Status.ERROR
                report["anomalies"].append({
                    "hook": name,
                    "status": Status.ERROR,
                    "message": str(e),
                })
                Notifier.alert(f"Error in hook {name}", {"error": str(e)})

        self.last_report = report

        if report["overall_status"] == Status.OK:
            Notifier.success("All Guardian hooks passed")
        else:
            Notifier.alert(
                f"Guardian detected issues: {len(report['anomalies'])} anomalies"
            )

        return report

    def get_schatten_paley_report(self) -> Dict[str, Any]:
        """
        Get the Schatten-Paley hook report specifically.

        This is a convenience method for the most common use case.

        Returns:
            Schatten-Paley analysis report
        """
        return self.run_hook("schatten_paley")

    def save_report(self, filepath: Optional[str] = None) -> Path:
        """
        Save the last report to a JSON file.

        Args:
            filepath: Optional output path. Defaults to data/guardian_report.json

        Returns:
            Path to saved report file
        """
        if self.last_report is None:
            self.run_all_hooks()

        if filepath is None:
            # Find data directory
            possible_paths = [
                Path("data"),
                Path(__file__).parent.parent / "data",
                Path.cwd() / "data",
            ]
            data_dir = next(
                (p for p in possible_paths if p.exists()), Path("data")
            )
            data_dir.mkdir(exist_ok=True)
            filepath = data_dir / "guardian_report.json"
        else:
            filepath = Path(filepath)

        with open(filepath, "w", encoding="utf-8") as f:
            json.dump(self.last_report, f, indent=2)

        Notifier.info(f"Report saved to: {filepath}")
        return filepath


def main() -> None:
    """Main entry point for Guardian Core execution."""
    print("=" * 70)
    print("NOESIS GUARDIAN - Spectral Operator Monitoring System")
    print("=" * 70)

    guardian = GuardianCore()
    report = guardian.run_all_hooks()

    print("\n" + "=" * 70)
    print("GUARDIAN REPORT")
    print("=" * 70)
    print(json.dumps(report, indent=2))

    # Process Schatten-Paley specifically
    sp_report = report["hooks"].get("schatten_paley", {})
    if sp_report.get("status") != "ok":
        Notifier.alert(
            "⚠️ Anomaly in Schatten–Paley functional invariants",
            sp_report
        )


if __name__ == "__main__":
    main()
