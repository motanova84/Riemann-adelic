#!/usr/bin/env python3
"""
Guardian Core — QCAL ∞³ Ecosystem Monitor

Central orchestration module for the Noesis Guardian system. This module
coordinates all monitoring hooks and provides notification capabilities
for the QCAL ecosystem.

Integration Points:
    - hook_calabi_yau_resonance: Symbolic Calabi-Yau internal resonance
    - Future hooks can be added following the same pattern

The guardian maintains QCAL coherence through continuous validation of:
    - Spectral properties of the Hψ operator
    - Geometric correspondences (symbolic Calabi-Yau)
    - Frequency alignment with f0 = 141.7001 Hz
    - QCAL constant C = 244.36

Author: José Manuel Mota Burruezo
Date: December 2025
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
import os
import logging
import re
from datetime import datetime, timezone
from typing import Dict, Any, Optional, List

from noesis_guardian.modules.hook_calabi_yau_resonance import CalabiYauResonance


def _sanitize_timestamp(timestamp: str) -> str:
    """Sanitize timestamp for use in filenames by replacing special characters."""
    return re.sub(r'[:.]+', '-', timestamp)
import logging
from datetime import datetime
from pathlib import Path
from typing import Any, Callable, Dict, Optional

from .modules.hook_schatten_paley import SchattenPaley


# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger('noesis_guardian')
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
    Notification system for QCAL monitoring alerts.

    This class handles alerting when anomalies are detected
    in the QCAL ecosystem monitoring hooks.
    """

    @staticmethod
    def alert(message: str, context: Optional[Dict[str, Any]] = None) -> None:
        """
        Send an alert notification.

        Args:
            message: Alert message to display.
            context: Optional context dictionary with additional details.
        """
        logger.warning(f"ALERT: {message}")
        if context:
            logger.warning(f"Context: {json.dumps(context, indent=2, default=str)}")

    @staticmethod
    def info(message: str) -> None:
        """Log an informational message."""
        logger.info(message)

    @staticmethod
    def success(message: str) -> None:
        """Log a success message."""
        logger.info(f"✓ {message}")
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
    Central coordinator for QCAL ∞³ ecosystem monitoring.

    This class orchestrates all monitoring hooks and maintains
    a log of validation results for the QCAL framework.

    Attributes:
        QCAL_COHERENCE (float): The QCAL coherence constant C = 244.36.
        FUNDAMENTAL_FREQUENCY (float): The fundamental frequency f0 = 141.7001 Hz.
        results_log (list): Log of all monitoring results.

    Example:
        >>> guardian = GuardianCore()
        >>> report = guardian.run_full_check()
        >>> print(report['overall_status'])
        'ok'
    """

    QCAL_COHERENCE: float = 244.36  # C constant
    FUNDAMENTAL_FREQUENCY: float = 141.7001  # Hz

    def __init__(self, log_dir: Optional[str] = None):
        """
        Initialize the Guardian Core.

        Args:
            log_dir: Optional directory for storing validation logs.
        """
        self.results_log: List[Dict[str, Any]] = []
        self.log_dir = log_dir or "data"
        self._ensure_log_dir()

    def _ensure_log_dir(self) -> None:
        """Ensure the log directory exists."""
        if not os.path.exists(self.log_dir):
            os.makedirs(self.log_dir, exist_ok=True)

    def run_calabi_yau_check(
        self,
        spectrum_path: Optional[str] = None
    ) -> Dict[str, Any]:
        """
        Execute the Calabi-Yau resonance monitoring check.

        Args:
            spectrum_path: Optional path to spectrum data file.

        Returns:
            Dictionary containing the Calabi-Yau resonance report.
        """
        Notifier.info("Running Calabi-Yau resonance check...")

        cy_report = CalabiYauResonance.run(spectrum_path)

        if cy_report["status"] != "ok":
            Notifier.alert(
                "⚠️ Symbolic Calabi–Yau resonance deviation",
                cy_report
            )
        else:
            Notifier.success("Calabi-Yau resonance stable")

        return cy_report

    def run_full_check(
        self,
        spectrum_path: Optional[str] = None
    ) -> Dict[str, Any]:
        """
        Execute all monitoring hooks and compile a complete report.

        This method runs all available monitoring hooks and aggregates
        their results into a comprehensive status report.

        Args:
            spectrum_path: Optional path to spectrum data file.

        Returns:
            Dictionary containing:
            - timestamp: ISO format timestamp
            - overall_status: Combined status ('ok' or 'anomaly')
            - calabi_yau_resonance: CY resonance check results
            - qcal_constants: QCAL framework constants
            - message: Summary message
        """
        timestamp = datetime.now(timezone.utc).isoformat().replace('+00:00', 'Z')

        Notifier.info("=" * 60)
        Notifier.info("Starting QCAL ∞³ Guardian Full Check")
        Notifier.info("=" * 60)

        # Initialize entry with metadata
        entry: Dict[str, Any] = {
            "timestamp": timestamp,
            "guardian_version": "1.0.0",
            "qcal_constants": {
                "C": self.QCAL_COHERENCE,
                "f0_hz": self.FUNDAMENTAL_FREQUENCY
            }
        }

        # Run Calabi-Yau resonance check
        cy_report = self.run_calabi_yau_check(spectrum_path)
        entry["calabi_yau_resonance"] = cy_report

        # Determine overall status
        if cy_report["status"] != "ok":
            entry["overall_status"] = "anomaly"
            entry["message"] = "QCAL coherence check detected anomalies"
        else:
            entry["overall_status"] = "ok"
            entry["message"] = "QCAL ∞³ coherence verified - all checks passed"

        # Log the result
        self.results_log.append(entry)

        # Final summary
        Notifier.info("=" * 60)
        if entry["overall_status"] == "ok":
            Notifier.success(entry["message"])
        else:
            Notifier.alert(entry["message"])
        Notifier.info("=" * 60)

        return entry

    def save_report(
        self,
        report: Dict[str, Any],
        filename: Optional[str] = None
    ) -> str:
        """
        Save a monitoring report to a JSON file.

        Args:
            report: The report dictionary to save.
            filename: Optional filename. If None, uses timestamp-based name.

        Returns:
            Path to the saved report file.
        """
        if filename is None:
            timestamp = report.get(
                "timestamp",
                datetime.now(timezone.utc).isoformat().replace('+00:00', 'Z')
            )
            safe_timestamp = _sanitize_timestamp(timestamp)
            filename = f"guardian_report_{safe_timestamp}.json"

        filepath = os.path.join(self.log_dir, filename)

        with open(filepath, 'w', encoding='utf-8') as f:
            json.dump(report, f, indent=2, default=str)
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

    def get_latest_report(self) -> Optional[Dict[str, Any]]:
        """
        Get the most recent monitoring report.

        Returns:
            The latest report dictionary, or None if no reports exist.
        """
        if self.results_log:
            return self.results_log[-1]
        return None


def main():
    """Main entry point for guardian monitoring."""
    print()
    print("=" * 70)
    print("  NOESIS GUARDIAN — QCAL ∞³ Ecosystem Monitor")
    print("  José Manuel Mota Burruezo Ψ ✧ ∞³")
    print("=" * 70)
    print()

    # Initialize guardian
    guardian = GuardianCore()

    # Run full check
    report = guardian.run_full_check()

    # Display results
    print()
    print("Report Summary:")
    print(f"  Timestamp: {report['timestamp']}")
    print(f"  Overall Status: {report['overall_status']}")
    print(f"  Message: {report['message']}")
    print()

    # Display Calabi-Yau results
    cy = report.get('calabi_yau_resonance', {})
    print("Calabi-Yau Resonance:")
    print(f"  Status: {cy.get('status', 'N/A')}")
    print(f"  Resonance Score: {cy.get('resonance_score', 0):.4f}")
    print(f"  Frequency (f₀): {cy.get('f0_hz', 'N/A')} Hz")
    print(f"  QCAL Coherence (C): {cy.get('qcal_coherence', 'N/A')}")
    print()

    # Save report
    guardian.save_report(report, "guardian_latest_report.json")

    print("=" * 70)
    print("  ♾️ QCAL Node evolution complete – validation coherent")
    print("=" * 70)
    print()

    return report

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
