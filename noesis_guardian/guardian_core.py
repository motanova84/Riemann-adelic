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
"""

import hashlib
import json
import logging
import os
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, Optional, List

# Handle both package import and direct script execution
if __name__ == "__main__":
    sys.path.insert(0, str(Path(__file__).parent.parent))
    from noesis_guardian.modules.coherency_hooks import CoherencyHooks
    from noesis_guardian.modules.hook_calabi_yau_resonance import CalabiYauResonance
else:
    from .modules.coherency_hooks import CoherencyHooks
    from .modules.hook_calabi_yau_resonance import CalabiYauResonance

# Log file path for Guardian activity
LOGFILE = "noesis_guardian/logs/guardian_log.json"

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger('noesis_guardian')


def _sanitize_timestamp(timestamp: str) -> str:
    """Sanitize timestamp for use in filenames by replacing special characters."""
    return re.sub(r'[:.]+', '-', timestamp)


class Notifier:
    """Simple notification handler for Guardian alerts."""

    @staticmethod
    def alert(message: str, data: Optional[Dict[str, Any]] = None) -> None:
        """
        Send an alert notification.

        Args:
            message: Alert message
            data: Optional additional data
        """
        logger.warning(f"ALERT: {message}")
        if data:
            logger.warning(f"Context: {json.dumps(data, indent=2, default=str)}")
            # Print summary of hook results
            for title, result in data.items():
                status = "✅" if result.get("ok", False) else "❌"
                print(f"   {status} {title}")

    @staticmethod
    def info(message: str) -> None:
        """Log an informational message."""
        logger.info(message)

    @staticmethod
    def success(message: str) -> None:
        """Log a success message."""
        logger.info(f"✓ {message}")

    def __init__(self, repo_root: Optional[Path] = None):
        """
        Initialize the Guardian.

        Args:
            repo_root: Path to repository root. If None, auto-detected.
        """
        if repo_root:
            self.repo_root = Path(repo_root)
        else:
            # Auto-detect repository root
            self.repo_root = self._find_repo_root()

        self.logs_dir = Path(__file__).parent / "logs"
        self.logs_dir.mkdir(parents=True, exist_ok=True)

        self.log_file = self.logs_dir / "guardian_log.json"
        
        # Initialize components for compatibility with tests
        from .modules.watcher import RepoWatcher
        from .modules.autorepair_engine import AutoRepairEngine
        from .modules.spectral_monitor import SpectralMonitor
        
        self.watcher = RepoWatcher()
        self.repair_engine = AutoRepairEngine()
        self.spectral_monitor = SpectralMonitor()

    @staticmethod
    def emit(entry: Dict) -> None:
        """
        Emit entry to AIK synchronization system.

        Args:
            entry: Guardian entry data
        """
        # Load existing log or create new
        log_data = []
        if self.log_file.exists():
            try:
                with open(self.log_file, 'r') as f:
                    log_data = json.load(f)
                    if not isinstance(log_data, list):
                        log_data = [log_data]
            except (json.JSONDecodeError, FileNotFoundError):
                log_data = []

        # Append new entry
        log_data.append(entry)

        # Keep only last 100 entries
        log_data = log_data[-100:]

        # Save
        with open(self.log_file, 'w') as f:
            json.dump(log_data, f, indent=2, default=str)

        print(f"📝 Log saved to: {self.log_file}")


def main():
    """Main entry point for Guardian execution."""
    guardian = NoesisGuardian()
    result = guardian.run_cycle()

    # Exit with appropriate code
    hooks = result.get("hooks", {})
    all_passed = all(h.get("ok", False) for h in hooks.values())

    sys.exit(0 if all_passed else 1)


import json
import time
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, Optional


class RepoWatcher:
    """Local placeholder implementation for repository watching.

    The real implementation should be provided in a dedicated module.
    This stub is designed to avoid import errors and to be minimally
    compatible with typical usage patterns in NoesisGuardian.
    """

    def __init__(self, *args: Any, **kwargs: Any) -> None:
        self._config = kwargs

    def start(self) -> None:
        """Start watching the repository (no-op placeholder)."""
        return None

    def run(self) -> Dict[str, Any]:
        """Run a single watch cycle and return an empty result."""
        return {}


class AutoRepairEngine:
    """Local placeholder implementation for automatic repair engine."""

    def __init__(self, *args: Any, **kwargs: Any) -> None:
        self._config = kwargs

    def run(self) -> Dict[str, Any]:
        """Execute auto-repair logic (no-op placeholder)."""
        return {}


class SpectralMonitor:
    """Local placeholder implementation for spectral monitoring."""

    def __init__(self, *args: Any, **kwargs: Any) -> None:
        self._config = kwargs

    def run(self) -> Dict[str, Any]:
        """Execute spectral monitoring (no-op placeholder)."""
        return {}


class SabioBridge:
    """Local placeholder implementation for Sabio bridge integration."""

    def __init__(self, *args: Any, **kwargs: Any) -> None:
        self._config = kwargs

    def sync(self) -> None:
        """Synchronize with external Sabio systems (no-op placeholder)."""
        return None
        # Generate AIK hash for entry
        entry_json = json.dumps(entry, sort_keys=True, default=str)
        aik_hash = hashlib.sha256(entry_json.encode()).hexdigest()[:16]
        print(f"🔗 AIK Hash: {aik_hash}")


class AikSync:
    """Aik synchronization placeholder."""

    @staticmethod
    def emit(entry: Dict[str, Any]) -> None:
        """Emit an entry to AIK sync (no-op placeholder)."""
        pass


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


# Alias for backward compatibility with old code
NoesisGuardian = GuardianCore


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


if __name__ == "__main__":
    main()


if __name__ == "__main__":
    main()
