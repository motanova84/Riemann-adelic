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

import hashlib
import json
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, Optional

# Handle both package import and direct script execution
if __name__ == "__main__":
    sys.path.insert(0, str(Path(__file__).parent.parent))
    from noesis_guardian.modules.coherency_hooks import CoherencyHooks
else:
    from .modules.coherency_hooks import CoherencyHooks

# Log file path for Guardian activity
LOGFILE = "noesis_guardian/logs/guardian_log.json"


class Notifier:
    """Simple notification handler for Guardian alerts."""

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

        Args:
            message: Alert message
            data: Optional additional data
        """
        print(f"🚨 ALERT: {message}")
        if data:
            # Print summary of hook results
            for title, result in data.items():
                status = "✅" if result.get("ok", False) else "❌"
                print(f"   {status} {title}")


# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger('noesis_guardian')
    format="%(asctime)s - %(name)s - %(levelname)s - %(message)s"
)
logger = logging.getLogger("NoesisGuardian")

    @staticmethod
    def emit(entry: Dict) -> None:
        """
        Emit entry to AIK synchronization system.

        Args:
            entry: Guardian entry data
        """
        # Generate AIK hash for entry
        entry_json = json.dumps(entry, sort_keys=True, default=str)
        aik_hash = hashlib.sha256(entry_json.encode()).hexdigest()[:16]
        print(f"🔗 AIK Hash: {aik_hash}")


class NoesisGuardian:
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

    Orchestrates validation cycles, coherency checks, and logging
    for the QCAL ∞³ framework.
    """

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
    def _find_repo_root() -> Path:
        """Find the repository root by looking for .git directory."""
        current = Path.cwd()
        while current != current.parent:
            if (current / '.git').exists():
                return current
            current = current.parent
        return Path.cwd()

    def get_repo_state(self) -> Dict[str, Any]:
        """
        Get current repository state information.

        Returns:
            Dictionary with repository state details.
        """
        state = {
            "path": str(self.repo_root),
            "timestamp": datetime.now(timezone.utc).isoformat(),
        }

        try:
            # Get current commit hash
            result = subprocess.run(
                ["git", "rev-parse", "HEAD"],
                cwd=self.repo_root,
                capture_output=True,
                text=True,
                timeout=10
            )
            if result.returncode == 0:
                state["commit"] = result.stdout.strip()

            # Get current branch
            result = subprocess.run(
                ["git", "rev-parse", "--abbrev-ref", "HEAD"],
                cwd=self.repo_root,
                capture_output=True,
                text=True,
                timeout=10
            )
            if result.returncode == 0:
                state["branch"] = result.stdout.strip()

        except Exception as e:
            state["error"] = str(e)

        return state

    def get_spectral_state(self) -> Dict[str, Any]:
        """
        Get spectral validation state.

        Returns:
            Dictionary with spectral state information.
        """
        state = {
            "base_frequency": 141.7001,  # Hz - QCAL base frequency
            "coherence_constant": 244.36,  # C constant
        }

        # Check for spectral data file
        spectral_file = self.repo_root / "Evac_Rpsi_data.csv"
        if spectral_file.exists():
            state["data_file"] = str(spectral_file)
            state["data_exists"] = True
        else:
            state["data_exists"] = False

        return state

    def run_cycle(self) -> Dict[str, Any]:
        """
        Run a complete Guardian validation cycle.

        Returns:
            Dictionary with complete cycle results.
        """
        print("🧠 NOESIS Guardian 3.0 — Starting cycle...")
        print("=" * 60)

        # Build entry
        entry: Dict[str, Any] = {
            "timestamp": datetime.now(timezone.utc).isoformat(),
            "version": "3.0.0",
        }

        # Get repository state
        print("\n📂 Checking repository state...")
        entry["repo"] = self.get_repo_state()

        # Get spectral state
        print("\n📊 Checking spectral state...")
        entry["spectral"] = self.get_spectral_state()

        # -------------------------
        #  COHERENCY HOOKS
        # -------------------------
        print("\n🔍 Running coherency hooks...")
        hook_report = CoherencyHooks.run_all()
        entry["hooks"] = hook_report

        # Check for failures
        if any(not h["ok"] for h in hook_report.values()):
            Notifier.alert("❌ Hook de coherencia falló", hook_report)
            AikSync.emit(entry)

        # Save log
        self._save_log(entry)

        print("\n" + "=" * 60)
        print("🧠 Guardian 3.0 ciclo completado.")

        # Print summary
        passed = sum(1 for h in hook_report.values() if h["ok"])
        total = len(hook_report)
        print(f"📈 Hooks: {passed}/{total} passed")

        return entry

    def _save_log(self, entry: Dict[str, Any]) -> None:
        """
        Save entry to log file.

        Args:
            entry: Entry data to save
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
"""

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


class AikSync:
    """Local placeholder implementation for Aik synchronization."""

    def __init__(self, *args: Any, **kwargs: Any) -> None:
        self._config = kwargs

    def sync(self) -> None:
        """Perform Aik synchronization (no-op placeholder)."""
        return None
class NoesisGuardian:
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

    Orquesta todos los componentes del sistema de monitoreo
    y autorreparación del repositorio QCAL.

    Attributes:
        watcher: Vigilante del repositorio
        repair: Motor de reparación automática
        spectral: Monitor de coherencia espectral
    """

    # Constantes QCAL
    F0_HZ = 141.7001  # Frecuencia fundamental
    COHERENCE_CONSTANT = 244.36  # C = 244.36
    DEFAULT_CYCLE_INTERVAL = 1800  # 30 minutos
    DEFAULT_LOG_FILENAME = "guardian_log_v2.json"

    def __init__(self, repo_root: Optional[Path] = None, log_path: Optional[str] = None):
        """
        Inicializa el Guardian NOESIS.

        Args:
            repo_root: Ruta raíz del repositorio (opcional)
            log_path: Ruta para el archivo de log (opcional)
        """
        if repo_root is None:
            repo_root = Path(__file__).resolve().parents[1]

        self.repo_root = Path(repo_root)
        self.log_path = log_path or str(
            self.repo_root / "noesis_guardian" / self.DEFAULT_LOG_FILENAME
        )

        # Inicializar componentes
        self.watcher = RepoWatcher(self.repo_root)
        self.repair = AutoRepairEngine(self.repo_root)
        self.spectral = SpectralMonitor()

        # Estado interno
        self._running = False
        self._cycle_count = 0

    def noesis_signal(self) -> Dict[str, Any]:
        """
        Calcula la señal NOESIS del sistema.

        Returns:
            Señal NOESIS con estado vital del organismo
        """
        return self.spectral.compute_noesis_signal()

    def log(self, data: Dict[str, Any]) -> None:
        """
        Registra datos en el log del Guardian.

        Args:
            data: Datos a registrar
        """
        Run the Guardian and produce a log entry.
        
        This is an alias for run_cycle() for backward compatibility.
        
        Returns:
            Dictionary with complete cycle results.
        """
        entry = {
            "timestamp": datetime.now(timezone.utc).isoformat(),
            "repo": self.get_repo_state(),
            "spectral": self.spectral_monitor.check(),
        }
        return entry

    def log(self, entry: Dict[str, Any]) -> None:
        """
        Log an entry to the log file.
        
        Args:
            entry: Entry data to log
        """
        self._save_log(entry)


def main():
    """Main entry point for Guardian execution."""
    guardian = NoesisGuardian()
    result = guardian.run_cycle()

    # Exit with appropriate code
    hooks = result.get("hooks", {})
    all_passed = all(h.get("ok", False) for h in hooks.values())

    sys.exit(0 if all_passed else 1)


if __name__ == "__main__":
    main()

class NoesisGuardian:
    """
    Core Guardian class that orchestrates repository monitoring and maintenance.

    This class coordinates multiple monitoring and repair components to ensure
    the QCAL repository maintains structural integrity and coherence.
    """

    def __init__(self) -> None:
        """Initialize all Guardian components."""
        self.watcher = RepoWatcher()
        self.repair_engine = AutoRepairEngine()
        self.spectral_monitor = SpectralMonitor()

    def log(self, entry: dict) -> None:
        """
        Append a log entry to the Guardian log file.

        Args:
            entry: Dictionary containing log data to record.
        """
        os.makedirs(os.path.dirname(LOGFILE), exist_ok=True)
        with open(LOGFILE, "a") as f:
            f.write(json.dumps(entry) + "\n")

    def run_cycle(self) -> None:
        """Run a single monitoring and maintenance cycle."""
        repo_state = self.watcher.scan()
        spectral_state = self.spectral.check()
    def run(self) -> dict:
        """
        Execute a complete Guardian monitoring cycle.

        Returns:
            Dictionary containing the results of the monitoring cycle.
        """
        repo_state = self.watcher.scan()
        spectral_state = self.spectral_monitor.check()

        entry = {
            "timestamp": datetime.now().isoformat(),
            "repo": repo_state,
            "spectral": spectral_state,
        }

        self._log(entry)

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


if __name__ == "__main__":
    main()
