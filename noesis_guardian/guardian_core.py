#!/usr/bin/env python3
"""
NOESIS GUARDIAN 3.0 — CORE
Sistema técnico de monitorización y mantenimiento ligero del repositorio.

No es un sistema consciente, ni autónomo en sentido fuerte:
simplemente automatiza chequeos y pequeñas reparaciones estructurales.
"""

from datetime import datetime
import json
import os

from noesis_guardian.modules.watcher import RepoWatcher
from noesis_guardian.modules.autorepair_engine import AutoRepairEngine
from noesis_guardian.modules.spectral_monitor import SpectralMonitor
from noesis_guardian.modules.ai_notifier import Notifier
from noesis_guardian.modules.sabio_bridge import SabioBridge
from noesis_guardian.modules.aik_sync import AikSync

LOGFILE = "noesis_guardian/logs/guardian_log.json"


class NoesisGuardian:
    """Main guardian class for repository monitoring and maintenance."""

    def __init__(self) -> None:
        """Initialize the guardian with all monitoring modules."""
        self.watcher = RepoWatcher()
        self.repair = AutoRepairEngine()
        self.spectral = SpectralMonitor()

    def _log(self, entry: dict) -> None:
        """Log an entry to the guardian log file."""
        # Ensure logs directory exists
        os.makedirs(os.path.dirname(LOGFILE), exist_ok=True)
        with open(LOGFILE, "a") as f:
            f.write(json.dumps(entry) + "\n")

    def run_cycle(self) -> None:
        """Run a single monitoring and maintenance cycle."""
        repo_state = self.watcher.scan()
        spectral_state = self.spectral.check()

        entry = {
            "timestamp": datetime.now().isoformat(),
            "repo": repo_state,
            "spectral": spectral_state,
        }

        self._log(entry)

        # Condición mínima de "algo raro pasa"
        if repo_state["errors"] or not spectral_state["coherent"]:
            self.repair.repair(repo_state)
            Notifier.alert("Guardian ejecutó reparación mínima", entry)
            AikSync.emit(entry)

        # Registro "cognitivo" simbólico
        SabioBridge.update(entry)

        print("🧠 Guardian 3.0 ciclo completado.")
        print("   → missing:", repo_state["missing"])
        print("   → coherent:", spectral_state["coherent"])


if __name__ == "__main__":
    guardian = NoesisGuardian()
    guardian.run_cycle()
