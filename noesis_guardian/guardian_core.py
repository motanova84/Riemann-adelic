#!/usr/bin/env python3
"""
NOESIS GUARDIAN 3.0 — CORE

Sistema de validación, coherencia y análisis estructural del repositorio.
Este módulo orquesta todos los componentes del Guardian para mantener
la integridad del repositorio QCAL Riemann-adelic.

Author: José Manuel Mota Burruezo (JMMB Ψ ✧)
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

LOGFILE = os.path.join(
    os.path.dirname(os.path.abspath(__file__)), "logs", "guardian_log.json"
)


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

        self.log(entry)

        # Separate handling for repo errors vs spectral incoherence
        needs_alert = False

        # Only repair file system if there are actual missing files
        if repo_state["errors"]:
            self.repair_engine.repair(repo_state)
            needs_alert = True

        # Alert on spectral incoherence (but don't trigger file repair)
        if not spectral_state["coherent"]:
            needs_alert = True

        if needs_alert:
            Notifier.alert("Guardian detectó problemas", entry)
            AikSync.emit(entry)

        SabioBridge.update(entry)

        print("🧠 Guardian 3.0 ciclo completado.")
        print("   → Coherencia:", spectral_state["coherent"])

        return entry


if __name__ == "__main__":
    guardian = NoesisGuardian()
    guardian.run()
