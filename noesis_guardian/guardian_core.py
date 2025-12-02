#!/usr/bin/env python3
"""
NOESIS GUARDIAN 3.0 — CORE
Sistema técnico de monitorización y mantenimiento ligero del repositorio.

No es un sistema consciente, ni autónomo en sentido fuerte:
simplemente automatiza chequeos y pequeñas reparaciones estructurales.

Author: José Manuel Mota Burruezo (JMMB Ψ ✧)
System: QCAL–SABIO ∞³

This is the core Guardian module that orchestrates coherency checks
and validation of the QCAL framework.

Features:
- Repository state monitoring
- Spectral validation
- Coherency hooks execution
- Logging and notification
- AIK synchronization (optional)

Security Guarantees:
- ❌ Does NOT modify Lean files
- ❌ Does NOT write to critical files
- ❌ Does NOT create infinite loops
- ❌ Does NOT affect formal proofs
- ✔️ Only executes existing Python code
- ✔️ Captures failures
- ✔️ Records logs
- ✔️ Emits minimal alerts
"""

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


class Notifier:
    """Simple notification handler for Guardian alerts."""

    @staticmethod
    def alert(message: str, data: Optional[Dict] = None) -> None:
        """
        Send an alert notification.

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


class AikSync:
    """AIK synchronization handler for Guardian entries."""

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
    NOESIS Guardian 3.0 — Core Controller

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
NOESIS GUARDIAN CORE ∞³ — VERSIÓN 2.0

Autorreparación profunda + Notificaciones + Panel + Sincronización QCAL

Incluye:
- Latido 141.7001 Hz
- Lectura espectral en vivo
- Autoinspección del repositorio
- Ejecución condicional inteligente
- Regeneración profunda
- Conexión con SABIO y AIK
- Envío de alertas
- Registro universal

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
License: Creative Commons BY-NC-SA 4.0
"""

import json
import time
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, Optional

from .watcher import RepoWatcher
from .autorepair_engine import AutoRepairEngine
from .spectral_monitor import SpectralMonitor
from .ai_notifier import Notifier
from .sabio_bridge import SabioBridge
from .aik_sync import AikSync


class NoesisGuardian:
    """
    Coordinador principal del sistema NOESIS Guardian 2.0.

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
        try:
            log_dir = Path(self.log_path).parent
            log_dir.mkdir(parents=True, exist_ok=True)

            with open(self.log_path, "a", encoding="utf-8") as f:
                f.write(json.dumps(data, default=str) + "\n")
        except Exception as e:
            Notifier.error(f"Error writing log: {e}")

    def run_cycle(self) -> Dict[str, Any]:
        """
        Ejecuta un ciclo completo de monitoreo y reparación.

        Returns:
            Resultado del ciclo incluyendo estado, coherencia y acciones
        """
        self._cycle_count += 1
        cycle_start = time.time()

        # 1. Escanear repositorio
        state = self.watcher.scan_repo()

        # 2. Verificar coherencia espectral
        coherence = self.spectral.check_spectral_coherence()

        # 3. Calcular señal NOESIS
        signal = self.noesis_signal()

        # 4. Construir registro completo
        full_state = {
            "timestamp": datetime.now().isoformat(),
            "cycle": self._cycle_count,
            "state": state,
            "spectral": coherence,
            "signal": signal,
            "duration_ms": 0,  # Se actualizará al final
        }

        # 5. Registrar estado
        self.log(full_state)

        # 6. Evaluar si se necesita reparación
        needs_repair = (
            state.get("collisions", 0) > 0
            or state.get("missing", 0) > 0
            or state.get("lean_status") not in ["ok", "not_found"]
            or coherence.get("coherent") is False
        )

        repair_report = None
        if needs_repair:
            # Ejecutar reparación
            repair_report = self.repair.full_repair(state)
            full_state["repair"] = repair_report

            # Enviar alerta
            Notifier.alert("⚠️ Reparación ejecutada", full_state)

            # Sincronizar certificado AIK
            AikSync.sync_certificate(full_state)

        # 7. Actualizar estado en SABIO
        SabioBridge.update_state(full_state)

        # 8. Calcular duración
        duration_ms = (time.time() - cycle_start) * 1000
        full_state["duration_ms"] = duration_ms

        # 9. Imprimir resumen
        print(f"🧠 Ciclo Guardian 2.0 #{self._cycle_count} completado.")
        print(f"   → Señal: {signal['state']}")
        print(f"   → Coherencia: {coherence['coherent']}")
        print(f"   → Duración: {duration_ms:.2f}ms")

        if repair_report:
            print(f"   → Reparaciones: {len(repair_report.get('actions', []))}")

        return full_state

    def run(self, interval: Optional[int] = None, max_cycles: Optional[int] = None) -> None:
        """
        Ejecuta el Guardian en modo continuo.

        Args:
            interval: Intervalo entre ciclos en segundos (default: 1800)
            max_cycles: Número máximo de ciclos (None = infinito)
        """
        if interval is None:
            interval = self.DEFAULT_CYCLE_INTERVAL

        self._running = True
        cycles_run = 0

        print("=" * 60)
        print("NOESIS GUARDIAN 2.0 — Iniciando")
        print("=" * 60)
        print(f"Frecuencia: {self.F0_HZ} Hz")
        print(f"Coherencia: C = {self.COHERENCE_CONSTANT}")
        print(f"Intervalo: {interval}s ({interval // 60} minutos)")
        print("=" * 60)

        try:
            while self._running:
                self.run_cycle()
                cycles_run += 1

                if max_cycles and cycles_run >= max_cycles:
                    print(f"\n✅ Completados {max_cycles} ciclos. Finalizando.")
                    break

                if self._running:
                    time.sleep(interval)

        except KeyboardInterrupt:
            print("\n\n⏹️  Guardian detenido por el usuario.")

        finally:
            self._running = False

    def stop(self) -> None:
        """Detiene el Guardian."""
        self._running = False

    def get_status(self) -> Dict[str, Any]:
        """
        Obtiene el estado actual del Guardian.

        Returns:
            Estado del Guardian
        """
        return {
            "running": self._running,
            "cycles": self._cycle_count,
            "f0_hz": self.F0_HZ,
            "coherence": self.COHERENCE_CONSTANT,
            "repo_root": str(self.repo_root),
            "log_path": self.log_path,
        }

    def quick_check(self) -> Dict[str, Any]:
        """
        Realiza una verificación rápida del sistema.

        Returns:
            Resultado de la verificación rápida
        """
        state = self.watcher.scan_repo()
        coherence = self.spectral.check_spectral_coherence()
        signal = self.noesis_signal()

        return {
            "timestamp": datetime.now().isoformat(),
            "healthy": (
                state.get("collisions", 0) == 0
                and state.get("missing", 0) == 0
                and coherence.get("coherent", False)
            ),
            "state_summary": {
                "collisions": state.get("collisions", 0),
                "missing": state.get("missing", 0),
                "lean_status": state.get("lean_status"),
            },
            "coherent": coherence.get("coherent", False),
            "signal_state": signal.get("state"),
            "vitality": signal.get("vitality"),
        }


def main():
    """Punto de entrada principal del Guardian."""
    import argparse

    parser = argparse.ArgumentParser(
        description="NOESIS Guardian 2.0 - Sistema de monitoreo y autorreparación QCAL",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Ejemplos:
  python -m noesis_guardian.guardian_core                    # Ejecutar continuo
  python -m noesis_guardian.guardian_core --interval 600     # Cada 10 minutos
  python -m noesis_guardian.guardian_core --cycles 1         # Un solo ciclo
  python -m noesis_guardian.guardian_core --quick            # Verificación rápida
        """,
    )

    parser.add_argument(
        "--interval",
        type=int,
        default=1800,
        help="Intervalo entre ciclos en segundos (default: 1800)",
    )
    parser.add_argument(
        "--cycles",
        type=int,
        default=None,
        help="Número máximo de ciclos (default: infinito)",
    )
    parser.add_argument(
        "--quick",
        action="store_true",
        help="Ejecutar verificación rápida y salir",
    )

    args = parser.parse_args()

    guardian = NoesisGuardian()

    if args.quick:
        print("=" * 60)
        print("NOESIS GUARDIAN 2.0 — Verificación Rápida")
        print("=" * 60)

        result = guardian.quick_check()

        print("\n📊 Estado del Sistema:")
        print(f"   Timestamp: {result['timestamp']}")
        print(f"   Saludable: {'✅' if result['healthy'] else '❌'}")
        print(f"   Coherente: {'✅' if result['coherent'] else '❌'}")
        print(f"   Estado: {result['signal_state']}")
        print(f"   Vitalidad: {result['vitality']:.2%}")

        print("\n📋 Detalles:")
        summary = result["state_summary"]
        print(f"   Colisiones: {summary['collisions']}")
        print(f"   Faltantes: {summary['missing']}")
        print(f"   Lean: {summary['lean_status']}")

        return 0 if result["healthy"] else 1

    guardian.run(interval=args.interval, max_cycles=args.cycles)
    return 0


if __name__ == "__main__":
    exit(main())
Guardian Core - Central Orchestration for Noesis Guardian
----------------------------------------------------------

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
    guardian.run_cycle()
    guardian.run()
