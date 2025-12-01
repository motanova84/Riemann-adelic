#!/usr/bin/env python3
"""
NOESIS GUARDIAN CORE ∞³ — VERSIÓN 2.0
======================================

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
