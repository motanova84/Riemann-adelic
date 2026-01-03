"""
NOESIS GUARDIAN 3.0 - Main Package

Sistema tecnico de validacion, analisis y autoreparacion del repositorio.
Un sistema profesional real que vigila el repositorio, repara archivos basicos,
calcula coherencia matematica tecnica, genera hashes, produce logs y emite diagnosticos.

Author: Jose Manuel Mota Burruezo (JMMB)
System: QCAL-SABIO

Features:
- Inspirado en el lenguaje simbolico QCAL
- Construido 100% sobre computacion real, segura y tecnica
- Compatible con Python, CI/CD, Lean, GitHub Actions
"""

from .guardian_core import NoesisGuardian
from .modules.coherency_hooks import CoherencyHooks
from .watcher import RepoWatcher, SORRY_THRESHOLD, MAX_UNICODE_ISSUES
from .guardian import (
    noesis_heartbeat,
    autorepair,
    run_cycle,
    FREQ,
    LOGFILE,
    LEAN_REBUILD_TIMEOUT,
    OPERATOR_VERIFICATION_TIMEOUT,
    DAEMON_INTERVAL
)

__all__ = [
    "NoesisGuardian",
    "CoherencyHooks",
    "RepoWatcher",
    "noesis_heartbeat",
    "autorepair",
    "run_cycle",
    "FREQ",
    "LOGFILE",
    "LEAN_REBUILD_TIMEOUT",
    "OPERATOR_VERIFICATION_TIMEOUT",
    "DAEMON_INTERVAL",
    "SORRY_THRESHOLD",
    "MAX_UNICODE_ISSUES",
]
__version__ = "3.0.0"
__author__ = 'JMMB'
