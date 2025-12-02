"""
NOESIS GUARDIAN ∞³ — Version 2.0

Sistema autorreparador profundo con monitoreo espectral y sincronización QCAL.

Modules:
    - guardian_core: Coordinador principal con latido 141.7001 Hz
    - watcher: Inspección del repositorio
    - autorepair_engine: Motor de reparación profunda
    - spectral_monitor: Monitoreo de coherencia espectral ζ
    - ai_notifier: Sistema de notificaciones
    - sabio_bridge: Conexión con SABIO INFINITY
    - aik_sync: Sincronización con AIK-Beacons

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
License: Creative Commons BY-NC-SA 4.0
"""

from .guardian_core import NoesisGuardian
from .watcher import RepoWatcher
from .autorepair_engine import AutoRepairEngine
from .spectral_monitor import SpectralMonitor
from .ai_notifier import Notifier
from .sabio_bridge import SabioBridge
from .aik_sync import AikSync

__version__ = "2.0.0"
__all__ = [
    "NoesisGuardian",
    "RepoWatcher",
    "AutoRepairEngine",
    "SpectralMonitor",
    "Notifier",
    "SabioBridge",
    "AikSync",
]
#!/usr/bin/env python3
"""
Noesis Guardian - Spectral Operator Monitoring System
------------------------------------------------------

This module provides monitoring hooks for the QCAL framework's
spectral operator analysis, ensuring mathematical invariants
are preserved across all operations.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
"""

from .modules.hook_schatten_paley import SchattenPaley
from .guardian_core import GuardianCore, Notifier, Status

__all__ = ["SchattenPaley", "GuardianCore", "Notifier", "Status"]
__version__ = "1.0.0"
