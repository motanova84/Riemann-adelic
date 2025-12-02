"""
Noesis Guardian Modules

This package contains the individual monitoring hooks for the QCAL system.
"""

from .hook_calabi_yau_resonance import CalabiYauResonance

__all__ = ['CalabiYauResonance']
#!/usr/bin/env python3
"""
Noesis Guardian 3.0 - Modules package
"""
NOESIS GUARDIAN 3.0 — Modules Package
NOESIS GUARDIAN 3.0 — Modules

Coherency hooks and validation modules for the Guardian system.
"""

from .coherency_hooks import CoherencyHooks

__all__ = ["CoherencyHooks"]
Noesis Guardian Modules
-----------------------

This package contains all the component modules for the Guardian system:
- watcher: Repository structure monitoring
- autorepair_engine: Automatic repair of missing structures
- spectral_monitor: Mathematical coherence validation
- ai_notifier: Alert system
- sabio_bridge: SABIO system integration
- aik_sync: AIK beacon synchronization
"""

from noesis_guardian.modules.watcher import RepoWatcher
from noesis_guardian.modules.autorepair_engine import AutoRepairEngine
from noesis_guardian.modules.spectral_monitor import SpectralMonitor
from noesis_guardian.modules.ai_notifier import Notifier
from noesis_guardian.modules.sabio_bridge import SabioBridge
from noesis_guardian.modules.aik_sync import AikSync

__all__ = [
    "RepoWatcher",
    "AutoRepairEngine",
    "SpectralMonitor",
    "Notifier",
    "SabioBridge",
    "AikSync",
]
