"""
Noesis Guardian 3.0 - Modules Package

Coherency hooks and validation modules for the Guardian system.

This package contains all the component modules for the Guardian system:
- watcher: Repository structure monitoring
- autorepair_engine: Automatic repair of missing structures  
- spectral_monitor: Mathematical coherence validation
- ai_notifier: Alert system
- sabio_bridge: SABIO system integration
- aik_sync: AIK beacon synchronization
- coherency_hooks: Coherency validation hooks
"""

from .coherency_hooks import CoherencyHooks
from .watcher import RepoWatcher
from .autorepair_engine import AutoRepairEngine
from .spectral_monitor import SpectralMonitor
from .ai_notifier import Notifier
from .sabio_bridge import SabioBridge
from .aik_sync import AikSync

__all__ = [
    "CoherencyHooks",
    "RepoWatcher",
    "AutoRepairEngine",
    "SpectralMonitor",
    "Notifier",
    "SabioBridge",
    "AikSync",
]
