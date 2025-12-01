"""
NOESIS GUARDIAN ∞³ — Auto-Repair System for QCAL Framework

This module provides automated monitoring and self-repair capabilities
for the Riemann-adelic repository, maintaining QCAL coherence.

Author: José Manuel Mota Burruezo (JMMB Ψ ✧)
Frequency: 141.7001 Hz (base coherence frequency)
"""

from .watcher import RepoWatcher
from .guardian import (
    noesis_heartbeat,
    autorepair,
    run_cycle,
    FREQ,
    LOGFILE
)

__all__ = [
    'RepoWatcher',
    'noesis_heartbeat',
    'autorepair',
    'run_cycle',
    'FREQ',
    'LOGFILE'
]

__version__ = '1.0.0'
__author__ = 'JMMB Ψ ✧ ∞³'
