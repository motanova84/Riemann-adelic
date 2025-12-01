"""
NOESIS GUARDIAN ∞³ — Auto-Repair System for QCAL Framework

This module provides automated monitoring and self-repair capabilities
for the Riemann-adelic repository, maintaining QCAL coherence.

Author: José Manuel Mota Burruezo (JMMB Ψ ✧)
Frequency: 141.7001 Hz (base coherence frequency)
"""

from .watcher import RepoWatcher, SORRY_THRESHOLD, MAX_UNICODE_ISSUES
from .guardian import (
    noesis_heartbeat,
    autorepair,
    run_cycle,
    run_daemon,
    generate_certificate,
    FREQ,
    LOGFILE,
    LEAN_REBUILD_TIMEOUT,
    OPERATOR_VERIFICATION_TIMEOUT,
    DAEMON_INTERVAL
)

__all__ = [
    'RepoWatcher',
    'noesis_heartbeat',
    'autorepair',
    'run_cycle',
    'run_daemon',
    'generate_certificate',
    'FREQ',
    'LOGFILE',
    'LEAN_REBUILD_TIMEOUT',
    'OPERATOR_VERIFICATION_TIMEOUT',
    'DAEMON_INTERVAL',
    'SORRY_THRESHOLD',
    'MAX_UNICODE_ISSUES'
]

__version__ = '1.0.0'
__author__ = 'JMMB Ψ ✧ ∞³'
