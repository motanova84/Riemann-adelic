#!/usr/bin/env python3
"""
NOESIS GUARDIAN 3.0

Guardian system for QCAL ∞³ coherence validation.
Executes key validators from the Riemann-adelic repository.

Author: José Manuel Mota Burruezo (JMMB Ψ ✧)
System: QCAL–SABIO ∞³
"""

from .guardian_core import NoesisGuardian
from .modules.coherency_hooks import CoherencyHooks

__all__ = ["NoesisGuardian", "CoherencyHooks"]
__version__ = "3.0.0"
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
