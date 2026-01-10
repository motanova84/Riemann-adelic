"""
QCAL Core Module - Axiomatic Constants and Functions
=====================================================

∴ D ≡ Ξ ∴ RH es verdadera ∴ El camino ya era completo antes de que yo caminara ∴

This module contains the core axiomatic constants and functions for the QCAL ∞³ framework.
The constants here are not observed but deduced by the global rigidity of the adelic flow
(Theorem 2.5, V4.1).

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Version: V4.1 - RAM-IX AXIOMÁTICA VIVA
Date: 2026-01-10
DOI: 10.5281/zenodo.17379721
SafeCreative: 2509143065474
"""

from .constants import (
    F0_ORIGEN,
    F0_AXIOMATIC,
    KAPPA_PI_RIGID,
    RH_EMERGENT,
    C_PRIMARY,
    C_COHERENCE,
    PSI_EQUATION,
    verify_axiomatic_coherence,
    get_axiomatic_status,
)

from .manifest import (
    manifest_intent,
    manifest_intent_real,
    get_manifestation_info,
)

from .daemon import (
    heartbeat,
    DIAHYGRHMGDaemon,
    DIAHYGRHMGSeal,
    DAEMON_CYCLE_SECONDS,
)

__all__ = [
    # Constants
    'F0_ORIGEN',
    'F0_AXIOMATIC',
    'KAPPA_PI_RIGID',
    'RH_EMERGENT',
    'C_PRIMARY',
    'C_COHERENCE',
    'PSI_EQUATION',
    # Constants functions
    'verify_axiomatic_coherence',
    'get_axiomatic_status',
    # Manifest functions
    'manifest_intent',
    'manifest_intent_real',
    'get_manifestation_info',
    # Daemon
    'heartbeat',
    'DIAHYGRHMGDaemon',
    'DIAHYGRHMGSeal',
    'DAEMON_CYCLE_SECONDS',
]

__version__ = '4.1.0'
__author__ = 'José Manuel Mota Burruezo Ψ ✧ ∞³'
