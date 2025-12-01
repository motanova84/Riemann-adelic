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
from .guardian_core import GuardianCore, Notifier

__all__ = ["SchattenPaley", "GuardianCore", "Notifier"]
__version__ = "1.0.0"
