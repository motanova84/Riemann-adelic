#!/usr/bin/env python3
"""
NOESIS GUARDIAN 3.0
==================

Guardian system for QCAL ∞³ coherence validation.
Executes key validators from the Riemann-adelic repository.

Author: José Manuel Mota Burruezo (JMMB Ψ ✧)
System: QCAL–SABIO ∞³
"""

from .guardian_core import NoesisGuardian
from .modules.coherency_hooks import CoherencyHooks

__all__ = ["NoesisGuardian", "CoherencyHooks"]
__version__ = "3.0.0"
