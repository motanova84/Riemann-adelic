#!/usr/bin/env python3
"""
NOESIS GUARDIAN 3.0 — Modules

Coherency hooks and validation modules for the Guardian system.
"""

from .coherency_hooks import CoherencyHooks

__all__ = ["CoherencyHooks"]
Noesis Guardian Modules
-----------------------

Collection of monitoring hooks for spectral operator analysis.

Available hooks:
- hook_schatten_paley: Monitors Schatten-Paley functional invariants
"""

from .hook_schatten_paley import SchattenPaley

__all__ = ["SchattenPaley"]
