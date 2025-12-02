#!/usr/bin/env python3
"""
Noesis Guardian Modules
-----------------------

Collection of monitoring hooks for spectral operator analysis.

Available hooks:
- hook_schatten_paley: Monitors Schatten-Paley functional invariants
"""

from .hook_schatten_paley import SchattenPaley

__all__ = ["SchattenPaley"]
