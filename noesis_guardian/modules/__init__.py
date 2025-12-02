"""
Noesis Guardian Modules

This package contains the individual monitoring hooks for the QCAL system.
"""

from .hook_calabi_yau_resonance import CalabiYauResonance

__all__ = ['CalabiYauResonance']
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
