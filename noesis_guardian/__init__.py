"""
NOESIS GUARDIAN 3.0 - Main Package

Sistema tecnico de validacion, analisis y autoreparacion del repositorio.
Un sistema profesional real que vigila el repositorio, repara archivos basicos,
calcula coherencia matematica tecnica, genera hashes, produce logs y emite diagnosticos.

Author: Jose Manuel Mota Burruezo (JMMB)
System: QCAL-SABIO

Features:
- Inspirado en el lenguaje simbolico QCAL
- Construido 100% sobre computacion real, segura y tecnica
- Compatible con Python, CI/CD, Lean, GitHub Actions
"""

from .guardian_core import NoesisGuardian
from .modules.coherency_hooks import CoherencyHooks

__all__ = ["NoesisGuardian", "CoherencyHooks"]
__version__ = "3.0.0"
__author__ = 'JMMB'
