"""
echo_qcal - Módulo de verificación del Teorema de Coherencia Soberana (ℂₛ)

Este módulo implementa las verificaciones de las tres capas del teorema:
- Cₖ: Capa Criptográfica (control de la llave de Génesis)
- Aₜ: Capa Cosmológica (alineación temporal con f₀ = 141.7001 Hz)
- Aᵤ: Capa Semántica (implementación en código)

Teorema ℂₛ: ℂₛ = Cₖ ∧ Aₜ ∧ Aᵤ

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
"""

from .A_t_verification import TemporalAlignmentVerifier

__all__ = ['TemporalAlignmentVerifier']
__version__ = '1.0.0'
