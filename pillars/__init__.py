"""
Four Pillars of the Riemann Hypothesis Proof

This package implements the four fundamental pillars of the non-circular
proof of the Riemann Hypothesis using adelic spectral methods.

Pillars:
1. Spectral Inversion: Reconstructs log p^k from zeros ρ
2. Poisson-Radón Duality: Geometrizes functional equation s ↔ 1-s
3. Paley-Wiener Uniqueness: Characterizes Ξ(s) uniquely
4. RH Operator Construction: Builds H from geometric principles
"""

from .pilar1_spectral_inversion import spectral_inversion, reconstruction_kernel
from .pilar2_poisson_radon import poisson_radon_duality, self_dual_lagrangian
from .pilar3_uniqueness import verify_uniqueness, weil_pairing
from .pilar4_rh_operator import build_rh_operator, thermal_kernel

__all__ = [
    'spectral_inversion',
    'reconstruction_kernel',
    'poisson_radon_duality',
    'self_dual_lagrangian',
    'verify_uniqueness',
    'weil_pairing',
    'build_rh_operator',
    'thermal_kernel'
]

__version__ = '1.0.0'
