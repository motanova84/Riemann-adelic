"""
Five Pillars of the Riemann Hypothesis Proof

This package implements the five fundamental pillars of the spectral
proof of the Riemann Hypothesis using adelic and Wu-Sprung methods.

Pillars:
1. Spectral Inversion: Reconstructs log p^k from zeros rho
2. Poisson-Radon Duality: Geometrizes functional equation s <-> 1-s
3. Paley-Wiener Uniqueness: Characterizes Xi(s) uniquely
4. RH Operator Construction: Builds H from geometric principles
5. Wu-Sprung Spectral Framework: Five pillars of Wu-Sprung/H = -d^2/dx^2 + V_WS
"""

from .pilar1_spectral_inversion import spectral_inversion, reconstruction_kernel
from .pilar2_poisson_radon import poisson_radon_duality, self_dual_lagrangian
from .pilar3_uniqueness import verify_uniqueness, weil_pairing
from .pilar4_rh_operator import build_rh_operator, thermal_kernel
from .pilar5_spectral_wu_sprung import (
    pilar1_convergence_analysis,
    pilar2_uniqueness_check,
    pilar3_continuous_spectrum_control,
    pilar4_no_extra_eigenvalues,
    pilar5_v_construction_without_functional_equation,
    verify_five_pillars,
)

__all__ = [
    'spectral_inversion',
    'reconstruction_kernel',
    'poisson_radon_duality',
    'self_dual_lagrangian',
    'verify_uniqueness',
    'weil_pairing',
    'build_rh_operator',
    'thermal_kernel',
    'pilar1_convergence_analysis',
    'pilar2_uniqueness_check',
    'pilar3_continuous_spectrum_control',
    'pilar4_no_extra_eigenvalues',
    'pilar5_v_construction_without_functional_equation',
    'verify_five_pillars',
]

__version__ = '2.0.0'
