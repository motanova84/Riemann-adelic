"""
Spectral inversion module for reconstructing primes from zeros.

This module provides tools for:
    - K_D: Kernel construction from zeta zeros
    - prime_measure_from_zeros: Prime measure reconstruction
    - kernel_glm: GLM (Gel'fand-Levitan-Marchenko) kernel for inverse scattering
    - marchenko_solve: Solve the Marchenko equation
    - reconstruct_potential: Reconstruct V(x) from K(x,x)
    - full_reconstruction: Complete pipeline ζ → γₙ → V(x)
"""
from .inversion_spectral import K_D, prime_measure_from_zeros
from .kernel_glm import (
    F_glm_kernel,
    construct_F_matrix,
    marchenko_solve,
    reconstruct_potential,
    validate_reconstruction,
    full_reconstruction,
    get_riemann_zeros,
    plot_reconstruction,
    kernel_glm,
    solve_marchenko,
)

__all__ = [
    'K_D',
    'prime_measure_from_zeros',
    'F_glm_kernel',
    'construct_F_matrix',
    'marchenko_solve',
    'reconstruct_potential',
    'validate_reconstruction',
    'full_reconstruction',
    'get_riemann_zeros',
    'plot_reconstruction',
    'kernel_glm',
    'solve_marchenko',
]
