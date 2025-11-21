"""
Operador H - Spectral Operators for Riemann Hypothesis

This module implements spectral operators for the Riemann Hypothesis:

1. operador_H.py: Gaussian kernel spectral operator with closed-form kernel
   - Uses analytical Gaussian kernel (no oscillatory integration)
   
2. operador_H_epsilon.py: Perturbed spectral operator H_ε with oscillatory potential
   - Implements H_ε = H₀ + λM_{Ω_{ε,R}}
   - Compares spectral measure with Riemann zeta zeros
"""

from .operador_H import (
    K_gauss,
    kernel_adelic_ultimus,
    cos_basis,
    build_R_matrix,
    spectrum_from_R,
    fourier_eigs_H,
    hermite_basis,
    K_gauss_rigorous,
    rigorous_H_construction,
    validate_convergence_bounds
)

from .operador_H_epsilon import (
    compute_oscillatory_potential,
    build_H_epsilon_operator,
    compute_spectral_measure,
    load_riemann_zeros,
    plot_spectral_comparison
)

__all__ = [
    # operador_H exports
    'K_gauss',
    'kernel_adelic_ultimus',
    'cos_basis',
    'build_R_matrix',
    'spectrum_from_R',
    'fourier_eigs_H',
    # operador_H_epsilon exports
    'compute_oscillatory_potential',
    'build_H_epsilon_operator',
    'compute_spectral_measure',
    'load_riemann_zeros',
    'plot_spectral_comparison'
    'hermite_basis',
    'K_gauss_rigorous',
    'rigorous_H_construction',
    'validate_convergence_bounds'
]
