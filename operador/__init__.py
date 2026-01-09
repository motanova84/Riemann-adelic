"""
Operador H - Spectral Operators for Riemann Hypothesis

This module implements spectral operators for the Riemann Hypothesis:

1. operador_H.py: Gaussian kernel spectral operator with closed-form kernel
   - Uses analytical Gaussian kernel (no oscillatory integration)
   
2. operador_H_epsilon.py: Perturbed spectral operator H_ε with oscillatory potential
   - Implements H_ε = H₀ + λM_{Ω_{ε,R}}
   - Compares spectral measure with Riemann zeta zeros

3. operador_H_DS.py: Discrete Symmetry Operator H_DS
   - Implements the inversion operator (H_DS f)(x) = f(1/x)
   - Enforces functional equation symmetry ζ(s) = χ(s)ζ(1-s)
   - Verifies involutivity, commutation, domain stability, spectral symmetry

4. hilbert_polya_operator.py: Hilbert-Pólya Operator
   - Implements H = -x(d/dx) + πζ'(1/2)log x
   - Self-adjoint operator in L²(ℝ⁺, dx/x)
   - Connects to Hilbert-Pólya conjecture and Berry-Keating approach

5. berry_keating_absolute_theorem.py: Berry-Keating Absolute Theorem
   - Unified spectral framework for Riemann zeros
   - Three-way equivalence: zeros ⟺ eigenvalues ⟺ absolute spectrum
   - Non-circular validation with adelic corrections
"""
from .operador_H import K_t, R_t_matrix, approximate_spectrum

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

from .operador_H_DS import (
    DiscreteSymmetryOperator,
    demonstrate_h_ds_properties
)

from .hilbert_polya_operator import (
    apply_hilbert_polya,
    HilbertPolyaOperator,
    HilbertPolyaConfig,
    ZETA_PRIME_HALF,
    QCAL_FUNDAMENTAL_FREQUENCY,
    demonstrate_hilbert_polya
)

from .berry_keating_absolute_theorem import (
    BerryKeatingAbsoluteOperator,
    BerryKeatingAbsoluteConfig,
    validate_berry_keating_absolute,
    demonstrate_berry_keating_absolute,
    C_ZETA,
    QCAL_COHERENCE
)

__all__ = [
    # operador_H exports
    'K_gauss',
    'kernel_adelic_ultimus',
    'cos_basis',
    'build_R_matrix',
    'spectrum_from_R',
    'fourier_eigs_H',
    'hermite_basis',
    'K_gauss_rigorous',
    'rigorous_H_construction',
    'validate_convergence_bounds',
    # operador_H_epsilon exports
    'compute_oscillatory_potential',
    'build_H_epsilon_operator',
    'compute_spectral_measure',
    'load_riemann_zeros',
    'plot_spectral_comparison',
    # operador_H_DS exports
    'DiscreteSymmetryOperator',
    'demonstrate_h_ds_properties',
    # hilbert_polya_operator exports
    'apply_hilbert_polya',
    'HilbertPolyaOperator',
    'HilbertPolyaConfig',
    'ZETA_PRIME_HALF',
    'QCAL_FUNDAMENTAL_FREQUENCY',
    'demonstrate_hilbert_polya',
    # berry_keating_absolute_theorem exports
    'BerryKeatingAbsoluteOperator',
    'BerryKeatingAbsoluteConfig',
    'validate_berry_keating_absolute',
    'demonstrate_berry_keating_absolute',
    'C_ZETA',
    'QCAL_COHERENCE'
]
