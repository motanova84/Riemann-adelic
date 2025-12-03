"""
Operators module for QCAL Riemann Hypothesis proof.

This module contains Hermitian operators that encode Riemann zeros
in their spectrum via constructive spectral theory.

Modules:
    - riemann_operator: H_Ψ Hermitian operator with spectrum reproducing
                        Riemann zeros to ultra-high precision
    - discrete_symmetry_operator: H_DS operator that validates space structure
                                 and enforces discrete symmetry G ≅ Z
    - operator_connection: Connection between H_Ψ and H_DS that demonstrates
                          how discrete symmetry forces zero reality
    - noetic_operator: H_ψ = -Δ + V_ψ noetic operator with p-adic corrections
                       implementing the spectral hierarchy:
                       Level 1: λ₀ ≈ 0.001588 → C = 1/λ₀ ≈ 629.83 (structure)
                       Level 2: C_QCAL = ⟨λ⟩²/λ₀ ≈ 244.36 (coherence)
                       Fusion: f₀ = 141.7001 Hz (harmonization)
                       implementing λ₀ ≈ 0.001588 and C = 1/λ₀ ≈ 629.83
    - spectral_constants: Dual spectral constant system implementing
                         C_PRIMARY = 629.83 (structure) and
                         C_COHERENCE = 244.36 (coherence) with
                         f₀ = 141.7001 Hz as natural manifestation
"""

from .riemann_operator import (
    construct_H_psi,
    compute_spectrum,
    validate_spectrum,
    load_riemann_zeros,
    oscillatory_weight,
    wave_equation_rhs,
    F0,
    OMEGA_0,
    ZETA_PRIME_HALF,
    C_QCAL
)

from .discrete_symmetry_operator import DiscreteSymmetryOperator

from .operator_connection import OperatorConnection

from .noetic_operator import (
    # Operator construction
    build_noetic_operator,
    build_discrete_laplacian,
    build_padic_potential,
    # Eigenvalue computation
    compute_first_eigenvalue,
    compute_C_from_lambda,
    # Spectral hierarchy (new)
    compute_spectral_mean,
    compute_C_coherence,
    compute_f0_from_hierarchy,
    validate_spectral_hierarchy,
    # Validation functions
    validate_lambda_C_relationship,
    analyze_f0_C_relationship,
    validate_operator_self_adjoint,
    run_complete_noetic_validation,
    # Constants - spectral hierarchy
    F0_TARGET,
    C_PRIMARY,
    C_COHERENCE,
    C_TARGET,
    LAMBDA_0_TARGET,
    EULER_MASCHERONI,
    PHI,
    DELTA_FRACTAL,
    O4_REFINEMENT
)

from .spectral_constants import (
    # Constants
    C_PRIMARY,
    C_COHERENCE,
    F0_BASE,
    LAMBDA_0,
    LAMBDA_MEAN_EFFECTIVE,
    PHI,
    EULER_GAMMA,
    # Functions
    compute_C_primary_from_lambda,
    compute_C_coherence_from_spectrum,
    compute_lambda_mean_from_coherence,
    analyze_constant_relationship,
    validate_f0_manifestation,
    build_spectral_H_operator,
    compute_spectral_constants_from_operator,
    validate_dual_constants,
    run_complete_spectral_validation,
)

__all__ = [
    'construct_H_psi',
    'compute_spectrum',
    'validate_spectrum',
    'load_riemann_zeros',
    'oscillatory_weight',
    'wave_equation_rhs',
    'F0',
    'OMEGA_0',
    'ZETA_PRIME_HALF',
    'C_QCAL',
    'DiscreteSymmetryOperator',
    'OperatorConnection',
    # Noetic operator exports
    'build_noetic_operator',
    'build_discrete_laplacian',
    'build_padic_potential',
    'compute_first_eigenvalue',
    'compute_C_from_lambda',
    # Spectral hierarchy (new)
    'compute_spectral_mean',
    'compute_C_coherence',
    'compute_f0_from_hierarchy',
    'validate_spectral_hierarchy',
    # Validation
    'validate_lambda_C_relationship',
    'analyze_f0_C_relationship',
    'validate_operator_self_adjoint',
    'run_complete_noetic_validation',
    # Constants - spectral hierarchy
    'F0_TARGET',
    'C_PRIMARY',
    'C_COHERENCE',
    'C_TARGET',
    'LAMBDA_0_TARGET',
    'EULER_MASCHERONI',
    'PHI',
    'DELTA_FRACTAL',
    'O4_REFINEMENT'
    # Spectral constants exports
    'C_PRIMARY',
    'C_COHERENCE',
    'F0_BASE',
    'LAMBDA_0',
    'LAMBDA_MEAN_EFFECTIVE',
    'PHI',
    'EULER_GAMMA',
    'compute_C_primary_from_lambda',
    'compute_C_coherence_from_spectrum',
    'compute_lambda_mean_from_coherence',
    'analyze_constant_relationship',
    'validate_f0_manifestation',
    'build_spectral_H_operator',
    'compute_spectral_constants_from_operator',
    'validate_dual_constants',
    'run_complete_spectral_validation',
]
