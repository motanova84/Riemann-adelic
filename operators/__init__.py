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
                       implementing λ₀ ≈ 0.001588 and C = 1/λ₀ ≈ 629.83
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
    build_noetic_operator,
    build_discrete_laplacian,
    build_padic_potential,
    compute_first_eigenvalue,
    compute_C_from_lambda,
    validate_lambda_C_relationship,
    analyze_f0_C_relationship,
    validate_operator_self_adjoint,
    run_complete_noetic_validation,
    F0_TARGET,
    C_TARGET,
    LAMBDA_0_TARGET
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
    'validate_lambda_C_relationship',
    'analyze_f0_C_relationship',
    'validate_operator_self_adjoint',
    'run_complete_noetic_validation',
    'F0_TARGET',
    'C_TARGET',
    'LAMBDA_0_TARGET'
]
