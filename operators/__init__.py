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
    - spectral_constants: Dual spectral constants framework unifying
                         C_PRIMARY = 629.83 (structure) and 
                         C_COHERENCE = 244.36 (form) to derive f₀ = 141.7001 Hz
    - dirac_spectral_operator: 𝔻_s = i d/ds Dirac spectral operator acting on
                               complex s-plane, dual to H_Ψ
    - hermetic_trace_operator: T_∞³ = √(1 + D_s²) Hermetic Noetic operator
                              implementing PHASE VI - Noetic Spectral Identity:
                              ζ(s) = Tr(T_∞³^(-s))
                              Hermetic Trace Formula (Gutzwiller-type):
                              Tr(e^(-t·T_∞³)) ∼ Σ_p A_p(t) cos(γ_p·t + φ_p)
    - master_operator_o3: 𝒪_∞³ = 𝔻_s ⊗ 𝟙 + 𝟙 ⊗ H_Ψ master operator unifying
                         complex and real perspectives
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
    C_QCAL,
    LAMBDA_0,
    C_UNIVERSAL
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
    # Fundamental constants
    C_PRIMARY,
    C_COHERENCE,
    LAMBDA_0,
    F0 as F0_SPECTRAL,
    OMEGA_0 as OMEGA_0_SPECTRAL,
    PHI,
    EULER_GAMMA,
    COHERENCE_FACTOR,
    # Classes
    SpectralLevel,
    # Functions
    compute_primary_constant,
    compute_coherence_constant,
    compute_coherence_factor,
    derive_f0_from_constants,
    verify_f0_coherence,
    validate_dual_constants
)

from .spectral_coordinates import (
    # Constants
    F0 as F0_COORDINATES,
    GAMMA_1,
    TAU_IMAGINARY_CONSTANT,
    # Functions
    compute_tau,
    compute_tau_real,
    compute_tau_imaginary,
    compute_tau_batch,
    compute_tau_dictionary,
    verify_monotonicity,
    verify_constant_imaginary,
    get_standard_examples,
    analyze_spectral_coordinates,
    validate_spectral_coordinates
)

from .horizon_detector import (
    HorizonDetector,
    detect_horizons_from_operator,
    validate_horizon_riemann_correspondence
)
from .dirac_spectral_operator import DiracSpectralOperator

from .hermetic_trace_operator import (
    # Operator construction
    build_dirac_spectral_operator,
    build_hermetic_noetic_operator,
    # Trace computations
    compute_trace_zeta_regularized,
    compute_hermetic_trace_formula,
    # Verification and demonstration
    verify_spectral_identity,
    demonstrate_hermetic_trace_identity,
    # Constants
    F0_QCAL
)

from .master_operator_o3 import MasterOperatorO3

from .t_infinity_cubed import TInfinityCubedOperator

from .atlas3_kato_rellich import (
    RelativeBoundednessTest,
    verify_atlas3_kato_rellich,
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
    'LAMBDA_0',
    'C_UNIVERSAL',
    'DiscreteSymmetryOperator',
    'OperatorConnection',
    # Noetic operator exports
    'build_noetic_operator',
    'build_discrete_laplacian',
    'build_padic_potential',
    'compute_first_eigenvalue',
    'compute_C_from_lambda',
    # Spectral hierarchy
    'compute_spectral_mean',
    'compute_C_coherence',
    'compute_f0_from_hierarchy',
    'validate_spectral_hierarchy',
    # Validation
    'validate_lambda_C_relationship',
    'analyze_f0_C_relationship',
    'validate_operator_self_adjoint',
    'run_complete_noetic_validation',
    # Constants from noetic_operator
    'F0_TARGET',
    'C_TARGET',
    'LAMBDA_0_TARGET',
    'EULER_MASCHERONI',
    'DELTA_FRACTAL',
    'O4_REFINEMENT',
    # Spectral constants exports
    'C_PRIMARY',
    'C_COHERENCE',
    'F0_SPECTRAL',
    'OMEGA_0_SPECTRAL',
    'PHI',
    'EULER_GAMMA',
    'COHERENCE_FACTOR',
    'SpectralLevel',
    'compute_primary_constant',
    'compute_coherence_constant',
    'compute_coherence_factor',
    'derive_f0_from_constants',
    'verify_f0_coherence',
    'validate_dual_constants',
    # Horizon detector exports
    'HorizonDetector',
    'detect_horizons_from_operator',
    'validate_horizon_riemann_correspondence',
    # Operator duality exports
    'DiracSpectralOperator',
    # Hermetic trace operator exports (PHASE VI)
    'build_dirac_spectral_operator',
    'build_hermetic_noetic_operator',
    'compute_trace_zeta_regularized',
    'compute_hermetic_trace_formula',
    'verify_spectral_identity',
    'demonstrate_hermetic_trace_identity',
    'F0_QCAL',
    # Master operator
    'MasterOperatorO3',
    'TInfinityCubedOperator',
    # Spectral coordinates exports
    'F0_COORDINATES',
    'GAMMA_1',
    'TAU_IMAGINARY_CONSTANT',
    'compute_tau',
    'compute_tau_real',
    'compute_tau_imaginary',
    'compute_tau_batch',
    'compute_tau_dictionary',
    'verify_monotonicity',
    'verify_constant_imaginary',
    'get_standard_examples',
    'analyze_spectral_coordinates',
    'validate_spectral_coordinates',
    # ATLAS³ Kato-Rellich exports
    'RelativeBoundednessTest',
    'verify_atlas3_kato_rellich',
]
