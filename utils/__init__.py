"""
Utilities module for Riemann Hypothesis validation and adelic analysis.

This package contains various utility functions and classes for:
- Critical line verification
- Adelic determinant calculations  
- Data fetching and validation
- Performance monitoring
- Mathematical tools for Riemann zeta function analysis
- Arithmetic fractal validation (SABIO ∞³ framework)
- Spectral graph analysis for expander graphs

The utilities support the numerical validation of the paper:
"A Complete Proof of the Riemann Hypothesis via S-Finite Adelic Systems (V5.1)"
by José Manuel Mota Burruezo.
"""

from .adelic_determinant import AdelicCanonicalDeterminant
from .arithmetic_fractal_validation import (
    ArithmeticFractalValidator,
    ArithmeticFractalResult,
    validate_arithmetic_fractal,
)
from .critical_line_checker import CriticalLineChecker
from .dilation_operator import (
    PrimePotentialConfig,
    build_dilation_operator,
    build_prime_potential,
)
from .performance_monitor import PerformanceMonitor, PerformanceMetrics
from .spectral_graph_analysis import (
    SpectralGraphResult,
    construct_g4_adjacency,
    construct_mini_ramanujan_g4,
    compute_spectral_analysis,
    analyze_g4_graph,
    analyze_mini_ramanujan_g4,
    validate_g4_properties,
)
from .weak_solution_existence import (
    WeakSolutionExistence,
    validate_weak_solution_theorem,
)
from .spectral_origin_constant import (
    LAMBDA_0,
    C_UNIVERSAL,
    F0_SPECTRAL,
    F0_QCAL,
    OMEGA_0_SPECTRAL,
    NoeticOperator,
    SpectralOriginResult,
    derive_universal_constant,
    validate_spectral_frequency_relation,
    verify_all_appearances_of_f0,
    mathematical_significance,
    run_complete_demonstration,
)

__all__ = [
    'AdelicCanonicalDeterminant',
    'ArithmeticFractalValidator',
    'ArithmeticFractalResult',
    'validate_arithmetic_fractal',
    'CriticalLineChecker',
    'PrimePotentialConfig',
    'build_dilation_operator',
    'build_prime_potential',
    'PerformanceMonitor',
    'PerformanceMetrics',
    # Spectral graph analysis
    'SpectralGraphResult',
    'construct_g4_adjacency',
    'construct_mini_ramanujan_g4',
    'compute_spectral_analysis',
    'analyze_g4_graph',
    'analyze_mini_ramanujan_g4',
    'validate_g4_properties',
    # Weak solution existence theorem
    'WeakSolutionExistence',
    'validate_weak_solution_theorem',
    # Spectral origin constant C = 629.83
    'LAMBDA_0',
    'C_UNIVERSAL',
    'F0_SPECTRAL',
    'F0_QCAL',
    'OMEGA_0_SPECTRAL',
    'NoeticOperator',
    'SpectralOriginResult',
    'derive_universal_constant',
    'validate_spectral_frequency_relation',
    'verify_all_appearances_of_f0',
    'mathematical_significance',
    'run_complete_demonstration',
]
