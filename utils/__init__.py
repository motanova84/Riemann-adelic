"""
Utilities module for Riemann Hypothesis validation and adelic analysis.

This package contains various utility functions and classes for:
- Critical line verification
- Adelic determinant calculations  
- Data fetching and validation
- Performance monitoring
- Mathematical tools for Riemann zeta function analysis
- Arithmetic fractal validation (SABIO ∞³ framework)

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
    'PerformanceMetrics'
]
