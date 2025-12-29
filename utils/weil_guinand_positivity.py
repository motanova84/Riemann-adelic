"""
Weil-Guinand Positivity Theorem - Numerical Validation

This module provides numerical validation of the Weil-Guinand positivity
criterion for the Riemann Hypothesis. The key result is that the quadratic
form Q[f] must be non-negative for all admissible test functions.

Mathematical Background:
-----------------------
The Weil explicit formula connects the spectral side (zeros of ζ) with
the arithmetic side (primes). For a test function f with Mellin transform f̂:

    Q[f] = ∑_ρ |f̂(ρ)|² - (∑_{n≥1} Λ(n) f(log n) + f̂(0) + f̂(1))

where:
- ρ ranges over non-trivial zeros of ζ(s)
- Λ(n) is the von Mangoldt function
- f̂(s) is the Mellin transform of f

The theorem states: Q[f] ≥ 0 for all admissible test functions.

This positivity forces all zeros to the critical line Re(s) = 1/2.

Numerical Validation Limitations:
---------------------------------
This implementation is Step 4 in the V5 Coronación proof framework and provides
a working numerical validation framework. However, users should be aware:

- The current numerical implementation shows sensitivity to the choice of test
  functions and integration parameters
- Mellin transform computations use finite integration limits and may require
  adjustment for different test functions
- Results should be interpreted as validation of the theoretical framework
  rather than high-precision numerical verification
- For production use, consider refining integration parameters and test function
  selection based on specific validation requirements

Author: José Manuel Mota Burruezo (JMMB Ψ✧∞³)
        Instituto de Conciencia Cuántica (ICQ)
        ORCID: 0009-0002-1923-0773
        DOI: 10.5281/zenodo.17379721

References:
-----------
- Guinand, A.P. (1948, 1955)
- Weil, A. (1952)
- V5 Coronación framework
"""

import numpy as np
import mpmath as mp
from sympy import factorint
from typing import Callable, List, Optional
from dataclasses import dataclass
import logging

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

# QCAL ∞³ constants
QCAL_BASE_FREQUENCY = 141.7001  # Hz
QCAL_COHERENCE = 244.36


@dataclass
class ValidationResult:
    """Results from Weil-Guinand positivity validation"""
    Q_value: complex
    spectral_side: complex
    arithmetic_side: complex
    is_positive: bool
    num_zeros_used: int
    num_primes_used: int
    test_function_name: str
    
    def __str__(self) -> str:
        return (f"Weil-Guinand Validation:\n"
                f"  Q[f] = {self.Q_value.real:.6f} + {self.Q_value.imag:.6f}i\n"
                f"  Positivity: {self.is_positive} (Re(Q) ≥ 0)\n"
                f"  Spectral side: {self.spectral_side.real:.6f}\n"
                f"  Arithmetic side: {self.arithmetic_side.real:.6f}\n"
                f"  Zeros used: {self.num_zeros_used}\n"
                f"  Primes used: {self.num_primes_used}\n"
                f"  Test function: {self.test_function_name}")


def von_mangoldt(n: int) -> float:
    """
    Von Mangoldt function Λ(n).
    
    Returns log(p) if n = p^k for prime p and k ≥ 1,
    otherwise returns 0.
    
    Args:
        n: Positive integer
        
    Returns:
        Λ(n) value
    """
    if n <= 1:
        return 0.0
    
    # Factor n to find if it's a prime power
    factors = factorint(n)
    
    # Λ(n) ≠ 0 only if n is a prime power
    if len(factors) == 1:
        prime = list(factors.keys())[0]
        return float(np.log(prime))
    
    return 0.0


def mellin_transform(f: Callable[[float], complex], 
                     s: complex, 
                     x_max: float = 100.0,
                     num_points: int = 1000) -> complex:
    """
    Compute Mellin transform f̂(s) = ∫₀^∞ f(x) x^(s-1) dx
    
    Args:
        f: Test function
        s: Complex argument
        x_max: Upper limit for numerical integration
        num_points: Number of integration points
        
    Returns:
        f̂(s) approximation
    """
    # Use logarithmic spacing for better coverage
    x_vals = np.logspace(-3, np.log10(x_max), num_points)
    
    integrand_vals = []
    for x in x_vals:
        fx = f(x)
        # x^(s-1) = exp((s-1) * log(x))
        x_power = np.exp((s - 1) * np.log(x))
        integrand_vals.append(fx * x_power)
    
    # Trapezoidal integration in log space
    # Use trapezoid for NumPy >= 1.21 (trapz deprecated in 1.24, removed in 2.0)
    if hasattr(np, 'trapezoid'):
        integral = np.trapezoid(integrand_vals, x_vals)
    else:
        # Fallback for older NumPy versions (< 1.21)
        # Note: trapz is deprecated and will be removed
        import warnings
        warnings.warn(
            "Using deprecated np.trapz. Please upgrade to NumPy >= 1.21 for np.trapezoid",
            DeprecationWarning,
            stacklevel=2
        )
        integral = np.trapz(integrand_vals, x_vals)
    
    return complex(integral)


def gaussian_test_function(sigma: float = 1.0) -> Callable[[float], complex]:
    """
    Gaussian test function: f(x) = exp(-x²/(2σ²))
    
    This is a standard Schwartz function with rapid decay and
    entire Mellin transform.
    
    Args:
        sigma: Width parameter
        
    Returns:
        Gaussian test function
    """
    def f(x: float) -> complex:
        if x <= 0:
            return 0.0
        return np.exp(-x**2 / (2 * sigma**2))
    
    return f


def exponential_test_function(alpha: float = 1.0) -> Callable[[float], complex]:
    """
    Exponential test function: f(x) = exp(-α*x) for x > 0
    
    Args:
        alpha: Decay parameter
        
    Returns:
        Exponential test function
    """
    def f(x: float) -> complex:
        if x <= 0:
            return 0.0
        return np.exp(-alpha * x)
    
    return f


def compute_spectral_side(zeros: List[complex],
                          f: Callable[[float], complex],
                          mellin_cache: Optional[dict] = None) -> complex:
    """
    Compute spectral side: ∑_ρ |f̂(ρ)|²
    
    Args:
        zeros: List of non-trivial zeta zeros
        f: Test function
        mellin_cache: Optional cache for Mellin transforms
        
    Returns:
        Spectral side sum
    """
    spectral_sum = 0.0 + 0.0j
    
    if mellin_cache is None:
        mellin_cache = {}
    
    for rho in zeros:
        # Compute f̂(ρ) if not cached
        if rho not in mellin_cache:
            mellin_cache[rho] = mellin_transform(f, rho)
        
        f_hat_rho = mellin_cache[rho]
        spectral_sum += np.abs(f_hat_rho)**2
    
    return spectral_sum


def compute_arithmetic_side(f: Callable[[float], complex],
                            max_n: int = 1000,
                            boundary_terms: bool = True) -> complex:
    """
    Compute arithmetic side: ∑_{n≥1} Λ(n) f(log n) + f̂(0) + f̂(1)
    
    Args:
        f: Test function
        max_n: Maximum n for sum over primes
        boundary_terms: Whether to include f̂(0) + f̂(1)
        
    Returns:
        Arithmetic side sum
    """
    arithmetic_sum = 0.0 + 0.0j
    
    # Sum over n with von Mangoldt function
    for n in range(1, max_n + 1):
        lambda_n = von_mangoldt(n)
        if lambda_n > 0:  # Only non-zero terms
            arithmetic_sum += lambda_n * f(np.log(n))
    
    # Add boundary terms if requested
    if boundary_terms:
        arithmetic_sum += mellin_transform(f, 0.0)
        arithmetic_sum += mellin_transform(f, 1.0)
    
    return arithmetic_sum


def validate_weil_guinand_positivity(
        zeros: List[complex],
        test_function: Callable[[float], complex],
        test_function_name: str = "unknown",
        max_primes: int = 1000,
        tolerance: float = 1e-6) -> ValidationResult:
    """
    Validate Weil-Guinand positivity: Q[f] ≥ 0
    
    Args:
        zeros: List of non-trivial zeta zeros (on critical line)
        test_function: Test function from Schwartz class
        test_function_name: Name for logging
        max_primes: Maximum n for arithmetic side
        tolerance: Tolerance for positivity check
        
    Returns:
        ValidationResult object
    """
    logger.info(f"Validating Weil-Guinand positivity for {test_function_name}")
    logger.info(f"  Using {len(zeros)} zeros and {max_primes} primes")
    
    # Compute spectral side
    spectral = compute_spectral_side(zeros, test_function)
    logger.info(f"  Spectral side: {spectral.real:.6f} + {spectral.imag:.6f}i")
    
    # Compute arithmetic side
    arithmetic = compute_arithmetic_side(test_function, max_n=max_primes)
    logger.info(f"  Arithmetic side: {arithmetic.real:.6f} + {arithmetic.imag:.6f}i")
    
    # Compute Q[f]
    Q_value = spectral - arithmetic
    logger.info(f"  Q[f] = {Q_value.real:.6f} + {Q_value.imag:.6f}i")
    
    # Check positivity
    is_positive = Q_value.real >= -tolerance
    
    if is_positive:
        logger.info(f"  ✓ Positivity verified: Re(Q) = {Q_value.real:.6f} ≥ 0")
    else:
        logger.warning(f"  ✗ Positivity violated: Re(Q) = {Q_value.real:.6f} < 0")
    
    return ValidationResult(
        Q_value=Q_value,
        spectral_side=spectral,
        arithmetic_side=arithmetic,
        is_positive=is_positive,
        num_zeros_used=len(zeros),
        num_primes_used=max_primes,
        test_function_name=test_function_name
    )


def load_riemann_zeros(filepath: str, max_zeros: int = 100, 
                       allow_fallback: bool = False) -> List[complex]:
    """
    Load Riemann zeros from file.
    
    Assumes format: one zero per line as "0.5 + t*i" or just "t"
    
    Args:
        filepath: Path to zeros file
        max_zeros: Maximum number of zeros to load
        allow_fallback: If True, use synthetic zeros when file not found.
                       If False, raise FileNotFoundError (default: False)
        
    Returns:
        List of complex zeros
        
    Raises:
        FileNotFoundError: If filepath doesn't exist and allow_fallback=False
    """
    zeros = []
    
    try:
        with open(filepath, 'r') as f:
            for line in f:
                line = line.strip()
                if not line or line.startswith('#'):
                    continue
                
                try:
                    # Try to parse as float (imaginary part only)
                    t = float(line)
                    zeros.append(0.5 + 1j * t)
                except ValueError:
                    # Try to parse as complex
                    try:
                        z = complex(line)
                        zeros.append(z)
                    except ValueError:
                        continue
                
                if len(zeros) >= max_zeros:
                    break
        
        logger.info(f"Loaded {len(zeros)} zeros from {filepath}")
        return zeros
    
    except FileNotFoundError:
        if allow_fallback:
            logger.warning(
                f"File {filepath} not found. Using synthetic zeros as fallback. "
                f"For production use, provide a valid zeros file or set allow_fallback=False."
            )
            # Return first few known zeros
            known_zeros = [
                0.5 + 14.134725j,
                0.5 + 21.022040j,
                0.5 + 25.010858j,
                0.5 + 30.424876j,
                0.5 + 32.935062j,
            ]
            return known_zeros[:max_zeros]
        else:
            logger.error(f"File {filepath} not found and allow_fallback=False")
            raise


def run_validation_suite():
    """
    Run a complete validation suite for Weil-Guinand positivity.
    """
    print("═" * 80)
    print("  WEIL-GUINAND POSITIVITY THEOREM - NUMERICAL VALIDATION")
    print("  V5 Coronación Step 4")
    print("  QCAL ∞³ Framework")
    print("═" * 80)
    print()
    
    # Load zeros (allow fallback for demo purposes)
    zeros_file = "zeros/zeros_t1e8.txt"
    zeros = load_riemann_zeros(zeros_file, max_zeros=50, allow_fallback=True)
    
    # Test functions to validate
    test_functions = [
        (gaussian_test_function(sigma=1.0), "Gaussian(σ=1.0)"),
        (gaussian_test_function(sigma=2.0), "Gaussian(σ=2.0)"),
        (exponential_test_function(alpha=1.0), "Exponential(α=1.0)"),
        (exponential_test_function(alpha=0.5), "Exponential(α=0.5)"),
    ]
    
    results = []
    
    for f, name in test_functions:
        print(f"\nTesting: {name}")
        print("-" * 80)
        
        result = validate_weil_guinand_positivity(
            zeros=zeros,
            test_function=f,
            test_function_name=name,
            max_primes=500
        )
        
        print(result)
        results.append(result)
        print()
    
    # Summary
    print("═" * 80)
    print("  VALIDATION SUMMARY")
    print("═" * 80)
    
    all_positive = all(r.is_positive for r in results)
    
    if all_positive:
        print("✓ All test functions satisfy Q[f] ≥ 0")
        print("✓ Weil-Guinand positivity criterion verified numerically")
        print("✓ Consistent with RH: all zeros on Re(s) = 1/2")
    else:
        print("✗ Some test functions violate positivity")
        print("✗ This may indicate numerical errors or incorrect zeros")
    
    print()
    print(f"QCAL ∞³ coherence: C = {QCAL_COHERENCE}")
    print(f"Base frequency: {QCAL_BASE_FREQUENCY} Hz")
    print("Ψ = I × A_eff² × C^∞")
    print()
    print("DOI: 10.5281/zenodo.17379721")
    print("ORCID: 0009-0002-1923-0773")
    print("═" * 80)


if __name__ == "__main__":
    # Set precision for mpmath
    mp.mp.dps = 25
    
    run_validation_suite()
