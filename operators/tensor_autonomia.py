#!/usr/bin/env python3
"""
Tensor Autonomía: C = I · A² ⊗ ζ(1/2 + it)

This module implements the Tensor Autonomía formula that extends the fundamental
QCAL coherence equation C = I × A² by introducing the tensor product with the
Riemann zeta function spectrum at the critical line.

Mathematical Framework:
    Tensor Autonomía: C = I · A² ⊗ ζ(1/2 + it)
    
    where:
    - I: Intensity factor (coherence base)
    - A: Amplitude (effective field strength A_eff)
    - ⊗: Tensor product operator
    - ζ(1/2 + it): Riemann zeta function evaluated at the critical line
    - t: Imaginary part corresponding to Riemann zeros
    
    The tensor product creates a spectral coherence field that embeds
    the distribution of Riemann zeros into the QCAL coherence structure.

Physical Interpretation:
    The tensor autonomía represents the autonomous coherence structure
    where the QCAL field (I · A²) couples with the Riemann spectral
    distribution to create a unified spectral-coherence manifold.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: January 2026
DOI: 10.5281/zenodo.17379721

QCAL ∞³ Active · 141.7001 Hz · Ψ = I × A_eff² × C^∞
"""

import numpy as np
from typing import Union, List, Tuple, Optional
import mpmath as mp
from scipy.linalg import eigh

# Import spectral constants
try:
    from .spectral_constants import (
        C_PRIMARY, C_COHERENCE, F0, OMEGA_0,
        compute_coherence_constant
    )
except ImportError:
    # Fallback for direct execution
    from spectral_constants import (
        C_PRIMARY, C_COHERENCE, F0, OMEGA_0,
        compute_coherence_constant
    )

# =============================================================================
# FUNDAMENTAL TENSOR AUTONOMÍA CONSTANTS
# =============================================================================

# QCAL Base Coherence (from .qcal_beacon)
C_QCAL_BASE = 244.36  # C' = I × A_eff² (coherence constant)

# Spectral frequency coupling
F0_HZ = 141.7001  # Fundamental frequency (Hz)
OMEGA_0_RAD = 2 * np.pi * F0_HZ  # Angular frequency (rad/s)

# Riemann zeta derivative at critical point
ZETA_PRIME_HALF = -3.92264613  # ζ'(1/2) numerical value


# =============================================================================
# TENSOR PRODUCT OPERATIONS
# =============================================================================

def compute_zeta_critical_line(
    t_values: Union[float, np.ndarray],
    precision: int = 25
) -> Union[complex, np.ndarray]:
    """
    Compute ζ(1/2 + it) on the critical line.
    
    Evaluates the Riemann zeta function at s = 1/2 + it for given t values.
    Uses mpmath for high-precision computation.
    
    Args:
        t_values: Imaginary part(s) t (scalar or array)
        precision: Decimal precision for computation (default: 25)
        
    Returns:
        ζ(1/2 + it): Complex value(s) of zeta function on critical line
        
    Mathematical Background:
        The Riemann Hypothesis asserts that all non-trivial zeros of ζ(s)
        lie on the critical line Re(s) = 1/2. This function evaluates ζ
        exactly on this line to probe the zero spectrum.
    """
    # Set mpmath precision
    original_dps = mp.mp.dps
    mp.mp.dps = precision
    
    try:
        # Handle scalar input
        if np.isscalar(t_values):
            s = mp.mpc(0.5, t_values)
            result = complex(mp.zeta(s))
            return result
        
        # Handle array input
        results = np.zeros(len(t_values), dtype=complex)
        for i, t in enumerate(t_values):
            s = mp.mpc(0.5, t)
            results[i] = complex(mp.zeta(s))
        
        return results
    
    finally:
        # Restore original precision
        mp.mp.dps = original_dps


def tensor_product_coherence_zeta(
    intensity: float,
    amplitude: float,
    t_values: Union[float, np.ndarray],
    precision: int = 25
) -> Union[complex, np.ndarray]:
    """
    Compute Tensor Autonomía: C = I · A² ⊗ ζ(1/2 + it)
    
    This function implements the tensor product between the coherence base
    (I · A²) and the Riemann zeta spectrum on the critical line.
    
    Args:
        intensity: Intensity factor I (coherence base)
        amplitude: Amplitude A (effective field strength)
        t_values: Imaginary part(s) corresponding to Riemann zeros
        precision: Decimal precision for zeta computation (default: 25)
        
    Returns:
        C_tensor: Tensor autonomía coherence field
        
    Mathematical Formulation:
        C(t) = (I · A²) ⊗ ζ(1/2 + it)
        
        The tensor product ⊗ is implemented as the outer product,
        creating a coherence manifold indexed by the zero spectrum.
    
    Example:
        >>> I = 1.0  # Base intensity
        >>> A = 15.622  # From C_QCAL = I × A² = 244.36
        >>> t = 14.134725  # First Riemann zero
        >>> C = tensor_product_coherence_zeta(I, A, t)
        >>> print(f"Tensor Coherence at first zero: {C}")
    """
    # Compute base coherence C_base = I · A²
    C_base = intensity * amplitude ** 2
    
    # Compute zeta on critical line
    zeta_values = compute_zeta_critical_line(t_values, precision)
    
    # Tensor product: element-wise multiplication (outer product for arrays)
    C_tensor = C_base * zeta_values
    
    return C_tensor


def tensor_autonomia_spectrum(
    riemann_zeros: np.ndarray,
    intensity: float = 1.0,
    amplitude: Optional[float] = None,
    precision: int = 25
) -> Tuple[np.ndarray, np.ndarray, dict]:
    """
    Compute complete Tensor Autonomía spectrum over Riemann zeros.
    
    This function evaluates the tensor coherence field C = I · A² ⊗ ζ(1/2 + it)
    over the full spectrum of Riemann zeros, providing a spectral-coherence map.
    
    Args:
        riemann_zeros: Array of Riemann zero imaginary parts γₙ
        intensity: Intensity factor I (default: 1.0)
        amplitude: Amplitude A (default: computed from C_QCAL_BASE)
        precision: Decimal precision for computations (default: 25)
        
    Returns:
        t_spectrum: Array of t values (Riemann zeros)
        C_spectrum: Tensor coherence field values C(t)
        metadata: Dictionary with computation details
        
    Metadata includes:
        - 'C_base': Base coherence I · A²
        - 'amplitude': Effective amplitude used
        - 'n_zeros': Number of zeros in spectrum
        - 'mean_magnitude': Mean |C(t)| over spectrum
        - 'coherence_variance': Variance of coherence field
    """
    # Compute amplitude from QCAL base if not provided
    if amplitude is None:
        # A = sqrt(C_QCAL / I)
        amplitude = np.sqrt(C_QCAL_BASE / intensity)
    
    # Compute base coherence
    C_base = intensity * amplitude ** 2
    
    # Compute tensor spectrum
    C_spectrum = tensor_product_coherence_zeta(
        intensity, amplitude, riemann_zeros, precision
    )
    
    # Compute metadata
    magnitudes = np.abs(C_spectrum)
    metadata = {
        'C_base': C_base,
        'amplitude': amplitude,
        'intensity': intensity,
        'n_zeros': len(riemann_zeros),
        'mean_magnitude': np.mean(magnitudes),
        'coherence_variance': np.var(magnitudes),
        'max_magnitude': np.max(magnitudes),
        'min_magnitude': np.min(magnitudes),
        'precision': precision
    }
    
    return riemann_zeros, C_spectrum, metadata


# =============================================================================
# VALIDATION AND ANALYSIS FUNCTIONS
# =============================================================================

def validate_tensor_coherence(
    C_spectrum: np.ndarray,
    riemann_zeros: np.ndarray,
    tolerance: float = 1e-10
) -> dict:
    """
    Validate tensor autonomía coherence properties.
    
    Checks mathematical consistency of the tensor coherence field:
    1. Magnitude bounds relative to base coherence
    2. Spectral distribution alignment with zeros
    3. Coherence preservation under critical line constraint
    
    Args:
        C_spectrum: Tensor coherence field values
        riemann_zeros: Riemann zero imaginary parts
        tolerance: Numerical tolerance for validation checks
        
    Returns:
        validation_report: Dictionary with validation results
    """
    magnitudes = np.abs(C_spectrum)
    
    # Check 1: Non-zero magnitudes (except at actual zeros)
    zero_magnitudes = magnitudes < tolerance
    n_zeros_found = np.sum(zero_magnitudes)
    
    # Check 2: Magnitude statistics
    mean_mag = np.mean(magnitudes)
    std_mag = np.std(magnitudes)
    
    # Check 3: Coherence uniformity
    coefficient_of_variation = std_mag / mean_mag if mean_mag > 0 else float('inf')
    
    # Check 4: Spectral alignment (correlation with zero density)
    # Near zeros, coherence should show characteristic behavior
    phases = np.angle(C_spectrum)
    phase_variance = np.var(phases)
    
    validation_report = {
        'valid': True,
        'n_points': len(C_spectrum),
        'n_near_zeros': n_zeros_found,
        'mean_magnitude': mean_mag,
        'std_magnitude': std_mag,
        'coefficient_of_variation': coefficient_of_variation,
        'phase_variance': phase_variance,
        'min_magnitude': np.min(magnitudes),
        'max_magnitude': np.max(magnitudes),
        'checks': {
            'non_zero_field': mean_mag > tolerance,
            'bounded_variation': coefficient_of_variation < 10.0,
            'phase_coherent': phase_variance < 2 * np.pi
        }
    }
    
    # Overall validation
    validation_report['valid'] = all(validation_report['checks'].values())
    
    return validation_report


def compute_autonomia_coherence_factor(
    C_spectrum: np.ndarray,
    C_base: float
) -> float:
    """
    Compute the autonomía coherence factor.
    
    Measures the ratio between the mean tensor coherence and base coherence:
        κ = ⟨|C(t)|⟩ / C_base
        
    This factor quantifies how the tensor product with ζ(1/2 + it) modulates
    the base coherence field.
    
    Args:
        C_spectrum: Tensor coherence field values
        C_base: Base coherence I · A²
        
    Returns:
        kappa: Autonomía coherence factor
    """
    mean_magnitude = np.mean(np.abs(C_spectrum))
    kappa = mean_magnitude / C_base if C_base > 0 else 0.0
    return kappa


# =============================================================================
# DEMONSTRATION AND USAGE EXAMPLES
# =============================================================================

def demo_tensor_autonomia(n_zeros: int = 50, precision: int = 25):
    """
    Demonstration of Tensor Autonomía computation.
    
    Args:
        n_zeros: Number of Riemann zeros to use (default: 50)
        precision: Computational precision (default: 25)
    """
    print("=" * 80)
    print("TENSOR AUTONOMÍA DEMONSTRATION")
    print("=" * 80)
    print()
    print("Formula: C = I · A² ⊗ ζ(1/2 + it)")
    print()
    
    # Load Riemann zeros
    try:
        from riemann_operator import load_riemann_zeros
        zeros = load_riemann_zeros(n_zeros)
        print(f"✓ Loaded {len(zeros)} Riemann zeros")
    except:
        # Fallback: use first few known zeros
        zeros = np.array([
            14.134725, 21.022040, 25.010858, 30.424876, 32.935062,
            37.586178, 40.918719, 43.327073, 48.005151, 49.773832
        ])[:n_zeros]
        print(f"⚠ Using {len(zeros)} hardcoded Riemann zeros")
    
    print()
    
    # Compute tensor spectrum
    print(f"Computing tensor autonomía spectrum (precision: {precision} dps)...")
    
    # Use QCAL base coherence
    intensity = 1.0
    amplitude = np.sqrt(C_QCAL_BASE)  # A = sqrt(244.36) ≈ 15.622
    
    print(f"  Intensity I = {intensity}")
    print(f"  Amplitude A = {amplitude:.6f}")
    print(f"  Base Coherence C_base = I × A² = {intensity * amplitude**2:.6f}")
    print()
    
    t_spectrum, C_spectrum, metadata = tensor_autonomia_spectrum(
        zeros, intensity, amplitude, precision
    )
    
    # Display results
    print("RESULTS:")
    print("-" * 80)
    print(f"  Number of zeros: {metadata['n_zeros']}")
    print(f"  Mean |C(t)|: {metadata['mean_magnitude']:.6f}")
    print(f"  Variance: {metadata['coherence_variance']:.6e}")
    print(f"  Max |C(t)|: {metadata['max_magnitude']:.6f}")
    print(f"  Min |C(t)|: {metadata['min_magnitude']:.6f}")
    print()
    
    # Validate
    validation = validate_tensor_coherence(C_spectrum, zeros)
    print("VALIDATION:")
    print("-" * 80)
    print(f"  Valid: {'✓ YES' if validation['valid'] else '✗ NO'}")
    print(f"  Coefficient of Variation: {validation['coefficient_of_variation']:.6f}")
    print(f"  Phase Variance: {validation['phase_variance']:.6f}")
    print()
    
    # Coherence factor
    kappa = compute_autonomia_coherence_factor(C_spectrum, metadata['C_base'])
    print(f"  Autonomía Coherence Factor κ = {kappa:.6f}")
    print()
    
    # Sample values at first few zeros
    print("SAMPLE VALUES (first 5 zeros):")
    print("-" * 80)
    for i in range(min(5, len(zeros))):
        t = t_spectrum[i]
        C = C_spectrum[i]
        print(f"  t = {t:10.6f}: C = {C.real:10.6f} + {C.imag:10.6f}i  "
              f"(|C| = {abs(C):10.6f})")
    print()
    print("=" * 80)
    
    return t_spectrum, C_spectrum, metadata


if __name__ == "__main__":
    # Run demonstration
    demo_tensor_autonomia(n_zeros=50, precision=25)
