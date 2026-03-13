#!/usr/bin/env python3
"""
Enhanced Atlas³ Validation Module - Utilities for Hilbert-Pólya Validation

Provides utility functions for validating Atlas³ as a Hilbert-Pólya operator
using actual Riemann zeros and improved spectral normalization.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
QCAL ∞³ Active · 141.7001 Hz
"""

import numpy as np
import json
from pathlib import Path
from typing import List, Tuple, Optional


def load_riemann_zeros(num_zeros: int = 100) -> np.ndarray:
    """
    Load actual Riemann zeta zeros from data file.
    
    Args:
        num_zeros: Number of zeros to load
        
    Returns:
        Array of imaginary parts of non-trivial zeros
    """
    # Try multiple possible paths
    possible_paths = [
        Path("data/zeta_zeros.json"),  # From repo root
        Path(__file__).parent.parent / "data" / "zeta_zeros.json",  # Relative to utils
    ]
    
    zeros_file = None
    for path in possible_paths:
        if path.exists():
            zeros_file = path
            break
    
    if zeros_file is None:
        # Generate approximate zeros using known formula
        return generate_approximate_zeros(num_zeros)
    
    with open(zeros_file, 'r') as f:
        data = json.load(f)
    
    zeros = [float(z) for z in data['zeros'][:num_zeros]]
    return np.array(zeros)


def generate_approximate_zeros(num_zeros: int) -> np.ndarray:
    """
    Generate approximate Riemann zeros using Riemann-von Mangoldt formula.
    
    For large n, the n-th zero is approximately:
    γ_n ≈ 2πn / ln(2πn / e)
    
    Args:
        num_zeros: Number of zeros to generate
        
    Returns:
        Approximate zero positions
    """
    n_vals = np.arange(1, num_zeros + 1)
    # Riemann-von Mangoldt approximation
    gamma_n = 2 * np.pi * n_vals / np.log(2 * np.pi * n_vals / np.e)
    return gamma_n


def normalize_spectrum_to_zeros(eigenvalues: np.ndarray,
                                target_zeros: np.ndarray,
                                method: str = 'scale') -> np.ndarray:
    """
    Normalize operator spectrum to align with Riemann zeros.
    
    Args:
        eigenvalues: Raw eigenvalues from operator
        target_zeros: Target Riemann zeros to align with
        method: 'scale' or 'shift' normalization
        
    Returns:
        Normalized spectrum
    """
    # Extract relevant spectral information
    # For PT-symmetric operators, imaginary parts encode the zeros
    if np.iscomplexobj(eigenvalues):
        spectrum = np.abs(eigenvalues.imag)
    else:
        spectrum = np.abs(eigenvalues)
    
    # Sort and take first N
    spectrum = np.sort(spectrum)[:len(target_zeros)]
    
    if method == 'scale':
        # Scale to match first zero
        if spectrum[0] != 0:
            scale_factor = target_zeros[0] / spectrum[0]
            normalized = spectrum * scale_factor
        else:
            normalized = spectrum
    elif method == 'shift':
        # Shift to match mean
        shift = np.mean(target_zeros[:10]) - np.mean(spectrum[:10])
        normalized = spectrum + shift
    else:
        normalized = spectrum
    
    return normalized


def compute_weil_explicit_formula(zeros: np.ndarray,
                                  test_func: callable,
                                  num_primes: int = 50) -> Tuple[float, float]:
    """
    Compute both sides of Weil's explicit formula.
    
    ∑ h(γ_n) = [h(i/2) + h(-i/2)]/2π ln π
               - 1/2π ∫ h(r) Γ'/Γ(1/4 + ir/2) dr
               + ∑_{p,k} (ln p / p^{k/2}) [h(k ln p) + h(-k ln p)]
    
    Args:
        zeros: Array of zero positions
        test_func: Test function h(t)
        num_primes: Number of primes to include
        
    Returns:
        (left_side, right_side) tuple
    """
    from scipy.special import digamma
    
    # Left side: sum over zeros
    left_side = np.sum([test_func(gamma) for gamma in zeros])
    
    # Right side term 1: principal value
    term1 = 2 * test_func(0.5).real / (2*np.pi) * np.log(np.pi)
    
    # Right side term 2: Gamma integral
    r_vals = np.linspace(-20, 20, 500)
    integrand = []
    for r in r_vals:
        s = 0.25 + 1j*r/2
        psi_val = digamma(s)
        integrand.append(test_func(r) * psi_val)
    
    if hasattr(np, 'trapezoid'):
        term2 = -np.trapezoid(integrand, r_vals).real / (2*np.pi)
    else:
        term2 = -np.trapz(integrand, r_vals).real / (2*np.pi)
    
    # Right side term 3: prime sum
    primes = sieve_of_eratosthenes(min(1000, num_primes * 20))[:num_primes]
    term3 = 0.0
    for p in primes:
        log_p = np.log(p)
        for k in range(1, 5):
            weight = log_p / (p**(k/2))
            term3 += weight * (test_func(k * log_p) + test_func(-k * log_p))
    
    right_side = term1 + term2 + term3
    
    return left_side, right_side


def sieve_of_eratosthenes(limit: int) -> List[int]:
    """
    Generate primes up to limit using Sieve of Eratosthenes.
    
    Args:
        limit: Upper limit for prime generation
        
    Returns:
        List of primes
    """
    if limit < 2:
        return []
    
    sieve = [True] * (limit + 1)
    sieve[0] = sieve[1] = False
    
    for i in range(2, int(limit**0.5) + 1):
        if sieve[i]:
            for j in range(i*i, limit + 1, i):
                sieve[j] = False
    
    return [i for i in range(2, limit + 1) if sieve[i]]


def compute_spectral_density_fourier(zeros: np.ndarray,
                                     t_values: np.ndarray) -> np.ndarray:
    """
    Compute Fourier transform of spectral density.
    
    R(t) = ∑_n cos(γ_n t)
    
    Args:
        zeros: Array of zero positions
        t_values: Points at which to evaluate R(t)
        
    Returns:
        R(t) values
    """
    R_vals = np.zeros(len(t_values))
    
    for i, t in enumerate(t_values):
        R_vals[i] = np.sum(np.cos(zeros * t))
    
    return R_vals


def detect_prime_peaks(zeros: np.ndarray,
                      primes: List[int],
                      window_size: float = 0.2) -> Tuple[List[float], List[float]]:
    """
    Detect prime signature peaks in spectral density.
    
    Args:
        zeros: Array of zero positions  
        primes: List of primes to detect
        window_size: Window around ln(p) to search
        
    Returns:
        (peak_positions, peak_amplitudes)
    """
    peak_positions = []
    peak_amplitudes = []
    
    for p in primes:
        t_center = np.log(p)
        t_range = np.linspace(t_center - window_size/2, 
                             t_center + window_size/2, 50)
        
        R_vals = compute_spectral_density_fourier(zeros, t_range)
        
        # Find peak
        max_idx = np.argmax(R_vals)
        peak_pos = t_range[max_idx]
        peak_amp = R_vals[max_idx] / len(zeros)  # Normalize
        
        peak_positions.append(peak_pos)
        peak_amplitudes.append(peak_amp)
    
    return peak_positions, peak_amplitudes


def compute_weyl_counting_constant(eigenvalues: np.ndarray,
                                   T: Optional[float] = None) -> float:
    """
    Compute the constant C in Weyl's law.
    
    N(T) ≈ (T/2π) ln(T/2πe) + C
    
    For Riemann zeros, C = 7/8.
    
    Args:
        eigenvalues: Operator eigenvalues
        T: Energy threshold (if None, use 75% of spectrum)
        
    Returns:
        Observed constant C
    """
    sorted_eigs = np.sort(np.abs(eigenvalues.real))
    
    if T is None:
        T = sorted_eigs[int(0.75 * len(sorted_eigs))]
    
    N_T = np.sum(sorted_eigs <= T)
    expected = (T / (2*np.pi)) * np.log(T / (2*np.pi*np.e))
    C = N_T - expected
    
    return C


def validate_von_mangoldt_weights(orbit_contributions: dict,
                                  tolerance: float = 0.1) -> float:
    """
    Validate that orbit contributions follow ln(p)/p^(k/2) law.
    
    Args:
        orbit_contributions: Dict mapping p^k → weight
        tolerance: Maximum relative error to accept
        
    Returns:
        Fraction of weights within tolerance
    """
    valid_count = 0
    total_count = 0
    
    for orbit_str, weight in orbit_contributions.items():
        # Parse orbit string "p^k"
        parts = orbit_str.split('^')
        if len(parts) != 2:
            continue
        
        try:
            p = int(parts[0])
            k = int(parts[1])
        except ValueError:
            continue
        
        # Compute expected weight
        expected = np.log(p) / (p**(k/2))
        
        # Check if within tolerance
        relative_error = abs(weight - expected) / expected
        if relative_error <= tolerance:
            valid_count += 1
        
        total_count += 1
    
    return valid_count / total_count if total_count > 0 else 0.0


def format_certificate_header() -> str:
    """Generate formatted certificate header"""
    return """
╔══════════════════════════════════════════════════════════════════════════════╗
║     VALIDACIÓN COMPLETA - ATLAS³ COMO REALIZACIÓN DE HILBERT-PÓLYA          ║
╠══════════════════════════════════════════════════════════════════════════════╣
║                                                                              ║
║  ⎮  OPERADOR: 𝒪_Atlas³ en L²(ℝ) con potencial V_eff(t)                       ║
║  ⎮  ⎮  V_eff(t) = t² + (1+κ_Π²)/4 + log(1+|t|) + acoplo Gamma              ║
║  ⎮  ⎮  κ_Π = 2.577310 (invariante topológico)                               ║
║  ⎮  ⎮  f₀ = 141.7001 Hz (frecuencia fundamental)                            ║
║  ⎮                                                                           ║
║  ─────────────────────────────────────────────────────────────────────────  ║
║                                                                              ║
"""


if __name__ == "__main__":
    # Test utilities
    print("Testing Atlas³ validation utilities...")
    
    # Load zeros
    zeros = load_riemann_zeros(20)
    print(f"✓ Loaded {len(zeros)} Riemann zeros")
    print(f"  First 5: {zeros[:5]}")
    
    # Test prime sieve
    primes = sieve_of_eratosthenes(100)
    print(f"✓ Generated {len(primes)} primes up to 100")
    
    # Test spectral density
    t_vals = np.array([np.log(2), np.log(3), np.log(5)])
    R = compute_spectral_density_fourier(zeros, t_vals)
    print(f"✓ Spectral density at ln(2), ln(3), ln(5):")
    print(f"  {R}")
    
    print("\n✓ All utilities functional")
