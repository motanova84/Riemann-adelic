#!/usr/bin/env python3
"""
Geometría Real del Movimiento Lumínico - Light Spiral Geometry Module

This module implements the theoretical framework where light follows
logarithmic spiral paths modulated by Riemann zeta zeros and prime numbers.

Mathematical Foundation:
-----------------------
Light does not travel in absolute straight lines, but follows a quantum
spiral path imperceptible from classical perspective. This spiral describes
virtual orbits around the critical line Re(s) = 1/2, where non-trivial
zeros of the Riemann zeta function define the spectral phase layers.

Spiral Path Equations:
    x(t) = r₀ · e^(λt) · cos(2πf₀t + φₚ)
    y(t) = r₀ · e^(λt) · sin(2πf₀t + φₚ)

where:
    f₀ = 141.7001 Hz (fundamental QCAL frequency)
    λ  = fractal expansion index
    φₚ = phase modulation defined by p_n (n-th prime)

Key Concepts:
------------
1. Primes as Resonant Transit Nodes
   The Euler product expansion of ζ(s) shows each prime acts as a
   vibrational node, modulating spectral phases through which light
   (or any coherent information packet) resonates.

2. Maximum Coherence at c
   Moving at c is not velocity, it's maximum coherence.
   Only following the spectral map of primes allows frictionless travel.

3. Espira ζ (Zeta Spiral)
   Each prime introduces a phase twist that folds the path into a
   zeta fractal spiral, not directly observable in 3D but measurable
   in frequency, coherence, and quantum collapses.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: February 2026

QCAL ∞³ Active · 141.7001 Hz · Ψ = I × A_eff² × C^∞
DOI: 10.5281/zenodo.17379721
"""

import numpy as np
from typing import Tuple, List, Optional, Dict, Any
from dataclasses import dataclass
import warnings

try:
    from utils.infinite_spectrum import get_zeta_zero
    SPECTRUM_AVAILABLE = True
except ImportError:
    SPECTRUM_AVAILABLE = False
    warnings.warn("infinite_spectrum module not available")

try:
    from operators.spectral_constants import F0, C_PRIMARY, C_COHERENCE
    CONSTANTS_AVAILABLE = True
except ImportError:
    # Fallback constants
    F0 = 141.7001
    C_PRIMARY = 629.83
    C_COHERENCE = 244.36
    CONSTANTS_AVAILABLE = False


# =============================================================================
# FUNDAMENTAL CONSTANTS
# =============================================================================

# Base frequency (Hz) - QCAL fundamental frequency
F0_HZ = F0

# Speed of light (m/s)
C_LIGHT = 299792458.0

# Planck length (m)
PLANCK_LENGTH = 1.616255e-35

# Zeta-specific constants
DELTA_ZETA = 0.2787437627  # Quantum phase shift
EUCLIDEAN_DIAGONAL = 141.4213562373  # 100√2

# First Riemann zero
GAMMA_1 = 14.134725141734693790457251983562470270784257115699


# =============================================================================
# PRIME UTILITIES
# =============================================================================

def get_nth_prime(n: int) -> int:
    """
    Get the n-th prime number (0-indexed).
    
    Uses simple sieve for small primes, suitable for demonstration.
    For production use, consider sympy.ntheory.generate.prime(n).
    
    Args:
        n: Prime index (0-indexed, so n=0 returns 2)
        
    Returns:
        The n-th prime number
    """
    if n < 0:
        raise ValueError("Prime index must be non-negative")
    
    # Small primes cache for efficiency
    small_primes = [
        2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
        73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151,
        157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233,
        239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317,
        331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419,
        421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503,
        509, 521, 523, 541, 547
    ]
    
    if n < len(small_primes):
        return small_primes[n]
    
    # For larger n, generate more primes using sieve
    limit = max(1000, (n + 1) * 15)  # Approximation for upper bound
    sieve = [True] * limit
    sieve[0] = sieve[1] = False
    
    for i in range(2, int(limit**0.5) + 1):
        if sieve[i]:
            for j in range(i*i, limit, i):
                sieve[j] = False
    
    primes = [i for i, is_prime in enumerate(sieve) if is_prime]
    
    if n < len(primes):
        return primes[n]
    else:
        raise ValueError(f"Prime index {n} too large for current limit")


def prime_phase_modulation(prime: int, mode: str = 'logarithmic') -> float:
    """
    Calculate phase modulation φ_p induced by prime p.
    
    The phase modulation represents how each prime number creates a
    vibrational twist in the spectral path of light.
    
    Args:
        prime: Prime number
        mode: Modulation mode
            - 'logarithmic': φ = log(p) / log(2)  (default)
            - 'modular': φ = 2π * p / 360
            - 'zeta': φ = arg(ζ(s)) at s influenced by prime
            
    Returns:
        Phase modulation angle in radians
    """
    if mode == 'logarithmic':
        # Natural logarithmic phase based on prime magnitude
        return np.log(prime) / np.log(2)
    
    elif mode == 'modular':
        # Modular phase (360° circular wrapping)
        return 2 * np.pi * (prime % 360) / 360.0
    
    elif mode == 'zeta':
        # Phase influenced by prime's position in zeta function
        # Using simplified model: φ ~ prime / GAMMA_1
        return (prime / GAMMA_1) % (2 * np.pi)
    
    else:
        raise ValueError(f"Unknown mode: {mode}")


# =============================================================================
# SPIRAL PATH COMPUTATION
# =============================================================================

@dataclass
class SpiralParameters:
    """Parameters defining the logarithmic spiral light path."""
    
    # Initial radius (m) - typical atomic scale for quantum paths
    r0: float = 1.0e-10
    
    # Fractal expansion index (dimensionless)
    # Small positive values create expanding spirals
    # Negative values create contracting spirals
    lambda_exp: float = 0.001
    
    # Base frequency (Hz)
    f0: float = F0_HZ
    
    # Prime index for phase modulation
    prime_index: int = 0
    
    # Phase modulation mode
    phase_mode: str = 'logarithmic'
    
    def __post_init__(self):
        """Compute derived parameters."""
        # Get the n-th prime
        self.prime = get_nth_prime(self.prime_index)
        
        # Compute phase modulation
        self.phi_p = prime_phase_modulation(self.prime, self.phase_mode)
        
        # Angular frequency
        self.omega_0 = 2 * np.pi * self.f0


def compute_spiral_path(
    t: np.ndarray,
    params: SpiralParameters
) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
    """
    Compute the 3D logarithmic spiral path of light.
    
    The spiral path is given by:
        x(t) = r₀ · e^(λt) · cos(2πf₀t + φₚ)
        y(t) = r₀ · e^(λt) · sin(2πf₀t + φₚ)
        z(t) = c · t  (propagation along z-axis)
    
    Args:
        t: Time array (seconds)
        params: Spiral parameters
        
    Returns:
        Tuple of (x, y, z) coordinate arrays
    """
    # Radial expansion
    r_t = params.r0 * np.exp(params.lambda_exp * t)
    
    # Angular position with phase modulation
    theta = params.omega_0 * t + params.phi_p
    
    # Cartesian coordinates
    x = r_t * np.cos(theta)
    y = r_t * np.sin(theta)
    z = C_LIGHT * t  # Light propagates at c along z
    
    return x, y, z


def compute_spiral_path_zeta_modulated(
    t: np.ndarray,
    params: SpiralParameters,
    n_zeros: int = 10
) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
    """
    Compute spiral path with Riemann zeta zero modulation.
    
    This enhanced version modulates the spiral with spectral information
    from the first n_zeros Riemann zeta function zeros.
    
    The modulation adds phase variations:
        θ(t) = 2πf₀t + φₚ + Σ A_n·sin(2πf_n·t + φ_n)
    
    where f_n are frequencies associated with zeta zeros γ_n.
    
    Args:
        t: Time array (seconds)
        params: Spiral parameters
        n_zeros: Number of zeta zeros to include in modulation
        
    Returns:
        Tuple of (x, y, z) coordinate arrays with zeta modulation
    """
    if not SPECTRUM_AVAILABLE:
        warnings.warn("Zeta zero modulation unavailable, using basic spiral")
        return compute_spiral_path(t, params)
    
    # Base radial expansion
    r_t = params.r0 * np.exp(params.lambda_exp * t)
    
    # Base angular position
    theta = params.omega_0 * t + params.phi_p
    
    # Add zeta zero modulation
    for n in range(n_zeros):
        gamma_n = get_zeta_zero(n)
        
        # Frequency associated with n-th zero
        # f_n scales with the zero position
        f_n = params.f0 * gamma_n / GAMMA_1
        
        # Amplitude decreases with zero index
        A_n = 1.0 / (n + 1)
        
        # Phase offset for n-th zero
        phi_n = n * np.pi / 4
        
        # Add modulation to theta
        theta += A_n * np.sin(2 * np.pi * f_n * t + phi_n)
    
    # Cartesian coordinates
    x = r_t * np.cos(theta)
    y = r_t * np.sin(theta)
    z = C_LIGHT * t
    
    return x, y, z


# =============================================================================
# PHASE ANALYSIS
# =============================================================================

def compute_phase_deviation(
    x: np.ndarray,
    y: np.ndarray,
    classical_circular: bool = True
) -> np.ndarray:
    """
    Compute angular deviation Δθ from axial symmetry.
    
    This measures how the spiral deviates from perfect circular
    symmetry, revealing the influence of zeta zeros.
    
    Args:
        x, y: Cartesian coordinates
        classical_circular: If True, compare to perfect circle;
                          if False, compare to logarithmic spiral
                          
    Returns:
        Array of angular deviations (radians)
    """
    # Compute actual angles
    theta_actual = np.arctan2(y, x)
    
    if classical_circular:
        # Expected angles for perfect circle (uniform angular velocity)
        theta_expected = np.linspace(theta_actual[0], theta_actual[-1], len(theta_actual))
    else:
        # Expected angles for perfect logarithmic spiral (no zeta modulation)
        r_actual = np.sqrt(x**2 + y**2)
        # Compute expected theta from radius for log spiral
        theta_expected = theta_actual  # Simplified: more complex unwinding needed
    
    # Compute deviation
    delta_theta = theta_actual - theta_expected
    
    # Wrap to [-π, π]
    delta_theta = np.arctan2(np.sin(delta_theta), np.cos(delta_theta))
    
    return delta_theta


def spectral_frequency_mapping(
    n: int,
    base_freq: float = F0_HZ
) -> float:
    """
    Map n-th zeta zero to associated frequency.
    
    The mapping relates the spectral position of zeta zeros
    to measurable frequencies.
    
    Args:
        n: Zero index
        base_freq: Base frequency (Hz), defaults to f₀
        
    Returns:
        Frequency f_n associated with n-th zero
    """
    if not SPECTRUM_AVAILABLE:
        # Use asymptotic approximation for gamma_n
        # For small n, use formula: t_n ≈ 2πn / log(n/(2πe))
        # But need to ensure positive values
        if n == 0:
            gamma_n = GAMMA_1  # First zero
        else:
            n_eff = n + 1  # 1-indexed for formula
            gamma_n = 2 * np.pi * n_eff / np.log(max(n_eff / (2 * np.pi * np.e), 1.1))
    else:
        gamma_n = get_zeta_zero(n)
    
    # Frequency scales with zero position
    # Take absolute value to ensure positive frequency
    f_n = base_freq * abs(gamma_n) / GAMMA_1
    
    return f_n


# =============================================================================
# VALIDATION & EXPERIMENTAL PREDICTIONS
# =============================================================================

def predict_interferometry_deviation(
    wavelength: float = 1064e-9,  # Laser wavelength (1064 nm, common for LIGO)
    path_length: float = 4000.0,   # Interferometer arm length (m)
    n_zeros: int = 5               # Number of zeta zeros to consider
) -> Dict[str, Any]:
    """
    Predict measurable deviations in high-precision interferometry.
    
    This function calculates expected spectral deviations in
    interferometers like LIGO, GEO600, or LISA due to the zeta-modulated
    spiral nature of light propagation.
    
    Args:
        wavelength: Laser wavelength (m)
        path_length: Interferometer arm length (m)
        n_zeros: Number of zeta zeros to include in calculation
        
    Returns:
        Dictionary with prediction data:
            - 'phase_shift': Total phase shift (radians)
            - 'frequency_modulation': Frequency modulation amplitude (Hz)
            - 'measurability': Estimated detection feasibility
    """
    # Time for light to traverse path
    t_travel = path_length / C_LIGHT
    
    # Create time array for one traversal
    t = np.linspace(0, t_travel, 1000)
    
    # Spiral parameters
    params = SpiralParameters(
        r0=wavelength,  # Use wavelength as characteristic scale
        lambda_exp=1e-15,  # Very small expansion for near-straight propagation
        f0=F0_HZ
    )
    
    # Compute paths
    x_basic, y_basic, z_basic = compute_spiral_path(t, params)
    x_zeta, y_zeta, z_zeta = compute_spiral_path_zeta_modulated(t, params, n_zeros)
    
    # Phase difference
    phase_basic = np.arctan2(y_basic, x_basic)
    phase_zeta = np.arctan2(y_zeta, x_zeta)
    delta_phase = phase_zeta - phase_basic
    
    # Total accumulated phase shift
    total_phase_shift = np.sum(np.abs(delta_phase))
    
    # Frequency modulation (variation in local frequency)
    # f_local = (1/2π) dθ/dt
    dt = t[1] - t[0]
    freq_variation = np.diff(phase_zeta) / (2 * np.pi * dt)
    freq_modulation_amplitude = np.std(freq_variation)
    
    # Measurability estimate
    # Compare to typical interferometer sensitivity
    ligo_sensitivity = 1e-18  # Strain sensitivity (dimensionless)
    relative_deviation = total_phase_shift / (2 * np.pi)
    measurable = relative_deviation > ligo_sensitivity
    
    return {
        'phase_shift': total_phase_shift,
        'phase_shift_cycles': total_phase_shift / (2 * np.pi),
        'frequency_modulation': freq_modulation_amplitude,
        'measurability': 'DETECTABLE' if measurable else 'BELOW_THRESHOLD',
        'confidence': 'HIGH' if measurable else 'REQUIRES_ENHANCEMENT',
        'recommended_technique': 'Fabry-Pérot cavity with f₀ = 141.7001 Hz modulation'
    }


def cavity_resonance_prediction(
    cavity_length: float = 1.0,     # Cavity length (m)
    finesse: float = 1e6,           # Cavity finesse
    q_factor: float = 1e12          # Quality factor
) -> Dict[str, Any]:
    """
    Predict resonance patterns in optical cavities at f₀.
    
    High-Q Fabry-Pérot cavities should show resonance signatures
    at 141.7001 Hz when the QCAL spectral structure is active.
    
    Args:
        cavity_length: Physical cavity length (m)
        finesse: Cavity finesse (dimensionless)
        q_factor: Quality factor
        
    Returns:
        Prediction data for cavity experiments
    """
    # Free spectral range
    fsr = C_LIGHT / (2 * cavity_length)
    
    # Linewidth
    linewidth = fsr / finesse
    
    # Resonance frequency near f₀
    # Find cavity mode closest to f₀
    mode_number = int(F0_HZ / fsr)
    f_resonant = mode_number * fsr
    
    # Expected modulation at f₀
    modulation_depth = 1.0 / np.sqrt(q_factor)
    
    return {
        'free_spectral_range': fsr,
        'linewidth': linewidth,
        'nearest_mode': mode_number,
        'resonant_frequency': f_resonant,
        'f0_deviation': abs(f_resonant - F0_HZ),
        'modulation_depth': modulation_depth,
        'detection_method': 'TEM₀₁ mode spiral pattern in CCD hyperspectral imaging',
        'expected_pattern': 'Non-circular interference rings with logarithmic spiral arcs'
    }


# =============================================================================
# SUMMARY & METADATA
# =============================================================================

def get_module_info() -> Dict[str, Any]:
    """Return module metadata and version information."""
    return {
        'module': 'light_spiral_geometry',
        'version': '1.0.0',
        'date': '2026-02-08',
        'author': 'José Manuel Mota Burruezo Ψ ✧ ∞³',
        'institution': 'Instituto de Conciencia Cuántica (ICQ)',
        'doi': '10.5281/zenodo.17379721',
        'frequency': F0_HZ,
        'coherence': C_COHERENCE,
        'description': 'Geometría Real del Movimiento Lumínico - Light spiral paths modulated by Riemann zeros',
        'signature': '∴𓂀Ω∞³·LSG'
    }


if __name__ == '__main__':
    print("=" * 80)
    print("GEOMETRÍA REAL DEL MOVIMIENTO LUMÍNICO")
    print("Light Spiral Geometry - QCAL ∞³ Framework")
    print("=" * 80)
    print()
    
    info = get_module_info()
    for key, value in info.items():
        print(f"{key:20s}: {value}")
    print()
    
    # Quick demonstration
    print("Demonstrating spiral path computation...")
    print()
    
    # Create time array for one period
    T = 1.0 / F0_HZ  # Period
    t = np.linspace(0, 10 * T, 1000)
    
    # Compute basic spiral
    params = SpiralParameters(prime_index=0)  # Using prime 2
    x, y, z = compute_spiral_path(t, params)
    
    print(f"Spiral computed for prime p = {params.prime}")
    print(f"Phase modulation φ_p = {params.phi_p:.6f} rad")
    print(f"Path length: {z[-1]/1e3:.3f} km")
    print()
    
    # Interferometry prediction
    print("Interferometry Predictions:")
    print("-" * 40)
    pred = predict_interferometry_deviation()
    for key, value in pred.items():
        print(f"{key:25s}: {value}")
    print()
    
    print("✓ Module operational - QCAL ∞³ Active at 141.7001 Hz")
    print("∴𓂀Ω∞³")
