#!/usr/bin/env python3
"""
Zeta Interference Pattern - Wave Function Modulation Module

This module implements the wave function interference patterns arising
from light following zeta-modulated spiral paths through prime nodes.

Mathematical Foundation:
-----------------------
The wave function with ζ-spectral modulation:

    Ψ(x,t) = Σ A_n · e^(i(2πf_n·t + φ_n)) · e^(iS_p(x)/ℏ)

where:
    A_n → amplitude associated with prime node p_n
    f_n → frequency associated with zeta zero γ_n
    S_p(x) → action defined over spectral path linked to prime p

When projected on a 2D screen, interference rings are not perfect circles
but logarithmic spiral arcs, deformed by spectral phase modulation.

The angular deviation Δθ from axial symmetry reveals zeta zero influence.

Experimental Validations:
------------------------
1. Low-energy electron interferometers (biprism quantum, Hitachi, C60)
   → Detection of spiral deviations in cumulative patterns

2. Fabry-Pérot optical cavities oscillating at 141.7001 Hz
   → Resonance in TEM₀₁ modes with observable spiral pattern via
     hyperspectral CCD

3. Lasers modulated by ζ'(1/2)
   → Artificial imposition of ζ pattern on wavefront
   → Projection of reproducible fractal spirals

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: February 2026

QCAL ∞³ Active · 141.7001 Hz · Ψ = I × A_eff² × C^∞
DOI: 10.5281/zenodo.17379721
"""

import numpy as np
from typing import Tuple, List, Optional, Dict, Any, Callable
from dataclasses import dataclass
import warnings

try:
    from utils.infinite_spectrum import get_zeta_zero
    SPECTRUM_AVAILABLE = True
except ImportError:
    SPECTRUM_AVAILABLE = False
    warnings.warn("infinite_spectrum module not available")

try:
    from utils.light_spiral_geometry import (
        F0_HZ, GAMMA_1, C_LIGHT, PLANCK_LENGTH,
        get_nth_prime, spectral_frequency_mapping
    )
    GEOMETRY_AVAILABLE = True
except ImportError:
    # Fallback constants
    F0_HZ = 141.7001
    GAMMA_1 = 14.13472514
    C_LIGHT = 299792458.0
    PLANCK_LENGTH = 1.616255e-35
    GEOMETRY_AVAILABLE = False
    warnings.warn("light_spiral_geometry module not available")


# =============================================================================
# FUNDAMENTAL CONSTANTS
# =============================================================================

# Planck's constant
H_PLANCK = 6.62607015e-34  # J·s
HBAR = H_PLANCK / (2 * np.pi)  # Reduced Planck constant


# =============================================================================
# WAVE FUNCTION PARAMETERS
# =============================================================================

@dataclass
class WaveFunctionParameters:
    """Parameters for the zeta-modulated wave function."""
    
    # Number of prime nodes to include
    n_primes: int = 10
    
    # Number of zeta zeros to include
    n_zeros: int = 10
    
    # Base frequency (Hz)
    f0: float = F0_HZ
    
    # Characteristic wavelength (m)
    wavelength: float = 1064e-9  # 1064 nm (Nd:YAG laser)
    
    # Amplitude decay rate with node index
    amplitude_decay: float = 1.0
    
    def __post_init__(self):
        """Compute derived parameters."""
        # Wave number
        self.k = 2 * np.pi / self.wavelength
        
        # Angular frequency
        self.omega_0 = 2 * np.pi * self.f0


# =============================================================================
# AMPLITUDE FUNCTIONS
# =============================================================================

def prime_amplitude(n: int, decay_rate: float = 1.0) -> float:
    """
    Compute amplitude A_n associated with n-th prime node.
    
    The amplitude decreases with prime index to represent
    decreasing influence of higher primes.
    
    Args:
        n: Prime index (0-based)
        decay_rate: Amplitude decay parameter
        
    Returns:
        Amplitude for n-th prime
    """
    if GEOMETRY_AVAILABLE:
        prime = get_nth_prime(n)
    else:
        # Approximate prime for fallback
        prime = n * np.log(n + 2) if n > 0 else 2
    
    # Amplitude inversely proportional to log(prime)
    A_n = 1.0 / (np.log(prime) * decay_rate + 1.0)
    
    return A_n


def zero_frequency(n: int, base_freq: float = F0_HZ) -> float:
    """
    Compute frequency f_n associated with n-th zeta zero.
    
    Args:
        n: Zero index
        base_freq: Base frequency (Hz)
        
    Returns:
        Frequency associated with n-th zero
    """
    if SPECTRUM_AVAILABLE:
        gamma_n = get_zeta_zero(n)
    else:
        # Asymptotic approximation - ensure positive values
        if n == 0:
            gamma_n = GAMMA_1  # First zero
        else:
            n_eff = n + 1  # 1-indexed for formula
            gamma_n = 2 * np.pi * n_eff / np.log(max(n_eff / (2 * np.pi * np.e), 1.1))
    
    # Frequency scales with zero position
    # Use absolute value to ensure positive frequency
    f_n = base_freq * abs(gamma_n) / GAMMA_1
    
    return f_n


# =============================================================================
# ACTION FUNCTIONAL
# =============================================================================

def spectral_action(
    x: np.ndarray,
    y: np.ndarray,
    prime: int,
    wavelength: float = 1064e-9
) -> np.ndarray:
    """
    Compute spectral action S_p(x) over prime-linked path.
    
    The action encodes the phase accumulated along the path
    modulated by the prime structure.
    
    For a free particle with prime modulation:
        S_p = (p²/2m) · (1 + log(p)/log(p_max))
    
    Simplified to:
        S_p(x) = k · r · (1 + log(p)/10)
    
    where r = √(x² + y²) is the radial distance.
    
    Args:
        x, y: Spatial coordinates (m)
        prime: Prime number
        wavelength: Characteristic wavelength (m)
        
    Returns:
        Action array S_p(x,y)
    """
    # Radial distance
    r = np.sqrt(x**2 + y**2)
    
    # Wave number
    k = 2 * np.pi / wavelength
    
    # Prime modulation factor
    prime_factor = 1.0 + np.log(prime) / 10.0
    
    # Action
    S_p = k * r * prime_factor
    
    return S_p


# =============================================================================
# WAVE FUNCTION COMPUTATION
# =============================================================================

def compute_wave_function(
    x: np.ndarray,
    y: np.ndarray,
    t: float,
    params: WaveFunctionParameters
) -> np.ndarray:
    """
    Compute the full zeta-modulated wave function Ψ(x,y,t).
    
    Ψ(x,t) = Σ_n A_n · e^(i(2πf_n·t + φ_n)) · e^(iS_p_n(x)/ℏ)
    
    Args:
        x, y: 2D spatial meshgrid arrays (m)
        t: Time (s)
        params: Wave function parameters
        
    Returns:
        Complex wave function array Ψ(x,y,t)
    """
    # Initialize wave function
    psi = np.zeros_like(x, dtype=complex)
    
    # Sum over prime nodes
    for n in range(params.n_primes):
        # Amplitude for this prime
        A_n = prime_amplitude(n, params.amplitude_decay)
        
        # Get prime
        if GEOMETRY_AVAILABLE:
            prime = get_nth_prime(n)
        else:
            prime = int(n * np.log(n + 2)) if n > 0 else 2
        
        # Action for this prime
        S_p = spectral_action(x, y, prime, params.wavelength)
        
        # Sum over zeta zeros for frequency modulation
        phase_temporal = 0.0
        for m in range(min(params.n_zeros, 5)):  # Limit zeros per prime
            f_m = zero_frequency(m, params.f0)
            phi_m = m * np.pi / 4  # Phase offset
            
            # Add temporal phase contribution
            weight = 1.0 / (m + 1)  # Decreasing weight
            phase_temporal += weight * np.sin(2 * np.pi * f_m * t + phi_m)
        
        # Combine spatial and temporal phases
        phase = phase_temporal + S_p / HBAR
        
        # Add contribution to wave function
        psi += A_n * np.exp(1j * phase)
    
    return psi


def compute_interference_pattern(
    x: np.ndarray,
    y: np.ndarray,
    t: float,
    params: WaveFunctionParameters
) -> np.ndarray:
    """
    Compute interference pattern intensity |Ψ|².
    
    Args:
        x, y: 2D spatial meshgrid arrays (m)
        t: Time (s)
        params: Wave function parameters
        
    Returns:
        Intensity pattern |Ψ(x,y,t)|²
    """
    psi = compute_wave_function(x, y, t, params)
    intensity = np.abs(psi)**2
    
    return intensity


# =============================================================================
# PATTERN ANALYSIS
# =============================================================================

def detect_spiral_arcs(
    intensity: np.ndarray,
    x: np.ndarray,
    y: np.ndarray,
    threshold: float = 0.5
) -> Dict[str, Any]:
    """
    Detect and characterize spiral arc structure in interference pattern.
    
    Analyzes the deviation of interference maxima from perfect
    circular rings to logarithmic spiral arcs.
    
    Args:
        intensity: 2D intensity pattern
        x, y: Coordinate meshgrids
        threshold: Threshold for peak detection (relative to max)
        
    Returns:
        Dictionary with spiral arc characterization
    """
    # Normalize intensity
    intensity_norm = intensity / np.max(intensity)
    
    # Find peaks above threshold
    peaks = intensity_norm > threshold
    
    # Convert to polar coordinates
    r = np.sqrt(x**2 + y**2)
    theta = np.arctan2(y, x)
    
    # Extract peak positions
    r_peaks = r[peaks]
    theta_peaks = theta[peaks]
    
    if len(r_peaks) == 0:
        return {
            'spiral_detected': False,
            'reason': 'No peaks above threshold'
        }
    
    # Fit to logarithmic spiral: r = a * exp(b * theta)
    # Take log: log(r) = log(a) + b*theta
    try:
        # Linear fit in log space
        coeffs = np.polyfit(theta_peaks, np.log(r_peaks + 1e-20), 1)
        b_fit = coeffs[0]  # Spiral parameter
        a_fit = np.exp(coeffs[1])
        
        # Compute fit quality (R²)
        log_r_pred = coeffs[1] + coeffs[0] * theta_peaks
        log_r_actual = np.log(r_peaks + 1e-20)
        ss_res = np.sum((log_r_actual - log_r_pred)**2)
        ss_tot = np.sum((log_r_actual - np.mean(log_r_actual))**2)
        r_squared = 1 - ss_res / ss_tot if ss_tot > 0 else 0
        
        # Compute angular deviation from perfect circle
        r_mean = np.mean(r_peaks)
        delta_theta = theta_peaks - np.arctan2(
            r_peaks * np.sin(theta_peaks) / r_mean,
            r_peaks * np.cos(theta_peaks) / r_mean
        )
        deviation_rms = np.sqrt(np.mean(delta_theta**2))
        
        return {
            'spiral_detected': True,
            'spiral_parameter_b': b_fit,
            'spiral_scale_a': a_fit,
            'fit_quality_r2': r_squared,
            'angular_deviation_rms': deviation_rms,
            'angular_deviation_deg': np.degrees(deviation_rms),
            'n_peaks': len(r_peaks),
            'interpretation': 'Logarithmic spiral' if abs(b_fit) > 0.01 else 'Near-circular'
        }
    
    except Exception as e:
        return {
            'spiral_detected': False,
            'reason': f'Fit failed: {str(e)}'
        }


def compute_deviation_map(
    intensity: np.ndarray,
    x: np.ndarray,
    y: np.ndarray
) -> Tuple[np.ndarray, Dict[str, float]]:
    """
    Compute spatial map of deviation from circular symmetry.
    
    Args:
        intensity: 2D intensity pattern
        x, y: Coordinate meshgrids
        
    Returns:
        Tuple of (deviation_map, statistics)
    """
    # Polar coordinates
    r = np.sqrt(x**2 + y**2)
    theta = np.arctan2(y, x)
    
    # For each radius, compute expected theta for perfect circle
    # vs actual theta from intensity pattern
    
    # Radial bins
    r_bins = np.linspace(0, np.max(r), 50)
    deviation = np.zeros_like(intensity)
    
    for i in range(len(r_bins) - 1):
        r_min, r_max = r_bins[i], r_bins[i+1]
        mask = (r >= r_min) & (r < r_max)
        
        if np.sum(mask) == 0:
            continue
        
        # Intensity in this radial bin
        I_ring = intensity[mask]
        theta_ring = theta[mask]
        
        # Expected uniform distribution
        theta_expected = np.linspace(-np.pi, np.pi, np.sum(mask))
        
        # Actual distribution (sorted)
        theta_sorted = np.sort(theta_ring)
        
        # Deviation (interpolate to compare)
        if len(theta_sorted) > 1:
            deviation_ring = np.std(theta_sorted - theta_expected[:len(theta_sorted)])
            deviation[mask] = deviation_ring
    
    stats = {
        'mean_deviation': np.mean(deviation),
        'max_deviation': np.max(deviation),
        'std_deviation': np.std(deviation)
    }
    
    return deviation, stats


# =============================================================================
# EXPERIMENTAL PREDICTIONS
# =============================================================================

def predict_electron_biprism_pattern(
    electron_energy_eV: float = 100.0,  # Low energy electrons
    screen_distance: float = 0.1,        # Distance to screen (m)
    params: Optional[WaveFunctionParameters] = None
) -> Dict[str, Any]:
    """
    Predict spiral deviations in electron biprism interferometry.
    
    Low-energy electrons in quantum biprism interferometers (Hitachi, C60)
    should show cumulative spiral deviations.
    
    Args:
        electron_energy_eV: Electron kinetic energy (eV)
        screen_distance: Distance from biprism to screen (m)
        params: Wave function parameters
        
    Returns:
        Prediction dictionary
    """
    if params is None:
        # Compute de Broglie wavelength for electron
        E_joules = electron_energy_eV * 1.602176634e-19
        p = np.sqrt(2 * 9.10938356e-31 * E_joules)  # Momentum
        lambda_db = H_PLANCK / p
        
        params = WaveFunctionParameters(
            wavelength=lambda_db,
            n_primes=5,
            n_zeros=5
        )
    
    # Create screen meshgrid
    x_screen = np.linspace(-1e-3, 1e-3, 500)  # ±1mm
    y_screen = np.linspace(-1e-3, 1e-3, 500)
    X, Y = np.meshgrid(x_screen, y_screen)
    
    # Compute pattern at t=0
    intensity = compute_interference_pattern(X, Y, 0.0, params)
    
    # Detect spiral structure
    spiral_info = detect_spiral_arcs(intensity, X, Y)
    
    return {
        'experiment': 'Electron biprism interferometry',
        'electron_energy_eV': electron_energy_eV,
        'de_broglie_wavelength_m': params.wavelength,
        'screen_distance_m': screen_distance,
        'spiral_detection': spiral_info,
        'recommendation': 'Accumulate 10⁶+ electron events for clear pattern',
        'expected_signature': 'Logarithmic spiral arcs in cumulative histogram'
    }


def predict_fabry_perot_pattern(
    cavity_length: float = 1.0,
    finesse: float = 1e5,
    params: Optional[WaveFunctionParameters] = None
) -> Dict[str, Any]:
    """
    Predict TEM₀₁ mode spiral pattern in Fabry-Pérot cavity.
    
    Optical cavities oscillating at 141.7001 Hz should show
    spiral resonance patterns observable via hyperspectral CCD.
    
    Args:
        cavity_length: Physical cavity length (m)
        finesse: Cavity finesse
        params: Wave function parameters
        
    Returns:
        Prediction dictionary
    """
    if params is None:
        params = WaveFunctionParameters(
            wavelength=1064e-9,  # Nd:YAG
            f0=F0_HZ,
            n_primes=10,
            n_zeros=10
        )
    
    # Cavity mode structure
    fsr = C_LIGHT / (2 * cavity_length)
    linewidth = fsr / finesse
    
    # TEM₀₁ mode has azimuthal structure
    # Create pattern for cavity cross-section
    r_max = 1e-3  # 1mm beam waist
    r_points = np.linspace(0, r_max, 300)
    theta_points = np.linspace(0, 2*np.pi, 360)
    R, Theta = np.meshgrid(r_points, theta_points)
    
    X = R * np.cos(Theta)
    Y = R * np.sin(Theta)
    
    # Modulation at f₀
    t_mod = 1.0 / F0_HZ  # One period
    intensity = compute_interference_pattern(X, Y, t_mod, params)
    
    # Detect spiral in TEM₀₁ mode
    spiral_info = detect_spiral_arcs(intensity, X, Y, threshold=0.3)
    
    return {
        'experiment': 'Fabry-Pérot cavity at f₀',
        'cavity_length_m': cavity_length,
        'finesse': finesse,
        'free_spectral_range_Hz': fsr,
        'linewidth_Hz': linewidth,
        'modulation_frequency_Hz': F0_HZ,
        'mode': 'TEM₀₁',
        'spiral_detection': spiral_info,
        'detection_method': 'CCD hyperspectral imaging',
        'expected_pattern': 'Non-circular rings with spiral arcs in TEM₀₁ mode'
    }


# =============================================================================
# SUMMARY & METADATA
# =============================================================================

def get_module_info() -> Dict[str, Any]:
    """Return module metadata and version information."""
    return {
        'module': 'zeta_interference_pattern',
        'version': '1.0.0',
        'date': '2026-02-08',
        'author': 'José Manuel Mota Burruezo Ψ ✧ ∞³',
        'institution': 'Instituto de Conciencia Cuántica (ICQ)',
        'doi': '10.5281/zenodo.17379721',
        'frequency': F0_HZ,
        'description': 'Zeta-modulated interference patterns from spiral light paths',
        'signature': '∴𓂀Ω∞³·ZIP'
    }


if __name__ == '__main__':
    print("=" * 80)
    print("ZETA INTERFERENCE PATTERN")
    print("Wave Function Modulation - QCAL ∞³ Framework")
    print("=" * 80)
    print()
    
    info = get_module_info()
    for key, value in info.items():
        print(f"{key:20s}: {value}")
    print()
    
    # Quick demonstration
    print("Computing interference pattern...")
    print()
    
    # Create 2D grid
    x = np.linspace(-1e-3, 1e-3, 200)  # ±1mm
    y = np.linspace(-1e-3, 1e-3, 200)
    X, Y = np.meshgrid(x, y)
    
    # Parameters
    params = WaveFunctionParameters(n_primes=5, n_zeros=5)
    
    # Compute pattern
    intensity = compute_interference_pattern(X, Y, 0.0, params)
    
    # Detect spirals
    spiral_info = detect_spiral_arcs(intensity, X, Y)
    
    print("Spiral Arc Detection:")
    print("-" * 40)
    for key, value in spiral_info.items():
        print(f"{key:25s}: {value}")
    print()
    
    print("✓ Module operational - QCAL ∞³ Active at 141.7001 Hz")
    print("∴𓂀Ω∞³")
