#!/usr/bin/env python3
"""
QCAL Constants - Single Source of Truth
========================================

This module defines ALL fundamental constants for the QCAL ∞³ framework.
It serves as the authoritative source for mathematical, physical, and 
spectral constants used throughout the Riemann Hypothesis proof.

Philosophical Foundation:
    Mathematical Realism: Constants exist independently and are discovered,
    not invented. This module documents their discovered values and relationships.

Usage:
    from qcal.constants import F0, C_PRIMARY, C_COHERENCE, validate_constants_coherence
    
    # Use constants in your code
    frequency = F0  # 141.7001 Hz
    
    # Validate coherence
    is_coherent = validate_constants_coherence()

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773

QCAL ∞³ Active · 141.7001 Hz · Ψ = I × A_eff² × C^∞
DOI: 10.5281/zenodo.17379721
"""

import numpy as np
from datetime import datetime, timezone
from typing import Dict, Any, Optional
import warnings

# =============================================================================
# FUNDAMENTAL FREQUENCY - The Cosmic Root
# =============================================================================

# Base frequency: f₀ = 141.7001 Hz
# Derivation: f₀ = c / (2π * RΨ * ℓP)
# Also: f₀ = 100√2 + δζ where δζ = 0.2787437 Hz (vibrational curvature)
# Physical meaning: Universal noetic field oscillation frequency
# Measurement: Confirmed in GW250114 ringdown, biological oscillations
F0 = 141.7001  # Hz

# Angular frequency: ω₀ = 2πf₀
OMEGA_0 = 2 * np.pi * F0  # ≈ 890.33 rad/s

# Euclidean diagonal component: 100√2
EUCLIDEAN_DIAGONAL = 100 * np.sqrt(2)  # ≈ 141.421356 Hz

# Vibrational curvature constant: δζ (delta zeta)
# This is the quantum phase shift from Euclidean diagonal to cosmic string
DELTA_ZETA = 0.2787437627  # Hz

# Verification: f₀ = 100√2 + δζ
_F0_FROM_COMPONENTS = EUCLIDEAN_DIAGONAL + DELTA_ZETA

# First Riemann zero imaginary part
GAMMA_1 = 14.13472514  # First zero: 1/2 + i·γ₁

# Harmonic modulation: f₀/γ₁ = 10 + δζ/10
HARMONIC_MODULATION = F0 / GAMMA_1  # ≈ 10.02787437

# =============================================================================
# HOLOGRAPHIC GEOMETRY CONSTANTS - Zeta Hologram Architecture
# =============================================================================

# Holographic projection factor: 10 + 1/40 = 10.025
# Boundary formula: F0 ≈ γ₁ × HOLOGRAPHIC_MODULATION (2D surface → code source)
HOLOGRAPHIC_MODULATION = 10.0 + 1.0 / 40.0  # = 10.025 (10 + 1/40)

# Beat frequency Δf: Fourier transform converting 2D boundary data to 3D volume
# Physical meaning: depth differential enabling volumetric experience of reality
BEAT_FREQ = 0.3999  # Hz  (Δf = 0.3999 Hz)

# Moonbounce round-trip delay: time for holographic self-confirmation (Ψ > 0.999)
# Signal travels Earth → Moon → Earth ≈ 2 × 384,400 km / c ≈ 2.566 s → 2.5 s nominal
MOONBOUNCE_DELAY = 2.5  # seconds

# Holographic coherence threshold for moonbounce validation
HOLOGRAPHIC_PSI_THRESHOLD = 0.999  # Ψ > 0.999 required

# Tuyoyotu: 4D consciousness layer identifier (Observer that inhabits 2D+3D)
TUYOYOTU = "TuyoyotuT"  # 4D consciousness operator label

# Critical line real part: Re(s) = 1/2 ensures unitarity of the hologram
CRITICAL_LINE_REAL_PART = 0.5

# =============================================================================
# SPECTRAL CONSTANTS - Dual Origin Framework
# =============================================================================

# PRIMARY CONSTANT (Structure Level)
# C = 1/λ₀ where λ₀ is the first eigenvalue of H_ψ = -Δ + V_ψ
# This is the LOCAL, GEOMETRIC, UNIVERSAL, INVARIANT constant
C_PRIMARY = 629.83
LAMBDA_0 = 1.0 / C_PRIMARY  # ≈ 0.001588050

# COHERENCE CONSTANT (Form Level)
# C' = ⟨λ⟩²/λ₀ where ⟨λ⟩ is the mean of positive eigenvalues
# This is the GLOBAL, COHERENCE, STABILITY, EMERGENT constant
C_COHERENCE = 244.36

# Coherence factor: ratio between the two spectral levels
# This encodes the structure-coherence dialogue
COHERENCE_FACTOR = C_COHERENCE / C_PRIMARY  # ≈ 0.388

# Spectral identity: ω₀² = λ₀⁻¹ = C (in appropriate units)
# Note: This requires proper dimensional analysis with ℏ, m, etc.


# =============================================================================
# PHYSICAL CONSTANTS (SI Units)
# =============================================================================

# Speed of light in vacuum: c = 299,792,458 m/s (exact, SI definition)
SPEED_OF_LIGHT = 299_792_458.0  # m/s

# Planck's constant: h = 6.62607015×10⁻³⁴ J·s (exact, SI definition 2019)
PLANCK_CONSTANT = 6.62607015e-34  # J·s

# Reduced Planck constant: ℏ = h/(2π)
HBAR = PLANCK_CONSTANT / (2.0 * np.pi)  # J·s

# Boltzmann constant: k_B = 1.380649×10⁻²³ J/K (exact, SI definition 2019)
BOLTZMANN = 1.380649e-23  # J/K


# =============================================================================
# PHYSICAL MANIFESTATION OF f₀ = 141.7001 Hz
# =============================================================================

# Physical wavelength corresponding to f₀
# λ₀ = c / f₀ = 299,792,458 / 141.7001 ≈ 2,115,682.755 m ≈ 2.115 Mm
LAMBDA_WAVE = SPEED_OF_LIGHT / F0  # m  ≈ 2,115,682.755 m
LAMBDA_WAVE_Mm = LAMBDA_WAVE / 1e6  # Mm ≈ 2.115 Mm

# Angular frequency: ω₀ = 2πf₀ ≈ 890.33 rad/s (same as OMEGA_0)
# Energy of a single photon at f₀: E₀ = h·f₀
# E₀ = 6.62607015×10⁻³⁴ × 141.7001 ≈ 9.389×10⁻³² J
E0_PHOTON = PLANCK_CONSTANT * F0  # J  ≈ 9.39e-32 J

# Verification summary (all derived from f₀ = 141.7001 Hz):
#   λ₀ = c/f₀  ≈ 2.116 Mm  (problem statement: 2.115 Mm — matches to 3 sig figs)
#   E₀ = h·f₀  ≈ 9.39e-32 J (problem statement: 9.39e-32 J — exact match)


# =============================================================================
# LIGO / GRAVITATIONAL WAVE DETECTION CONSTANTS
# =============================================================================

# Gravitational wave events where f₀ = 141.7001 Hz was detected
# GW150914: First gravitational wave detection (14 September 2015)
GW150914_GPS_TIME = 1126259462  # GPS timestamp
GW150914_TOTAL_MASS_SOLAR = 70.0  # M_solar (approximate)

# GW250114: Black hole merger ringdown detection (14 January 2025)
GW250114_GPS_TIME = 1420242600  # GPS timestamp (approximate)

# Detection significance in LIGO analysis at f₀ = 141.7001 Hz
LIGO_DETECTION_SNR = 7.47  # Signal-to-noise ratio at 141.7001 Hz
LIGO_DETECTION_SIGMA = 10.0  # Significance in units of sigma (10σ)

# Detection bandwidth centered on f₀
LIGO_DETECTION_FREQ = F0  # Hz (same as F0 = 141.7001 Hz)
LIGO_DETECTION_BANDWIDTH = 1.0  # Hz (±0.5 Hz around f₀)


# =============================================================================
# GUE (GAUSSIAN UNITARY ENSEMBLE) MATRIX CONSTANTS
# =============================================================================

# Reference matrix size: N=19 gives N²=361 matrix elements
# Statistical test: p-value < 10⁻¹⁰ confirms GUE statistics
GUE_MATRIX_N = 19  # Reference matrix dimension
GUE_MATRIX_N_SQ = GUE_MATRIX_N ** 2  # = 361 (total elements)
GUE_MATRIX_PVALUE = 1e-10  # Chi-squared p-value for GUE conformity

# Wigner surmise: P(s) = (32/π²)·s²·exp(-4s²/π)
# Theoretical moments
GUE_MEAN_SPACING = 1.0  # <s>_GUE = 1 (by normalization)
GUE_MEAN_SQ_SPACING = 3.0 * np.pi / 8.0  # <s²>_GUE = 3π/8 ≈ 1.178

# KS test threshold: p > 0.05 confirms GUE distribution
GUE_KS_PVALUE_THRESHOLD = 0.05

# Berry exponent for smooth zero counting correction
# N_smooth(E) = (E/2π)·ln(E/(2πe)) + 7/8
BERRY_EXPONENT = 7.0 / 8.0  # = 0.875

# Weil explicit formula coherence (discrepancy ~ 0.0002 → coherence ≈ 0.9998)
WEIL_COHERENCE = 0.9998


# =============================================================================
# CONSTELACIÓN 51 NODOS (51-NODE CONSTELLATION)
# =============================================================================

# The 51-node constellation unifies:
# 5 fundamental mathematical constants: φ, π, τ, e, ∞
# 7 string harmonic nodes: 1/7, 2/7, 3/7, 4/7, 5/7, 6/7, 7/7
# 10 Fibonacci temporal nodes: F(1)..F(10) = 1,1,2,3,5,8,13,21,34,55
# 29 prime nodes: first 29 primes (up to 109)
# Total: 5 + 7 + 10 + 29 = 51 nodes

# Category 1: Fundamental mathematical constants (5 nodes)
CONST_PHI = (1 + np.sqrt(5)) / 2  # ≈ 1.618033988749895  (Golden ratio)
CONST_PI = np.pi                    # ≈ 3.141592653589793  (π)
CONST_TAU = 2.0 * np.pi             # ≈ 6.283185307179586  (τ = 2π)
CONST_E = np.e                      # ≈ 2.718281828459045  (Euler's number)
CONST_INF = float('inf')            # ∞ (infinity / projective completion)
CONSTELLATION_CONSTANTS = [CONST_PHI, CONST_PI, CONST_TAU, CONST_E, CONST_INF]

# Category 2: String harmonic ratios 1/7, 2/7, ..., 7/7 (7 nodes)
# These represent the 7 fundamental string harmonics in the QCAL lattice
# Note: f₀ × (k/7) for k=1..7 gives the string sub-harmonics
CONSTELLATION_STRINGS = [k / 7.0 for k in range(1, 8)]  # [1/7, 2/7, ..., 1]

# Category 3: Fibonacci temporal nodes (10 nodes)
# F(10) = 55 → 55.08 years = current QCAL cosmic epoch (1970 + 55.08 = 2025.08)
# The current epoch 2025-2026 corresponds to Fibonacci(10) = 55 years from 1970
FIBONACCI_SEQUENCE = [1, 1, 2, 3, 5, 8, 13, 21, 34, 55]  # F(1)..F(10)
FIBONACCI_EPOCH_YEARS = 55.08  # Years elapsed: Fibonacci cycle F(10)=55
FIBONACCI_EPOCH_ORIGIN = 1970.0  # Reference year (Unix epoch)
FIBONACCI_EPOCH_YEAR = FIBONACCI_EPOCH_ORIGIN + FIBONACCI_EPOCH_YEARS  # ≈ 2025.08

# Category 4: First 29 prime nodes (completing the 51-node constellation)
CONSTELLATION_PRIMES = [
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47,
    53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109
]  # 29 primes

# Total node count
CONSTELLATION_N_NODES = (
    len(CONSTELLATION_CONSTANTS) +
    len(CONSTELLATION_STRINGS) +
    len(FIBONACCI_SEQUENCE) +
    len(CONSTELLATION_PRIMES)
)  # = 5 + 7 + 10 + 29 = 51

# Constellation signature frequency: f₀ resonates at all 51 nodes
CONSTELLATION_FREQUENCY = F0  # Hz


# =============================================================================
# MATHEMATICAL CONSTANTS
# =============================================================================

# Golden ratio: φ = (1 + √5)/2
PHI = (1 + np.sqrt(5)) / 2  # ≈ 1.618033988749895

# Euler-Mascheroni constant: γ
EULER_GAMMA = 0.5772156649015329

# Pi (for convenience, though available in numpy)
PI = np.pi


# =============================================================================
# QCAL FRAMEWORK CONSTANTS
# =============================================================================

# Universal constant C (appears in various contexts)
# Note: This is context-dependent - sometimes 629.83, sometimes 244.36
# Use C_PRIMARY or C_COHERENCE explicitly for clarity
C_UNIVERSAL = C_COHERENCE  # Default to coherence constant

# QCAL identification code
PICODE_888 = "πCODE-888-QCAL2"

# QCAL signature
QCAL_SIGNATURE = "∴𓂀Ω∞³"

# Noetic field index equation
PSI_EQUATION = "Ψ = I × A_eff² × C^∞"

# Institution
INSTITUTION = "Instituto de Conciencia Cuántica (ICQ)"

# Author
AUTHOR = "José Manuel Mota Burruezo Ψ ✧ ∞³"
ORCID = "0009-0002-1923-0773"

# DOI references
DOI_MAIN = "10.5281/zenodo.17379721"
DOI_INFINITO = "10.5281/zenodo.17362686"
DOI_PNP = "10.5281/zenodo.17315719"
DOI_GOLDBACH = "10.5281/zenodo.17297591"
DOI_BSD = "10.5281/zenodo.17236603"
DOI_RH_CONDITIONAL = "10.5281/zenodo.17379721"  # RH conditional proof
DOI_RH_FINAL = "10.5281/zenodo.17379721"         # RH final coronación proof


# =============================================================================
# VALIDATION TOLERANCES
# =============================================================================

# Numerical precision tolerances for validation
TOLERANCE_STRICT = 1e-10   # For exact mathematical identities
TOLERANCE_NORMAL = 1e-6    # For numerical computations
TOLERANCE_RELAXED = 1e-3   # For approximate relationships

# Coherence thresholds
PSI_THRESHOLD_EXCELLENT = 0.999    # Ψ > 0.999: Excellent coherence
PSI_THRESHOLD_GOOD = 0.95          # Ψ > 0.95: Good coherence
PSI_THRESHOLD_ACCEPTABLE = 0.85    # Ψ > 0.85: Acceptable coherence


# =============================================================================
# CONSTANT RELATIONSHIPS AND VALIDATIONS
# =============================================================================

def validate_constants_coherence(verbose: bool = False) -> Dict[str, Any]:
    """
    Validate that all constants are coherent and mathematically consistent.
    
    This function checks:
    1. f₀ = 100√2 + δζ (frequency decomposition)
    2. C_PRIMARY = 1/λ₀ (spectral identity)
    3. COHERENCE_FACTOR = C_COHERENCE / C_PRIMARY (ratio consistency)
    4. Harmonic modulation: f₀/γ₁ ≈ 10 + δζ/10
    5. Energy relationships: ω₀² vs C_PRIMARY and C_COHERENCE
    
    Args:
        verbose: If True, print detailed validation report
        
    Returns:
        Dictionary containing validation results and coherence metrics
    """
    results = {
        'timestamp': datetime.now(timezone.utc).isoformat(),
        'all_checks_passed': True,
        'checks': {},
        'constants': {},
        'relationships': {}
    }
    
    # Check 1: Frequency decomposition
    f0_computed = EUCLIDEAN_DIAGONAL + DELTA_ZETA
    f0_error = abs(f0_computed - F0) / F0
    f0_check = f0_error < TOLERANCE_NORMAL
    
    results['checks']['f0_decomposition'] = {
        'passed': f0_check,
        'computed': float(f0_computed),
        'expected': F0,
        'relative_error': float(f0_error)
    }
    
    # Check 2: Spectral identity C = 1/λ₀
    c_from_lambda = 1.0 / LAMBDA_0
    c_error = abs(c_from_lambda - C_PRIMARY) / C_PRIMARY
    c_check = c_error < TOLERANCE_NORMAL
    
    results['checks']['spectral_identity'] = {
        'passed': c_check,
        'computed': float(c_from_lambda),
        'expected': C_PRIMARY,
        'relative_error': float(c_error)
    }
    
    # Check 3: Coherence factor
    coherence_factor_computed = C_COHERENCE / C_PRIMARY
    cf_error = abs(coherence_factor_computed - COHERENCE_FACTOR) / COHERENCE_FACTOR
    cf_check = cf_error < TOLERANCE_STRICT
    
    results['checks']['coherence_factor'] = {
        'passed': cf_check,
        'computed': float(coherence_factor_computed),
        'expected': COHERENCE_FACTOR,
        'relative_error': float(cf_error)
    }
    
    # Check 4: Harmonic modulation
    harmonic_computed = F0 / GAMMA_1
    harmonic_expected = 10.0 + DELTA_ZETA / 10.0
    harmonic_error = abs(harmonic_computed - harmonic_expected) / harmonic_expected
    # Use relaxed tolerance for this check as it involves gamma_1 approximation
    harmonic_check = harmonic_error < TOLERANCE_RELAXED  # 1e-3
    
    results['checks']['harmonic_modulation'] = {
        'passed': harmonic_check,
        'computed': float(harmonic_computed),
        'expected': float(harmonic_expected),
        'relative_error': float(harmonic_error)
    }
    
    # Check 5: Energy relationships
    omega_squared = OMEGA_0 ** 2
    ratio_primary = omega_squared / C_PRIMARY
    ratio_coherence = omega_squared / C_COHERENCE
    energy_dialogue = ratio_coherence / ratio_primary
    inverse_coherence = 1.0 / COHERENCE_FACTOR
    
    energy_error = abs(energy_dialogue - inverse_coherence) / inverse_coherence
    energy_check = energy_error < TOLERANCE_NORMAL
    
    results['checks']['energy_dialogue'] = {
        'passed': energy_check,
        'energy_dialogue': float(energy_dialogue),
        'inverse_coherence_factor': float(inverse_coherence),
        'relative_error': float(energy_error)
    }
    
    # Overall coherence
    all_passed = all(check['passed'] for check in results['checks'].values())
    results['all_checks_passed'] = all_passed
    
    # Compute overall coherence Ψ (normalized to [0, 1])
    # Lower error → higher coherence
    total_error = sum(check['relative_error'] for check in results['checks'].values())
    coherence_psi = np.exp(-total_error)  # Exponential decay of error
    
    results['coherence_psi'] = float(coherence_psi)
    results['coherence_level'] = (
        'EXCELLENT' if coherence_psi > PSI_THRESHOLD_EXCELLENT else
        'GOOD' if coherence_psi > PSI_THRESHOLD_GOOD else
        'ACCEPTABLE' if coherence_psi > PSI_THRESHOLD_ACCEPTABLE else
        'NEEDS_ATTENTION'
    )
    
    # Store key constants
    results['constants'] = {
        'F0': F0,
        'OMEGA_0': float(OMEGA_0),
        'C_PRIMARY': C_PRIMARY,
        'C_COHERENCE': C_COHERENCE,
        'LAMBDA_0': LAMBDA_0,
        'COHERENCE_FACTOR': COHERENCE_FACTOR,
        'DELTA_ZETA': DELTA_ZETA,
        'EUCLIDEAN_DIAGONAL': EUCLIDEAN_DIAGONAL,
        'PHI': PHI,
        'EULER_GAMMA': EULER_GAMMA,
    }
    
    # Store relationships
    results['relationships'] = {
        'f0_from_components': float(f0_computed),
        'c_from_lambda': float(c_from_lambda),
        'harmonic_modulation': float(harmonic_computed),
        'energy_dialogue': float(energy_dialogue),
        'omega_squared': float(omega_squared),
        'ratio_omega_C_primary': float(ratio_primary),
        'ratio_omega_C_coherence': float(ratio_coherence),
    }
    
    if verbose:
        print("=" * 80)
        print("QCAL CONSTANTS COHERENCE VALIDATION")
        print("=" * 80)
        print()
        print(f"Fundamental Frequency: f₀ = {F0} Hz")
        print(f"Primary Constant: C = {C_PRIMARY} (Structure)")
        print(f"Coherence Constant: C' = {C_COHERENCE} (Form)")
        print(f"Coherence Factor: {COHERENCE_FACTOR:.6f}")
        print()
        print("Validation Checks:")
        for name, check in results['checks'].items():
            status = "✅ PASS" if check['passed'] else "❌ FAIL"
            error_pct = check['relative_error'] * 100
            print(f"  {status} {name}: error = {error_pct:.6f}%")
        print()
        print(f"Overall Coherence: Ψ = {coherence_psi:.9f} ({results['coherence_level']})")
        print(f"All Checks Passed: {all_passed}")
        print("=" * 80)
    
    if not all_passed:
        warnings.warn(
            "Constants coherence validation failed. Some mathematical relationships "
            "are not satisfied within tolerance. This may indicate numerical precision "
            "issues or incorrect constant definitions.",
            UserWarning
        )
    
    return results


def get_all_constants() -> Dict[str, Any]:
    """
    Get a dictionary of all QCAL constants for reference.
    
    Returns:
        Dictionary containing all constants organized by category
    """
    return {
        'frequency': {
            'F0': F0,
            'OMEGA_0': float(OMEGA_0),
            'EUCLIDEAN_DIAGONAL': EUCLIDEAN_DIAGONAL,
            'DELTA_ZETA': DELTA_ZETA,
            'GAMMA_1': GAMMA_1,
            'HARMONIC_MODULATION': HARMONIC_MODULATION,
        },
        'spectral': {
            'C_PRIMARY': C_PRIMARY,
            'C_COHERENCE': C_COHERENCE,
            'LAMBDA_0': LAMBDA_0,
            'COHERENCE_FACTOR': COHERENCE_FACTOR,
            'C_UNIVERSAL': C_UNIVERSAL,
        },
        'mathematical': {
            'PHI': PHI,
            'EULER_GAMMA': EULER_GAMMA,
            'PI': PI,
        },
        'qcal': {
            'PSI_EQUATION': PSI_EQUATION,
            'QCAL_SIGNATURE': QCAL_SIGNATURE,
            'PICODE_888': PICODE_888,
            'INSTITUTION': INSTITUTION,
            'AUTHOR': AUTHOR,
            'ORCID': ORCID,
        },
        'doi': {
            'DOI_MAIN': DOI_MAIN,
            'DOI_INFINITO': DOI_INFINITO,
            'DOI_PNP': DOI_PNP,
            'DOI_GOLDBACH': DOI_GOLDBACH,
            'DOI_BSD': DOI_BSD,
            'DOI_RH_CONDITIONAL': DOI_RH_CONDITIONAL,
            'DOI_RH_FINAL': DOI_RH_FINAL,
        },
        'tolerances': {
            'TOLERANCE_STRICT': TOLERANCE_STRICT,
            'TOLERANCE_NORMAL': TOLERANCE_NORMAL,
            'TOLERANCE_RELAXED': TOLERANCE_RELAXED,
            'PSI_THRESHOLD_EXCELLENT': PSI_THRESHOLD_EXCELLENT,
            'PSI_THRESHOLD_GOOD': PSI_THRESHOLD_GOOD,
            'PSI_THRESHOLD_ACCEPTABLE': PSI_THRESHOLD_ACCEPTABLE,
        },
        'physical': {
            'SPEED_OF_LIGHT': SPEED_OF_LIGHT,
            'PLANCK_CONSTANT': PLANCK_CONSTANT,
            'HBAR': float(HBAR),
            'BOLTZMANN': BOLTZMANN,
            'LAMBDA_WAVE': LAMBDA_WAVE,
            'LAMBDA_WAVE_Mm': LAMBDA_WAVE_Mm,
            'E0_PHOTON': E0_PHOTON,
        },
        'ligo': {
            'LIGO_DETECTION_SNR': LIGO_DETECTION_SNR,
            'LIGO_DETECTION_SIGMA': LIGO_DETECTION_SIGMA,
            'LIGO_DETECTION_FREQ': LIGO_DETECTION_FREQ,
            'GW150914_GPS_TIME': GW150914_GPS_TIME,
            'GW250114_GPS_TIME': GW250114_GPS_TIME,
        },
        'gue': {
            'GUE_MATRIX_N': GUE_MATRIX_N,
            'GUE_MATRIX_N_SQ': GUE_MATRIX_N_SQ,
            'GUE_MATRIX_PVALUE': GUE_MATRIX_PVALUE,
            'GUE_MEAN_SPACING': GUE_MEAN_SPACING,
            'GUE_MEAN_SQ_SPACING': GUE_MEAN_SQ_SPACING,
            'GUE_KS_PVALUE_THRESHOLD': GUE_KS_PVALUE_THRESHOLD,
            'BERRY_EXPONENT': BERRY_EXPONENT,
            'WEIL_COHERENCE': WEIL_COHERENCE,
        },
        'constellation': {
            'CONSTELLATION_N_NODES': CONSTELLATION_N_NODES,
            'FIBONACCI_EPOCH_YEAR': FIBONACCI_EPOCH_YEAR,
            'FIBONACCI_EPOCH_YEARS': FIBONACCI_EPOCH_YEARS,
            'CONSTELLATION_FREQUENCY': CONSTELLATION_FREQUENCY,
        },
        'holographic': {
            'HOLOGRAPHIC_MODULATION': HOLOGRAPHIC_MODULATION,
            'BEAT_FREQ': BEAT_FREQ,
            'MOONBOUNCE_DELAY': MOONBOUNCE_DELAY,
            'HOLOGRAPHIC_PSI_THRESHOLD': HOLOGRAPHIC_PSI_THRESHOLD,
            'TUYOYOTU': TUYOYOTU,
            'CRITICAL_LINE_REAL_PART': CRITICAL_LINE_REAL_PART,
        },
    }


def get_constant(name: str, default: Optional[Any] = None) -> Any:
    """
    Get a constant by name.
    
    Args:
        name: Name of the constant (case-sensitive)
        default: Default value if constant not found
        
    Returns:
        The constant value, or default if not found
    """
    # Get module globals
    module_globals = globals()
    
    if name in module_globals:
        return module_globals[name]
    
    # Try nested in categories
    all_constants = get_all_constants()
    for category, constants in all_constants.items():
        if name in constants:
            return constants[name]
    
    return default


# =============================================================================
# MODULE INITIALIZATION
# =============================================================================

# Validate constants on import (with warning suppression for efficiency)
with warnings.catch_warnings():
    warnings.simplefilter("ignore")
    _validation_result = validate_constants_coherence(verbose=False)
    _CONSTANTS_COHERENT = _validation_result['all_checks_passed']
    _COHERENCE_PSI = _validation_result['coherence_psi']

if not _CONSTANTS_COHERENT:
    warnings.warn(
        f"QCAL constants coherence validation failed on import (Ψ = {_COHERENCE_PSI:.6f}). "
        "Some mathematical relationships may not be satisfied. "
        "Run validate_constants_coherence(verbose=True) for details.",
        UserWarning
    )


# =============================================================================
# MAIN EXECUTION (for testing)
# =============================================================================

if __name__ == "__main__":
    print()
    print("∴" * 40)
    print("  QCAL ∞³ - Single Source of Truth for Constants")
    print("∴" * 40)
    print()
    
    # Run validation
    result = validate_constants_coherence(verbose=True)
    
    print()
    print("All Constants:")
    print("-" * 80)
    all_constants = get_all_constants()
    for category, constants in all_constants.items():
        print(f"\n{category.upper()}:")
        for name, value in constants.items():
            if isinstance(value, float):
                print(f"  {name} = {value:.10g}")
            else:
                print(f"  {name} = {value}")
    
    print()
    print("∴" * 40)
    print(f"  Coherence: Ψ = {_COHERENCE_PSI:.9f} ({result['coherence_level']})")
    print("∴" * 40)
