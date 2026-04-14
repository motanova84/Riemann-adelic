#!/usr/bin/env python3
"""
Tests for Spectral Coordinates Module - QCAL ∞³

This module tests the spectral coordinates τ(p) implementation that maps
prime numbers to complex spectral time.

Key tests validate:
    1. τ(p) computation accuracy
    2. Monotonicity property: Re(τ(p₁)) < Re(τ(p₂)) if p₁ < p₂
    3. Constant imaginary part: Im(τ(p)) = γ₁/(2πf₀) for all p
    4. Standard examples match problem statement
    5. Batch computations work correctly

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: February 2026

QCAL ∞³ Active · 141.7001 Hz
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add root to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from operators.spectral_coordinates import (
    # Constants
    F0,
    GAMMA_1,
    TAU_IMAGINARY_CONSTANT,
    TWO_PI_F0,
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


# =============================================================================
# CONSTANT TESTS
# =============================================================================

def test_fundamental_constants():
    """Test that fundamental constants have correct values."""
    assert F0 == 141.7001, "Base frequency should be 141.7001 Hz"
    assert GAMMA_1 == 14.134725, "First Riemann zero should be 14.134725"
    
    # Check derived constants
    expected_2pi_f0 = 2 * np.pi * F0
    assert abs(TWO_PI_F0 - expected_2pi_f0) < 1e-10
    
    expected_tau_imag = GAMMA_1 / (2 * np.pi * F0)
    assert abs(TAU_IMAGINARY_CONSTANT - expected_tau_imag) < 1e-10


def test_imaginary_constant_value():
    """Test that the universal imaginary part has the expected value."""
    # From problem statement: Im(τ) ≈ 0.0159
    tau_imag = compute_tau_imaginary()
    assert abs(tau_imag - 0.0159) < 0.001, \
        f"Universal imaginary part should be ≈ 0.0159, got {tau_imag}"


# =============================================================================
# BASIC COMPUTATION TESTS
# =============================================================================

def test_compute_tau_basic():
    """Test basic spectral coordinate computation."""
    # Test prime 3
    tau_3 = compute_tau(3)
    assert isinstance(tau_3, complex)
    assert tau_3.real > 0
    assert tau_3.imag > 0
    
    # Test prime 5
    tau_5 = compute_tau(5)
    assert tau_5.real > tau_3.real, "tau(5) real part should be > tau(3) real part"
    assert abs(tau_5.imag - tau_3.imag) < 1e-10, "Imaginary parts should be equal"


def test_compute_tau_invalid_input():
    """Test that invalid inputs raise appropriate errors."""
    with pytest.raises(ValueError):
        compute_tau(0)
    
    with pytest.raises(ValueError):
        compute_tau(-5)


def test_compute_tau_real():
    """Test computation of real part only."""
    p = 7
    tau = compute_tau(p)
    tau_real = compute_tau_real(p)
    
    assert abs(tau.real - tau_real) < 1e-10
    
    # Test formula: Re(τ) = log(p)/f₀
    expected = np.log(p) / F0
    assert abs(tau_real - expected) < 1e-10


def test_compute_tau_imaginary():
    """Test that imaginary part function returns constant."""
    tau_imag = compute_tau_imaginary()
    
    # Should be the same for all primes
    assert tau_imag == TAU_IMAGINARY_CONSTANT
    
    # Check against formula
    expected = GAMMA_1 / TWO_PI_F0
    assert abs(tau_imag - expected) < 1e-10


# =============================================================================
# BATCH COMPUTATION TESTS
# =============================================================================

def test_compute_tau_batch():
    """Test batch computation of spectral coordinates."""
    primes = [3, 5, 7, 11, 13]
    taus = compute_tau_batch(primes)
    
    assert len(taus) == len(primes)
    assert isinstance(taus, np.ndarray)
    
    # Verify each value
    for i, p in enumerate(primes):
        expected = compute_tau(p)
        assert abs(taus[i] - expected) < 1e-10


def test_compute_tau_dictionary():
    """Test dictionary computation of spectral coordinates."""
    primes = [3, 5, 7]
    tau_dict = compute_tau_dictionary(primes)
    
    assert len(tau_dict) == len(primes)
    
    for p in primes:
        assert p in tau_dict
        expected = compute_tau(p)
        assert abs(tau_dict[p] - expected) < 1e-10


# =============================================================================
# PROPERTY VERIFICATION TESTS
# =============================================================================

def test_monotonicity_property():
    """Test monotonicity property: Re(τ(p₁)) < Re(τ(p₂)) if p₁ < p₂."""
    # Test with standard examples
    assert verify_monotonicity([3, 5, 7, 17])
    
    # Test with extended list
    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
    assert verify_monotonicity(primes)
    
    # Test with single prime (should return True)
    assert verify_monotonicity([7])
    
    # Test with reversed list (should fail)
    assert not verify_monotonicity([17, 7, 5, 3])


def test_constant_imaginary_property():
    """Test that all spectral coordinates have the same imaginary part."""
    # Test with standard examples
    assert verify_constant_imaginary([3, 5, 7, 17])
    
    # Test with larger list
    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]
    assert verify_constant_imaginary(primes)
    
    # Verify actual values
    taus = compute_tau_batch(primes)
    imaginary_parts = np.imag(taus)
    
    # All should be very close to TAU_IMAGINARY_CONSTANT
    for imag_part in imaginary_parts:
        assert abs(imag_part - TAU_IMAGINARY_CONSTANT) < 1e-10


def test_real_parts_strictly_increasing():
    """Test that real parts are strictly increasing with prime order."""
    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
    taus = compute_tau_batch(primes)
    real_parts = np.real(taus)
    
    # Check strict monotonicity
    for i in range(len(real_parts) - 1):
        assert real_parts[i] < real_parts[i + 1], \
            f"Real parts not strictly increasing: {real_parts[i]} >= {real_parts[i+1]}"


# =============================================================================
# STANDARD EXAMPLES TESTS
# =============================================================================

def test_standard_examples():
    """Test standard examples from problem statement."""
    examples = get_standard_examples()
    
    # Should have 4 standard examples
    assert len(examples) == 4
    assert 3 in examples
    assert 5 in examples
    assert 7 in examples
    assert 17 in examples
    
    # Check structure
    for p in [3, 5, 7, 17]:
        assert 'prime' in examples[p]
        assert 'tau' in examples[p]
        assert 'real' in examples[p]
        assert 'imaginary' in examples[p]
        assert 'interpretation' in examples[p]
        assert examples[p]['prime'] == p


def test_standard_example_values():
    """Test that standard examples follow the mathematical formula correctly."""
    examples = get_standard_examples()
    
    tolerance = 1e-10  # Strict numerical tolerance for formula validation
    
    for p in [3, 5, 7, 17]:
        computed = examples[p]
        
        # Check formula: Re(τ) = log(p)/f₀
        expected_real = np.log(p) / F0
        assert abs(computed['real'] - expected_real) < tolerance, \
            f"Prime {p}: real part {computed['real']:.10f} != log({p})/{F0} = {expected_real:.10f}"
        
        # Check formula: Im(τ) = γ₁/(2πf₀)
        expected_imag = GAMMA_1 / (2 * np.pi * F0)
        assert abs(computed['imaginary'] - expected_imag) < tolerance, \
            f"Prime {p}: imaginary part {computed['imaginary']:.10f} != γ₁/(2πf₀) = {expected_imag:.10f}"


def test_prime_3_interpretation():
    """Test that prime 3 has correct interpretation."""
    examples = get_standard_examples()
    assert examples[3]['interpretation'] == "Dualidad creativa"


def test_prime_17_interpretation():
    """Test that prime 17 has correct interpretation."""
    examples = get_standard_examples()
    assert examples[17]['interpretation'] == "Comunicación universal"


# =============================================================================
# ANALYSIS TESTS
# =============================================================================

def test_analyze_spectral_coordinates():
    """Test spectral coordinates analysis function."""
    primes = [3, 5, 7, 17]
    results = analyze_spectral_coordinates(primes, verbose=False)
    
    # Check structure
    assert 'constants' in results
    assert 'primes' in results
    assert 'spectral_coordinates' in results
    assert 'real_parts' in results
    assert 'imaginary_parts' in results
    assert 'properties' in results
    assert 'statistics' in results
    
    # Check constants
    assert results['constants']['f0'] == F0
    assert results['constants']['gamma_1'] == GAMMA_1
    
    # Check properties
    assert results['properties']['monotonic'] is True
    assert results['properties']['constant_imaginary'] is True
    
    # Check statistics
    assert results['statistics']['num_primes'] == 4
    assert results['statistics']['min_real'] < results['statistics']['max_real']


def test_analyze_large_prime_set():
    """Test analysis with a larger set of primes."""
    # First 20 primes
    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71]
    results = analyze_spectral_coordinates(primes, verbose=False)
    
    assert results['statistics']['num_primes'] == 20
    assert results['properties']['monotonic'] is True
    assert results['properties']['constant_imaginary'] is True
    
    # Real parts should span a range
    real_range = results['statistics']['max_real'] - results['statistics']['min_real']
    assert real_range > 0.02, "Real parts should span significant range"
    
    # Imaginary standard deviation should be very small (nearly constant)
    assert results['statistics']['imaginary_std'] < 1e-9


# =============================================================================
# VALIDATION TESTS
# =============================================================================

def test_validate_spectral_coordinates():
    """Test validation against known examples."""
    validation = validate_spectral_coordinates()
    
    assert 'validated' in validation
    assert 'tolerance' in validation
    assert 'results' in validation
    assert 'properties_verified' in validation
    
    # Should pass validation
    assert validation['validated'] is True
    
    # Should verify properties
    assert validation['properties_verified']['monotonicity'] is True
    assert validation['properties_verified']['constant_imaginary'] is True
    
    # Check all standard examples
    for p in [3, 5, 7, 17]:
        assert p in validation['results']
        assert validation['results'][p]['passed'] is True


def test_validation_tolerance():
    """Test validation with different tolerance levels."""
    # Strict tolerance - should still pass
    validation_strict = validate_spectral_coordinates(tolerance=1e-4)
    assert validation_strict['validated'] is True
    
    # Very loose tolerance - definitely should pass
    validation_loose = validate_spectral_coordinates(tolerance=1.0)
    assert validation_loose['validated'] is True


# =============================================================================
# FORMULA VERIFICATION TESTS
# =============================================================================

def test_formula_real_part():
    """Test that real part follows the formula Re(τ) = log(p)/f₀."""
    test_primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
    
    for p in test_primes:
        tau = compute_tau(p)
        expected_real = np.log(p) / F0
        assert abs(tau.real - expected_real) < 1e-10, \
            f"Prime {p}: real part {tau.real} != log({p})/{F0} = {expected_real}"


def test_formula_imaginary_part():
    """Test that imaginary part follows the formula Im(τ) = γ₁/(2πf₀)."""
    test_primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
    expected_imag = GAMMA_1 / (2 * np.pi * F0)
    
    for p in test_primes:
        tau = compute_tau(p)
        assert abs(tau.imag - expected_imag) < 1e-10, \
            f"Prime {p}: imaginary part {tau.imag} != γ₁/(2πf₀) = {expected_imag}"


# =============================================================================
# EDGE CASE TESTS
# =============================================================================

def test_prime_2():
    """Test spectral coordinate for the smallest prime."""
    tau_2 = compute_tau(2)
    
    assert tau_2.real > 0
    assert tau_2.imag == TAU_IMAGINARY_CONSTANT
    
    # Should be the smallest real part for any prime
    tau_3 = compute_tau(3)
    assert tau_2.real < tau_3.real


def test_large_prime():
    """Test spectral coordinate for a large prime."""
    large_prime = 104729  # 10000th prime
    tau_large = compute_tau(large_prime)
    
    assert tau_large.real > 0
    assert tau_large.imag == TAU_IMAGINARY_CONSTANT
    
    # Should have much larger real part than small primes
    tau_3 = compute_tau(3)
    assert tau_large.real > 10 * tau_3.real


def test_very_small_difference():
    """Test that consecutive primes have small but measurable τ difference."""
    # Twin primes
    tau_41 = compute_tau(41)
    tau_43 = compute_tau(43)
    
    diff = tau_43.real - tau_41.real
    assert diff > 0, "Consecutive primes should have different τ values"
    assert diff < 0.001, "Difference should be small for close primes"


# =============================================================================
# INTEGRATION TESTS
# =============================================================================

def test_full_workflow():
    """Test complete workflow from computation to validation."""
    # Step 1: Define primes
    primes = [3, 5, 7, 11, 13, 17, 19, 23]
    
    # Step 2: Compute spectral coordinates
    taus = compute_tau_batch(primes)
    assert len(taus) == len(primes)
    
    # Step 3: Verify properties
    assert verify_monotonicity(primes)
    assert verify_constant_imaginary(primes)
    
    # Step 4: Analyze results
    results = analyze_spectral_coordinates(primes, verbose=False)
    assert results['properties']['monotonic']
    assert results['properties']['constant_imaginary']
    
    # Step 5: Validate against standards
    validation = validate_spectral_coordinates()
    assert validation['validated']


def test_qcal_coherence():
    """Test that spectral coordinates maintain QCAL ∞³ coherence."""
    # Get standard examples
    examples = get_standard_examples()
    
    # All should use the same base frequency
    for p in [3, 5, 7, 17]:
        # Reverse-engineer f₀ from τ
        tau = examples[p]['tau']
        p_value = examples[p]['prime']
        
        # f₀ = log(p) / Re(τ)
        derived_f0 = np.log(p_value) / tau.real
        
        # Should match F0 within numerical precision
        assert abs(derived_f0 - F0) < 1e-3, \
            f"Prime {p}: derived f₀ = {derived_f0} != {F0}"


# =============================================================================
# MAIN TEST EXECUTION
# =============================================================================

if __name__ == "__main__":
    # Run tests with verbose output
    pytest.main([__file__, "-v", "-s"])
