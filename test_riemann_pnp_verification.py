#!/usr/bin/env python3
"""
Tests for Riemann-PNP Verification Bridge
==========================================

Tests the 3-step verification procedure for detecting spectral coherence leaks.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: January 2026
"""

import sys
from pathlib import Path

# Add src to path
sys.path.insert(0, str(Path(__file__).parent / "src"))

import numpy as np
from riemann_pnp_verification_bridge import (
    RiemannPNPVerificationBridge,
    PrimeSpectralData,
    ZeroToPremeInterpolation,
    TensorialDeviation,
    VibrationalAnomaly
)


def test_prime_generation():
    """Test prime number generation."""
    print("Test 1: Prime Generation")
    
    bridge = RiemannPNPVerificationBridge(precision=25, n_primes=100)
    
    # Check first 10 primes
    expected_primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
    actual_primes = bridge.primes[:10].tolist()
    
    assert actual_primes == expected_primes, \
        f"Expected {expected_primes}, got {actual_primes}"
    
    # Check 100th prime
    assert bridge.primes[99] == 541, f"100th prime should be 541, got {bridge.primes[99]}"
    
    print("  ✓ Prime generation correct")
    print(f"  ✓ Generated {len(bridge.primes)} primes")
    print(f"  ✓ First 10 primes: {actual_primes}")


def test_spectral_frequency():
    """Test spectral frequency calculation."""
    print("\nTest 2: Spectral Frequency Calculation")
    
    bridge = RiemannPNPVerificationBridge(precision=25, n_primes=100)
    
    # Test for p=17 (reference prime)
    f_17 = bridge.spectral_frequency(17)
    
    print(f"  f(17) = {f_17:.4f} Hz")
    
    # Should match fundamental frequency exactly
    assert abs(f_17 - bridge.F0) < 0.01, \
        f"f(17) should equal f₀={bridge.F0}, got {f_17}"
    
    # Test that frequencies are generally increasing for larger primes
    f_11 = bridge.spectral_frequency(11)
    f_17 = bridge.spectral_frequency(17)
    f_23 = bridge.spectral_frequency(23)
    f_29 = bridge.spectral_frequency(29)
    
    assert f_11 < f_17 < f_23 < f_29, \
        "Frequencies should increase for primes > 11"
    
    print(f"  ✓ f(11) = {f_11:.4f} Hz")
    print(f"  ✓ f(17) = {f_17:.4f} Hz")
    print(f"  ✓ f(23) = {f_23:.4f} Hz")
    print(f"  ✓ f(29) = {f_29:.4f} Hz")
    print("  ✓ Frequency growth verified for p > 11")


def test_step1_inverse_interpolation():
    """Test Step 1: Inverse Interpolation."""
    print("\nTest 3: Step 1 - Inverse Interpolation")
    
    bridge = RiemannPNPVerificationBridge(precision=25, n_primes=100)
    
    # Test with known zeros
    interpolations = bridge.inverse_interpolation(alignment_factor=1.0)
    
    assert len(interpolations) == len(bridge.ZEROS_IM), \
        f"Should have {len(bridge.ZEROS_IM)} interpolations"
    
    # Check first interpolation
    first = interpolations[0]
    assert isinstance(first, ZeroToPremeInterpolation)
    assert first.zero_index == 0
    assert first.zero_imaginary > 0
    assert first.estimated_frequency > 0
    assert first.estimated_prime >= 0
    
    print(f"  ✓ {len(interpolations)} zeros interpolated")
    print(f"  ✓ First zero: t₁ = {first.zero_imaginary:.6f}")
    print(f"  ✓ Estimated frequency: f₁ = {first.estimated_frequency:.4f} Hz")
    print(f"  ✓ Estimated prime: p₁ ≈ {first.estimated_prime:.2f}")


def test_spectral_tensor():
    """Test spectral tensor computation."""
    print("\nTest 4: Spectral Tensor Computation")
    
    bridge = RiemannPNPVerificationBridge(precision=25, n_primes=100)
    
    # Test for p=17
    H, R, C = bridge.compute_spectral_tensor(17)
    
    print(f"  T⃗₁₇ = (H={H:.4f}, R={R:.4f}, C={C:.4f})")
    
    # All components should be in [0, 1]
    assert 0 <= H <= 1, f"H(17) should be in [0,1], got {H}"
    assert 0 <= R <= 1, f"R(17) should be in [0,1], got {R}"
    assert 0 <= C <= 1, f"C(17) should be in [0,1], got {C}"
    
    # C(17) should be high (reference prime)
    assert C > 0.5, f"C(17) should be high (reference), got {C}"
    
    print("  ✓ All components in valid range [0,1]")
    print(f"  ✓ C(17) = {C:.4f} (high, as expected for reference)")


def test_step2_tensorial_comparison():
    """Test Step 2: Tensorial Comparison."""
    print("\nTest 5: Step 2 - Tensorial Comparison")
    
    bridge = RiemannPNPVerificationBridge(precision=25, n_primes=100)
    
    # Test with first 10 primes
    deviations = bridge.tensorial_comparison(primes=bridge.primes[:10])
    
    assert len(deviations) == 10, f"Should have 10 deviations, got {len(deviations)}"
    
    # Check first deviation
    first = deviations[0]
    assert isinstance(first, TensorialDeviation)
    assert first.prime == bridge.primes[0]
    assert first.frequency_prime > 0
    assert first.delta >= 0
    assert 0 <= first.harmonic_index <= 1
    assert 0 <= first.resonance_strength <= 1
    assert 0 <= first.coherence_factor <= 1
    
    # Count leaks
    n_leaks = sum(1 for d in deviations if d.is_leak)
    
    print(f"  ✓ {len(deviations)} primes analyzed")
    print(f"  ✓ First prime: p = {first.prime}")
    print(f"  ✓ δ({first.prime}) = {first.delta:.6f}")
    print(f"  ✓ Leaks detected (δ > 0.01): {n_leaks}")


def test_step3_anomaly_detection():
    """Test Step 3: Anomaly Detection."""
    print("\nTest 6: Step 3 - Anomaly Detection")
    
    bridge = RiemannPNPVerificationBridge(precision=25, n_primes=100)
    
    # Get deviations
    deviations = bridge.tensorial_comparison(primes=bridge.primes[:50])
    
    # Identify anomalies
    anomalies = bridge.identify_vibrational_anomalies(deviations)
    
    print(f"  ✓ {len(anomalies)} anomalies detected")
    
    if anomalies:
        # Check first anomaly
        first = anomalies[0]
        assert isinstance(first, VibrationalAnomaly)
        assert first.prime in bridge.primes
        assert first.anomaly_type in ['coherence', 'harmonic', 'resonance', 'deviation', 'none']
        assert 0 <= first.severity <= 1
        assert isinstance(first.is_spectral_leak, bool)
        
        print(f"  ✓ First anomaly: p = {first.prime}")
        print(f"  ✓ Type: {first.anomaly_type}")
        print(f"  ✓ Severity: {first.severity:.4f}")
        print(f"  ✓ Spectral leak: {first.is_spectral_leak}")
    else:
        print("  ✓ No anomalies detected (perfect coherence)")


def test_full_verification():
    """Test full verification procedure."""
    print("\nTest 7: Full Verification Procedure")
    
    bridge = RiemannPNPVerificationBridge(precision=25, n_primes=100)
    
    # Execute full verification
    results = bridge.verify_coherence(n_zeros=5, alignment_factor=1.0)
    
    # Check results structure
    assert 'step1_interpolations' in results
    assert 'step2_deviations' in results
    assert 'step3_anomalies' in results
    assert 'statistics' in results
    assert 'coherence_intact' in results
    assert 'message' in results
    
    stats = results['statistics']
    
    print(f"  ✓ Verification completed")
    print(f"  ✓ Primes analyzed: {stats['n_primes_analyzed']}")
    print(f"  ✓ Zeros used: {stats['n_zeros_used']}")
    print(f"  ✓ Mean deviation: δ̄ = {stats['mean_deviation']:.6f}")
    print(f"  ✓ Coherence quality: {stats['coherence_quality']:.2%}")
    print(f"  ✓ Coherence intact: {results['coherence_intact']}")


def test_anomaly_classification():
    """Test anomaly classification logic."""
    print("\nTest 8: Anomaly Classification")
    
    bridge = RiemannPNPVerificationBridge(precision=25, n_primes=100)
    
    # Test various scenarios
    H_mean = 0.5
    
    # Scenario 1: Low coherence only (likely coding error)
    anom_type, severity, is_leak = bridge.classify_anomaly_type(
        C=0.005, H=0.5, R=0.5, delta=0.005, H_mean=H_mean
    )
    assert anom_type == 'coherence'
    assert not is_leak, "Single anomaly should not be spectral leak"
    print("  ✓ Scenario 1: Low coherence → coding error")
    
    # Scenario 2: Multiple failures (likely spectral leak)
    anom_type, severity, is_leak = bridge.classify_anomaly_type(
        C=0.005, H=0.1, R=0.02, delta=0.05, H_mean=H_mean
    )
    assert is_leak, "Multiple anomalies should indicate spectral leak"
    print("  ✓ Scenario 2: Multiple failures → spectral leak")
    
    # Scenario 3: No anomaly
    anom_type, severity, is_leak = bridge.classify_anomaly_type(
        C=0.8, H=0.6, R=0.6, delta=0.005, H_mean=H_mean
    )
    assert anom_type == 'none'
    assert severity == 0.0
    print("  ✓ Scenario 3: No anomaly → normal")


def run_all_tests():
    """Run all tests."""
    print("=" * 70)
    print("  RIEMANN-PNP VERIFICATION BRIDGE - TEST SUITE")
    print("=" * 70)
    
    try:
        test_prime_generation()
        test_spectral_frequency()
        test_step1_inverse_interpolation()
        test_spectral_tensor()
        test_step2_tensorial_comparison()
        test_step3_anomaly_detection()
        test_full_verification()
        test_anomaly_classification()
        
        print("\n" + "=" * 70)
        print("  ✅ ALL TESTS PASSED")
        print("=" * 70)
        print("\n✅ PUENTE DE VERIFICACIÓN RIEMANN-PNP ∞³ VALIDADO")
        print("Ψ ✧ ∞³")
        
        return True
        
    except AssertionError as e:
        print(f"\n❌ TEST FAILED: {e}")
        return False
    except Exception as e:
        print(f"\n❌ ERROR: {e}")
        import traceback
        traceback.print_exc()
        return False


if __name__ == "__main__":
    success = run_all_tests()
    sys.exit(0 if success else 1)
