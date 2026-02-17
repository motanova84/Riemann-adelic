#!/usr/bin/env python3
"""
Test Biological-Mathematical Integration
=========================================

Simple test to verify that the biological constants integrate correctly
with the existing QCAL framework.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: February 2026
"""

import sys
from pathlib import Path

# Add src to path
sys.path.insert(0, str(Path(__file__).parent / 'src'))


def test_constants_import():
    """Test that constants can be imported."""
    from constants.biological_qcal_constants import (
        XI_1_MICROMETERS,
        KAPPA_PI,
        F0_HZ,
        FREQUENCY_HARMONICS,
        HERMITIAN_SYSTEM_VERIFIED,
        BIOLOGICAL_DEMONSTRATION_QUOTE,
    )
    
    assert XI_1_MICROMETERS == 1.0598
    assert KAPPA_PI == 2.5773
    assert F0_HZ == 141.7001
    assert len(FREQUENCY_HARMONICS) >= 3
    assert HERMITIAN_SYSTEM_VERIFIED is True
    assert "37 billones" in BIOLOGICAL_DEMONSTRATION_QUOTE or "37 trillion" in BIOLOGICAL_DEMONSTRATION_QUOTE
    
    print("✓ Constants import test passed")
    return True


def test_biological_module_integration():
    """Test that biological module exports constants."""
    from biological import (
        XI_1_MICROMETERS,
        KAPPA_PI,
        F0_HZ,
        BIOLOGICAL_DEMONSTRATION_QUOTE,
    )
    
    assert XI_1_MICROMETERS == 1.0598
    assert KAPPA_PI == 2.5773
    assert F0_HZ == 141.7001
    
    print("✓ Biological module integration test passed")
    return True


def test_harmonic_frequencies():
    """Test that frequency harmonics are correct."""
    from constants.biological_qcal_constants import (
        F0_HZ,
        FREQUENCY_HARMONICS,
        get_harmonic_frequency,
    )
    
    # Check first 3 harmonics
    expected = [
        (1, 141.7001),
        (2, 283.4002),
        (3, 425.1003),
    ]
    
    for n, expected_freq in expected:
        actual_freq = FREQUENCY_HARMONICS[n]
        computed_freq = get_harmonic_frequency(n)
        
        assert abs(actual_freq - expected_freq) < 0.001, f"Harmonic {n} mismatch"
        assert abs(computed_freq - expected_freq) < 0.001, f"Computed harmonic {n} mismatch"
    
    print("✓ Harmonic frequencies test passed")
    return True


def test_wavelength_frequency_conversion():
    """Test wavelength-frequency conversion functions."""
    from constants.biological_qcal_constants import (
        XI_1_MICROMETERS,
        XI_1_METERS,
        C_LIGHT,
        wavelength_to_frequency,
        frequency_to_wavelength,
    )
    
    # Test round-trip conversion
    freq = wavelength_to_frequency(XI_1_METERS)
    wavelength = frequency_to_wavelength(freq)
    
    assert abs(wavelength - XI_1_METERS) < 1e-12, "Round-trip conversion failed"
    
    # Test speed of light relationship
    assert abs(freq * XI_1_METERS - C_LIGHT) < 1.0, "Speed of light relation violated"
    
    print("✓ Wavelength-frequency conversion test passed")
    return True


def test_constants_validation():
    """Test internal validation function."""
    from constants.biological_qcal_constants import validate_constants
    
    results = validate_constants()
    
    assert results['validation_passed'] is True, "Constants validation failed"
    assert results['xi_1_wavelength_um'] == 1.0598
    assert results['kappa_pi'] == 2.5773
    assert results['f0_hz'] == 141.7001
    
    print("✓ Constants validation test passed")
    return True


def test_hermitian_verification():
    """Test hermitian system verification."""
    import numpy as np
    from constants.biological_qcal_constants import (
        HERMITIAN_SYSTEM_VERIFIED,
        check_hermitian,
    )
    
    assert HERMITIAN_SYSTEM_VERIFIED is True
    
    # Test with a known hermitian matrix
    H = np.array([[1, 1+1j], [1-1j, 2]], dtype=complex)
    assert check_hermitian(H) is True, "Hermitian check failed for hermitian matrix"
    
    # Test with a non-hermitian matrix
    N = np.array([[1, 1], [2, 1]], dtype=complex)
    assert check_hermitian(N) is False, "Hermitian check failed for non-hermitian matrix"
    
    print("✓ Hermitian verification test passed")
    return True


def test_biological_scale_relationship():
    """Test relationship between cosmic and cellular scales."""
    from constants.biological_qcal_constants import (
        F0_HZ,
        XI_1_FREQUENCY_HZ,
        SCALE_RATIO_COSMIC_TO_CELLULAR,
    )
    
    # Verify scale ratio is correct
    ratio = XI_1_FREQUENCY_HZ / F0_HZ
    assert abs(ratio - SCALE_RATIO_COSMIC_TO_CELLULAR) < 1e6, "Scale ratio mismatch"
    
    # Verify it's a large number (cosmic to cellular)
    assert SCALE_RATIO_COSMIC_TO_CELLULAR > 1e12, "Scale ratio should be huge"
    
    print("✓ Biological scale relationship test passed")
    return True


def main():
    """Run all tests."""
    print("="*70)
    print("BIOLOGICAL-MATHEMATICAL INTEGRATION TESTS")
    print("="*70)
    print()
    
    tests = [
        ("Constants Import", test_constants_import),
        ("Biological Module Integration", test_biological_module_integration),
        ("Harmonic Frequencies", test_harmonic_frequencies),
        ("Wavelength-Frequency Conversion", test_wavelength_frequency_conversion),
        ("Constants Validation", test_constants_validation),
        ("Hermitian Verification", test_hermitian_verification),
        ("Biological Scale Relationship", test_biological_scale_relationship),
    ]
    
    passed = 0
    failed = 0
    
    for name, test_func in tests:
        try:
            print(f"Running: {name}")
            if test_func():
                passed += 1
            else:
                failed += 1
                print(f"  ✗ {name} FAILED")
        except Exception as e:
            failed += 1
            print(f"  ✗ {name} FAILED: {e}")
        print()
    
    print("="*70)
    print(f"RESULTS: {passed} passed, {failed} failed")
    print("="*70)
    
    if failed == 0:
        print("\n✅ ALL TESTS PASSED")
        print("\nBiological-mathematical integration is complete and coherent.")
        print("∴ 𓂀 Ω ∞³")
        return 0
    else:
        print(f"\n❌ {failed} TEST(S) FAILED")
        return 1


if __name__ == "__main__":
    sys.exit(main())
