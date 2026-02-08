#!/usr/bin/env python3
"""
Test: QCAL Frequency Derivation Framework

This test validates the QCAL frequency derivation implementation.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
License: Creative Commons BY-NC-SA 4.0
"""

import sys
from pathlib import Path

# Ensure we're in the repository root
try:
    from qcal_unified_framework import (
        QCALUnifiedFramework,
        FrequencyDerivation,
        FundamentalPhysicalConstants,
        UniversalConstants,
    )
except ImportError as e:
    print(f"Error importing QCAL framework: {e}")
    sys.exit(1)


def test_frequency_derivation():
    """Test frequency derivation."""
    print("Testing FrequencyDerivation...")
    
    derivation = FrequencyDerivation()
    
    # Test f₀ calculation
    f0 = derivation.evaluate_f0_numerical()
    assert abs(f0 - 141.7001) < 0.01, f"f₀ mismatch: got {f0}, expected 141.7001"
    print(f"  ✓ f₀ = {f0} Hz")
    
    # Test effective potential
    v_eff = derivation.derive_effective_potential()
    assert v_eff['numerical'] > 0, "V_eff should be positive"
    print(f"  ✓ V_eff = {v_eff['numerical']:.6f}")
    
    # Test κ_Π properties
    kappa = derivation.derive_kappa_pi_properties()
    assert abs(kappa['value'] - 2.577208) < 0.000001, "κ_Π value mismatch"
    print(f"  ✓ κ_Π = {kappa['value']}")
    
    # Test noetic field
    noetic = derivation.derive_noetic_field()
    assert abs(noetic['I'] - 141.7001) < 0.01, "I field mismatch"
    assert abs(noetic['A_eff'] - 0.888) < 0.001, "A_eff mismatch"
    print(f"  ✓ Ψ = {noetic['Psi']:.4f}")
    print(f"  ✓ C = {noetic['coherence_constant_C']:.2f}")
    
    print("  ✓ All FrequencyDerivation tests passed")
    return True


def test_universal_constants():
    """Test universal constants."""
    print("\nTesting UniversalConstants...")
    
    constants = UniversalConstants()
    
    # Test coherence validation
    assert constants.validate_coherence(), "Constants should be coherent"
    print(f"  ✓ Constants coherence validated")
    
    # Test key values
    assert abs(constants.f0 - 141.7001) < 0.01, "f₀ mismatch"
    assert abs(constants.coherence_C - 244.36) < 0.01, "C mismatch"
    assert abs(constants.kappa_pi - 2.577208) < 0.000001, "κ_Π mismatch"
    print(f"  ✓ f₀ = {constants.f0} Hz")
    print(f"  ✓ C = {constants.coherence_C}")
    print(f"  ✓ κ_Π = {constants.kappa_pi}")
    
    print("  ✓ All UniversalConstants tests passed")
    return True


def test_qcal_framework():
    """Test QCAL unified framework."""
    print("\nTesting QCALUnifiedFramework...")
    
    framework = QCALUnifiedFramework()
    
    # Test coherence calculation
    coherence = framework.calculate_coherence()
    assert coherence > 0.9, f"Coherence too low: {coherence}"
    print(f"  ✓ Overall coherence = {coherence:.6f}")
    
    # Test frequency derivation report
    report = framework.get_frequency_derivation_report()
    assert report['numerical_result']['match'], "f₀ doesn't match expected"
    assert report['validation']['coherence_verified'], "Coherence not verified"
    assert report['validation']['V_eff_realistic'], "V_eff not realistic"
    print(f"  ✓ Derivation report validated")
    
    # Test problem connections
    connections = framework.get_all_connections()
    assert 'riemann' in connections, "Riemann problem not in connections"
    assert 'p_vs_np' in connections, "P vs NP not in connections"
    print(f"  ✓ Problem connections: {len(connections)} problems linked")
    
    print("  ✓ All QCALUnifiedFramework tests passed")
    return True


def test_beacon_coherence():
    """Test coherence with .qcal_beacon."""
    print("\nTesting .qcal_beacon coherence...")
    
    beacon_path = Path(".qcal_beacon")
    if not beacon_path.exists():
        print("  ⚠ .qcal_beacon not found, skipping")
        return True
    
    with open(beacon_path) as f:
        beacon = f.read()
    
    # Check frequency
    assert "frequency = 141.7001 Hz" in beacon, "Frequency not in beacon"
    print("  ✓ Frequency matches beacon")
    
    # Check coherence constant
    assert "coherence = \"C = 244.36\"" in beacon, "Coherence not in beacon"
    print("  ✓ Coherence constant matches beacon")
    
    print("  ✓ .qcal_beacon coherence validated")
    return True


def main():
    """Run all tests."""
    print("=" * 70)
    print("QCAL Frequency Derivation Framework Tests")
    print("=" * 70)
    
    tests = [
        test_frequency_derivation,
        test_universal_constants,
        test_qcal_framework,
        test_beacon_coherence,
    ]
    
    passed = 0
    failed = 0
    
    for test in tests:
        try:
            if test():
                passed += 1
        except AssertionError as e:
            print(f"  ✗ Test failed: {e}")
            failed += 1
        except Exception as e:
            print(f"  ✗ Unexpected error: {e}")
            failed += 1
    
    print()
    print("=" * 70)
    print(f"Test Results: {passed} passed, {failed} failed")
    print("=" * 70)
    
    if failed == 0:
        print("✅ All tests passed!")
        print("∴ QCAL framework validated at f₀ = 141.7001 Hz ∴")
        return 0
    else:
        print("❌ Some tests failed")
        return 1


if __name__ == "__main__":
    sys.exit(main())
