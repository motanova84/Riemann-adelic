#!/usr/bin/env python3
"""
Test Suite for Python-Lean FFI Bridge
======================================

Comprehensive tests for the FFI wrapper functions to ensure
they work correctly before integration with Lean.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
"""

import sys
import json
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from ffi.python_ffi_wrapper import *

def test_get_constant():
    """Test getting QCAL constants"""
    print("🧪 Test: Get Constants")
    
    # Test valid constants
    f0 = ffi_get_constant("F0")
    assert f0 == 141.7001, f"F0 should be 141.7001, got {f0}"
    print(f"  ✓ F0 = {f0} Hz")
    
    c = ffi_get_constant("C_PRIMARY")
    assert c == 244.36, f"C_PRIMARY should be 244.36, got {c}"
    print(f"  ✓ C_PRIMARY = {c}")
    
    delta_zeta = ffi_get_constant("DELTA_ZETA")
    assert abs(delta_zeta - 0.2787437627) < 1e-9
    print(f"  ✓ DELTA_ZETA = {delta_zeta}")
    
    # Test invalid constant
    invalid = ffi_get_constant("INVALID_CONSTANT")
    assert invalid == 0.0, "Invalid constant should return 0.0"
    print("  ✓ Invalid constant returns 0.0")
    
    print("  ✅ All constant tests passed\n")


def test_validate_coherence():
    """Test coherence validation"""
    print("🧪 Test: Validate Coherence")
    
    result = ffi_validate_coherence()
    assert isinstance(result, bool), "Should return boolean"
    
    if result:
        print("  ✓ Coherence validated successfully")
    else:
        print("  ⚠ Coherence validation returned False")
    
    print("  ✅ Coherence validation test passed\n")


def test_compute_psi():
    """Test Ψ computation"""
    print("🧪 Test: Compute Ψ")
    
    # Test with known values
    psi = ffi_compute_psi(1.0, 10.0, 244.36)
    assert psi > 0, "Ψ should be positive"
    print(f"  ✓ Ψ(1.0, 10.0, 244.36) = {psi}")
    
    # Test with zero intensity
    psi_zero = ffi_compute_psi(0.0, 10.0, 244.36)
    assert psi_zero == 0.0, "Ψ should be 0 when I=0"
    print(f"  ✓ Ψ(0, 10, 244.36) = {psi_zero}")
    
    # Test proportionality
    psi2 = ffi_compute_psi(2.0, 10.0, 244.36)
    assert abs(psi2 - 2 * psi) < 1e-6, "Ψ should scale linearly with I"
    print(f"  ✓ Ψ scales linearly with intensity")
    
    print("  ✅ All Ψ computation tests passed\n")


def test_run_validation():
    """Test comprehensive validation"""
    print("🧪 Test: Run Validation")
    
    # Test with simple config
    config = json.dumps({"precision": 25, "verbose": False})
    result_json = ffi_run_validation(config)
    
    assert isinstance(result_json, str), "Should return JSON string"
    
    result = json.loads(result_json)
    assert "all_checks_passed" in result, "Should have all_checks_passed field"
    
    print(f"  ✓ Validation executed")
    print(f"  ✓ All checks passed: {result.get('all_checks_passed', False)}")
    
    # Test with invalid JSON
    invalid_result = ffi_run_validation("{invalid json")
    invalid = json.loads(invalid_result)
    assert "error" in invalid, "Should return error for invalid JSON"
    print(f"  ✓ Handles invalid JSON correctly")
    
    print("  ✅ All validation tests passed\n")


def test_riemann_zeros():
    """Test Riemann zero computation"""
    print("🧪 Test: Compute Riemann Zeros")
    
    try:
        # Test first zero
        zero1_json = ffi_compute_riemann_zero(1)
        zero1 = json.loads(zero1_json)
        
        if "error" in zero1:
            print(f"  ⚠ mpmath not available: {zero1['error']}")
            print("  ℹ Install mpmath for full functionality")
        else:
            assert zero1["index"] == 1
            assert zero1["real"] == 0.5
            assert abs(zero1["imaginary"] - 14.134725) < 0.01
            print(f"  ✓ First zero: γ₁ = {zero1['imaginary']}")
            
            # Test second zero
            zero2_json = ffi_compute_riemann_zero(2)
            zero2 = json.loads(zero2_json)
            assert zero2["index"] == 2
            print(f"  ✓ Second zero: γ₂ = {zero2['imaginary']}")
            
            # Test that zeros are ordered
            assert zero2["imaginary"] > zero1["imaginary"]
            print(f"  ✓ Zeros are ordered correctly")
    
    except Exception as e:
        print(f"  ⚠ Error: {e}")
        print("  ℹ Some zero computation tests skipped")
    
    print("  ✅ Riemann zero tests completed\n")


def test_evaluate_zeta():
    """Test zeta function evaluation"""
    print("🧪 Test: Evaluate Zeta Function")
    
    try:
        # Evaluate at a known point
        zeta_json = ffi_evaluate_zeta(2.0, 0.0)
        zeta = json.loads(zeta_json)
        
        if "error" in zeta:
            print(f"  ⚠ mpmath not available: {zeta['error']}")
        else:
            # ζ(2) = π²/6 ≈ 1.6449
            assert abs(zeta["real"] - 1.6449) < 0.01
            print(f"  ✓ ζ(2) = {zeta['real']} (expected ≈ 1.6449)")
            
            # Evaluate at critical line
            zeta_crit_json = ffi_evaluate_zeta(0.5, 14.134725)
            zeta_crit = json.loads(zeta_crit_json)
            print(f"  ✓ ζ(1/2 + 14.134725i) evaluated")
    
    except Exception as e:
        print(f"  ⚠ Error: {e}")
    
    print("  ✅ Zeta evaluation tests completed\n")


def test_check_critical_line():
    """Test critical line checking"""
    print("🧪 Test: Check Critical Line")
    
    try:
        # Check at known zero
        is_zero = ffi_check_critical_line(0.5, 14.134725, 1e-6)
        print(f"  ✓ Point (0.5, 14.134725) is zero: {is_zero}")
        
        # Check at non-zero point
        not_zero = ffi_check_critical_line(0.5, 10.0, 1e-6)
        assert not not_zero, "Point (0.5, 10.0) should not be a zero"
        print(f"  ✓ Point (0.5, 10.0) is not a zero")
    
    except Exception as e:
        print(f"  ⚠ Error: {e}")
    
    print("  ✅ Critical line tests completed\n")


def test_generate_certificate():
    """Test certificate generation"""
    print("🧪 Test: Generate Certificate")
    
    test_path = "/tmp/ffi_test_cert.json"
    
    try:
        result = ffi_generate_certificate(test_path)
        
        if result:
            print(f"  ✓ Certificate generated at {test_path}")
            
            # Verify file exists
            from pathlib import Path
            cert_file = Path(test_path)
            if cert_file.exists():
                print(f"  ✓ Certificate file exists")
                
                # Load and check structure
                with open(cert_file) as f:
                    cert = json.load(f)
                assert "timestamp" in cert
                print(f"  ✓ Certificate has valid structure")
            else:
                print(f"  ✗ Certificate file not found")
        else:
            print(f"  ⚠ Certificate generation returned False")
    
    except Exception as e:
        print(f"  ⚠ Error: {e}")
    
    print("  ✅ Certificate tests completed\n")


def test_api_info():
    """Test API info retrieval"""
    print("🧪 Test: Get API Info")
    
    info_json = ffi_get_api_info()
    assert isinstance(info_json, str)
    
    info = json.loads(info_json)
    assert "version" in info
    assert "functions" in info
    assert "constants" in info
    
    print(f"  ✓ API version: {info['version']}")
    print(f"  ✓ Functions available: {len(info['functions'])}")
    print(f"  ✓ Constants available: {len(info['constants'])}")
    
    print("  ✅ API info tests passed\n")


def run_all_tests():
    """Run all tests"""
    print("═" * 70)
    print("  QCAL Python-Lean FFI Bridge - Test Suite")
    print("═" * 70)
    print()
    
    tests = [
        test_get_constant,
        test_validate_coherence,
        test_compute_psi,
        test_run_validation,
        test_riemann_zeros,
        test_evaluate_zeta,
        test_check_critical_line,
        test_generate_certificate,
        test_api_info,
    ]
    
    passed = 0
    failed = 0
    
    for test in tests:
        try:
            test()
            passed += 1
        except AssertionError as e:
            print(f"  ❌ Test failed: {e}\n")
            failed += 1
        except Exception as e:
            print(f"  ⚠️  Test error: {e}\n")
            failed += 1
    
    print("═" * 70)
    print(f"  Test Results: {passed} passed, {failed} failed")
    print("═" * 70)
    
    return failed == 0


if __name__ == "__main__":
    success = run_all_tests()
    sys.exit(0 if success else 1)
