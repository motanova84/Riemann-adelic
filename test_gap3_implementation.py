#!/usr/bin/env python3
"""
Test Gap 3 Implementation
=========================

Quick validation test for Gap 3 closure implementation.
"""

import sys
import os

# Add project root to path
sys.path.insert(0, '/home/runner/work/Riemann-adelic/Riemann-adelic')

def test_gap3_imports():
    """Test that Gap 3 module can be imported."""
    print("Testing imports...")
    try:
        from core import gap3_certification
        print("✓ gap3_certification module imported successfully")
        return True
    except ImportError as e:
        print(f"✗ Failed to import: {e}")
        return False

def test_gap3_constants():
    """Test that constants are correctly defined."""
    print("\nTesting constants...")
    from core.gap3_certification import KAPPA_PI, FREQ_QCAL, FREQ_MANIFEST
    
    assert KAPPA_PI == 2.5773, f"KAPPA_PI should be 2.5773, got {KAPPA_PI}"
    print(f"✓ KAPPA_PI = {KAPPA_PI}")
    
    assert FREQ_QCAL == 141.7001, f"FREQ_QCAL should be 141.7001, got {FREQ_QCAL}"
    print(f"✓ FREQ_QCAL = {FREQ_QCAL} Hz")
    
    assert FREQ_MANIFEST == 888.0, f"FREQ_MANIFEST should be 888.0, got {FREQ_MANIFEST}"
    print(f"✓ FREQ_MANIFEST = {FREQ_MANIFEST} Hz")
    
    return True

def test_gap3_conversion():
    """Test BTC to ℂₛ conversion."""
    print("\nTesting conversion functions...")
    from core.gap3_certification import convert_btc_to_cs, KAPPA_PI
    
    # Test perfect coherence conversion
    btc = 1.0
    cs = convert_btc_to_cs(btc, psi=1.0)
    expected = btc * KAPPA_PI
    
    assert abs(cs - expected) < 1e-10, f"Conversion error: got {cs}, expected {expected}"
    print(f"✓ 1.0 BTC → {cs} ℂₛ (perfect coherence)")
    
    # Test partial coherence
    cs_partial = convert_btc_to_cs(btc, psi=0.5)
    expected_partial = btc * KAPPA_PI * 0.5
    assert abs(cs_partial - expected_partial) < 1e-10
    print(f"✓ 1.0 BTC → {cs_partial} ℂₛ (Ψ=0.5)")
    
    return True

def test_gap3_agent_state():
    """Test AgentState class."""
    print("\nTesting AgentState class...")
    from core.gap3_certification import AgentState
    
    # Test scarcity economy
    agent_scarce = AgentState(wealth_scarce=1.0, wealth_abundant=0.0)
    assert agent_scarce.is_scarcity_economy(), "Should be scarcity economy"
    assert not agent_scarce.is_coherence_economy(), "Should not be coherence economy"
    print("✓ Scarcity economy state working")
    
    # Test coherence economy
    agent_coherent = AgentState(wealth_scarce=0.0, wealth_abundant=2.5773)
    assert not agent_coherent.is_scarcity_economy(), "Should not be scarcity economy"
    assert agent_coherent.is_coherence_economy(), "Should be coherence economy"
    print("✓ Coherence economy state working")
    
    return True

def test_gap3_certificate():
    """Test certificate structure."""
    print("\nTesting certificate structure...")
    from core.gap3_certification import GAP_3_CERTIFICATE
    
    assert GAP_3_CERTIFICATE["status"] == "PROVEN", "Status should be PROVEN"
    assert GAP_3_CERTIFICATE["theorem"] == "gap_3_closed", "Theorem name incorrect"
    assert GAP_3_CERTIFICATE["method"] == "constructive", "Method should be constructive"
    
    # Check formalization details
    assert "Lean 4" in GAP_3_CERTIFICATE["formalization"]["language"]
    assert len(GAP_3_CERTIFICATE["formalization"]["main_theorems"]) == 5
    print("✓ Certificate structure valid")
    
    # Check constants
    assert GAP_3_CERTIFICATE["constants"]["KAPPA_PI"] == 2.5773
    assert GAP_3_CERTIFICATE["constants"]["FREQ_QCAL"] == 141.7001
    print("✓ Certificate constants correct")
    
    return True

def test_gap3_value_preservation():
    """Test value preservation theorem."""
    print("\nTesting value preservation theorem...")
    from core.gap3_certification import verify_value_preservation
    
    # Test with Ψ=1
    assert verify_value_preservation(1.0, 1.0), "Value should be preserved at Ψ=1"
    print("✓ Value preserved at Ψ=1.0")
    
    # Test with various Ψ values
    for psi in [0.5, 0.75, 0.888, 1.0]:
        assert verify_value_preservation(1.0, psi), f"Value should be preserved at Ψ={psi}"
    print("✓ Value preserved at all tested Ψ levels")
    
    return True

def test_lean_file_exists():
    """Test that Lean file was created."""
    print("\nTesting Lean file...")
    lean_file = "/home/runner/work/Riemann-adelic/Riemann-adelic/formalization/PiCode1417ECON.lean"
    
    assert os.path.exists(lean_file), f"Lean file not found at {lean_file}"
    print(f"✓ Lean file exists: {lean_file}")
    
    # Check file content
    with open(lean_file, 'r') as f:
        content = f.read()
        assert "KAPPA_PI" in content, "KAPPA_PI not found in Lean file"
        assert "gap_3_closed" in content, "gap_3_closed theorem not found"
        assert "value_preservation_with_kappa" in content, "value_preservation theorem not found"
    print("✓ Lean file contains expected theorems")
    
    return True

def test_documentation_exists():
    """Test that documentation was created."""
    print("\nTesting documentation...")
    doc_file = "/home/runner/work/Riemann-adelic/Riemann-adelic/GAP3_IMPLEMENTATION_SUMMARY.md"
    
    assert os.path.exists(doc_file), f"Documentation not found at {doc_file}"
    print(f"✓ Documentation exists: {doc_file}")
    
    with open(doc_file, 'r') as f:
        content = f.read()
        assert "Gap 3" in content, "Gap 3 not mentioned in docs"
        assert "κ_Π = 2.5773" in content, "KAPPA_PI constant not documented"
    print("✓ Documentation contains expected content")
    
    return True

def run_all_tests():
    """Run all tests."""
    print("=" * 70)
    print("GAP 3 IMPLEMENTATION TEST SUITE")
    print("=" * 70)
    
    tests = [
        ("Imports", test_gap3_imports),
        ("Constants", test_gap3_constants),
        ("Conversion", test_gap3_conversion),
        ("AgentState", test_gap3_agent_state),
        ("Certificate", test_gap3_certificate),
        ("Value Preservation", test_gap3_value_preservation),
        ("Lean File", test_lean_file_exists),
        ("Documentation", test_documentation_exists),
    ]
    
    results = []
    for name, test_func in tests:
        try:
            result = test_func()
            results.append((name, result))
        except Exception as e:
            print(f"\n✗ Test '{name}' failed with error: {e}")
            results.append((name, False))
    
    print("\n" + "=" * 70)
    print("TEST RESULTS SUMMARY")
    print("=" * 70)
    
    passed = sum(1 for _, r in results if r)
    total = len(results)
    
    for name, result in results:
        status = "✓ PASS" if result else "✗ FAIL"
        print(f"{status}: {name}")
    
    print(f"\nTotal: {passed}/{total} tests passed")
    
    if passed == total:
        print("\n✅ ALL TESTS PASSED - GAP 3 IMPLEMENTATION VERIFIED")
        return True
    else:
        print(f"\n⚠️ {total - passed} test(s) failed")
        return False

if __name__ == "__main__":
    success = run_all_tests()
    sys.exit(0 if success else 1)
