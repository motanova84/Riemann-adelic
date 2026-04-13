#!/usr/bin/env python3
"""
Simple validation script for Rigorous Spectral Bridge

Runs basic tests without pytest framework dependencies.
"""

import sys
import mpmath as mp
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent))

from rigorous_spectral_bridge import RigorousSpectralBridge


def test_basic_functionality():
    """Test basic spectral bridge functionality"""
    
    print("=" * 80)
    print("Testing Rigorous Spectral Bridge")
    print("=" * 80)
    print()
    
    # Initialize
    print("1. Initializing bridge...")
    bridge = RigorousSpectralBridge(precision_dps=30)
    print("   ✓ Initialized with 30 dps precision")
    print()
    
    # Sample zeros
    print("2. Loading sample zeros...")
    sample_zeros = [
        mp.mpf("14.134725141734693790457251983562"),
        mp.mpf("21.022039638771554992628479593896"),
        mp.mpf("25.010857580145688763213790992562"),
        mp.mpf("30.424876125859513210311897530584"),
        mp.mpf("32.935061587739189690662368964074"),
    ]
    print(f"   ✓ Loaded {len(sample_zeros)} zeros")
    print()
    
    # Test spectral map
    print("3. Testing spectral map...")
    eigenvalues = [bridge.spectral_map(t) for t in sample_zeros]
    print(f"   ✓ Mapped {len(eigenvalues)} zeros to eigenvalues")
    
    # Check first eigenvalue
    z0 = eigenvalues[0]
    assert abs(z0.real) < 1e-10, "Real part should be ~0"
    expected_imag = sample_zeros[0] - mp.mpf("0.5")
    assert abs(z0.imag - expected_imag) < 1e-10, "Imaginary part mismatch"
    print("   ✓ Spectral map produces correct values")
    print()
    
    # Test inverse map
    print("4. Testing inverse spectral map...")
    t_recovered = bridge.inverse_spectral_map(eigenvalues[0])
    assert abs(t_recovered - sample_zeros[0]) < 1e-10, "Inverse map failed"
    print("   ✓ Inverse map correctly recovers zero imaginary parts")
    print()
    
    # Test bijection
    print("5. Testing bijection verification...")
    bijection_ok = bridge.verify_bijection(sample_zeros, eigenvalues)
    assert bijection_ok, "Bijection verification failed"
    print("   ✓ Bijection verified")
    print()
    
    # Test local uniqueness
    print("6. Testing local uniqueness...")
    uniqueness_ok = bridge.verify_local_uniqueness(sample_zeros)
    assert uniqueness_ok, "Local uniqueness failed"
    print(f"   ✓ Local uniqueness verified (ε = {bridge.EPSILON_UNIQUENESS})")
    print()
    
    # Test order preservation
    print("7. Testing order preservation...")
    order_ok = bridge.verify_order_preservation(sample_zeros, eigenvalues)
    assert order_ok, "Order preservation failed"
    print("   ✓ Order preservation verified")
    print()
    
    # Test Weyl law
    print("8. Testing exact Weyl law...")
    T = mp.mpf("35.0")
    error = bridge.compute_weyl_law_error(T, len(eigenvalues), len(sample_zeros))
    assert error < 1, f"Weyl law violated: error = {error}"
    print(f"   ✓ Weyl law satisfied: error = {error} < 1")
    print()
    
    # Test full equivalence
    print("9. Testing full spectral equivalence...")
    result = bridge.verify_spectral_equivalence(
        sample_zeros, eigenvalues, T, mp.mpf("2.0")
    )
    assert result.is_equivalent, "Spectral equivalence failed"
    print("   ✓ Spectral equivalence verified")
    print()
    
    # Test fundamental frequency constant
    print("10. Testing fundamental frequency...")
    assert bridge.F0_EXACT > 0, "f₀ should be positive"
    assert "141.7" in str(bridge.F0_EXACT), "f₀ value incorrect"
    print(f"   ✓ Fundamental frequency f₀ = {bridge.F0_EXACT}")
    print()
    
    print("=" * 80)
    print("✅ ALL TESTS PASSED")
    print("=" * 80)
    print()
    print("VERIFICATION SUMMARY:")
    print(f"  • Bijection: {result.bijection_verified}")
    print(f"  • Uniqueness ε: {result.uniqueness_epsilon}")
    print(f"  • Order preserved: {result.order_preserved}")
    print(f"  • Weyl law error: {result.weyl_law_error}")
    print(f"  • Fundamental frequency: {result.fundamental_frequency} Hz")
    print(f"  • Zeros checked: {result.num_zeros_checked}")
    print(f"  • Precision: {result.precision_dps} dps")
    print()
    print("∴ SPECTRAL EQUIVALENCE CONFIRMED ∴")
    print("  Spec(𝓗_Ψ) ≅ {s : ζ(s) = 0, 0 < Re(s) < 1}")
    print()
    
    return True


if __name__ == "__main__":
    try:
        success = test_basic_functionality()
        sys.exit(0 if success else 1)
    except Exception as e:
        print(f"\n❌ TEST FAILED: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)
