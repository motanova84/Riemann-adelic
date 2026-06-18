#!/usr/bin/env python3
"""
Standalone validation for Berry-Keating Omega-8 Operator.
No pytest dependencies - direct execution.
"""

import sys
from pathlib import Path
import numpy as np

# Add operators to path
repo_root = Path(__file__).parent
sys.path.insert(0, str(repo_root / "operators"))

from berry_keating_omega8_operator import (
    validate_omega8_operator,
    Omega8HilbertSpace,
    DilationOperator,
    sieve_of_eratosthenes
)

def test_basic_functionality():
    """Test basic operator functionality."""
    print("\n" + "="*70)
    print("TESTING BERRY-KEATING OMEGA-8 OPERATOR")
    print("="*70)
    
    # Test 1: Prime sieve
    print("\n[TEST 1] Prime sieve...")
    primes = sieve_of_eratosthenes(30)
    expected = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
    assert primes == expected, f"Prime sieve failed: {primes} != {expected}"
    print(f"   ✓ Generated {len(primes)} primes correctly")
    
    # Test 2: Hilbert space
    print("\n[TEST 2] Vortex 8 Hilbert space...")
    hilbert = Omega8HilbertSpace.create_symmetric_gaussian(N=64)
    assert len(hilbert.x_grid) == 64
    assert hilbert.is_symmetric
    assert np.isclose(hilbert.norm, 1.0, atol=0.01)
    print(f"   ✓ Created symmetric space with {len(hilbert.x_grid)} points")
    print(f"   ✓ Inversion symmetry: {hilbert.is_symmetric}")
    print(f"   ✓ Normalized: {hilbert.norm:.6f}")
    
    # Test 3: Dilation operator
    print("\n[TEST 3] Dilation operator...")
    x_grid = np.exp(np.linspace(-2, 2, 64))
    dilation = DilationOperator(x_grid)
    H0 = dilation.construct_matrix()
    
    # Check Hermiticity
    diff = np.max(np.abs(H0 - H0.conj().T))
    assert diff < 1e-10, f"H₀ not Hermitian: diff={diff}"
    print(f"   ✓ Constructed {H0.shape} matrix")
    print(f"   ✓ Hermiticity verified (diff={diff:.2e})")
    
    # Test 4: Full validation
    print("\n[TEST 4] Full operator validation...")
    certificate = validate_omega8_operator(N=64, coupling_g=0.5, n_zeros=10)
    
    assert "operator" in certificate
    assert certificate["operator"] == "Berry-Keating Omega-8"
    assert "coherence_psi" in certificate
    assert 0.0 <= certificate["coherence_psi"] <= 1.0
    
    print(f"\n   ✓ Certificate generated")
    print(f"   ✓ Operator: {certificate['operator']}")
    print(f"   ✓ Grid size: {certificate['grid_size']}")
    print(f"   ✓ Eigenvalues: {certificate['eigenvalues_computed']}")
    print(f"   ✓ Coherence Ψ: {certificate['coherence_psi']:.6f}")
    print(f"   ✓ Status: {certificate['status']}")
    
    print("\n" + "="*70)
    print("✅ ALL TESTS PASSED")
    print("="*70)
    print("\n∴𓂀Ω∞³Φ - QCAL VALIDATION COMPLETE")
    
    return certificate

if __name__ == "__main__":
    try:
        certificate = test_basic_functionality()
        sys.exit(0)
    except Exception as e:
        print(f"\n❌ TEST FAILED: {e}", file=sys.stderr)
        import traceback
        traceback.print_exc()
        sys.exit(1)
