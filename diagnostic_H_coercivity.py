#!/usr/bin/env python3
"""
Diagnostic script for testing H operator coercivity and positive definiteness.

This script runs the diagnostic test from the problem statement to verify that
the operator H constructed in operador_H_real.py is positive definite.
"""

import sys
from pathlib import Path

# Add spectral_RH to path for imports
sys.path.insert(0, str(Path(__file__).parent / "spectral_RH"))

from operador.operador_H_real import build_H_real
import numpy as np


def test_H_positive_definite(n_basis=50, t=0.01, verbose=True):
    """
    Test básico de coercividad - verifies that H is positive definite.
    
    A positive definite operator H must have all eigenvalues > 0.
    This is critical for the Riemann Hypothesis framework because:
    - H represents the thermal kernel operator
    - Positive definiteness ensures well-defined spectral inversion
    - Eigenvalues λ relate to zeros via: ρ = 1/2 + i√(λ - 1/4)
    
    Args:
        n_basis: Number of basis functions (matrix size)
        t: Thermal parameter
        verbose: Print detailed output
        
    Returns:
        bool: True if all eigenvalues are positive (test passes)
    """
    if verbose:
        print("=" * 60)
        print("DIAGNOSTIC TEST: H OPERATOR POSITIVE DEFINITENESS")
        print("=" * 60)
        print(f"Matrix size: {n_basis}x{n_basis}")
        print(f"Thermal parameter t: {t}")
        print()
    
    # Build operator H
    H = build_H_real(n_basis=n_basis, t=t)
    
    # Compute eigenvalues (real symmetric matrix)
    eigenvalues = np.linalg.eigvalsh(H)
    
    min_eigenval = np.min(eigenvalues)
    max_eigenval = np.max(eigenvalues)
    all_positive = np.all(eigenvalues > 0)
    
    if verbose:
        print()
        print("EIGENVALUE ANALYSIS:")
        print(f"  Min eigenvalue: {min_eigenval:.10f}")
        print(f"  Max eigenvalue: {max_eigenval:.10f}")
        print(f"  Number of eigenvalues: {len(eigenvalues)}")
        print(f"  All positive: {all_positive}")
        print()
        
        # Show first few eigenvalues
        print("First 5 eigenvalues:")
        for i, λ in enumerate(eigenvalues[:5]):
            # Convert to zero: ρ = 1/2 + iγ where γ = √(λ - 1/4)
            γ = np.sqrt(max(λ - 0.25, 0))
            print(f"  λ_{i+1} = {λ:.6f}  →  ρ = 0.5 + {γ:.6f}i")
        print()
        
        if all_positive:
            print("✅ TEST PASSED: H is positive definite")
            print("   All eigenvalues are positive, confirming coercivity:")
            print("   <f, Hf> > 0 for all non-zero f")
        else:
            print("❌ TEST FAILED: H is NOT positive definite")
            print("   Found negative eigenvalues - operator is not coercive")
            negative_count = np.sum(eigenvalues <= 0)
            print(f"   Number of non-positive eigenvalues: {negative_count}")
        print("=" * 60)
    else:
        print(f"Min eigenvalue: {min_eigenval}")
        print(f"Max eigenvalue: {max_eigenval}")
        print(f"Test passed: {all_positive}")
    
    return all_positive


def test_coercivity_with_vectors(n_basis=10, t=0.01, n_trials=20):
    """
    Test coercivity directly: <f, Hf> ≥ 0 for random vectors.
    
    This tests the quadratic form directly to verify that
    H is positive semidefinite by checking random vectors.
    
    Args:
        n_basis: Matrix size
        t: Thermal parameter
        n_trials: Number of random vectors to test
        
    Returns:
        bool: True if all quadratic forms are non-negative
    """
    print()
    print("COERCIVITY TEST: Random vector verification")
    print("-" * 60)
    
    H = build_H_real(n_basis=n_basis, t=t)
    
    all_nonnegative = True
    min_quadratic = float('inf')
    
    for trial in range(n_trials):
        # Random test vector
        f = np.random.randn(n_basis)
        f = f / np.linalg.norm(f)  # Normalize
        
        # Compute quadratic form <f, Hf>
        quadratic_form = f @ H @ f
        
        min_quadratic = min(min_quadratic, quadratic_form)
        
        if quadratic_form < 0:
            all_nonnegative = False
            print(f"  Trial {trial+1}: <f,Hf> = {quadratic_form:.10f} ❌ NEGATIVE")
        elif trial < 5:  # Show first few
            print(f"  Trial {trial+1}: <f,Hf> = {quadratic_form:.10f} ✓")
    
    print()
    print(f"Minimum quadratic form over {n_trials} trials: {min_quadratic:.10f}")
    
    if all_nonnegative:
        print("✅ Coercivity verified: <f,Hf> ≥ 0 for all test vectors")
    else:
        print("❌ Coercivity violated: Found negative quadratic forms")
    
    print("-" * 60)
    return all_nonnegative


def main():
    """Run all diagnostic tests."""
    print()
    print("╔" + "═" * 58 + "╗")
    print("║" + " " * 10 + "H OPERATOR DIAGNOSTIC SUITE" + " " * 21 + "║")
    print("╚" + "═" * 58 + "╝")
    print()
    
    # Test 1: Positive definiteness with n_basis=50
    result1 = test_H_positive_definite(n_basis=50, t=0.01, verbose=True)
    
    # Test 2: Coercivity with random vectors
    result2 = test_coercivity_with_vectors(n_basis=10, t=0.01, n_trials=20)
    
    # Summary
    print()
    print("=" * 60)
    print("DIAGNOSTIC SUMMARY")
    print("=" * 60)
    print(f"  Positive definiteness test: {'✅ PASSED' if result1 else '❌ FAILED'}")
    print(f"  Coercivity test:            {'✅ PASSED' if result2 else '❌ FAILED'}")
    print()
    
    if result1 and result2:
        print("🎉 ALL TESTS PASSED")
        print("   Operator H is correctly positive definite and coercive.")
        return 0
    else:
        print("⚠️  SOME TESTS FAILED")
        print("   Review operator construction in operador_H_real.py")
        return 1


if __name__ == "__main__":
    exit_code = main()
    sys.exit(exit_code)
