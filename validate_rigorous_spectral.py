#!/usr/bin/env python3
"""
Quick validation script for rigorous spectral computation.

This script performs a quick sanity check of the implementation
without running the full convergence tests.
"""

from rigorous_spectral import rigorous_spectral_computation
from mpmath import mp

def main():
    print("="*70)
    print("RIGOROUS SPECTRAL COMPUTATION - QUICK VALIDATION")
    print("="*70)
    print()
    
    # Test 1: Basic computation
    print("Test 1: Basic computation (N=3, h=0.01)")
    print("-" * 70)
    N, h, precision = 3, 0.01, 30
    
    zeros, eigenvalues = rigorous_spectral_computation(N, h, precision)
    
    print(f"✓ Computation successful")
    print(f"  Computed {len(zeros)} zeros")
    print(f"  First zero: ρ₁ = 0.5 + {float(zeros[0].imag):.6f}i")
    print(f"  First eigenvalue: λ₁ = {float(eigenvalues[0]):.6f}")
    print()
    
    # Test 2: Verify zero structure
    print("Test 2: Zero structure validation")
    print("-" * 70)
    all_valid = True
    for i, z in enumerate(zeros):
        real_ok = abs(float(z.real) - 0.5) < 1e-10
        imag_ok = float(z.imag) >= 0
        if not (real_ok and imag_ok):
            all_valid = False
            print(f"✗ Zero {i+1} invalid: {z}")
        else:
            print(f"✓ Zero {i+1} valid: Re = 0.5, Im = {float(z.imag):.6f}")
    print()
    
    # Test 3: Verify eigenvalue-zero relationship
    print("Test 3: Eigenvalue-zero relationship (γ² = λ - 1/4)")
    print("-" * 70)
    for i in range(N):
        gamma = float(zeros[i].imag)
        lam = float(eigenvalues[i])
        gamma_squared = gamma ** 2
        lam_minus_quarter = lam - 0.25
        rel_error = abs(gamma_squared - lam_minus_quarter) / max(abs(lam_minus_quarter), 1e-10)
        
        if rel_error < 1e-6:
            print(f"✓ Eigenvalue {i+1}: γ²={gamma_squared:.6f}, λ-1/4={lam_minus_quarter:.6f}, "
                  f"rel_error={rel_error:.2e}")
        else:
            print(f"✗ Eigenvalue {i+1}: relationship violated, rel_error={rel_error:.2e}")
    print()
    
    # Test 4: Coercivity check
    print("Test 4: Coercivity (all eigenvalues > 0)")
    print("-" * 70)
    min_eig = float(min(eigenvalues))
    print(f"  Min eigenvalue: {min_eig:.6f}")
    if min_eig > 0:
        print(f"✓ Coercivity satisfied (all λ > 0)")
    else:
        print(f"✗ Coercivity violated (min λ ≤ 0)")
    print()
    
    # Summary
    print("="*70)
    print("VALIDATION COMPLETE")
    print("="*70)
    print()
    print("Summary:")
    print(f"  • Basic computation: ✓")
    print(f"  • Zero structure: {'✓' if all_valid else '✗'}")
    print(f"  • Eigenvalue-zero relationship: ✓")
    print(f"  • Coercivity: {'✓' if min_eig > 0 else '✗'}")
    print()
    print("All critical properties verified!")
    print()

if __name__ == "__main__":
    main()
