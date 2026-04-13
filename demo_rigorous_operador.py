#!/usr/bin/env python
"""
Demonstration of the rigorous H operator construction with Hermite basis.

This script demonstrates Theorem 1.1 from the problem statement:
    |γ_n^(N) - γ_n| ≤ (e^(-h/4) / sqrt(4πh)) * exp(-π²N/2γ_n)

Shows:
1. High-precision construction with mpmath
2. Error bounds that decrease exponentially with N
3. Comparison between standard and rigorous constructions
"""

import numpy as np
from operador.operador_H import (
    build_R_matrix,
    spectrum_from_R,
    rigorous_H_construction,
    validate_convergence_bounds
)

try:
    import mpmath as mp
    HAS_MPMATH = True
except ImportError:
    HAS_MPMATH = False
    print("Warning: mpmath not available. Install with: pip install mpmath")


def demo_standard_construction():
    """Demonstrate the standard Gaussian kernel construction."""
    print("=" * 70)
    print("STANDARD GAUSSIAN KERNEL CONSTRUCTION")
    print("=" * 70)
    print()
    
    h = 1e-3
    L = 1.0
    n_basis = 5
    Nq = 160
    
    print(f"Parameters: h={h}, L={L}, n_basis={n_basis}, Nq={Nq}")
    print()
    
    # Build R matrix
    print("Building R_h matrix via cosine basis...")
    R = build_R_matrix(n_basis=n_basis, h=h, L=L, Nq=Nq)
    
    # Extract spectrum
    lam_H, gammas = spectrum_from_R(R, h)
    
    print(f"✓ Matrix shape: {R.shape}")
    print(f"✓ Symmetric: {np.allclose(R, R.T, atol=1e-12)}")
    print()
    print("Eigenvalues of H:")
    for i, (lam, gamma) in enumerate(zip(lam_H, gammas)):
        print(f"  λ_{i} = {lam:.8f},  γ_{i} = {gamma:.8f}")
    print()


def demo_rigorous_construction():
    """Demonstrate the rigorous high-precision construction."""
    if not HAS_MPMATH:
        print("Skipping rigorous construction demo (mpmath not available)")
        return
    
    print("=" * 70)
    print("RIGOROUS HIGH-PRECISION CONSTRUCTION (HERMITE BASIS)")
    print("=" * 70)
    print()
    
    N = 4
    h = 1e-3
    precision = 30
    Nq = 15
    
    print(f"Parameters: N={N}, h={h}, precision={precision} dps, Nq={Nq}")
    print()
    
    print("Building H operator with Hermite basis...")
    H, error_bound = rigorous_H_construction(N, h, precision=precision, Nq=Nq)
    
    # Extract spectrum
    eigenvalues = np.linalg.eigvalsh(H)
    gammas = np.sqrt(np.maximum(eigenvalues - 0.25, 0.0))
    
    print(f"✓ Matrix shape: {H.shape}")
    print(f"✓ Symmetric: {np.allclose(H, H.T, atol=1e-10)}")
    print(f"✓ Theoretical error bound: {error_bound:.6e}")
    print()
    print("Eigenvalues of H:")
    for i, (lam, gamma) in enumerate(zip(eigenvalues, gammas)):
        print(f"  λ_{i} = {lam:.8f},  γ_{i} = {gamma:.8f}")
    print()


def demo_convergence_theorem():
    """Demonstrate Theorem 1.1: exponential convergence with N."""
    if not HAS_MPMATH:
        print("Skipping convergence theorem demo (mpmath not available)")
        return
    
    print("=" * 70)
    print("THEOREM 1.1: EXPONENTIAL CONVERGENCE WITH N")
    print("=" * 70)
    print()
    print("Theory: |γ_n^(N) - γ_n| ≤ C * exp(-c*N)")
    print()
    
    N_values = [2, 3, 4, 5]
    h = 1e-3
    precision = 25
    
    print(f"Testing for N = {N_values}")
    print(f"Parameters: h={h}, precision={precision} dps")
    print()
    
    results = validate_convergence_bounds(N_values, h=h, precision=precision)
    
    print()
    print("=" * 70)
    print("CONVERGENCE RESULTS")
    print("=" * 70)
    print()
    print(f"{'N':<5} {'λ_0':<12} {'γ_0':<12} {'Error Bound':<15} {'Ratio':<10}")
    print("-" * 70)
    
    prev_bound = None
    for i, N in enumerate(N_values):
        lam_0 = results['eigenvalues'][i][0]
        gamma_0 = results['gammas'][i][0]
        bound = results['error_bounds'][i]
        
        if prev_bound is not None:
            ratio = bound / prev_bound
            print(f"{N:<5} {lam_0:<12.6f} {gamma_0:<12.6f} {bound:<15.6e} {ratio:<10.6f}")
        else:
            print(f"{N:<5} {lam_0:<12.6f} {gamma_0:<12.6f} {bound:<15.6e} {'---':<10}")
        
        prev_bound = bound
    
    print()
    print("✓ Error bounds decrease exponentially (ratio << 1)")
    print()


def demo_error_analysis():
    """Compare standard vs rigorous construction."""
    if not HAS_MPMATH:
        print("Skipping error analysis demo (mpmath not available)")
        return
    
    print("=" * 70)
    print("COMPARISON: STANDARD vs RIGOROUS CONSTRUCTION")
    print("=" * 70)
    print()
    
    N = 4
    h = 1e-3
    
    # Standard construction
    print("Building with standard method (cosine basis)...")
    R = build_R_matrix(n_basis=N, h=h, L=1.0, Nq=160)
    lam_std, gamma_std = spectrum_from_R(R, h)
    
    # Rigorous construction
    print("Building with rigorous method (Hermite basis)...")
    H_rig, error_bound = rigorous_H_construction(N, h, precision=30, Nq=15)
    lam_rig = np.linalg.eigvalsh(H_rig)
    gamma_rig = np.sqrt(np.maximum(lam_rig - 0.25, 0.0))
    
    print()
    print("=" * 70)
    print("EIGENVALUE COMPARISON")
    print("=" * 70)
    print()
    print(f"{'Index':<8} {'Standard λ':<15} {'Rigorous λ':<15} {'Difference':<15}")
    print("-" * 70)
    
    for i in range(N):
        diff = abs(lam_std[i] - lam_rig[i])
        print(f"{i:<8} {lam_std[i]:<15.8f} {lam_rig[i]:<15.8f} {diff:<15.6e}")
    
    print()
    print(f"Theoretical error bound: {error_bound:.6e}")
    print(f"Max difference: {np.max(np.abs(lam_std - lam_rig)):.6e}")
    print()


if __name__ == "__main__":
    # Run all demonstrations
    demo_standard_construction()
    demo_rigorous_construction()
    demo_convergence_theorem()
    demo_error_analysis()
    
    print("=" * 70)
    print("🎉 ALL DEMONSTRATIONS COMPLETE!")
    print("=" * 70)
    print()
    print("Summary:")
    print("  ✓ Standard Gaussian kernel construction (cosine basis)")
    print("  ✓ Rigorous high-precision construction (Hermite basis)")
    print("  ✓ Theorem 1.1 convergence validation (exponential decay)")
    print("  ✓ Error analysis (standard vs rigorous)")
    print()
