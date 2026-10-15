#!/usr/bin/env python3
"""
Debug script to understand the golden ratio kernel behavior.
"""

import numpy as np
from scipy.linalg import eigh
from scipy.special import sinc as scipy_sinc

PHI = (1 + np.sqrt(5)) / 2
INV_PHI = 1 / PHI

def test_kernel_simple(L=10, N=50):
    """Simple test with small L and N."""
    print(f"\n=== Testing L={L}, N={N} ===")
    
    # Gauss-Legendre quadrature
    x_gauss, w_gauss = np.polynomial.legendre.leggauss(N)
    x = L/2 * (x_gauss + 1)
    w = w_gauss * L/2
    
    print(f"x range: [{x.min():.4f}, {x.max():.4f}]")
    print(f"Sum of weights: {w.sum():.4f} (should be ≈ {L})")
    
    # Build kernel matrix
    K = np.zeros((N, N))
    for i in range(N):
        for j in range(N):
            if i == j:
                K[i, j] = w[j] * x[i]
            else:
                K[i, j] = w[j] * scipy_sinc(x[i] - x[j]) * np.sqrt(x[i] * x[j])
    
    # Check symmetry
    symm_err = np.max(np.abs(K - K.T))
    print(f"Symmetry error: {symm_err:.2e}")
    
    # Eigenvalues
    evals = eigh(K, eigvals_only=True)
    lambda_max = evals[-1]
    lambda_min = evals[0]
    
    print(f"λ_max = {lambda_max:.6f}")
    print(f"λ_min = {lambda_min:.6f}")
    print(f"Trace = {np.trace(K):.6f}")
    print(f"Sum of eigenvalues = {evals.sum():.6f}")
    
    # Compute α
    alpha = np.pi * lambda_max / (2 * L)
    print(f"α(L) = π*λ_max/(2L) = {alpha:.6f}")
    print(f"Target 1/Φ = {INV_PHI:.6f}")
    print(f"Error = {abs(alpha - INV_PHI):.6f}")
    
    # Expected scaling: λ_max ~ 2L/(πΦ)
    lambda_expected = 2 * L / (np.pi * PHI)
    print(f"\nExpected λ_max ≈ 2L/(πΦ) = {lambda_expected:.6f}")
    print(f"Ratio actual/expected = {lambda_max / lambda_expected:.6f}")
    
    return alpha, lambda_max


def test_scaling():
    """Test if λ_max scales linearly with L."""
    print("\n" + "="*60)
    print("TESTING SCALING: λ_max vs L")
    print("="*60)
    
    L_vals = [5, 10, 20, 50]
    N_vals = [100, 100, 150, 200]
    
    results = []
    for L, N in zip(L_vals, N_vals):
        alpha, lambda_max = test_kernel_simple(L, N)
        results.append({
            'L': L,
            'N': N,
            'lambda_max': lambda_max,
            'alpha': alpha,
            'lambda_over_L': lambda_max / L
        })
    
    print("\n" + "="*60)
    print("SUMMARY:")
    print(f"{'L':<10} {'N':<10} {'λ_max':<15} {'α(L)':<15} {'λ_max/L':<15}")
    print("-"*60)
    for r in results:
        print(f"{r['L']:<10} {r['N']:<10} {r['lambda_max']:<15.6f} "
              f"{r['alpha']:<15.6f} {r['lambda_over_L']:<15.6f}")
    
    # Expected λ/L ratio: 2/(πΦ) ≈ 0.393
    expected_ratio = 2 / (np.pi * PHI)
    print(f"\nExpected λ_max/L → 2/(πΦ) ≈ {expected_ratio:.6f}")
    

if __name__ == "__main__":
    print("Golden Ratio Kernel Debug Tests")
    print("="*60)
    test_scaling()
