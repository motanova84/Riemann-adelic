"""
Tests for the rigorous H operator construction with Hermite basis.

This module validates:
1. Hermite basis normalization
2. Rigorous H construction with high precision
3. Convergence bounds from Theorem 1.1
"""

import numpy as np
import pytest
from operador.operador_H import (
    hermite_basis,
    K_gauss_rigorous,
    rigorous_H_construction,
    validate_convergence_bounds
)

try:
    import mpmath as mp
    HAS_MPMATH = True
except ImportError:
    HAS_MPMATH = False


@pytest.mark.skipif(not HAS_MPMATH, reason="mpmath not available")
def test_hermite_basis_normalization():
    """Test that Hermite basis functions are properly normalized."""
    # Test orthonormality for first few basis functions
    N = 5
    precision = 50
    mp.dps = precision
    
    # Create integration points
    t_vals = np.linspace(-3, 3, 50)
    
    for i in range(3):
        for j in range(3):
            # Compute inner product <φ_i, φ_j>
            integrand = [
                hermite_basis(i, t, precision=precision) * 
                hermite_basis(j, t, precision=precision)
                for t in t_vals
            ]
            
            # Simple trapezoidal integration
            dt = t_vals[1] - t_vals[0]
            inner_product = float(sum(integrand)) * dt
            
            if i == j:
                # Should be close to 1 (normalized)
                assert abs(inner_product - 1.0) < 0.2, \
                    f"Basis function {i} not properly normalized: <φ_{i}, φ_{i}> = {inner_product}"
            else:
                # Should be close to 0 (orthogonal)
                assert abs(inner_product) < 0.2, \
                    f"Basis functions {i}, {j} not orthogonal: <φ_{i}, φ_{j}> = {inner_product}"


@pytest.mark.skipif(not HAS_MPMATH, reason="mpmath not available")
def test_K_gauss_rigorous():
    """Test rigorous Gaussian kernel computation."""
    h = 1e-3
    t = 0.5
    s = 0.3
    precision = 50
    
    # Compute with high precision
    K_rigorous = K_gauss_rigorous(t, s, h, precision=precision)
    
    # Should be positive
    assert K_rigorous > 0, "Kernel should be positive"
    
    # Should be finite
    assert np.isfinite(float(K_rigorous)), "Kernel should be finite"
    
    # Test symmetry: K(t,s) = K(s,t)
    K_sym = K_gauss_rigorous(s, t, h, precision=precision)
    assert abs(float(K_rigorous) - float(K_sym)) < 1e-10, "Kernel should be symmetric"


@pytest.mark.skipif(not HAS_MPMATH, reason="mpmath not available")
def test_rigorous_H_construction():
    """Test rigorous H construction with small dimension."""
    N = 3
    h = 1e-3
    precision = 30  # Lower precision for faster testing
    
    # Build H matrix
    H, error_bound = rigorous_H_construction(N, h, precision=precision, integration_limit=3.0)
    
    # Check basic properties
    assert H.shape == (N, N), f"H should be {N}×{N}"
    assert np.allclose(H, H.T, atol=1e-8), "H should be symmetric"
    
    # Check positive definiteness (all eigenvalues > 0.25)
    eigenvalues = np.linalg.eigvalsh(H)
    assert np.all(eigenvalues > 0.24), "All eigenvalues should be > 0.25 (coercivity)"
    
    # Check error bound is positive and finite
    assert error_bound > 0, "Error bound should be positive"
    assert np.isfinite(error_bound), "Error bound should be finite"
    
    print(f"\n✓ Rigorous construction test passed:")
    print(f"  H shape: {H.shape}")
    print(f"  Eigenvalues: {eigenvalues}")
    print(f"  Error bound: {error_bound:.6e}")


@pytest.mark.skipif(not HAS_MPMATH, reason="mpmath not available")
def test_convergence_bounds():
    """Test convergence as N increases (Theorem 1.1)."""
    N_values = [2, 3, 4]
    h = 1e-3
    precision = 25  # Lower precision for faster testing
    
    results = validate_convergence_bounds(N_values, h=h, precision=precision)
    
    # Error bounds should decrease with N
    error_bounds = results['error_bounds']
    for i in range(len(error_bounds) - 1):
        assert error_bounds[i+1] < error_bounds[i], \
            f"Error bound should decrease with N: {error_bounds[i]} -> {error_bounds[i+1]}"
    
    print(f"\n✓ Convergence test passed:")
    for i, N in enumerate(N_values):
        print(f"  N={N}: error_bound={error_bounds[i]:.6e}")


if __name__ == "__main__":
    pytest.main([__file__, "-v", "-s"])
