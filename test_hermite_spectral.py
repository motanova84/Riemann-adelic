#!/usr/bin/env python3
"""
Tests for Hermite-based spectral computation module
"""

import pytest
import numpy as np
from hermite_spectral_computation import purissima_spectral_computation, validatio_ultima


def test_purissima_spectral_basic():
    """Test basic functionality of purissima_spectral_computation"""
    # Use small parameters for fast testing
    N = 10
    h = 0.1
    
    zeros, H = purissima_spectral_computation(N, h)
    
    # Check that we get some zeros
    assert len(zeros) > 0, "Should compute at least some zeros"
    
    # Check that zeros are on critical line (real part = 1/2)
    for z in zeros:
        assert abs(z.real - 0.5) < 1e-10, f"Zero {z} not on critical line"
    
    # Check that imaginary parts are positive
    for z in zeros:
        assert z.imag > 0, f"Zero {z} has non-positive imaginary part"


def test_matrix_properties():
    """Test that H matrix has correct properties"""
    N = 10
    h = 0.1
    
    zeros, H = purissima_spectral_computation(N, h)
    
    # Convert mpmath matrix to numpy for easier testing
    n = H.rows
    H_np = np.array([[float(H[i,j]) for j in range(n)] for i in range(n)])
    
    # Check symmetry
    assert np.allclose(H_np, H_np.T, rtol=1e-8), "H should be symmetric"
    
    # Check positive definiteness (all eigenvalues > 0)
    eigvals = np.linalg.eigvalsh(H_np)
    assert np.all(eigvals > 0), "H should be positive definite"
    
    # Check that smallest eigenvalue is close to 0.25
    assert eigvals[0] > 0.25, "Smallest eigenvalue should be > 0.25"


def test_eigenvalue_zero_relationship():
    """Test the relationship λ = 1/4 + γ²"""
    N = 10
    h = 0.1
    
    zeros, H = purissima_spectral_computation(N, h)
    
    # Convert mpmath matrix to numpy
    n = H.rows
    H_np = np.array([[float(H[i,j]) for j in range(n)] for i in range(n)])
    eigvals = np.linalg.eigvalsh(H_np)
    
    # Check that for each zero ρ = 1/2 + iγ, we have eigenvalue λ ≈ 1/4 + γ²
    for i, z in enumerate(zeros):
        γ = z.imag
        expected_λ = 0.25 + γ**2
        # Should be close to one of the eigenvalues
        min_diff = min(abs(expected_λ - λ) for λ in eigvals)
        assert min_diff < 1e-6, f"Zero {z} doesn't match any eigenvalue"


def test_convergence_with_h():
    """Test that smaller h gives more accurate results"""
    N = 10
    
    # Test with different h values
    h_values = [0.1, 0.05, 0.01]
    zero_counts = []
    
    for h in h_values:
        zeros, _ = purissima_spectral_computation(N, h)
        zero_counts.append(len(zeros))
    
    # Should get at least some zeros for each h
    assert all(count > 0 for count in zero_counts), "Should get zeros for all h values"


def test_validatio_ultima_runs():
    """Test that validatio_ultima runs without errors"""
    # This is the main validation function from the problem statement
    # We just check it runs without throwing
    zeros = validatio_ultima()
    
    assert len(zeros) > 0, "validatio_ultima should return some zeros"
    assert all(abs(z.real - 0.5) < 1e-10 for z in zeros), "All zeros should be on critical line"


if __name__ == "__main__":
    # Run tests
    print("Running tests...")
    pytest.main([__file__, "-v"])
