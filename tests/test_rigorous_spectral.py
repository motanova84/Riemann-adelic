"""
Tests for rigorous_spectral.py

Validates the Legendre basis spectral computation implementation.
"""

import pytest
from mpmath import mp
from rigorous_spectral import rigorous_spectral_computation, verify_convergence


def test_basic_computation():
    """Test that basic computation runs without errors."""
    N = 5
    h = 0.01
    precision = 30
    
    zeros, eigenvalues_H = rigorous_spectral_computation(N, h, precision)
    
    # Check that we got results
    assert len(zeros) == N, f"Expected {N} zeros, got {len(zeros)}"
    assert len(eigenvalues_H) == N, f"Expected {N} eigenvalues, got {len(eigenvalues_H)}"
    
    # Check that eigenvalues are sorted
    for i in range(N-1):
        assert eigenvalues_H[i] <= eigenvalues_H[i+1], "Eigenvalues should be sorted"


def test_eigenvalue_positivity():
    """Test that eigenvalues are positive (coercivity)."""
    N = 5
    h = 0.01
    precision = 30
    
    zeros, eigenvalues_H = rigorous_spectral_computation(N, h, precision)
    
    # All eigenvalues should be positive
    for i, lam in enumerate(eigenvalues_H):
        assert lam > 0, f"Eigenvalue {i+1} = {lam} should be positive"


def test_zero_structure():
    """Test that zeros have the correct structure (0.5 + iγ)."""
    N = 5
    h = 0.01
    precision = 30
    
    zeros, eigenvalues_H = rigorous_spectral_computation(N, h, precision)
    
    for i, z in enumerate(zeros):
        # Real part should be 0.5
        assert abs(z.real - 0.5) < 1e-10, f"Zero {i+1} real part = {z.real}, expected 0.5"
        # Imaginary part should be non-negative
        assert z.imag >= 0, f"Zero {i+1} imaginary part = {z.imag} should be non-negative"


def test_eigenvalue_zero_relationship():
    """Test the relationship between eigenvalues and zeros: γ² = λ - 1/4."""
    N = 5
    h = 0.01
    precision = 30
    
    zeros, eigenvalues_H = rigorous_spectral_computation(N, h, precision)
    
    for i in range(N):
        gamma = zeros[i].imag
        lam = eigenvalues_H[i]
        
        # Check: γ² should equal λ - 1/4
        gamma_squared = gamma ** 2
        lam_minus_quarter = lam - 0.25
        
        # Allow for small numerical error
        rel_error = abs(gamma_squared - lam_minus_quarter) / max(abs(lam_minus_quarter), 1e-10)
        assert rel_error < 1e-6, f"For eigenvalue {i+1}: γ²={gamma_squared}, λ-1/4={lam_minus_quarter}"


def test_precision_setting():
    """Test that precision setting works."""
    N = 3
    h = 0.01
    
    # Low precision
    mp.dps = 15
    zeros1, eigs1 = rigorous_spectral_computation(N, h, precision=15)
    
    # High precision
    mp.dps = 30
    zeros2, eigs2 = rigorous_spectral_computation(N, h, precision=30)
    
    # Both should complete successfully
    assert len(zeros1) == N
    assert len(zeros2) == N


def test_h_parameter_effect():
    """Test that different h values give different results."""
    N = 3  # Use smaller N for faster test
    precision = 30
    
    zeros_h1, eigs_h1 = rigorous_spectral_computation(N, 0.01, precision)
    zeros_h2, eigs_h2 = rigorous_spectral_computation(N, 0.005, precision)
    
    # Results should be different
    # (smaller h should give larger eigenvalues)
    assert eigs_h2[0] > eigs_h1[0], "Smaller h should give larger eigenvalues"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
