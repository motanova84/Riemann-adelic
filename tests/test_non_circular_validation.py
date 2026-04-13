"""
Tests for non-circular H_ε validation.

Validates the construction and basic properties of the operator.
"""

import pytest
import numpy as np
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from validate_non_circular_h_epsilon import (
    load_riemann_zeros_lmfdb,
    riemann_von_mangoldt_estimate,
    construct_H_epsilon_theory,
    compute_eigenvalues,
    compare_with_zeros,
    p_adic_correction_term,
    coupling_coefficient
)


class TestRiemannZeroLoading:
    """Test loading of Riemann zeros."""
    
    def test_load_first_30_zeros(self):
        """Should load first 30 zeros without calculation."""
        zeros = load_riemann_zeros_lmfdb(30)
        assert len(zeros) == 30
        assert zeros[0] > 14.1  # First zero around 14.13
        assert zeros[0] < 14.2
        
    def test_zeros_monotonic(self):
        """Zeros should be monotonically increasing."""
        zeros = load_riemann_zeros_lmfdb(20)
        assert np.all(np.diff(zeros) > 0)


class TestRiemannVonMangoldtEstimate:
    """Test the zero estimation formula."""
    
    def test_first_zero_estimate(self):
        """First zero estimate should be close to actual."""
        est = riemann_von_mangoldt_estimate(0)
        assert 14.0 < est < 14.5
        
    def test_estimates_positive(self):
        """All estimates should be positive."""
        for n in range(20):
            est = riemann_von_mangoldt_estimate(n)
            assert est > 0, f"Estimate for n={n} should be positive"
            
    def test_estimates_increasing(self):
        """Estimates should generally increase."""
        estimates = [riemann_von_mangoldt_estimate(n) for n in range(10)]
        # Most should be increasing (allowing for some variation)
        increases = sum(1 for i in range(len(estimates)-1) 
                       if estimates[i+1] > estimates[i])
        assert increases >= 7, "Estimates should mostly increase"


class TestPAdicCorrections:
    """Test p-adic correction terms."""
    
    def test_correction_is_complex(self):
        """P-adic correction should return complex number."""
        corr = p_adic_correction_term(0, primes_count=10)
        assert isinstance(corr, complex)
        
    def test_correction_magnitude_bounded(self):
        """Correction magnitude should be reasonable."""
        for n in range(10):
            corr = p_adic_correction_term(n, primes_count=20)
            assert abs(corr) < 1.0, f"Correction too large for n={n}"


class TestCouplingCoefficient:
    """Test coupling coefficients."""
    
    def test_adjacent_coupling_nonzero(self):
        """Adjacent states should have nonzero coupling."""
        coup = coupling_coefficient(0, 1, eps=0.01)
        assert coup != 0
        
    def test_distant_coupling_zero(self):
        """Distant states should have zero coupling."""
        coup = coupling_coefficient(0, 10, eps=0.01)
        assert coup == 0
        
    def test_coupling_scales_with_eps(self):
        """Coupling should scale with epsilon."""
        coup1 = coupling_coefficient(0, 1, eps=0.001)
        coup2 = coupling_coefficient(0, 1, eps=0.01)
        assert abs(coup2) > abs(coup1)


class TestHEpsilonConstruction:
    """Test H_ε operator construction."""
    
    def test_matrix_dimensions(self):
        """Matrix should have correct dimensions."""
        N = 50
        H = construct_H_epsilon_theory(N, eps=0.001, primes_count=10)
        assert H.shape == (N, N)
        
    def test_matrix_symmetric(self):
        """Matrix should be symmetric."""
        N = 30
        H = construct_H_epsilon_theory(N, eps=0.001, primes_count=10)
        assert np.allclose(H, H.T), "H_ε should be symmetric"
        
    def test_matrix_real(self):
        """Matrix should be real (not complex)."""
        N = 30
        H = construct_H_epsilon_theory(N, eps=0.001, primes_count=10)
        assert np.all(np.isreal(H)), "H_ε should be real"
        
    def test_diagonal_positive(self):
        """Diagonal elements should be positive."""
        N = 30
        H = construct_H_epsilon_theory(N, eps=0.001, primes_count=10)
        diag = np.diag(H)
        assert np.all(diag > 0), "Diagonal should be positive"


class TestEigenvalueComputation:
    """Test eigenvalue computation."""
    
    def test_eigenvalues_real(self):
        """Eigenvalues of symmetric matrix should be real."""
        N = 20
        H = construct_H_epsilon_theory(N, eps=0.001, primes_count=5)
        eigenvalues = compute_eigenvalues(H)
        assert np.all(np.isreal(eigenvalues))
        
    def test_eigenvalues_sorted(self):
        """Eigenvalues should be sorted."""
        N = 20
        H = construct_H_epsilon_theory(N, eps=0.001, primes_count=5)
        eigenvalues = compute_eigenvalues(H)
        assert np.all(np.diff(eigenvalues) >= 0), "Eigenvalues should be sorted"
        
    def test_eigenvalues_positive(self):
        """Eigenvalues should be positive."""
        N = 20
        H = construct_H_epsilon_theory(N, eps=0.001, primes_count=5)
        eigenvalues = compute_eigenvalues(H)
        assert np.all(eigenvalues > 0), "Eigenvalues should be positive"


class TestComparison:
    """Test comparison with true zeros."""
    
    def test_comparison_shape(self):
        """Comparison should return correct shapes."""
        eigenvalues = np.array([14.1, 21.0, 25.0])
        true_zeros = np.array([14.13, 21.02, 25.01])
        mean_error, errors = compare_with_zeros(eigenvalues, true_zeros)
        
        assert isinstance(mean_error, (float, np.floating))
        assert len(errors) == 3
        
    def test_comparison_error_positive(self):
        """Errors should be positive."""
        eigenvalues = np.array([14.1, 21.0])
        true_zeros = np.array([14.13, 21.02])
        mean_error, errors = compare_with_zeros(eigenvalues, true_zeros)
        
        assert mean_error >= 0
        assert np.all(errors >= 0)


class TestIntegration:
    """Integration tests for full workflow."""
    
    @pytest.mark.slow
    def test_small_validation(self):
        """Run a small validation (N=20)."""
        N = 20
        n_zeros = 20
        
        # Load zeros
        true_zeros = load_riemann_zeros_lmfdb(n_zeros)
        assert len(true_zeros) == n_zeros
        
        # Construct operator
        H = construct_H_epsilon_theory(N, eps=0.001, primes_count=10)
        assert H.shape == (N, N)
        
        # Compute eigenvalues
        eigenvalues = compute_eigenvalues(H)
        assert len(eigenvalues) == N
        
        # Compare
        mean_error, errors = compare_with_zeros(eigenvalues, true_zeros)
        
        # First eigenvalue should be reasonably close
        assert errors[0] < 5.0, "First eigenvalue should be within 5 of first zero"
        
        # Mean error should be finite
        assert np.isfinite(mean_error)
        assert mean_error > 0


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
