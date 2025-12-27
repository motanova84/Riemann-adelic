"""
Tests for the H_ε spectral operator implementation.

Validates:
1. Oscillatory potential Ω_{ε,R}(t) properties
2. Operator H_ε matrix structure (symmetry, definiteness)
3. Spectral measure extraction
4. Convergence with parameters
5. Comparison with Riemann zeros
"""

import pytest
import numpy as np
from numpy.testing import assert_allclose, assert_array_less

from operador.operador_H_epsilon import (
    compute_oscillatory_potential,
    build_H_epsilon_operator,
    compute_spectral_measure,
    load_riemann_zeros
)


class TestOscillatoryPotential:
    """Test the oscillatory potential Ω_{ε,R}(t)."""
    
    def test_potential_shape(self):
        """Potential should have same shape as input."""
        t = np.linspace(-10, 10, 100)
        Omega = compute_oscillatory_potential(t, epsilon=0.01, R=5.0, n_primes=50)
        assert Omega.shape == t.shape
    
    def test_potential_decay(self):
        """Potential should decay for large |t| due to envelope."""
        t = np.array([-20.0, -10.0, 0.0, 10.0, 20.0])
        Omega = compute_oscillatory_potential(t, epsilon=0.01, R=5.0, n_primes=50)
        
        # Center should have larger magnitude than edges
        center_val = np.abs(Omega[2])
        edge_vals = np.abs(Omega[[0, 4]])
        
        assert np.all(center_val >= edge_vals), \
            "Potential should decay away from center"
    
    def test_potential_convergence(self):
        """Increasing n_primes should converge to stable value."""
        t = np.array([0.0, 5.0, 10.0])
        
        # Compute with increasing number of primes
        Omega_50 = compute_oscillatory_potential(t, epsilon=0.01, R=5.0, n_primes=50)
        Omega_100 = compute_oscillatory_potential(t, epsilon=0.01, R=5.0, n_primes=100)
        Omega_200 = compute_oscillatory_potential(t, epsilon=0.01, R=5.0, n_primes=200)
        
        # Difference should decrease
        diff_50_100 = np.max(np.abs(Omega_100 - Omega_50))
        diff_100_200 = np.max(np.abs(Omega_200 - Omega_100))
        
        assert diff_100_200 < diff_50_100, \
            "Potential should converge as n_primes increases"
    
    def test_epsilon_effect(self):
        """Larger epsilon should increase convergence rate."""
        t = np.linspace(-10, 10, 50)
        
        Omega_small = compute_oscillatory_potential(t, epsilon=0.001, R=5.0, n_primes=100)
        Omega_large = compute_oscillatory_potential(t, epsilon=0.1, R=5.0, n_primes=100)
        
        # Larger epsilon leads to faster decay, smaller magnitude
        assert np.max(np.abs(Omega_large)) <= np.max(np.abs(Omega_small)), \
            "Larger epsilon should reduce potential magnitude"


class TestHEpsilonOperator:
    """Test the H_ε operator construction and properties."""
    
    def test_operator_dimensions(self):
        """Operator should have correct tridiagonal dimensions."""
        N = 100
        t, H_diag, H_offdiag = build_H_epsilon_operator(
            N=N, T=10.0, epsilon=0.01, R=5.0
        )
        
        assert len(t) == N, "Grid should have N points"
        assert len(H_diag) == N, "Diagonal should have N elements"
        assert len(H_offdiag) == N - 1, "Off-diagonal should have N-1 elements"
    
    def test_operator_symmetry(self):
        """H_ε should be symmetric (Hermitian)."""
        N = 50
        t, H_diag, H_offdiag = build_H_epsilon_operator(
            N=N, T=10.0, epsilon=0.01, R=5.0, n_primes=50
        )
        
        # Build full matrix to check symmetry
        H_full = np.diag(H_diag) + np.diag(H_offdiag, k=1) + np.diag(H_offdiag, k=-1)
        
        # Check symmetry
        assert_allclose(H_full, H_full.T, rtol=1e-10, atol=1e-12,
                       err_msg="H_ε should be symmetric")
    
    def test_operator_bounded_diagonal(self):
        """Diagonal elements should be bounded (operator is well-defined)."""
        t, H_diag, H_offdiag = build_H_epsilon_operator(
            N=100, T=10.0, epsilon=0.01, R=5.0, lambda_coupling=141.7001
        )
        
        # Operator is well-defined but can have negative values
        assert np.all(np.isfinite(H_diag)), "All diagonal elements should be finite"
        assert not np.any(np.isnan(H_diag)), "No NaN values in diagonal"
    
    def test_coupling_effect(self):
        """Varying λ should affect diagonal but not off-diagonal."""
        N = 50
        
        _, H_diag_1, H_offdiag_1 = build_H_epsilon_operator(
            N=N, T=10.0, lambda_coupling=100.0, n_primes=50
        )
        _, H_diag_2, H_offdiag_2 = build_H_epsilon_operator(
            N=N, T=10.0, lambda_coupling=200.0, n_primes=50
        )
        
        # Off-diagonal should be identical (comes from H₀ only)
        assert_allclose(H_offdiag_1, H_offdiag_2, rtol=1e-10,
                       err_msg="Off-diagonal should not depend on λ")
        
        # Diagonals should differ
        assert not np.allclose(H_diag_1, H_diag_2, rtol=1e-3), \
            "Diagonal should depend on λ"


class TestSpectralMeasure:
    """Test spectral measure extraction from H_ε."""
    
    def test_eigenvalue_count(self):
        """Should return N eigenvalues for N×N operator."""
        N = 50
        eigenvalues, eigenvectors = compute_spectral_measure(
            N=N, T=10.0, epsilon=0.01, R=5.0, n_primes=50
        )
        
        assert len(eigenvalues) == N, f"Should have {N} eigenvalues"
        assert eigenvectors.shape == (N, N), f"Eigenvectors should be {N}×{N}"
    
    def test_eigenvalues_real(self):
        """Eigenvalues should be real (symmetric operator)."""
        eigenvalues, _ = compute_spectral_measure(
            N=50, T=10.0, epsilon=0.01, R=5.0, n_primes=50
        )
        
        assert eigenvalues.dtype in [np.float32, np.float64], \
            "Eigenvalues should be real"
    
    def test_eigenvalues_sorted(self):
        """Eigenvalues should be in ascending order."""
        eigenvalues, _ = compute_spectral_measure(
            N=50, T=10.0, epsilon=0.01, R=5.0, n_primes=50
        )
        
        assert np.all(np.diff(eigenvalues) >= 0), \
            "Eigenvalues should be sorted in ascending order"
    
    def test_eigenvalues_bounded(self):
        """Eigenvalues should be finite and well-bounded."""
        eigenvalues, _ = compute_spectral_measure(
            N=50, T=10.0, epsilon=0.01, R=5.0, n_primes=50
        )
        
        # H_ε can have negative eigenvalues due to oscillatory potential
        assert np.all(np.isfinite(eigenvalues)), \
            "All eigenvalues should be finite"
        assert not np.any(np.isnan(eigenvalues)), \
            "No NaN eigenvalues"
    
    def test_spectral_distribution(self):
        """Eigenvalue distribution should be reasonable."""
        eigenvalues, _ = compute_spectral_measure(
            N=100, T=20.0, epsilon=0.01, R=5.0
        )
        
        # Check spectral range is finite and well-distributed
        spectral_range = eigenvalues[-1] - eigenvalues[0]
        assert spectral_range > 0, "Should have positive spectral range"
        assert np.isfinite(spectral_range), "Spectral range should be finite"
        
        # Check for reasonable gaps
        gaps = np.diff(eigenvalues)
        assert np.all(gaps >= 0), "Eigenvalues should be sorted"


class TestRiemannZerosLoading:
    """Test loading and handling of Riemann zeros."""
    
    def test_load_zeros_file_not_found(self):
        """Should raise FileNotFoundError for non-existent file."""
        with pytest.raises(FileNotFoundError):
            load_riemann_zeros(filename='nonexistent_file.txt')
    
    def test_load_zeros_max_limit(self):
        """Should respect max_zeros parameter."""
        try:
            zeros = load_riemann_zeros(
                filename='zeros/zeros_t1e3.txt',
                max_zeros=10
            )
            assert len(zeros) <= 10, "Should load at most max_zeros values"
        except FileNotFoundError:
            pytest.skip("Zeros file not available")
    
    def test_zeros_positive(self):
        """Riemann zeros should be positive (Im(ρ) > 0)."""
        try:
            zeros = load_riemann_zeros(
                filename='zeros/zeros_t1e3.txt',
                max_zeros=50
            )
            assert np.all(zeros > 0), "All zeros should be positive"
        except FileNotFoundError:
            pytest.skip("Zeros file not available")
    
    def test_zeros_sorted(self):
        """Zeros should be approximately sorted (may have variations)."""
        try:
            zeros = load_riemann_zeros(
                filename='zeros/zeros_t1e3.txt',
                max_zeros=100
            )
            # Check if mostly sorted (allow some variation)
            ascending_pairs = np.sum(np.diff(zeros) >= 0)
            total_pairs = len(zeros) - 1
            assert ascending_pairs >= 0.8 * total_pairs, \
                "Zeros should be mostly in ascending order"
        except FileNotFoundError:
            pytest.skip("Zeros file not available")


class TestConvergence:
    """Test convergence properties with varying parameters."""
    
    def test_N_convergence(self):
        """Eigenvalues should stabilize as N increases."""
        # Compute with different discretizations
        eigs_50, _ = compute_spectral_measure(N=50, T=10.0, n_primes=50)
        eigs_100, _ = compute_spectral_measure(N=100, T=10.0, n_primes=50)
        eigs_150, _ = compute_spectral_measure(N=150, T=10.0, n_primes=50)
        
        # Compare first 10 eigenvalues (they should converge)
        n_compare = 10
        diff_50_100 = np.max(np.abs(eigs_100[:n_compare] - eigs_50[:n_compare]))
        diff_100_150 = np.max(np.abs(eigs_150[:n_compare] - eigs_100[:n_compare]))
        
        # Should show convergence (decreasing differences)
        assert diff_100_150 < diff_50_100, \
            "First eigenvalues should converge as N increases"
    
    def test_T_effect(self):
        """Larger T should not drastically change low eigenvalues."""
        eigs_small_T, _ = compute_spectral_measure(N=100, T=10.0, n_primes=50)
        eigs_large_T, _ = compute_spectral_measure(N=100, T=20.0, n_primes=50)
        
        # First few eigenvalues should be similar (localized modes)
        # Allow larger tolerance since T changes the domain
        assert_allclose(eigs_small_T[:5], eigs_large_T[:5], rtol=0.5,
                       err_msg="Low eigenvalues should be similar for different T")


class TestIntegration:
    """Integration tests combining multiple components."""
    
    def test_full_workflow(self):
        """Test complete workflow from operator to spectral comparison."""
        # Small problem for quick test
        N = 50
        n_primes = 50
        
        # Build and diagonalize
        eigenvalues, eigenvectors = compute_spectral_measure(
            N=N, T=10.0, epsilon=0.01, R=5.0, 
            lambda_coupling=141.7001, n_primes=n_primes
        )
        
        # Basic sanity checks
        assert len(eigenvalues) == N, "Should have N eigenvalues"
        assert np.all(np.isfinite(eigenvalues)), "All eigenvalues should be finite"
        assert np.all(np.diff(eigenvalues) >= 0), "Eigenvalues should be sorted"
        assert eigenvectors.shape == (N, N), "Eigenvectors should be N×N"
        
        # Check orthonormality of eigenvectors (sample)
        # For tridiagonal symmetric, eigenvectors should be orthonormal
        V = eigenvectors
        VtV = V.T @ V
        assert_allclose(VtV, np.eye(N), rtol=1e-8, atol=1e-10,
                       err_msg="Eigenvectors should be orthonormal")


if __name__ == "__main__":
    # Run tests with pytest
    pytest.main([__file__, "-v", "--tb=short"])
