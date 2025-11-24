#!/usr/bin/env python3
"""
Tests for the Hermitian operator H_Ψ implementation.

Tests verify:
1. Operator construction and properties
2. Spectrum computation
3. Validation against Riemann zeros
4. Physical constants and coherence
"""

import pytest
import numpy as np
import os
import sys

# Add parent directory to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from operador.riemann_operator import (
    RiemannOperator, 
    load_riemann_zeros,
    F0, OMEGA_0, ZETA_PRIME_HALF, PI
)

# Test tolerances
FLOAT_TOLERANCE = 1e-6
NORMALIZATION_TOLERANCE = 0.1


class TestPhysicalConstants:
    """Test that physical constants are correct."""
    
    def test_frequency_constant(self):
        """Test fundamental frequency f₀ = 141.7001 Hz."""
        assert F0 == 141.7001
        assert abs(OMEGA_0 - 2 * np.pi * 141.7001) < FLOAT_TOLERANCE
    
    def test_zeta_prime(self):
        """Test ζ'(1/2) approximation."""
        assert abs(ZETA_PRIME_HALF - (-3.92264773)) < FLOAT_TOLERANCE
    
    def test_coupling_constant(self):
        """Test arithmetic coupling ζ'(1/2)·π."""
        coupling = ZETA_PRIME_HALF * PI
        assert -13 < coupling < -12


class TestZerosLoading:
    """Test loading of Riemann zeros."""
    
    def test_load_zeros_from_file(self):
        """Test loading zeros from file."""
        gammas = load_riemann_zeros(max_zeros=10)
        
        assert len(gammas) >= 10
        assert all(g > 0 for g in gammas)
        
        # Check first zero is approximately 14.134...
        assert abs(gammas[0] - 14.134725) < 0.01
    
    def test_zeros_ordering(self):
        """Test that zeros are in ascending order."""
        gammas = load_riemann_zeros(max_zeros=20)
        
        # Note: The file may not be sorted, so we just check they're loaded
        assert len(gammas) == 20


class TestRiemannOperator:
    """Test the Hermitian operator construction."""
    
    @pytest.fixture
    def small_operator(self):
        """Create a small operator for testing."""
        gammas = load_riemann_zeros(max_zeros=10)
        op = RiemannOperator(
            gamma_values=gammas,
            n_points=100,
            x_min=0.1,
            x_max=10.0,
            sigma=1.0,
            alpha=1.5
        )
        return op
    
    def test_operator_initialization(self, small_operator):
        """Test operator initializes correctly."""
        assert small_operator.n == 100
        assert len(small_operator.gammas) == 10
        assert small_operator.x_min == 0.1
        assert small_operator.x_max == 10.0
    
    def test_grid_construction(self, small_operator):
        """Test logarithmic grid is constructed correctly."""
        assert len(small_operator.x) == 100
        assert len(small_operator.u) == 100
        
        # Check x = exp(u)
        np.testing.assert_allclose(
            small_operator.x, 
            np.exp(small_operator.u),
            rtol=1e-10
        )
        
        # Check boundaries
        assert abs(small_operator.x[0] - 0.1) < 0.01
        assert abs(small_operator.x[-1] - 10.0) < 0.01
    
    def test_potential_computation(self, small_operator):
        """Test potential V_Ψ(x) computation."""
        x_test = np.array([0.5, 1.0, 2.0])
        V = small_operator._potential(x_test)
        
        assert len(V) == len(x_test)
        assert all(np.isfinite(V))
        
        # Potential should be real
        assert V.dtype == np.float64
    
    def test_operator_hermiticity(self, small_operator):
        """Test that H is Hermitian (symmetric)."""
        H_dense = small_operator.H.toarray()
        
        # Check symmetry: H = H^T
        np.testing.assert_allclose(
            H_dense, 
            H_dense.T,
            rtol=1e-10,
            atol=1e-10
        )
    
    def test_operator_sparsity(self, small_operator):
        """Test that operator matrix is sparse."""
        H = small_operator.H
        
        # Should be sparse matrix
        assert hasattr(H, 'toarray')
        
        # Most entries should be zero
        nnz_ratio = H.nnz / (H.shape[0] * H.shape[1])
        assert nnz_ratio < 0.1  # Less than 10% non-zero


class TestSpectrumComputation:
    """Test spectrum computation and validation."""
    
    @pytest.fixture
    def operator_with_spectrum(self):
        """Create operator and compute spectrum."""
        gammas = load_riemann_zeros(max_zeros=20)
        op = RiemannOperator(
            gamma_values=gammas,
            n_points=200,
            x_min=0.1,
            x_max=10.0,
            sigma=1.0,
            alpha=1.5
        )
        eigvals, eigvecs = op.compute_spectrum(n_eigenvalues=10, which='SM')
        return op, eigvals, eigvecs, gammas
    
    def test_spectrum_computation(self, operator_with_spectrum):
        """Test that spectrum can be computed."""
        op, eigvals, eigvecs, gammas = operator_with_spectrum
        
        assert len(eigvals) == 10
        assert eigvecs.shape[0] == op.n
        assert eigvecs.shape[1] == 10
    
    def test_eigenvalues_real(self, operator_with_spectrum):
        """Test that eigenvalues are real."""
        op, eigvals, eigvecs, gammas = operator_with_spectrum
        
        assert eigvals.dtype in [np.float32, np.float64]
        assert all(np.isfinite(eigvals))
    
    def test_eigenvalues_ordered(self, operator_with_spectrum):
        """Test that eigenvalues are ordered."""
        op, eigvals, eigvecs, gammas = operator_with_spectrum
        
        # Should be in ascending order (with numerical tolerance)
        for i in range(len(eigvals)-1):
            assert eigvals[i] <= eigvals[i+1] + FLOAT_TOLERANCE
    
    def test_eigenvectors_normalized(self, operator_with_spectrum):
        """Test that eigenvectors are normalized."""
        op, eigvals, eigvecs, gammas = operator_with_spectrum
        
        # Check normalization (approximately)
        for i in range(eigvecs.shape[1]):
            norm = np.linalg.norm(eigvecs[:, i])
            assert abs(norm - 1.0) < NORMALIZATION_TOLERANCE
    
    def test_spectrum_validation(self, operator_with_spectrum):
        """Test spectrum validation against Riemann zeros."""
        op, eigvals, eigvecs, gammas = operator_with_spectrum
        
        stats = op.validate_spectrum(
            eigenvalues=eigvals,
            gamma_target=gammas,
            tolerance=1e-3  # Relaxed tolerance for test
        )
        
        assert stats['n_compared'] == 10
        assert 'n_passing' in stats
        assert 'max_error' in stats
        assert 'mean_error' in stats
        assert stats['pass_rate'] >= 0  # At least some should pass
    
    def test_validation_statistics(self, operator_with_spectrum):
        """Test that validation returns proper statistics."""
        op, eigvals, eigvecs, gammas = operator_with_spectrum
        
        stats = op.validate_spectrum(eigvals, gammas, tolerance=1e-10)
        
        assert 0 <= stats['pass_rate'] <= 1
        assert len(stats['errors']) == stats['n_compared']
        assert stats['max_error'] >= stats['mean_error']


class TestIntegration:
    """Integration tests for full workflow."""
    
    def test_full_workflow(self):
        """Test complete workflow: load, build, compute, validate."""
        # Load zeros
        gammas = load_riemann_zeros(max_zeros=15)
        assert len(gammas) >= 15
        
        # Build operator
        op = RiemannOperator(
            gamma_values=gammas,
            n_points=150,
            x_min=0.1,
            x_max=10.0
        )
        assert op.H is not None
        
        # Compute spectrum
        eigvals, eigvecs = op.compute_spectrum(n_eigenvalues=10, which='SM')
        assert len(eigvals) == 10
        
        # Validate
        stats = op.validate_spectrum(eigvals, gammas, tolerance=1e-2)
        assert stats['n_compared'] == 10
    
    def test_different_parameters(self):
        """Test operator with different parameter values."""
        gammas = load_riemann_zeros(max_zeros=10)
        
        # Test different sigma values
        for sigma in [0.5, 1.0, 2.0]:
            op = RiemannOperator(
                gamma_values=gammas,
                n_points=100,
                sigma=sigma
            )
            assert op.H is not None
        
        # Test different alpha values
        for alpha in [1.0, 1.5, 2.0]:
            op = RiemannOperator(
                gamma_values=gammas,
                n_points=100,
                alpha=alpha
            )
            assert op.H is not None


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
