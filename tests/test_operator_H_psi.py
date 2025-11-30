#!/usr/bin/env python3
"""
Test suite for operator_H_psi.py - H_Ψ operator construction for Riemann Hypothesis.

This module tests the spectral operator H_Ψ = -d²/dx² + V(x) construction,
validating self-adjointness, spectral properties, and numerical accuracy.

Author: José Manuel Mota Burruezo Ψ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: November 2025
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773
"""

import sys
from pathlib import Path

# Add repository root to path for imports
REPO_ROOT = Path(__file__).parent.parent
sys.path.insert(0, str(REPO_ROOT))

import pytest
import numpy as np


class TestQCALConstants:
    """Tests for QCAL integration constants."""

    def test_import_module(self):
        """Test that the module can be imported."""
        from spectral_RH.operator_H_psi import (
            QCAL_BASE_FREQUENCY,
            QCAL_COHERENCE,
            LAMBDA_PARAM,
            EPSILON_PARAM
        )
        assert QCAL_BASE_FREQUENCY is not None
        assert QCAL_COHERENCE is not None

    def test_qcal_base_frequency(self):
        """Verify QCAL base frequency is 141.7001 Hz."""
        from spectral_RH.operator_H_psi import QCAL_BASE_FREQUENCY
        assert QCAL_BASE_FREQUENCY == 141.7001

    def test_qcal_coherence(self):
        """Verify QCAL coherence constant is 244.36."""
        from spectral_RH.operator_H_psi import QCAL_COHERENCE
        assert QCAL_COHERENCE == 244.36

    def test_lambda_param(self):
        """Verify λ = (141.7001)²."""
        from spectral_RH.operator_H_psi import LAMBDA_PARAM, QCAL_BASE_FREQUENCY
        expected = QCAL_BASE_FREQUENCY ** 2
        assert abs(LAMBDA_PARAM - expected) < 1e-10

    def test_epsilon_param(self):
        """Verify ε = 1/e."""
        import math
        from spectral_RH.operator_H_psi import EPSILON_PARAM
        expected = 1 / math.e
        assert abs(EPSILON_PARAM - expected) < 1e-15


class TestPotentialFunctions:
    """Tests for potential functions V(x)."""

    def test_potential_v_returns_array(self):
        """Test that potential_V returns numpy array."""
        from spectral_RH.operator_H_psi import potential_V
        x = np.linspace(-10, 10, 100)
        V = potential_V(x)
        assert isinstance(V, np.ndarray)
        assert V.shape == x.shape

    def test_potential_v_symmetric(self):
        """Test that V(-x) = V(x) (symmetry)."""
        from spectral_RH.operator_H_psi import potential_V
        x = np.linspace(0.1, 10, 50)
        V_positive = potential_V(x)
        V_negative = potential_V(-x)
        np.testing.assert_allclose(V_positive, V_negative, rtol=1e-14)

    def test_potential_v_positive_large_x(self):
        """Test that V(x) > 0 for large |x| (confining)."""
        from spectral_RH.operator_H_psi import potential_V
        x = np.array([100, 1000, 10000])
        V = potential_V(x)
        assert np.all(V > 0)

    def test_potential_v_smooth_at_zero(self):
        """Test that V(x) is finite at x=0 (smooth, no singularity)."""
        from spectral_RH.operator_H_psi import potential_V
        x = np.array([0.0])
        V = potential_V(x)
        assert np.isfinite(V[0])

    def test_potential_v_resonant_returns_array(self):
        """Test that potential_V_resonant returns numpy array."""
        from spectral_RH.operator_H_psi import potential_V_resonant
        x = np.linspace(-10, 10, 100)
        V = potential_V_resonant(x)
        assert isinstance(V, np.ndarray)
        assert V.shape == x.shape

    def test_potential_v_resonant_symmetric(self):
        """Test that resonant potential is symmetric V(-x) = V(x)."""
        from spectral_RH.operator_H_psi import potential_V_resonant
        x = np.linspace(0.1, 10, 50)
        V_positive = potential_V_resonant(x)
        V_negative = potential_V_resonant(-x)
        np.testing.assert_allclose(V_positive, V_negative, rtol=1e-14)


class TestMatrixConstruction:
    """Tests for H_Ψ matrix construction."""

    def test_build_dense_matrix_shape(self):
        """Test that dense matrix has correct shape."""
        from spectral_RH.operator_H_psi import build_H_psi_matrix_dense
        H, x = build_H_psi_matrix_dense(N=100, R=10.0)
        assert H.shape == (100, 100)
        assert x.shape == (100,)

    def test_build_sparse_matrix_shape(self):
        """Test that sparse matrix has correct shape."""
        from spectral_RH.operator_H_psi import build_H_psi_matrix_sparse
        H, x = build_H_psi_matrix_sparse(N=200, R=10.0)
        assert H.shape == (200, 200)
        assert x.shape == (200,)

    def test_build_resonant_matrix_shape(self):
        """Test that resonant matrix has correct shape."""
        from spectral_RH.operator_H_psi import build_H_psi_resonant
        H, x = build_H_psi_resonant(N=100, L=10.0)
        assert H.shape == (100, 100)
        assert x.shape == (100,)

    def test_matrix_is_symmetric(self):
        """Test that H matrix is symmetric (H = H^T)."""
        from spectral_RH.operator_H_psi import build_H_psi_matrix_dense
        H, _ = build_H_psi_matrix_dense(N=50, R=10.0)
        np.testing.assert_allclose(H, H.T, atol=1e-14)

    def test_matrix_is_real(self):
        """Test that H matrix is real (no imaginary parts)."""
        from spectral_RH.operator_H_psi import build_H_psi_matrix_dense
        H, _ = build_H_psi_matrix_dense(N=50, R=10.0)
        assert np.isrealobj(H)

    def test_matrix_no_nan_or_inf(self):
        """Test that matrix has no NaN or infinite values."""
        from spectral_RH.operator_H_psi import build_H_psi_matrix_dense
        H, _ = build_H_psi_matrix_dense(N=100, R=10.0)
        assert not np.any(np.isnan(H))
        assert not np.any(np.isinf(H))


class TestSelfAdjointness:
    """Tests for self-adjointness of H_Ψ."""

    def test_self_adjoint_validation(self):
        """Test self-adjointness validation function."""
        from spectral_RH.operator_H_psi import build_H_psi_matrix_dense, validate_self_adjointness
        H, _ = build_H_psi_matrix_dense(N=100, R=10.0)
        result = validate_self_adjointness(H, n_tests=50)
        assert result['is_self_adjoint']
        assert result['is_symmetric']

    def test_inner_product_equality(self):
        """Test that ⟨Hf, g⟩ = ⟨f, Hg⟩ for random vectors."""
        from spectral_RH.operator_H_psi import build_H_psi_matrix_dense
        H, _ = build_H_psi_matrix_dense(N=100, R=10.0)

        np.random.seed(42)
        for _ in range(20):
            f = np.random.randn(100)
            g = np.random.randn(100)

            Hf_g = np.dot(H @ f, g)
            f_Hg = np.dot(f, H @ g)

            np.testing.assert_allclose(Hf_g, f_Hg, rtol=1e-10)


class TestEigenvalues:
    """Tests for eigenvalue computation."""

    def test_eigenvalues_are_real(self):
        """Test that all eigenvalues are real (for symmetric matrix)."""
        from spectral_RH.operator_H_psi import (
            build_H_psi_matrix_dense,
            compute_eigenvalues_eigenvectors
        )
        H, _ = build_H_psi_matrix_dense(N=100, R=10.0)
        eigenvalues, _ = compute_eigenvalues_eigenvectors(H, k=10)
        assert np.all(np.imag(eigenvalues) == 0)

    def test_eigenvalues_count(self):
        """Test correct number of eigenvalues returned."""
        from spectral_RH.operator_H_psi import (
            build_H_psi_matrix_dense,
            compute_eigenvalues_eigenvectors
        )
        H, _ = build_H_psi_matrix_dense(N=100, R=10.0)
        eigenvalues, _ = compute_eigenvalues_eigenvectors(H, k=5)
        assert len(eigenvalues) == 5

    def test_eigenvalues_sorted(self):
        """Test that eigenvalues are sorted in ascending order."""
        from spectral_RH.operator_H_psi import (
            build_H_psi_matrix_dense,
            compute_eigenvalues_eigenvectors
        )
        H, _ = build_H_psi_matrix_dense(N=100, R=10.0)
        eigenvalues, _ = compute_eigenvalues_eigenvectors(H, k=10)
        assert np.all(np.diff(eigenvalues) >= -1e-10)

    def test_eigenvectors_orthonormal(self):
        """Test that eigenvectors are orthonormal."""
        from spectral_RH.operator_H_psi import (
            build_H_psi_matrix_dense,
            compute_eigenvalues_eigenvectors
        )
        H, _ = build_H_psi_matrix_dense(N=100, R=10.0)
        _, eigenvectors = compute_eigenvalues_eigenvectors(H, k=5)

        # Check orthonormality: V^T @ V ≈ I
        VtV = eigenvectors.T @ eigenvectors
        np.testing.assert_allclose(VtV, np.eye(5), atol=1e-10)


class TestRiemannZeros:
    """Tests for Riemann zeros comparison."""

    def test_get_known_zeros_count(self):
        """Test that we get the requested number of zeros."""
        from spectral_RH.operator_H_psi import get_known_riemann_zeros
        zeros = get_known_riemann_zeros(10)
        assert len(zeros) == 10

    def test_known_zeros_values(self):
        """Test first few known zeros are correct (Odlyzko values)."""
        from spectral_RH.operator_H_psi import get_known_riemann_zeros
        zeros = get_known_riemann_zeros(5)

        # First few Riemann zeta zeros (imaginary parts)
        expected = [14.1347, 21.0220, 25.0109, 30.4249, 32.9351]
        np.testing.assert_allclose(zeros, expected, rtol=1e-3)

    def test_comparison_returns_dict(self):
        """Test that comparison function returns expected dictionary."""
        from spectral_RH.operator_H_psi import (
            build_H_psi_matrix_dense,
            compute_eigenvalues_eigenvectors,
            compare_spectrum_with_zeros
        )
        H, _ = build_H_psi_matrix_dense(N=100, R=10.0)
        eigenvalues, _ = compute_eigenvalues_eigenvectors(H, k=10)
        result = compare_spectrum_with_zeros(eigenvalues, n_zeros=5)

        assert 'eigenvalues' in result
        assert 'zeros' in result
        assert 'l2_deviation' in result
        assert 'max_deviation' in result


class TestValidation:
    """Tests for complete validation routines."""

    def test_run_spectral_validation(self):
        """Test that spectral validation runs without error."""
        from spectral_RH.operator_H_psi import run_spectral_validation
        results = run_spectral_validation(N=100, R=10.0, k=5, verbose=False)

        assert 'N' in results
        assert 'eigenvalues' in results
        assert 'self_adjoint' in results

    def test_run_resonant_validation(self):
        """Test that resonant validation runs without error."""
        from spectral_RH.operator_H_psi import run_resonant_validation
        results = run_resonant_validation(N=100, L=5.0, k=5, verbose=False)

        assert 'eigenvalues' in results
        assert results['success']  # Should be self-adjoint


class TestResonantOperator:
    """Tests specific to the resonant operator from problem statement."""

    def test_resonant_eigenvalues_pattern(self):
        """Test that resonant operator produces eigenvalue pattern as in problem statement."""
        from spectral_RH.operator_H_psi import (
            build_H_psi_resonant,
            compute_eigenvalues_eigenvectors
        )
        H, _ = build_H_psi_resonant(N=500, L=10.0)
        eigenvalues, _ = compute_eigenvalues_eigenvectors(H, k=10)

        # Eigenvalues should be increasing (from problem statement pattern)
        assert np.all(np.diff(eigenvalues) > 0)

    def test_resonant_operator_self_adjoint(self):
        """Test that resonant operator is self-adjoint."""
        from spectral_RH.operator_H_psi import (
            build_H_psi_resonant,
            validate_self_adjointness
        )
        H, _ = build_H_psi_resonant(N=200, L=10.0)
        result = validate_self_adjointness(H)
        assert result['is_self_adjoint']


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
