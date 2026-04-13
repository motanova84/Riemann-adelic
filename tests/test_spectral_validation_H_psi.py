#!/usr/bin/env python3
"""
Test suite for spectral validation of operator H_Ψ.

This module tests the spectral_validation_H_psi.py module which implements
the numerical validation of the Hilbert-Pólya conjecture realization.

Author: José Manuel Mota Burruezo
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: November 2025
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773
"""

import sys
from pathlib import Path

# Add repository root to path for imports (before other imports)
REPO_ROOT = Path(__file__).parent.parent
sys.path.insert(0, str(REPO_ROOT))

import pytest  # noqa: E402
import numpy as np  # noqa: E402

from spectral_validation_H_psi import (  # noqa: E402
    construct_H_psi_matrix,
    compute_eigenvalues,
    validate_spectral_reality,
    validate_self_adjointness,
    validate_matrix_symmetry,
    run_spectral_validation,
    QCAL_BASE_FREQUENCY,
    QCAL_COHERENCE,
)


class TestQCALConstants:
    """Tests for QCAL integration constants."""

    def test_qcal_base_frequency(self):
        """Verify QCAL base frequency is correct."""
        assert QCAL_BASE_FREQUENCY == 141.7001

    def test_qcal_coherence(self):
        """Verify QCAL coherence constant is correct."""
        assert QCAL_COHERENCE == 244.36


class TestMatrixConstruction:
    """Tests for H_Ψ matrix construction."""

    def test_matrix_shape_default(self):
        """Test matrix has correct shape with default N."""
        H = construct_H_psi_matrix(N=100)
        assert H.shape == (98, 98)  # N-2 interior points

    def test_matrix_shape_custom(self):
        """Test matrix has correct shape with custom N."""
        H = construct_H_psi_matrix(N=500)
        assert H.shape == (498, 498)

    def test_matrix_is_2d(self):
        """Test matrix is 2D numpy array."""
        H = construct_H_psi_matrix(N=100)
        assert H.ndim == 2

    def test_matrix_is_real(self):
        """Test matrix contains only real values."""
        H = construct_H_psi_matrix(N=100)
        assert np.isrealobj(H)

    def test_matrix_no_nan(self):
        """Test matrix contains no NaN values."""
        H = construct_H_psi_matrix(N=100)
        assert not np.any(np.isnan(H))

    def test_matrix_no_inf(self):
        """Test matrix contains no infinite values."""
        H = construct_H_psi_matrix(N=100)
        assert not np.any(np.isinf(H))


class TestMatrixSymmetry:
    """Tests for matrix symmetry (self-adjointness)."""

    def test_matrix_is_symmetric(self):
        """Test matrix is exactly symmetric (H = H^T)."""
        H = construct_H_psi_matrix(N=100)
        assert np.allclose(H, H.T)

    def test_symmetry_validation(self):
        """Test symmetry validation function."""
        H = construct_H_psi_matrix(N=100)
        result = validate_matrix_symmetry(H)
        assert result["is_symmetric"]
        assert result["max_asymmetry"] < 1e-14

    def test_non_symmetric_matrix_detected(self):
        """Test that non-symmetric matrices are detected."""
        H = np.array([[1, 2], [3, 4]])  # Not symmetric
        result = validate_matrix_symmetry(H)
        assert not result["is_symmetric"]


class TestSelfAdjointness:
    """Tests for self-adjointness validation via inner products."""

    def test_self_adjoint_validation_passes(self):
        """Test that self-adjoint matrix passes validation."""
        H = construct_H_psi_matrix(N=100)
        result = validate_self_adjointness(H, n_test_functions=100)
        assert result["is_self_adjoint"]

    def test_self_adjoint_returns_dict(self):
        """Test that validation returns a dictionary with expected keys."""
        H = construct_H_psi_matrix(N=100)
        result = validate_self_adjointness(H, n_test_functions=10)
        assert "is_self_adjoint" in result
        assert "max_error" in result
        assert "mean_error" in result
        assert "n_tests" in result

    def test_n_tests_matches(self):
        """Test that number of tests matches requested."""
        H = construct_H_psi_matrix(N=100)
        result = validate_self_adjointness(H, n_test_functions=50)
        assert result["n_tests"] == 50


class TestEigenvalueComputation:
    """Tests for eigenvalue computation."""

    def test_eigenvalues_count(self):
        """Test correct number of eigenvalues returned."""
        H = construct_H_psi_matrix(N=100)
        eigenvalues = compute_eigenvalues(H, k=10)
        assert len(eigenvalues) == 10

    def test_eigenvalues_are_real(self):
        """Test that eigenvalues are real (imaginary part = 0)."""
        H = construct_H_psi_matrix(N=100)
        eigenvalues = compute_eigenvalues(H, k=10)
        assert np.all(np.imag(eigenvalues) == 0)

    def test_eigenvalues_finite(self):
        """Test that eigenvalues are finite."""
        H = construct_H_psi_matrix(N=100)
        eigenvalues = compute_eigenvalues(H, k=10)
        assert np.all(np.isfinite(eigenvalues))


class TestSpectralReality:
    """Tests for spectral reality validation."""

    def test_real_eigenvalues_pass(self):
        """Test that real eigenvalues pass validation."""
        eigenvalues = np.array([1.0, 2.0, 3.0, 4.0, 5.0])
        result = validate_spectral_reality(eigenvalues)
        assert result["all_real"]
        assert result["max_imag"] == 0.0

    def test_complex_eigenvalues_fail(self):
        """Test that complex eigenvalues fail validation."""
        eigenvalues = np.array([1.0 + 0.1j, 2.0, 3.0])
        result = validate_spectral_reality(eigenvalues)
        assert not result["all_real"]

    def test_spectral_reality_returns_dict(self):
        """Test that validation returns expected dictionary."""
        eigenvalues = np.array([1.0, 2.0, 3.0])
        result = validate_spectral_reality(eigenvalues)
        assert "all_real" in result
        assert "max_imag" in result
        assert "eigenvalues_imag" in result
        assert "eigenvalues_real" in result
        assert "count" in result

    def test_count_matches(self):
        """Test that count matches input."""
        eigenvalues = np.array([1.0, 2.0, 3.0, 4.0, 5.0])
        result = validate_spectral_reality(eigenvalues)
        assert result["count"] == 5


class TestFullValidation:
    """Tests for the complete validation pipeline."""

    def test_validation_runs_successfully(self):
        """Test that full validation runs without errors."""
        result = run_spectral_validation(N=100, k=10, verbose=False)
        assert "success" in result

    def test_validation_returns_expected_keys(self):
        """Test that validation returns all expected keys."""
        result = run_spectral_validation(N=100, k=10, verbose=False)
        expected_keys = [
            "N",
            "k",
            "success",
            "qcal_base_frequency",
            "qcal_coherence",
            "matrix_shape",
            "symmetry",
            "self_adjoint",
            "eigenvalues",
            "spectral_reality",
        ]
        for key in expected_keys:
            assert key in result, f"Missing key: {key}"

    def test_validation_small_n_passes(self):
        """Test that validation passes with small N."""
        result = run_spectral_validation(N=100, k=10, verbose=False)
        assert result["success"]

    def test_eigenvalues_imaginary_parts_zero(self):
        """Test that all eigenvalue imaginary parts are exactly zero."""
        result = run_spectral_validation(N=100, k=10, verbose=False)
        imag_parts = result["spectral_reality"]["eigenvalues_imag"]
        assert np.all(imag_parts == 0)

    def test_matrix_shape_correct(self):
        """Test that matrix shape is recorded correctly."""
        result = run_spectral_validation(N=200, k=10, verbose=False)
        assert result["matrix_shape"] == (198, 198)


class TestHilbertPolyaConjecture:
    """Tests specifically validating Hilbert-Pólya conjecture properties."""

    def test_spectrum_real_hilbert_polya(self):
        """
        Validate core Hilbert-Pólya property: spectrum is real.

        For a self-adjoint operator, all eigenvalues must be real.
        This is the key mathematical requirement for the Hilbert-Pólya
        realization.
        """
        H = construct_H_psi_matrix(N=500)
        eigenvalues = compute_eigenvalues(H, k=20)

        # All imaginary parts must be exactly zero
        assert np.all(np.imag(eigenvalues) == 0), "Hilbert-Pólya requires real spectrum"

    def test_self_adjoint_hilbert_polya(self):
        """
        Validate self-adjointness as required by Hilbert-Pólya.

        The operator must be self-adjoint (symmetric for real matrices)
        for the spectrum to be guaranteed real.
        """
        H = construct_H_psi_matrix(N=500)

        # Matrix must be symmetric
        sym_result = validate_matrix_symmetry(H)
        assert sym_result["is_symmetric"], "Hilbert-Pólya requires self-adjoint operator"

        # Inner product test must pass
        sa_result = validate_self_adjointness(H, n_test_functions=100)
        assert sa_result["is_self_adjoint"], "Hilbert-Pólya requires ⟨Hf,g⟩ = ⟨f,Hg⟩"


class TestDocumentation:
    """Tests for module documentation."""

    def test_module_has_docstring(self):
        """Test that module has a docstring."""
        import spectral_validation_H_psi as module

        assert module.__doc__ is not None

    def test_functions_have_docstrings(self):
        """Test that all public functions have docstrings."""
        functions = [
            construct_H_psi_matrix,
            compute_eigenvalues,
            validate_spectral_reality,
            validate_self_adjointness,
            validate_matrix_symmetry,
            run_spectral_validation,
        ]
        for func in functions:
            assert func.__doc__ is not None, f"{func.__name__} missing docstring"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
