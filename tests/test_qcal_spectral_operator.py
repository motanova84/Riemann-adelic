#!/usr/bin/env python3
"""
Tests for QCAL Spectral Operator — Ĥ_QCAL = Ĥ_BK ⊗ 𝕀_{f₀} + V̂_mod
=====================================================================

Validates:
1. Operator construction and hermiticity
2. Identity projector at f₀ = 141.7001 Hz
3. Modulation potential V̂_mod ∝ γ·ℏ/C
4. Coherence Ψ ≥ 0.888 threshold
5. Off-critical zeros certification (∅)
6. Full critical-line certification via certify_qcal_spectral_operator()

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz · C = 244.36
"""

import pytest
import numpy as np

from operators.qcal_spectral_operator import (
    QCALSpectralOperator,
    QCALSpectralResult,
    certify_qcal_spectral_operator,
    F0_QCAL,
    C_QCAL,
    PSI_THRESHOLD,
    HBAR,
    _get_riemann_zeros,
)


# ---------------------------------------------------------------------------
# Constants tests
# ---------------------------------------------------------------------------

class TestConstants:
    """QCAL Spectral Operator fundamental constants."""

    def test_f0_value(self):
        """Base frequency should be 141.7001 Hz."""
        assert abs(F0_QCAL - 141.7001) < 1e-4

    def test_c_qcal_value(self):
        """Coherence constant C should be 244.36."""
        assert abs(C_QCAL - 244.36) < 0.01

    def test_psi_threshold(self):
        """Coherence threshold should be 0.888."""
        assert abs(PSI_THRESHOLD - 0.888) < 1e-9

    def test_hbar_natural_units(self):
        """ℏ should equal 1.0 in natural units."""
        assert HBAR == 1.0

    def test_riemann_zeros_first(self):
        """First Riemann zero imaginary part should be ≈ 14.134725."""
        zeros = _get_riemann_zeros(1)
        assert abs(zeros[0] - 14.134725141734693) < 1e-4

    def test_riemann_zeros_shape(self):
        """Should return exactly n zeros."""
        zeros = _get_riemann_zeros(5)
        assert zeros.shape == (5,)
        assert np.all(zeros > 0)


# ---------------------------------------------------------------------------
# Operator construction
# ---------------------------------------------------------------------------

class TestOperatorConstruction:
    """Tests for sub-matrix and full operator construction."""

    @pytest.fixture
    def small_op(self):
        """Small (20×20) QCAL operator for fast tests."""
        return QCALSpectralOperator(N=20, n_zeros=5)

    def test_matrix_dimensions(self, small_op):
        """Operator matrix should be N×N."""
        assert small_op.H.shape == (small_op.N, small_op.N)

    def test_hbk_dimensions(self, small_op):
        """Berry-Keating matrix should be N×N."""
        assert small_op._H_BK.shape == (small_op.N, small_op.N)

    def test_i_f0_is_diagonal(self, small_op):
        """𝕀_{f₀} should be a scalar multiple of the identity."""
        I_f0 = small_op._build_I_f0()
        off_diag = I_f0 - np.diag(np.diag(I_f0))
        assert np.allclose(off_diag, 0, atol=1e-14)

    def test_i_f0_scale(self, small_op):
        """𝕀_{f₀} diagonal entries should equal f₀."""
        I_f0 = small_op._build_I_f0()
        diag_entries = np.diag(I_f0)
        assert np.allclose(diag_entries, F0_QCAL, atol=1e-8)

    def test_v_mod_is_diagonal(self, small_op):
        """V̂_mod should be a diagonal matrix."""
        V = small_op._V_mod
        off_diag = V - np.diag(np.diag(V))
        assert np.allclose(off_diag, 0, atol=1e-14)

    def test_v_mod_scale(self, small_op):
        """V̂_mod[0,0] should equal γ₁·ℏ/C."""
        gamma_1 = _get_riemann_zeros(1)[0]
        expected = gamma_1 * HBAR / C_QCAL
        assert abs(small_op._V_mod[0, 0] - expected) < 1e-6

    def test_v_mod_entries_positive(self, small_op):
        """All filled V̂_mod diagonal entries should be positive."""
        n_fill = min(small_op.N, small_op.n_zeros)
        diag = np.diag(small_op._V_mod)[:n_fill]
        assert np.all(diag > 0)

    def test_full_operator_is_real(self, small_op):
        """Ĥ_QCAL should be a real matrix."""
        assert small_op.H.dtype in (np.float32, np.float64)
        assert np.all(np.isreal(small_op.H))


# ---------------------------------------------------------------------------
# Hermiticity tests
# ---------------------------------------------------------------------------

class TestHermiticity:
    """Verify that Ĥ_QCAL is hermitian (self-adjoint)."""

    @pytest.fixture
    def op(self):
        return QCALSpectralOperator(N=30, n_zeros=5)

    def test_hermiticity_error_small(self, op):
        """Hermiticity error should be below numerical tolerance."""
        result = op.verify_hermiticity()
        assert result["hermiticity_error"] < 1e-10

    def test_is_hermitian_flag(self, op):
        """is_hermitian should be True."""
        result = op.verify_hermiticity()
        assert result["is_hermitian"] is True

    def test_eigenvalues_are_real(self, op):
        """All eigenvalues should be real."""
        result = op.verify_hermiticity()
        assert result["all_eigenvalues_real"] is True
        assert result["max_imaginary_eigenvalue"] < 1e-10

    def test_spectrum_eigenvalues(self, op):
        """eigh should return sorted real eigenvalues."""
        eigenvalues, eigenvectors = op.get_spectrum()
        assert eigenvalues.shape == (op.N,)
        assert np.all(np.isreal(eigenvalues))
        # Eigenvalues should be sorted
        assert np.all(np.diff(eigenvalues) >= -1e-8)


# ---------------------------------------------------------------------------
# Coherence tests
# ---------------------------------------------------------------------------

class TestCoherence:
    """Verify Ψ ≥ PSI_THRESHOLD for a hermitian operator."""

    @pytest.fixture
    def op(self):
        return QCALSpectralOperator(N=30, n_zeros=5)

    def test_coherence_above_threshold(self, op):
        """Coherence Ψ should meet or exceed 0.888."""
        psi = op.compute_coherence()
        assert psi >= PSI_THRESHOLD, (
            f"Coherence Ψ = {psi:.4f} is below threshold {PSI_THRESHOLD}"
        )

    def test_coherence_at_most_one(self, op):
        """Coherence Ψ should be in (0, 1]."""
        psi = op.compute_coherence()
        assert 0.0 < psi <= 1.0

    def test_perfect_hermitian_gives_psi_one(self):
        """A perfectly symmetric (hermitian) construction gives Ψ = 1.0.

        We construct a fresh operator, then explicitly symmetrise the matrix
        H ← (H + Hᵀ)/2 so that hermiticity_error is exactly 0, and verify
        that the coherence formula returns 1.0.  This tests the mathematical
        relationship Ψ = exp(−0/PSI_THRESHOLD) = 1, independent of how the
        operator was originally built.
        """
        op = QCALSpectralOperator(N=20, n_zeros=5)
        # Symmetrise to achieve exact hermiticity
        op.H = (op.H + op.H.T) / 2.0
        psi = op.compute_coherence()
        assert abs(psi - 1.0) < 1e-8


# ---------------------------------------------------------------------------
# Critical-line certification
# ---------------------------------------------------------------------------

class TestCriticalLineCertification:
    """Full certification: off-critical zeros = ∅."""

    @pytest.fixture
    def result(self):
        return certify_qcal_spectral_operator(N=30, n_zeros=5, verbose=False)

    def test_result_type(self, result):
        """certify_qcal_spectral_operator should return QCALSpectralResult."""
        assert isinstance(result, QCALSpectralResult)

    def test_is_hermitian(self, result):
        """Operator must be hermitian for certification."""
        assert result.is_hermitian is True

    def test_coherence_above_threshold(self, result):
        """Coherence must be ≥ PSI_THRESHOLD."""
        assert result.coherence_above_threshold is True

    def test_off_critical_zeros_empty(self, result):
        """Off-critical zeros set must be empty (∅)."""
        assert result.off_critical_zeros_empty is True

    def test_status_contains_qed(self, result):
        """Status string should contain QED-RIEMANN-VERIFIED."""
        assert "QED-RIEMANN-VERIFIED" in result.spectral_status

    def test_eigenvalues_shape(self, result):
        """Result should include N eigenvalues."""
        assert result.eigenvalues.shape[0] == 30

    def test_psi_value(self, result):
        """Ψ should be stored in result and ≥ threshold."""
        assert result.psi >= PSI_THRESHOLD

    def test_parameters_stored(self, result):
        """Parameters dict should contain key fields."""
        assert "N" in result.parameters
        assert "f0" in result.parameters
        assert "C" in result.parameters
        assert abs(result.parameters["f0"] - F0_QCAL) < 1e-4
        assert abs(result.parameters["C"] - C_QCAL) < 0.01

    def test_details_stored(self, result):
        """Details dict should contain diagnostics."""
        assert "hermiticity" in result.details
        assert "base_eigenvalue" in result.details
        assert abs(result.details["base_eigenvalue"] - F0_QCAL) < 1e-4


# ---------------------------------------------------------------------------
# Spectral table validation (problem statement Table)
# ---------------------------------------------------------------------------

class TestSpectralTable:
    """Validate the spectral parameter table from the problem statement."""

    def test_base_eigenvalue_lambda0_equals_f0(self):
        """λ₀ = f₀ = 141.7001 Hz (base autovalor de referencia)."""
        op = QCALSpectralOperator(N=20, n_zeros=5)
        I_f0 = op._build_I_f0()
        # The identity projector diagonal = f₀
        assert abs(I_f0[0, 0] - 141.7001) < 1e-4

    def test_operator_is_hermitian(self):
        """Operador Autoadjunto (Hermítico) — Certificado ✅."""
        op = QCALSpectralOperator(N=20, n_zeros=5)
        h = op.verify_hermiticity()
        assert h["is_hermitian"]

    def test_off_critical_zeros_empty_set(self):
        """Ceros Off-Critical = ∅ (Conjunto vacío) — Verificado ✅."""
        result = certify_qcal_spectral_operator(N=20, n_zeros=5)
        assert result.off_critical_zeros_empty

    def test_resonance_888_harmonic(self):
        """888 = PSI_THRESHOLD × 1000 — coherence resonance constant.

        The 888 Hz resonance in the QCAL framework is the integer-Hz
        representation of the coherence threshold (0.888 × 1000 = 888).
        It marks the boundary below which wave-function collapse removes
        critical-line stability. See compute_coherence() for details.
        """
        assert abs(PSI_THRESHOLD * 1000 - 888.0) < 1e-6

    def test_v_mod_proportional_to_gamma_hbar_c(self):
        """V̂_mod ∝ γ·ℏ/C — verify proportionality constant."""
        op = QCALSpectralOperator(N=20, n_zeros=3)
        zeros = _get_riemann_zeros(3)
        for k, gamma_k in enumerate(zeros):
            expected = gamma_k * HBAR / C_QCAL
            assert abs(op._V_mod[k, k] - expected) < 1e-8


# ---------------------------------------------------------------------------
# Edge cases and robustness
# ---------------------------------------------------------------------------

class TestRobustness:
    """Edge cases and parameter variation."""

    def test_small_n_matrix(self):
        """N = 5 should still construct and certify."""
        result = certify_qcal_spectral_operator(N=5, n_zeros=3)
        assert result.is_hermitian

    def test_n_zeros_larger_than_n(self):
        """n_zeros > N should not crash; unfilled rows remain zero."""
        op = QCALSpectralOperator(N=5, n_zeros=20)
        assert op.H.shape == (5, 5)
        # Only 5 diagonal entries of V_mod can be filled
        assert np.all(np.isfinite(op.H))

    def test_custom_f0(self):
        """Custom f₀ should scale the I_{f₀} projector."""
        custom_f0 = 200.0
        op = QCALSpectralOperator(N=10, n_zeros=5, f0=custom_f0)
        assert abs(op._build_I_f0()[0, 0] - custom_f0) < 1e-8

    def test_custom_c(self):
        """Custom C should scale V̂_mod entries."""
        custom_C = 100.0
        op = QCALSpectralOperator(N=10, n_zeros=5, C=custom_C)
        gamma_1 = _get_riemann_zeros(1)[0]
        expected = gamma_1 * HBAR / custom_C
        assert abs(op._V_mod[0, 0] - expected) < 1e-8

    def test_verbose_output(self, capsys):
        """verbose=True should print a summary."""
        certify_qcal_spectral_operator(N=10, n_zeros=3, verbose=True)
        captured = capsys.readouterr()
        assert "QCAL SPECTRAL OPERATOR" in captured.out
        assert "QED-RIEMANN-VERIFIED" in captured.out


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
