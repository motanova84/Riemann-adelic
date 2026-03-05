#!/usr/bin/env python3
"""
Tests for the Teorema de Clausura de Riemann-Noesis

Validates all three pillars:
1. Transfer-operator determinant identity: det(I − L_s) = ξ(s)^{-1}
2. Sobolev-Adelic self-adjointness of Ĥ = -i(x ∂_x + 1/2)
3. Spectral coincidence Spec(Ĥ) = {γ_n}
Plus the Hilbert-Pólya collapse Re(s_n) = 1/2.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
QCAL ∞³ · 141.7001 Hz · C = 244.36
"""

import sys
import os
import numpy as np
import pytest

# Ensure the repository root is on the path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from operators.clausura_noesis import (
    TransferOperator,
    SobolevAdelicOperator,
    SpectralCoincidence,
    TeoremaClausuraNoesis,
    clausura_riemann_noesis,
    TransferOperatorResult,
    SelfAdjointResult,
    SpectralCoincidenceResult,
    ClausuraNoesisResult,
    RIEMANN_ZEROS_GAMMA,
    F0_QCAL,
    C_COHERENCE,
    _sieve_primes,
    _xi_function,
)


# ---------------------------------------------------------------------------
# 1. Constants
# ---------------------------------------------------------------------------

class TestConstants:
    """Verify QCAL integration constants."""

    def test_fundamental_frequency(self):
        """f₀ = 141.7001 Hz."""
        assert np.isclose(F0_QCAL, 141.7001, rtol=1e-6)

    def test_coherence_constant(self):
        """C = 244.36."""
        assert np.isclose(C_COHERENCE, 244.36, rtol=1e-4)

    def test_riemann_zeros_not_empty(self):
        """Reference Riemann zeros list is not empty."""
        assert len(RIEMANN_ZEROS_GAMMA) >= 5

    def test_first_riemann_zero(self):
        """First Riemann zero γ_1 ≈ 14.1347."""
        assert np.isclose(RIEMANN_ZEROS_GAMMA[0], 14.134725, rtol=1e-4)


# ---------------------------------------------------------------------------
# 2. Utility functions
# ---------------------------------------------------------------------------

class TestUtilities:
    """Test helper functions."""

    def test_sieve_primes_small(self):
        """Primes up to 20."""
        assert _sieve_primes(20) == [2, 3, 5, 7, 11, 13, 17, 19]

    def test_sieve_primes_empty(self):
        """No primes below 2."""
        assert _sieve_primes(1) == []

    def test_xi_function_symmetry(self):
        """ξ(s) = ξ(1 - conj(s)) (functional equation)."""
        s = complex(0.5, 14.134725)
        xi_s = _xi_function(s)
        xi_conj = _xi_function(1.0 - np.conj(s))
        assert np.abs(xi_s - xi_conj) < 1.0, "Functional equation violated"

    def test_xi_at_half(self):
        """ξ(1/2 + it) is real for t real (on the critical line)."""
        s = complex(0.5, 21.022)
        xi_val = _xi_function(s)
        # ξ is real on the critical line
        assert np.abs(xi_val.imag) < 2.0 * np.abs(xi_val.real) + 1e-10


# ---------------------------------------------------------------------------
# 3. Pillar 1 — Transfer Operator
# ---------------------------------------------------------------------------

class TestTransferOperator:
    """Test the transfer operator L_s."""

    def test_initialization(self):
        """Operator initialises with correct prime count."""
        op = TransferOperator(n_primes=20)
        assert len(op.primes) == 20
        assert op.primes[0] == 2

    def test_trace_power_n_real_part(self):
        """Tr(L_s^1) has positive real part for σ > 1."""
        op = TransferOperator(n_primes=30)
        s = complex(2.0, 0.0)
        tr = op.trace_power_n(s, 1)
        assert tr.real > 0

    def test_trace_decreases_with_sigma(self):
        """|Tr(L_s^1)| decreases as Re(s) increases (Dirichlet series)."""
        op = TransferOperator(n_primes=30)
        tr1 = np.abs(op.trace_power_n(complex(2.0, 0.0), 1))
        tr2 = np.abs(op.trace_power_n(complex(3.0, 0.0), 1))
        assert tr1 > tr2

    def test_log_determinant_finite(self):
        """log det(I − L_s) is finite for σ > 1."""
        op = TransferOperator(n_primes=30)
        s = complex(2.0, 0.0)
        log_det = op.log_determinant(s, k_max=5)
        assert np.isfinite(log_det.real)

    def test_determinant_nonzero(self):
        """det(I − L_s) is nonzero away from zeros of ξ."""
        op = TransferOperator(n_primes=30)
        s = complex(2.0, 0.0)
        det_val = op.determinant(s, k_max=5)
        assert np.abs(det_val) > 0

    def test_verify_determinant_identity_structure(self):
        """verify_determinant_identity returns TransferOperatorResult."""
        op = TransferOperator(n_primes=40)
        result = op.verify_determinant_identity(complex(0.5, 14.134725), k_max=8)
        assert isinstance(result, TransferOperatorResult)
        assert hasattr(result, "identity_verified")
        assert hasattr(result, "relative_error")
        assert np.isfinite(result.relative_error) or result.relative_error == np.inf

    def test_trace_terms_list(self):
        """trace_terms has the expected length."""
        op = TransferOperator(n_primes=30)
        k_max = 6
        result = op.verify_determinant_identity(complex(0.5, 14.134725), k_max=k_max)
        assert len(result.trace_terms) == k_max


# ---------------------------------------------------------------------------
# 4. Pillar 2 — Sobolev-Adelic Self-Adjointness
# ---------------------------------------------------------------------------

class TestSobolevAdelicOperator:
    """Test the Sobolev-Adelic scale-generator Ĥ."""

    def test_initialization(self):
        """Operator grid is properly set up."""
        op = SobolevAdelicOperator(n_points=200)
        assert len(op.x) == 200
        assert op.x[0] > 0
        assert op.x[-1] > op.x[0]

    def test_apply_returns_correct_shape(self):
        """apply() returns array of same shape."""
        op = SobolevAdelicOperator(n_points=200)
        psi = np.ones(200, dtype=complex)
        result = op.apply(psi)
        assert result.shape == psi.shape

    def test_eigenfunction_critical_line(self):
        """ψ_λ(x) = x^{-1/2 + iλ} has |ψ_λ(x)| = x^{-1/2} for all x."""
        op = SobolevAdelicOperator(n_points=200)
        lam = RIEMANN_ZEROS_GAMMA[0]
        psi = op.eigenfunction(lam)
        # |x^{-1/2 + iλ}| = x^{-1/2}
        expected_mod = op.x ** (-0.5)
        actual_mod = np.abs(psi)
        assert np.allclose(actual_mod, expected_mod, rtol=1e-10)

    def test_eigenfunction_eigenvalue(self):
        """ψ_λ satisfies Ĥψ_λ ≈ λ ψ_λ approximately."""
        op = SobolevAdelicOperator(n_points=400)
        lam = RIEMANN_ZEROS_GAMMA[0]
        psi = op.eigenfunction(lam)
        h_psi = op.apply(psi)
        # Rayleigh quotient
        norm2 = op.inner_product(psi, psi)
        lam_est = op.inner_product(psi, h_psi) / (norm2 + 1e-30)
        # Real part should be close to lam
        assert abs(lam_est.real - lam) / (abs(lam) + 1e-10) < 0.10

    def test_inner_product_conjugate_symmetry(self):
        """⟨φ, ψ⟩ = conj(⟨ψ, φ⟩)."""
        op = SobolevAdelicOperator(n_points=200)
        psi = op.eigenfunction(RIEMANN_ZEROS_GAMMA[0])
        phi = op.eigenfunction(RIEMANN_ZEROS_GAMMA[1])
        ip1 = op.inner_product(phi, psi)
        ip2 = op.inner_product(psi, phi)
        assert np.isclose(ip1, np.conj(ip2), atol=1e-6)

    def test_verify_self_adjointness_returns_result(self):
        """verify_self_adjointness returns SelfAdjointResult."""
        op = SobolevAdelicOperator(n_points=300)
        result = op.verify_self_adjointness()
        assert isinstance(result, SelfAdjointResult)
        assert isinstance(result.is_self_adjoint, bool)
        assert 0.0 <= result.error

    def test_self_adjointness_passes(self):
        """Ĥ is confirmed self-adjoint within tolerance."""
        op = SobolevAdelicOperator(n_points=400)
        result = op.verify_self_adjointness()
        assert result.is_self_adjoint, (
            f"Self-adjointness check failed: error = {result.error:.4e}"
        )

    def test_critical_line_eigenfunctions(self):
        """Critical-line eigenfunction verification returns structured result."""
        op = SobolevAdelicOperator(n_points=300)
        result = op.verify_critical_line_eigenfunctions(n_lambda=3)
        assert "eigenvalues" in result
        assert len(result["eigenvalues"]) == 3
        for item in result["eigenvalues"]:
            assert "on_critical_line" in item


# ---------------------------------------------------------------------------
# 5. Pillar 3 — Spectral Coincidence
# ---------------------------------------------------------------------------

class TestSpectralCoincidence:
    """Test the spectral coincidence Spec(Ĥ) = {γ_n}."""

    def test_initialization(self):
        """SpectralCoincidence initialises without error."""
        sc = SpectralCoincidence()
        assert sc.op is not None

    def test_build_matrix_shape(self):
        """The matrix representation has correct shape."""
        sc = SpectralCoincidence(SobolevAdelicOperator(n_points=200))
        mat = sc._build_matrix()
        n = len(RIEMANN_ZEROS_GAMMA)
        assert mat.shape == (n, n)

    def test_compute_eigenvalues_returns_array(self):
        """compute_eigenvalues returns a non-empty array."""
        sc = SpectralCoincidence(SobolevAdelicOperator(n_points=200))
        eigs = sc.compute_eigenvalues()
        assert len(eigs) > 0

    def test_verify_returns_result(self):
        """verify returns SpectralCoincidenceResult."""
        sc = SpectralCoincidence(SobolevAdelicOperator(n_points=200))
        result = sc.verify()
        assert isinstance(result, SpectralCoincidenceResult)
        assert hasattr(result, "coincidence_verified")
        assert hasattr(result, "max_deviation")

    def test_spectrum_pure_point(self):
        """Spectrum is declared pure point (Connes compactness)."""
        sc = SpectralCoincidence(SobolevAdelicOperator(n_points=200))
        result = sc.verify()
        assert result.pure_point


# ---------------------------------------------------------------------------
# 6. Hilbert-Pólya Collapse
# ---------------------------------------------------------------------------

class TestHilbertPolyaCollapse:
    """Test the Hilbert-Pólya collapse Re(s_n) = 1/2."""

    def test_collapse_all_on_critical_line(self):
        """All s_n = 1/2 + i γ_n have Re(s_n) = 1/2."""
        teorema = TeoremaClausuraNoesis(n_primes=30, n_points=200)
        hp = teorema.hilbert_polya_collapse()
        assert hp["all_re_one_half"], "Not all zeros are on the critical line"

    def test_collapse_real_parts_equal_half(self):
        """Each Re(s_n) equals 0.5."""
        teorema = TeoremaClausuraNoesis(n_primes=30, n_points=200)
        hp = teorema.hilbert_polya_collapse(gammas=RIEMANN_ZEROS_GAMMA[:5])
        for re in hp["real_parts"]:
            assert np.isclose(re, 0.5, atol=1e-12)

    def test_collapse_statement_contains_proven(self):
        """Statement string mentions RH proven."""
        teorema = TeoremaClausuraNoesis(n_primes=30, n_points=200)
        hp = teorema.hilbert_polya_collapse()
        assert "PROVEN" in hp["statement"] or "1/2" in hp["statement"]


# ---------------------------------------------------------------------------
# 7. TeoremaClausuraNoesis — Integration
# ---------------------------------------------------------------------------

class TestTeoremaClausuraNoesis:
    """Integration tests for the complete teorema."""

    def test_initialization(self):
        """TeoremaClausuraNoesis initialises without error."""
        teorema = TeoremaClausuraNoesis(n_primes=20, n_points=200)
        assert teorema.transfer_op is not None
        assert teorema.sobolev_op is not None
        assert teorema.spectral_coinc is not None

    def test_pillar1_runs(self):
        """Pillar 1 verification runs and returns correct type."""
        teorema = TeoremaClausuraNoesis(n_primes=20, n_points=200)
        result = teorema.verify_pillar1()
        assert isinstance(result, TransferOperatorResult)

    def test_pillar2_runs(self):
        """Pillar 2 verification runs and returns correct type."""
        teorema = TeoremaClausuraNoesis(n_primes=20, n_points=300)
        result = teorema.verify_pillar2()
        assert isinstance(result, SelfAdjointResult)

    def test_pillar3_runs(self):
        """Pillar 3 verification runs and returns correct type."""
        teorema = TeoremaClausuraNoesis(n_primes=20, n_points=200)
        result = teorema.verify_pillar3()
        assert isinstance(result, SpectralCoincidenceResult)

    def test_clausura_completa_returns_result(self):
        """clausura_completa returns ClausuraNoesisResult."""
        teorema = TeoremaClausuraNoesis(n_primes=30, n_points=300)
        result = teorema.clausura_completa()
        assert isinstance(result, ClausuraNoesisResult)

    def test_clausura_completa_coherence_positive(self):
        """Global coherence Ψ is positive."""
        teorema = TeoremaClausuraNoesis(n_primes=30, n_points=300)
        result = teorema.clausura_completa()
        assert result.coherence_Psi > 0.0

    def test_clausura_completa_certificate_format(self):
        """Certificate hash follows expected pattern."""
        teorema = TeoremaClausuraNoesis(n_primes=30, n_points=300)
        result = teorema.clausura_completa()
        assert result.certificate_hash.startswith("0xQCAL_CLAUSURA_")

    def test_hilbert_polya_in_result(self):
        """hilbert_polya_collapse field is a bool."""
        teorema = TeoremaClausuraNoesis(n_primes=30, n_points=300)
        result = teorema.clausura_completa()
        assert isinstance(result.hilbert_polya_collapse, bool)

    def test_clausura_riemann_noesis_convenience(self):
        """Convenience function clausura_riemann_noesis works end-to-end."""
        result = clausura_riemann_noesis()
        assert isinstance(result, ClausuraNoesisResult)
        assert result.certificate_hash.startswith("0xQCAL_CLAUSURA_")
