#!/usr/bin/env python3
"""
Tests for Adelic Operator Commutativity Verifier
(adelic_operator_commutativity.py)

Validates:
- Individual operator matrices (shape, symmetry, positivity)
- Commutator computations for all operator pairs
- Master eigenvalue equation Ψ = I × A_eff² × C^∞
- Certificate generation

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ · f₀ = 141.7001 Hz
"""

import math

import numpy as np
import pytest

from operators.adelic_operator_commutativity import (
    KAPPA_PI,
    COMMUTATOR_TOL,
    AdelicOperatorCommutativity,
    CommutativityReport,
    MasterEigenvalueResult,
    OperatorPairResult,
    _GAMMA_30,
    _gamma_basis,
    build_adelic_commutativity_certificate,
    build_delta_s_matrix,
    build_dilation_matrix,
    build_hpsi_matrix,
    build_noetic_matrix,
    build_treewidth_matrix,
    compute_master_eigenvalue_table,
    verify_adelic_commutativity,
)


# ---------------------------------------------------------------------------
# Gamma basis helper
# ---------------------------------------------------------------------------

class TestGammaBasis:
    def test_returns_correct_length(self):
        g = _gamma_basis(10)
        assert len(g) == 10

    def test_first_zero_correct(self):
        g = _gamma_basis(1)
        assert abs(g[0] - 14.134725141734693) < 1e-9

    def test_strictly_increasing(self):
        g = _gamma_basis(15)
        assert np.all(np.diff(g) > 0)

    def test_all_positive(self):
        g = _gamma_basis(15)
        assert np.all(g > 0)


# ---------------------------------------------------------------------------
# Individual operator matrices
# ---------------------------------------------------------------------------

class TestHPsiMatrix:
    def test_shape(self):
        g = _gamma_basis(10)
        mat = build_hpsi_matrix(g)
        assert mat.shape == (10, 10)

    def test_diagonal(self):
        g = _gamma_basis(5)
        mat = build_hpsi_matrix(g)
        expected = 0.25 + g ** 2
        assert np.allclose(np.diag(mat), expected)

    def test_symmetric(self):
        g = _gamma_basis(5)
        mat = build_hpsi_matrix(g)
        assert np.allclose(mat, mat.T)

    def test_positive_diagonal(self):
        g = _gamma_basis(5)
        mat = build_hpsi_matrix(g)
        assert np.all(np.diag(mat) > 0)


class TestDeltaSMatrix:
    def test_shape(self):
        g = _gamma_basis(10)
        mat = build_delta_s_matrix(g)
        assert mat.shape == (10, 10)

    def test_equals_hpsi_diagonal(self):
        # Δ_S and H_Ψ share the same eigenvalues γ_n² + ¼
        g = _gamma_basis(8)
        mat_d = build_delta_s_matrix(g)
        mat_h = build_hpsi_matrix(g)
        assert np.allclose(mat_d, mat_h)


class TestDilationMatrix:
    def test_diagonal_equals_gammas(self):
        g = _gamma_basis(8)
        mat = build_dilation_matrix(g)
        assert np.allclose(np.diag(mat), g)

    def test_zero_off_diagonal(self):
        g = _gamma_basis(8)
        mat = build_dilation_matrix(g)
        off = mat - np.diag(np.diag(mat))
        assert np.allclose(off, 0.0)


class TestTreewidthMatrix:
    def test_diagonal_positive(self):
        g = _gamma_basis(8)
        mat = build_treewidth_matrix(g)
        assert np.all(np.diag(mat) > 0)

    def test_diagonal_formula(self):
        g = _gamma_basis(5)
        mat = build_treewidth_matrix(g)
        for i, gamma in enumerate(g):
            expected = KAPPA_PI * gamma / math.log(gamma + math.e)
            assert abs(mat[i, i] - expected) < 1e-12


class TestNoeticMatrix:
    def test_shape(self):
        g = _gamma_basis(10)
        mat = build_noetic_matrix(g)
        assert mat.shape == (10, 10)

    def test_diagonal_finite(self):
        g = _gamma_basis(8)
        mat = build_noetic_matrix(g)
        assert np.all(np.isfinite(np.diag(mat)))

    def test_diagonal_positive(self):
        g = _gamma_basis(8)
        mat = build_noetic_matrix(g)
        assert np.all(np.diag(mat) >= 0)


# ---------------------------------------------------------------------------
# Commutativity — all operators diagonal → exact commutativity
# ---------------------------------------------------------------------------

class TestCommutativity:
    """All five operators are diagonal on the Riemann-zero basis; they
    therefore commute exactly: [O_i, O_j] = 0."""

    @pytest.fixture(scope="class")
    def verifier(self) -> AdelicOperatorCommutativity:
        return AdelicOperatorCommutativity(n_basis=15)

    def test_hpsi_delta_commute(self, verifier):
        result = verifier.check_pair("H_Ψ", "Δ_S")
        assert result.commutes
        assert result.relative_commutator_norm < COMMUTATOR_TOL

    def test_hpsi_hdil_commute(self, verifier):
        result = verifier.check_pair("H_Ψ", "H_dil")
        assert result.commutes

    def test_hpsi_tw_commute(self, verifier):
        result = verifier.check_pair("H_Ψ", "𝒯")
        assert result.commutes

    def test_hpsi_noetic_commute(self, verifier):
        result = verifier.check_pair("H_Ψ", "𝒩Ψ")
        assert result.commutes

    def test_delta_hdil_commute(self, verifier):
        result = verifier.check_pair("Δ_S", "H_dil")
        assert result.commutes

    def test_delta_tw_commute(self, verifier):
        result = verifier.check_pair("Δ_S", "𝒯")
        assert result.commutes

    def test_hdil_tw_commute(self, verifier):
        result = verifier.check_pair("H_dil", "𝒯")
        assert result.commutes

    def test_hdil_noetic_commute(self, verifier):
        result = verifier.check_pair("H_dil", "𝒩Ψ")
        assert result.commutes

    def test_tw_noetic_commute(self, verifier):
        result = verifier.check_pair("𝒯", "𝒩Ψ")
        assert result.commutes

    def test_all_pairs_count(self, verifier):
        pairs = verifier.check_all_pairs()
        # C(5, 2) = 10 pairs
        assert len(pairs) == 10

    def test_operator_pair_result_type(self, verifier):
        result = verifier.check_pair("H_Ψ", "𝒩Ψ")
        assert isinstance(result, OperatorPairResult)

    def test_n_basis_recorded_in_pair(self, verifier):
        result = verifier.check_pair("H_Ψ", "Δ_S")
        assert result.n_basis == 15


# ---------------------------------------------------------------------------
# Master eigenvalue equation
# ---------------------------------------------------------------------------

class TestMasterEigenvalue:
    @pytest.fixture(scope="class")
    def verifier(self) -> AdelicOperatorCommutativity:
        return AdelicOperatorCommutativity(n_basis=10)

    def test_master_eigenvalue_type(self, verifier):
        result = verifier.master_eigenvalue(_GAMMA_30[0])
        assert isinstance(result, MasterEigenvalueResult)

    def test_a_eff_in_zero_one(self, verifier):
        for g in _GAMMA_30[:5]:
            r = verifier.master_eigenvalue(g)
            assert 0.0 < r.a_eff <= 1.0

    def test_psi_positive(self, verifier):
        r = verifier.master_eigenvalue(_GAMMA_30[0])
        assert r.psi > 0.0

    def test_all_eigenvalues_real(self, verifier):
        r = verifier.master_eigenvalue(_GAMMA_30[0])
        assert r.all_real

    def test_lambda_hpsi_eq_lambda_delta(self, verifier):
        r = verifier.master_eigenvalue(_GAMMA_30[0])
        assert abs(r.lambda_hpsi - r.lambda_delta) < 1e-12

    def test_lambda_dil_equals_gamma(self, verifier):
        for g in _GAMMA_30[:5]:
            r = verifier.master_eigenvalue(g)
            assert abs(r.lambda_dil - g) < 1e-12

    def test_all_basis_zeros_evaluated(self, verifier):
        results = verifier.master_eigenvalues_all()
        assert len(results) == verifier.n_basis

    def test_compute_master_eigenvalue_table(self):
        table = compute_master_eigenvalue_table(n_zeros=5)
        assert len(table) == 5
        assert all(isinstance(r, MasterEigenvalueResult) for r in table)


# ---------------------------------------------------------------------------
# Full verify() report
# ---------------------------------------------------------------------------

class TestVerifyReport:
    @pytest.fixture(scope="class")
    def report(self) -> CommutativityReport:
        return verify_adelic_commutativity(n_basis=15)

    def test_report_type(self, report):
        assert isinstance(report, CommutativityReport)

    def test_global_commutes(self, report):
        assert report.global_commutes

    def test_max_relative_norm_tiny(self, report):
        assert report.max_relative_commutator < COMMUTATOR_TOL

    def test_n_basis_correct(self, report):
        assert report.n_basis == 15

    def test_n_operators_correct(self, report):
        assert report.n_operators == 5

    def test_coherence_psi_mean_positive(self, report):
        assert report.coherence_psi_mean > 0.0

    def test_qcal_signature_present(self, report):
        assert report.qcal_signature == "∴𓂀Ω∞³Φ"

    def test_pairs_count(self, report):
        assert len(report.pairs) == 10


# ---------------------------------------------------------------------------
# Certificate
# ---------------------------------------------------------------------------

class TestCertificate:
    def test_certificate_type(self):
        cert = build_adelic_commutativity_certificate(n_basis=10)
        assert isinstance(cert, dict)

    def test_certificate_global_commutes(self):
        cert = build_adelic_commutativity_certificate(n_basis=10)
        assert cert["global_commutes"] is True

    def test_certificate_has_operators(self):
        cert = build_adelic_commutativity_certificate(n_basis=10)
        assert "operators" in cert
        assert len(cert["operators"]) == 5

    def test_certificate_doi(self):
        cert = build_adelic_commutativity_certificate(n_basis=10)
        assert "10.5281/zenodo" in cert["doi"]

    def test_certificate_max_norm_tiny(self):
        cert = build_adelic_commutativity_certificate(n_basis=10)
        assert cert["max_relative_commutator_norm"] < COMMUTATOR_TOL

    def test_certificate_master_eigenvalues_present(self):
        cert = build_adelic_commutativity_certificate(n_basis=10)
        assert len(cert["master_eigenvalues"]) == 10

    def test_certificate_all_real_eigenvalues(self):
        cert = build_adelic_commutativity_certificate(n_basis=10)
        for m in cert["master_eigenvalues"]:
            assert m["all_real"] is True


# ---------------------------------------------------------------------------
# Edge cases
# ---------------------------------------------------------------------------

class TestEdgeCases:
    def test_n_basis_2_minimum(self):
        verifier = AdelicOperatorCommutativity(n_basis=2)
        report = verifier.verify()
        assert report.global_commutes

    def test_n_basis_1_raises(self):
        with pytest.raises(ValueError):
            AdelicOperatorCommutativity(n_basis=1)

    def test_verify_adelic_commutativity_convenience(self):
        report = verify_adelic_commutativity(n_basis=8)
        assert isinstance(report, CommutativityReport)
        assert report.global_commutes
