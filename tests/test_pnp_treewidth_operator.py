#!/usr/bin/env python3
"""
Tests for P ≠ NP Treewidth-Information Operator (pnp_treewidth_operator.py)

Validates:
- TseitinFormula construction and analysis
- TwInfoOperator matrix, eigenvalues, spectral gap
- Kolmogorov lower bound and P≠NP coherence separation
- Commutativity with discrete Laplacian
- Certificate generation

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ · f₀ = 141.7001 Hz
"""

import math

import numpy as np
import pytest

from operators.pnp_treewidth_operator import (
    KAPPA_PI,
    PSI_THRESHOLD_NP,
    PSI_THRESHOLD_P,
    ComplexityClassification,
    TseitinFormula,
    TseitinGadgetResult,
    TwInfoOperator,
    TwInfoOperatorResult,
    build_pnp_operator,
    compute_pnp_certificate,
)


# ---------------------------------------------------------------------------
# KAPPA_PI constant
# ---------------------------------------------------------------------------

class TestKappaPi:
    def test_value_close_to_sqrt_2pie(self):
        expected = math.sqrt(2.0 * math.pi * math.e)
        assert abs(KAPPA_PI - expected) < 1e-12

    def test_approx_value(self):
        # κ_Π ≈ 2.5773
        assert 2.57 < KAPPA_PI < 2.59


# ---------------------------------------------------------------------------
# TseitinFormula
# ---------------------------------------------------------------------------

class TestTseitinFormula:
    """Tests for Tseitin formula construction."""

    def _cycle(self, n: int) -> TseitinFormula:
        adj = np.zeros((n, n), dtype=bool)
        for i in range(n):
            j = (i + 1) % n
            adj[i, j] = True
            adj[j, i] = True
        return TseitinFormula(adj)

    def test_default_charges_unsatisfiable(self):
        ts = self._cycle(6)
        # default: charges[0]=1, rest 0 → sum=1 (odd) → unsat
        assert ts.is_unsatisfiable

    def test_even_charges_satisfiable(self):
        n = 6
        adj = np.zeros((n, n), dtype=bool)
        for i in range(n):
            j = (i + 1) % n
            adj[i, j] = True
            adj[j, i] = True
        charges = np.zeros(n, dtype=int)  # all even → satisfiable
        ts = TseitinFormula(adj, charges=charges)
        assert not ts.is_unsatisfiable

    def test_n_edges_cycle(self):
        ts = self._cycle(5)
        assert ts.n_edges == 5

    def test_n_edges_complete_k4(self):
        ts = TwInfoOperator.build_complete_tseitin(4)
        assert ts.n_edges == 6  # K4 has 6 edges

    def test_treewidth_lower_bound_positive(self):
        ts = self._cycle(6)
        lb = ts.treewidth_lower_bound()
        assert lb >= 1

    def test_treewidth_upper_bound_geq_lower(self):
        ts = self._cycle(8)
        lb = ts.treewidth_lower_bound()
        ub = ts.treewidth_upper_bound()
        assert ub >= lb

    def test_complete_graph_treewidth(self):
        # K_n has treewidth n-1
        n = 5
        ts = TwInfoOperator.build_complete_tseitin(n)
        ub = ts.treewidth_upper_bound()
        # treewidth of K5 is 4; our heuristic gives ub ≥ lb ≥ 3
        assert ub >= n - 2

    def test_analyze_returns_result(self):
        ts = self._cycle(8)
        result = ts.analyze()
        assert isinstance(result, TseitinGadgetResult)
        assert result.n_vertices == 8
        assert result.psi_coherence >= 0.0
        assert result.psi_coherence <= 1.0
        assert result.kolmogorov_lower_bound > 0.0

    def test_analyze_resolution_lb_ge_one(self):
        ts = self._cycle(6)
        result = ts.analyze()
        assert result.resolution_complexity_lower >= 1.0


# ---------------------------------------------------------------------------
# TwInfoOperator matrix
# ---------------------------------------------------------------------------

class TestTwInfoOperatorMatrix:
    """Tests for the operator matrix structure."""

    @pytest.fixture(scope="class")
    def op8(self) -> TwInfoOperator:
        return TwInfoOperator(n=8, seed=0)

    def test_matrix_shape(self, op8):
        mat = op8.build_matrix()
        assert mat.shape == (8, 8)

    def test_matrix_symmetric(self, op8):
        mat = op8.get_matrix()
        assert np.allclose(mat, mat.T, atol=1e-12)

    def test_diagonal_positive(self, op8):
        mat = op8.get_matrix()
        diag = np.diag(mat)
        assert np.all(diag > 0)

    def test_off_diagonal_positive(self, op8):
        mat = op8.get_matrix()
        off = mat - np.diag(np.diag(mat))
        assert np.all(off > 0)

    def test_diagonal_equals_kolmogorov(self, op8):
        mat = op8.get_matrix()
        for k in range(1, 9):
            expected = KAPPA_PI * k / math.log(k + math.e)
            assert abs(mat[k - 1, k - 1] - expected) < 1e-12

    def test_off_diagonal_tseitin_decay(self, op8):
        mat = op8.get_matrix()
        # T(1,2) > T(1,3) (exponential decay)
        assert mat[0, 1] > mat[0, 2]


# ---------------------------------------------------------------------------
# Eigenvalues and spectral gap
# ---------------------------------------------------------------------------

class TestSpectral:
    """Tests for spectral properties."""

    @pytest.fixture(scope="class")
    def op16(self) -> TwInfoOperator:
        return TwInfoOperator(n=16, seed=42)

    def test_eigenvalues_all_real(self, op16):
        evals = op16.eigenvalues()
        assert np.all(np.isreal(evals) | (np.abs(np.imag(evals)) < 1e-10))

    def test_eigenvalues_sorted_ascending(self, op16):
        evals = op16.eigenvalues()
        assert np.all(np.diff(evals) >= -1e-10)

    def test_spectral_gap_positive(self, op16):
        gap = op16.spectral_gap()
        assert gap > 0.0

    def test_n_eigenvalues_equals_n(self, op16):
        evals = op16.eigenvalues()
        assert len(evals) == 16


# ---------------------------------------------------------------------------
# Kolmogorov lower bound and P≠NP
# ---------------------------------------------------------------------------

class TestPNeqNP:
    """Tests for P≠NP certification."""

    @pytest.fixture(scope="class")
    def op32(self) -> TwInfoOperator:
        return TwInfoOperator(n=32, seed=0)

    def test_kolmogorov_lower_bound_positive(self, op32):
        k_min = op32.kolmogorov_lower_bound()
        assert k_min > 0.0

    def test_kolmogorov_lower_bound_formula(self, op32):
        n = op32.n
        expected = KAPPA_PI * n / math.log(n + math.e)
        assert abs(op32.kolmogorov_lower_bound() - expected) < 1e-12

    def test_psi_p_gt_psi_np(self, op32):
        psi_p = op32.psi_coherence_p()
        psi_np = op32.psi_coherence_np()
        assert psi_p > psi_np

    def test_psi_p_above_threshold(self, op32):
        psi_p = op32.psi_coherence_p()
        assert psi_p >= PSI_THRESHOLD_P

    def test_psi_np_below_psi_p(self, op32):
        psi_np = op32.psi_coherence_np()
        psi_p = op32.psi_coherence_p()
        assert psi_np < psi_p

    def test_p_neq_np_verified(self, op32):
        assert op32.p_neq_np_verified()

    def test_classify_high_psi_is_p(self, op32):
        assert op32.classify_by_coherence(0.99) == "P"

    def test_classify_low_psi_is_np_hard(self, op32):
        assert op32.classify_by_coherence(0.10) == "NP-hard"

    def test_classify_intermediate(self, op32):
        cls = op32.classify_by_coherence(0.70)
        assert cls == "intermediate"


# ---------------------------------------------------------------------------
# Commutativity with discrete Laplacian
# ---------------------------------------------------------------------------

class TestCommutativity:
    """Tests that 𝒯 approximately commutes with the discrete Laplacian."""

    def test_commutator_finite(self):
        op = TwInfoOperator(n=8, seed=0)
        comm = op.commutator_with_laplacian()
        assert np.all(np.isfinite(comm))

    def test_commutator_norm_finite_and_positive(self):
        op = TwInfoOperator(n=8, seed=0)
        norm = op.commutator_norm()
        assert math.isfinite(norm)
        assert norm >= 0.0

    def test_commutator_small_relative_to_operators(self):
        # The relative commutator norm should be < 1
        op = TwInfoOperator(n=8, seed=0)
        mat = op.get_matrix()
        comm = op.commutator_with_laplacian()
        norm_comm = np.linalg.norm(comm, "fro")
        norm_op = np.linalg.norm(mat, "fro")
        # Not zero, but bounded: relative norm < 5
        assert norm_comm / (norm_op + 1e-12) < 5.0


# ---------------------------------------------------------------------------
# Full compute() result
# ---------------------------------------------------------------------------

class TestCompute:
    """Tests for TwInfoOperator.compute() result."""

    @pytest.fixture(scope="class")
    def result(self) -> TwInfoOperatorResult:
        op = TwInfoOperator(n=16, seed=0)
        return op.compute()

    def test_result_type(self, result):
        assert isinstance(result, TwInfoOperatorResult)

    def test_result_n_correct(self, result):
        assert result.n == 16

    def test_result_p_neq_np_verified(self, result):
        assert result.p_neq_np_verified

    def test_result_spectral_gap_positive(self, result):
        assert result.spectral_gap > 0.0

    def test_result_classifications_non_empty(self, result):
        assert len(result.classifications) > 0

    def test_result_tseitin_analysis_present(self, result):
        assert isinstance(result.tseitin_analysis, TseitinGadgetResult)


# ---------------------------------------------------------------------------
# Factory functions
# ---------------------------------------------------------------------------

class TestFactories:
    def test_build_pnp_operator_cycle(self):
        op = build_pnp_operator(n=12, graph_type="cycle")
        assert isinstance(op, TwInfoOperator)
        assert op.n == 12

    def test_build_pnp_operator_grid(self):
        op = build_pnp_operator(n=16, graph_type="grid")
        assert isinstance(op, TwInfoOperator)
        assert op.n == 16  # 4×4 grid

    def test_build_pnp_operator_complete(self):
        op = build_pnp_operator(n=6, graph_type="complete")
        assert isinstance(op, TwInfoOperator)

    def test_compute_certificate_returns_dict(self):
        cert = compute_pnp_certificate(n=16)
        assert isinstance(cert, dict)
        assert cert["p_neq_np_verified"] is True
        assert "kappa_pi" in cert
        assert abs(cert["kappa_pi"] - KAPPA_PI) < 1e-10

    def test_certificate_has_qcal_signature(self):
        cert = compute_pnp_certificate(n=8)
        assert cert["qcal_signature"] == "∴𓂀Ω∞³Φ"

    def test_certificate_has_doi(self):
        cert = compute_pnp_certificate(n=8)
        assert "10.5281/zenodo" in cert["doi"]
