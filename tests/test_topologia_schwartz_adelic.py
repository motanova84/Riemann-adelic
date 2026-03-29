"""
Tests for operators/topologia_schwartz_adelic.py
================================================

Validates the three-pillar V8 rigour framework:
  - Pilar 1: Topology of S(A_Q) and Nuclearity of L_t
  - Pilar 2: Transversal Determinant W_{p,k} = log(p) / p^{k/2}
  - Pilar 3: Convergence and Absence of Residual Terms
"""

import importlib.util
import math
import sys
from pathlib import Path

import numpy as np
import pytest

# ---------------------------------------------------------------------------
# Import module directly (avoids the operators package __init__ matplotlib dep)
# ---------------------------------------------------------------------------
PROJECT_ROOT = Path(__file__).parent.parent
_spec = importlib.util.spec_from_file_location(
    "topologia_schwartz_adelic",
    PROJECT_ROOT / "operators" / "topologia_schwartz_adelic.py",
)
tsa = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(tsa)


# ===========================================================================
# Pilar 1 — Nuclearity
# ===========================================================================

class TestPilar1Nuclearity:
    """Tests for Pilar 1: Schwartz-Bruhat topology and nuclearity of L_t."""

    def test_peter_weyl_block_diagonal_phase(self):
        """L_t acts as a pure phase on each character: |e^{it λ_χ}| = 1."""
        proj = tsa.PeterWeylProjection(t=1.0, characters=[0, 1, 2], eigenvalues=[0.0, 1.0, 2.0])
        for chi in [0.0, 0.5, 1.0, 2.0, -3.0]:
            action = proj.block_diagonal_action(chi)
            assert abs(abs(action) - 1.0) < 1e-12, (
                f"Block-diagonal action should be a pure phase, got |{action}| ≠ 1"
            )

    def test_grothendieck_trace_partial_zero_time(self):
        """At t = 0 the partial trace equals the number of terms (each e^0 = 1)."""
        eigenvalues = list(range(10))
        proj = tsa.PeterWeylProjection(t=0.0, characters=eigenvalues, eigenvalues=eigenvalues)
        trace = proj.grothendieck_trace_partial(10)
        assert abs(trace.real - 10.0) < 1e-12
        assert abs(trace.imag) < 1e-12

    def test_nuclear_kernel_coefficient_decay(self):
        """Peter-Weyl coefficients of K_t decay as (1 + |χ|)^{-2}."""
        kernel = tsa.NuclearKernelBound(t=1.0)
        c1 = kernel.coefficient_bound(1)
        c10 = kernel.coefficient_bound(10)
        # Ratio should be approximately (1+1)^2 / (1+10)^2 = 4/121
        expected_ratio = (1.0 + 1.0) ** 2 / (1.0 + 10.0) ** 2
        assert abs(c10 / c1 - expected_ratio) < 1e-10

    def test_trace_norm_bound_finite(self):
        """The trace-norm bound should be finite (= truncation_T = 888)."""
        kernel = tsa.NuclearKernelBound(t=1.0, truncation_T=888.0)
        assert kernel.trace_norm_bound() == 888.0
        assert kernel.is_nuclear()

    def test_verify_nuclearity_pilar1_structure(self):
        """verify_nuclearity_pilar1 returns the expected keys and status."""
        result = tsa.verify_nuclearity_pilar1(t=1.0, n_characters=20)
        assert result["pilar"] == 1
        assert result["is_nuclear"] is True
        assert result["block_diagonal_verified"] is True
        assert result["status"] == "VERIFIED"
        assert "trace_norm_bound" in result
        assert result["trace_norm_bound"] > 0

    def test_grothendieck_trace_is_tempered(self):
        """The partial trace should be bounded (distributional, not classical)."""
        result = tsa.verify_nuclearity_pilar1(t=2.0, n_characters=50)
        # The real and imaginary parts are bounded (distributional trace)
        assert abs(result["grothendieck_trace_partial_re"]) < 1e6
        assert abs(result["grothendieck_trace_partial_im"]) < 1e6


# ===========================================================================
# Pilar 2 — Transversal Determinant
# ===========================================================================

class TestPilar2TransversalDeterminant:
    """Tests for Pilar 2: orbit weights W_{p,k} = log(p) / p^{k/2}."""

    @pytest.mark.parametrize("p,k", [(2, 1), (2, 2), (3, 1), (5, 1), (7, 2)])
    def test_archimedean_factor(self, p, k):
        """Archimedean factor should be p^k."""
        contrib = tsa.LocalPlaceContribution(p=float(p), k=k)
        assert abs(contrib.archimedean_factor() - float(p) ** k) < 1e-12

    @pytest.mark.parametrize("p,k", [(2, 1), (3, 1), (5, 2)])
    def test_padic_factor(self, p, k):
        """p-adic factor should be p^{-k}."""
        contrib = tsa.LocalPlaceContribution(p=float(p), k=k)
        assert abs(contrib.padic_factor() - float(p) ** (-k)) < 1e-12

    @pytest.mark.parametrize("p,k", [(2, 1), (2, 3), (3, 2), (5, 1), (11, 1)])
    def test_product_formula(self, p, k):
        """Product of archimedean and p-adic factors must equal 1 (product formula)."""
        contrib = tsa.LocalPlaceContribution(p=float(p), k=k)
        assert abs(contrib.adelic_norm_product() - 1.0) < 1e-12, (
            f"Product formula violated for p={p}, k={k}: "
            f"|p^k|_∞ · |p^k|_p = {contrib.adelic_norm_product()} ≠ 1"
        )

    @pytest.mark.parametrize("p,k", [(2, 1), (3, 1), (5, 2), (7, 1), (13, 3)])
    def test_transversal_determinant(self, p, k):
        """Transversal determinant should be p^{k/2}."""
        contrib = tsa.LocalPlaceContribution(p=float(p), k=k)
        expected = float(p) ** (k / 2.0)
        assert abs(contrib.transversal_determinant() - expected) < 1e-10, (
            f"det(I - dφ_t)_N = {contrib.transversal_determinant()} ≠ {expected}"
        )

    @pytest.mark.parametrize("p,k", [(2, 1), (3, 1), (5, 1)])
    def test_orbit_weight_formula(self, p, k):
        """Orbit weight should equal log(p) / p^{k/2}."""
        contrib = tsa.LocalPlaceContribution(p=float(p), k=k)
        expected = math.log(p) / float(p) ** (k / 2.0)
        assert abs(contrib.orbit_weight() - expected) < 1e-12

    def test_unramified_factor_is_one(self):
        """Unramified places contribute a factor of 1."""
        contrib = tsa.LocalPlaceContribution(p=5.0, k=2)
        assert contrib.unramified_factor() == 1.0

    def test_weights_decay_with_k(self):
        """For fixed p, W_{p,k} should decrease as k increases."""
        p = 3
        weights = [
            tsa.LocalPlaceContribution(p=float(p), k=k).orbit_weight()
            for k in range(1, 5)
        ]
        for i in range(len(weights) - 1):
            assert weights[i] > weights[i + 1], (
                f"W_{{p,k}} should decrease: W_{{3,{i+1}}} = {weights[i]:.6f} "
                f"≤ W_{{3,{i+2}}} = {weights[i+1]:.6f}"
            )

    def test_compute_orbit_weights_sorted(self):
        """compute_orbit_weights should return sorted by orbit period."""
        primes = [2, 3, 5]
        table = tsa.compute_orbit_weights(primes, max_k=2)
        periods = [row[2] for row in table]
        assert periods == sorted(periods), "Orbit table should be sorted by period t = k log p"

    def test_verify_transversal_determinant_pilar2_all_pass(self):
        """Full Pilar 2 verification should pass for standard primes."""
        result = tsa.verify_transversal_determinant_pilar2(primes=[2, 3, 5, 7])
        assert result["pilar"] == 2
        assert result["all_checks_passed"] is True
        assert result["status"] == "VERIFIED"
        for r in result["results"]:
            assert r["product_formula_ok"], f"Product formula failed for p={r['p']}, k={r['k']}"
            assert r["det_ok"], f"Determinant wrong for p={r['p']}, k={r['k']}"
            assert r["weight_ok"], f"Weight wrong for p={r['p']}, k={r['k']}"


# ===========================================================================
# Pilar 3 — Convergence
# ===========================================================================

class TestPilar3Convergence:
    """Tests for Pilar 3: convergence and absence of residual terms."""

    def test_exact_kernel_is_delta(self):
        """ExactTraceKernel attributes confirm pure-translation (no residual) structure."""
        kernel = tsa.ExactTraceKernel(n_primes=10)
        # Verify conceptual flags
        conv = kernel.verify_convergence(T_max=5.0)
        assert conv["no_residual_terms"] is True

    def test_geometric_trace_nonnegative(self):
        """Geometric trace values should be non-negative (weights are positive)."""
        kernel = tsa.ExactTraceKernel(n_primes=15)
        t_grid = np.linspace(0.5, 8.0, 100)
        geo = kernel.geometric_trace(t_grid, sigma=0.1)
        assert np.all(geo >= 0.0), "Geometric trace should be non-negative (all weights > 0)"

    def test_geometric_trace_peaks_near_log_primes(self):
        """Geometric trace should peak near t = log p for small primes."""
        kernel = tsa.ExactTraceKernel(n_primes=20, max_k=1)
        t_dense = np.linspace(0.1, 4.0, 2000)
        geo = kernel.geometric_trace(t_dense, sigma=0.05)

        # Check for peak near log(2) ≈ 0.693
        log2 = np.log(2.0)
        idx_window = np.abs(t_dense - log2) < 0.2
        assert np.max(geo[idx_window]) > np.mean(geo), (
            "Expected a peak near t = log(2)"
        )

    def test_convergence_partial_sum_finite(self):
        """Partial sum of orbit weights should be finite."""
        kernel = tsa.ExactTraceKernel(n_primes=20)
        conv = kernel.verify_convergence(T_max=10.0)
        assert conv["converges"]
        assert np.isfinite(conv["partial_sum_final"])

    def test_smooth_term_constant(self):
        """Smooth Weyl term should be the constant 1/(2π)."""
        kernel = tsa.ExactTraceKernel(n_primes=10)
        t_grid = np.array([1.0, 2.0, 3.0])
        smooth = kernel.smooth_term(t_grid)
        expected = 1.0 / (2.0 * np.pi)
        assert np.allclose(smooth, expected, rtol=1e-12)

    def test_verify_convergence_pilar3_structure(self):
        """Full Pilar 3 verification should return the expected structure."""
        result = tsa.verify_convergence_pilar3(t_max=8.0, n_primes=20)
        assert result["pilar"] == 3
        assert result["kernel_exact"] is True
        assert result["no_diffraction"] is True
        assert result["no_residual_terms"] is True
        assert result["weights_all_positive"] is True
        assert result["status"] == "VERIFIED"


# ===========================================================================
# Combined V8 rigour
# ===========================================================================

class TestV8RigorCombined:
    """Tests for the combined V8 rigour verification."""

    def test_v8_rigour_all_verified(self):
        """verify_v8_rigour should report all three pillars as VERIFIED."""
        result = tsa.verify_v8_rigour(t=1.0, n_primes=15, n_characters=30)
        assert result.all_verified, f"Not all pillars verified:\n{result.summary()}"

    def test_v8_summary_string(self):
        """Summary string should mention all three pillars and overall status."""
        result = tsa.verify_v8_rigour(t=0.5, n_primes=10, n_characters=20)
        summary = result.summary()
        assert "Pilar 1" in summary
        assert "Pilar 2" in summary
        assert "Pilar 3" in summary
        assert "VERIFIED" in summary

    def test_v8_rigour_result_dataclass(self):
        """V8RigorResult should have pilar1, pilar2, pilar3 dicts."""
        result = tsa.verify_v8_rigour(t=1.0, n_primes=10, n_characters=20)
        assert isinstance(result.pilar1, dict)
        assert isinstance(result.pilar2, dict)
        assert isinstance(result.pilar3, dict)
        assert result.pilar1["pilar"] == 1
        assert result.pilar2["pilar"] == 2
        assert result.pilar3["pilar"] == 3


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
