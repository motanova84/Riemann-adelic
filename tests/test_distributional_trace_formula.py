#!/usr/bin/env python3
"""
Tests for Distributional Trace Formula
=======================================

Validates:
  1. DistributionalTraceKernel — orbit amplitudes and integral pairing
  2. ReturnMapDeterminant — p^{k/2} Jacobian, local-global decomposition
  3. ExactTraceFormula — geometric + smooth terms, prime orbit weights
  4. SpectralIdentification — ξ(s) functional equation, zeros, Δ=ξ

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz
"""

import math
import sys
from pathlib import Path

import numpy as np
import pytest

repo_root = Path(__file__).parent.parent
sys.path.insert(0, str(repo_root / "operators"))

from distributional_trace_formula import (
    RIEMANN_ZEROS,
    DistributionalTraceKernel,
    ExactTraceFormula,
    ReturnMapDeterminant,
    SpectralIdentification,
    TraceFormulaResult,
    compute_distributional_trace_formula,
    _sieve_primes,
    F0_QCAL,
    C_QCAL,
    DOI,
    NormalTransverseSpace,
    ArchimedeanContribution,
)


# ---------------------------------------------------------------------------
# DistributionalTraceKernel
# ---------------------------------------------------------------------------

class TestDistributionalTraceKernel:
    """Tests for DistributionalTraceKernel."""

    def setup_method(self):
        self.kernel = DistributionalTraceKernel(
            n_primes=10, k_max=3, smoothing_sigma=0.2
        )

    def test_initialization_defaults(self):
        k = DistributionalTraceKernel()
        assert k.n_primes == 30
        assert k.k_max == 5
        assert k.smoothing_sigma == 0.2

    def test_initialization_custom(self):
        k = DistributionalTraceKernel(n_primes=5, k_max=2, smoothing_sigma=0.1)
        assert k.n_primes == 5
        assert k.k_max == 2
        assert k.smoothing_sigma == 0.1

    def test_invalid_n_primes(self):
        with pytest.raises(ValueError, match="n_primes"):
            DistributionalTraceKernel(n_primes=0)

    def test_invalid_k_max(self):
        with pytest.raises(ValueError, match="k_max"):
            DistributionalTraceKernel(k_max=0)

    def test_invalid_sigma(self):
        with pytest.raises(ValueError, match="smoothing_sigma"):
            DistributionalTraceKernel(smoothing_sigma=0.0)

    def test_orbit_table_size(self):
        k = DistributionalTraceKernel(n_primes=5, k_max=3)
        # 5 primes × 3 powers = 15 orbits
        assert len(k._orbits) == 15

    def test_orbit_amplitudes(self):
        """amplitude = log p / p^{k/2} for each orbit."""
        k = DistributionalTraceKernel(n_primes=5, k_max=2)
        for amplitude, length, ki, pi in k._orbits:
            p = float(pi)
            expected_amp = math.log(p) / (p ** (ki / 2.0))
            assert abs(amplitude - expected_amp) < 1e-10, (
                f"Amplitude mismatch for p={pi}, k={ki}"
            )

    def test_orbit_lengths(self):
        """orbit length = k * log p."""
        k = DistributionalTraceKernel(n_primes=5, k_max=3)
        for amplitude, length, ki, pi in k._orbits:
            p = float(pi)
            expected_length = ki * math.log(p)
            assert abs(length - expected_length) < 1e-10

    def test_evaluate_returns_correct_shape(self):
        t = np.linspace(0.5, 5.0, 100)
        K = self.kernel.evaluate(t)
        assert K.shape == (100,)

    def test_evaluate_nonnegative(self):
        """Distributional kernel is nonneg (sum of Gaussians)."""
        t = np.linspace(0.1, 10.0, 200)
        K = self.kernel.evaluate(t)
        assert np.all(K >= 0.0)

    def test_gaussian_delta_at_center(self):
        """Gaussian delta at t=t0 equals 1/(σ√(2π))."""
        sigma = 0.3
        k = DistributionalTraceKernel(smoothing_sigma=sigma)
        val = k._gaussian_delta(np.array([0.0]), 0.0, sigma)[0]
        expected = 1.0 / (sigma * math.sqrt(2.0 * math.pi))
        assert abs(val - expected) < 1e-10

    def test_gaussian_delta_integrates_to_one(self):
        """Gaussian delta integrates to ≈ 1."""
        sigma = 0.3
        k = DistributionalTraceKernel(smoothing_sigma=sigma)
        t = np.linspace(-5 * sigma, 5 * sigma, 1000)
        dt = float(t[1] - t[0])
        vals = k._gaussian_delta(t, 0.0, sigma)
        integral = float(np.sum(vals) * dt)
        assert abs(integral - 1.0) < 1e-3

    def test_evaluate_peak_near_log_p(self):
        """G(t) has a peak near t = log p for the smallest prime p=2.

        We use a very narrow sigma to isolate the p=2 orbit peak.
        """
        kernel = DistributionalTraceKernel(n_primes=3, k_max=2, smoothing_sigma=0.05)
        t = np.linspace(0.5, 0.85, 500)
        K = kernel.evaluate(t)
        t_peak_idx = np.argmax(K)
        t_peak = float(t[t_peak_idx])
        expected = math.log(2.0)
        assert abs(t_peak - expected) < 0.05

    def test_integrate_against(self):
        """Distributional pairing is a scalar."""
        t = np.linspace(0.1, 5.0, 200)
        f = np.exp(-t)
        result = self.kernel.integrate_against(f, t)
        assert isinstance(result, float)
        assert np.isfinite(result)

    def test_integrate_against_positive(self):
        """Pairing with positive f gives positive result."""
        t = np.linspace(0.1, 5.0, 200)
        f = np.ones_like(t)
        result = self.kernel.integrate_against(f, t)
        assert result > 0.0


# ---------------------------------------------------------------------------
# ReturnMapDeterminant
# ---------------------------------------------------------------------------

class TestReturnMapDeterminant:
    """Tests for ReturnMapDeterminant."""

    def setup_method(self):
        self.rmd = ReturnMapDeterminant(k_max=5)

    def test_archimedean_jacobian(self):
        """J_∞(p, k) = p^k."""
        assert abs(self.rmd.archimedean_jacobian(2.0, 1) - 2.0) < 1e-12
        assert abs(self.rmd.archimedean_jacobian(3.0, 2) - 9.0) < 1e-12
        assert abs(self.rmd.archimedean_jacobian(5.0, 3) - 125.0) < 1e-10

    def test_padic_contraction_factor(self):
        """c_p(p, k) = 1/p^k."""
        assert abs(self.rmd.padic_contraction_factor(2.0, 1) - 0.5) < 1e-12
        assert abs(self.rmd.padic_contraction_factor(3.0, 2) - 1.0 / 9.0) < 1e-12

    def test_idele_norm_preserved(self):
        """J_∞(p,k) × c_p(p,k) = 1 (adele norm constraint)."""
        for p in [2.0, 3.0, 5.0, 7.0, 11.0]:
            for k in range(1, 5):
                product = (
                    self.rmd.archimedean_jacobian(p, k)
                    * self.rmd.padic_contraction_factor(p, k)
                )
                assert abs(product - 1.0) < 1e-10, (
                    f"Norm not preserved for p={p}, k={k}: product={product}"
                )

    def test_transversal_determinant(self):
        """det_transv(p, k) = p^{k/2}."""
        assert abs(self.rmd.transversal_determinant(2.0, 1) - math.sqrt(2)) < 1e-12
        assert abs(self.rmd.transversal_determinant(4.0, 2) - 4.0) < 1e-12
        assert abs(self.rmd.transversal_determinant(3.0, 2) - 3.0) < 1e-12

    def test_transversal_is_geometric_mean(self):
        """det_transv(p,k) = sqrt(J_∞(p,k)) since c_p(p,k) = 1/J_∞(p,k)."""
        for p in [2.0, 3.0, 5.0]:
            for k in range(1, 4):
                j_inf = self.rmd.archimedean_jacobian(p, k)
                trans = self.rmd.transversal_determinant(p, k)
                assert abs(trans - j_inf ** 0.5) < 1e-10

    def test_orbit_weight_formula(self):
        """W(p, k) = log p / p^{k/2}."""
        for p in [2.0, 3.0, 5.0]:
            for k in range(1, 4):
                w = self.rmd.orbit_weight(p, k)
                expected = math.log(p) / (p ** (k / 2.0))
                assert abs(w - expected) < 1e-10

    def test_orbit_weight_positive(self):
        """Orbit weights must be strictly positive."""
        for p, k, w in self.rmd.weight_table():
            assert w > 0.0

    def test_orbit_weight_decreasing_in_k(self):
        """W(p, k) decreases with k for fixed p (since p^{k/2} grows)."""
        for p in [2.0, 3.0, 5.0]:
            weights = [self.rmd.orbit_weight(p, k) for k in range(1, 5)]
            diffs = np.diff(weights)
            assert np.all(diffs < 0), f"Weights not decreasing for p={p}"

    def test_verify_local_global_decomposition(self):
        """Verification helper returns True for both checks."""
        result = self.rmd.verify_local_global_decomposition()
        assert result["norm_preserved"] is True
        assert result["transversal_correct"] is True

    def test_weight_table_size(self):
        rmd = ReturnMapDeterminant(k_max=3)
        n_primes = len(rmd.primes)
        table = rmd.weight_table()
        assert len(table) == n_primes * 3


# ---------------------------------------------------------------------------
# ExactTraceFormula
# ---------------------------------------------------------------------------

class TestExactTraceFormula:
    """Tests for ExactTraceFormula."""

    def setup_method(self):
        self.formula = ExactTraceFormula(
            n_primes=10, k_max=3, smoothing_sigma=0.2,
            E_cutoff=30.0, n_energy=500,
        )

    def test_geometric_term_shape(self):
        t = np.linspace(0.5, 5.0, 100)
        G = self.formula.geometric_term(t)
        assert G.shape == (100,)

    def test_geometric_term_nonneg(self):
        t = np.linspace(0.1, 10.0, 200)
        G = self.formula.geometric_term(t)
        assert np.all(G >= 0.0)

    def test_smooth_term_shape(self):
        t = np.linspace(0.5, 5.0, 50)
        S = self.formula.smooth_term(t)
        assert S.shape == (50,)

    def test_smooth_term_finite(self):
        t = np.linspace(0.5, 5.0, 50)
        S = self.formula.smooth_term(t)
        assert np.all(np.isfinite(S))

    def test_compute_returns_result(self):
        t = np.linspace(0.5, 5.0, 30)
        result = self.formula.compute(t)
        assert isinstance(result, TraceFormulaResult)
        assert result.status == "EXACTA"

    def test_compute_shapes(self):
        t = np.linspace(0.5, 5.0, 50)
        result = self.formula.compute(t)
        assert result.geometric_term.shape == (50,)
        assert result.smooth_term.shape == (50,)
        assert result.total_trace.shape == (50,)

    def test_compute_total_is_sum(self):
        t = np.linspace(0.5, 5.0, 30)
        result = self.formula.compute(t)
        diff = np.abs(result.total_trace - result.geometric_term - result.smooth_term)
        assert np.max(diff) < 1e-10

    def test_geometric_peak_at_log_2(self):
        """G(t) has a local peak near t = log 2.

        Use small sigma to isolate the p=2,k=1 orbit contribution.
        """
        formula = ExactTraceFormula(n_primes=3, k_max=2, smoothing_sigma=0.05)
        t = np.linspace(0.5, 0.85, 500)
        G = formula.geometric_term(t)
        t_peak = float(t[np.argmax(G)])
        assert abs(t_peak - math.log(2.0)) < 0.05

    def test_geometric_peak_at_log_3(self):
        """G(t) has a visible peak near t = log 3."""
        formula = ExactTraceFormula(n_primes=5, k_max=2, smoothing_sigma=0.1)
        t = np.linspace(0.9, 1.3, 500)
        G = formula.geometric_term(t)
        t_peak = float(t[np.argmax(G)])
        assert abs(t_peak - math.log(3.0)) < 0.05

    def test_verify_prime_orbit_weights(self):
        """Orbit weight verification passes."""
        assert self.formula.verify_prime_orbit_weights() is True

    def test_parameters_stored(self):
        t = np.linspace(0.5, 3.0, 10)
        result = self.formula.compute(t)
        assert "n_primes" in result.parameters
        assert "k_max" in result.parameters
        assert result.parameters["doi"] == DOI

    def test_convenience_function(self):
        result = compute_distributional_trace_formula(
            t_min=0.5, t_max=5.0, n_t=30, n_primes=5, k_max=2
        )
        assert isinstance(result, TraceFormulaResult)
        assert result.status == "EXACTA"


# ---------------------------------------------------------------------------
# SpectralIdentification
# ---------------------------------------------------------------------------

class TestSpectralIdentification:
    """Tests for SpectralIdentification."""

    def setup_method(self):
        self.si = SpectralIdentification(n_primes=20, k_max=3)

    def test_xi_at_half_plus_i_gamma(self):
        """ξ(1/2 + iγ) ≈ 0 for known Riemann zeros γ."""
        for gamma in RIEMANN_ZEROS[:3]:
            s = complex(0.5, float(gamma))
            xi_val = self.si.xi_function(s)
            assert abs(xi_val) < 1e-3, (
                f"|ξ(1/2 + i{gamma:.4f})| = {abs(xi_val):.2e}, expected ≈ 0"
            )

    def test_xi_functional_equation(self):
        """ξ(s) = ξ(1 − s)."""
        for sigma in [0.3, 0.5, 0.7, 1.5]:
            s = complex(sigma, 5.0)
            xi_s = self.si.xi_function(s)
            xi_1ms = self.si.xi_function(1 - s)
            assert abs(xi_s - xi_1ms) / (abs(xi_s) + 1e-30) < 1e-6

    def test_verify_xi_functional_equation_passes(self):
        result = self.si.verify_xi_functional_equation()
        assert result["passes"] is True
        assert result["max_error"] < 1e-6

    def test_verify_zeros_on_critical_line_passes(self):
        result = self.si.verify_zeros_on_critical_line()
        assert result["passes"] is True
        assert result["max_residual"] < 1e-4

    def test_verify_delta_equals_xi_passes(self):
        result = self.si.verify_delta_equals_xi()
        assert result["passes"] is True
        assert result["max_error"] < 1e-10

    def test_euler_product_converges_for_large_re_s(self):
        """Euler product ∏_p (1 − p^{−s})^{−1} converges for Re(s) > 1."""
        for sigma in [1.5, 2.0, 3.0]:
            s = complex(sigma, 0.0)
            Z = self.si.euler_product_truncated(s, n_primes=20)
            assert np.isfinite(abs(Z))
            assert abs(Z) > 0.0

    def test_gamma_factor_positive_real(self):
        """Γ_∞(s) = π^{−σ/2} Γ(σ/2) is real and positive for real s > 0."""
        for sigma in [0.5, 1.0, 1.5, 2.0]:
            gf = self.si.gamma_factor(complex(sigma, 0.0))
            # For real s the imaginary part should be negligible
            assert abs(gf.imag) < 1e-10, f"Imaginary part non-zero for real s={sigma}"
            assert gf.real > 0.0, f"Gamma factor not positive for s={sigma}"

    def test_spectral_determinant_equals_xi(self):
        """Δ(s) = ξ(s) by definition."""
        for s in [complex(0.5, 5.0), complex(2.0, 0.0)]:
            delta = self.si.spectral_determinant(s)
            xi = self.si.xi_function(s)
            assert abs(delta - xi) < 1e-12

    def test_xi_real_on_critical_line(self):
        """ξ(1/2 + it) is real-valued on the critical line.

        This follows from the functional equation symmetry ξ(s) = ξ(1 - s̄),
        which implies ξ(1/2 + it) = ξ̄(1/2 + it), so the value is real.
        """
        for gamma in [1.0, 5.0, 10.0, 14.0]:
            s = complex(0.5, gamma)
            xi_val = self.si.xi_function(s)
            # |Im(ξ)| / |ξ| should be tiny
            if abs(xi_val) > 1e-20:
                rel_imag = abs(xi_val.imag) / abs(xi_val)
                assert rel_imag < 1e-8, (
                    f"ξ(1/2 + i{gamma}) is not real: Im/|ξ| = {rel_imag:.2e}"
                )


# ---------------------------------------------------------------------------
# Helper: _sieve_primes
# ---------------------------------------------------------------------------

class TestSievePrimes:
    """Tests for the prime sieve helper."""

    def test_first_prime(self):
        assert _sieve_primes(1)[0] == 2.0

    def test_first_five_primes(self):
        primes = _sieve_primes(5)
        expected = np.array([2.0, 3.0, 5.0, 7.0, 11.0])
        np.testing.assert_array_equal(primes, expected)

    def test_length(self):
        for n in [1, 5, 10, 20]:
            assert len(_sieve_primes(n)) == n


# ---------------------------------------------------------------------------
# QCAL Constants
# ---------------------------------------------------------------------------

def test_qcal_constants():
    """Verify QCAL ∞³ constants are present and correct."""
    assert abs(F0_QCAL - 141.7001) < 0.001
    assert abs(C_QCAL - 244.36) < 0.01
    assert DOI == "10.5281/zenodo.17379721"


# ---------------------------------------------------------------------------
# Integration: formula consistent with Selberg / Weil structure
# ---------------------------------------------------------------------------

class TestTraceFormulaIntegration:
    """Integration tests checking overall structure of the trace formula."""

    def test_geometric_term_decreases_with_p(self):
        """Weights W(p,1) = log p / sqrt(p) have max near p ≈ e² ≈ 7.39.

        For large primes (p >> e²) the weights should decrease.
        """
        # W(p,1) = log(p)/sqrt(p) is maximised near p=e²≈7.39
        # So W(2,1) < W(7,1) < W(11,1) is NOT guaranteed; instead verify
        # that W decreases for large primes as expected.
        primes_large = [11.0, 13.0, 17.0, 19.0, 23.0]
        weights = [math.log(p) / math.sqrt(p) for p in primes_large]
        diffs = np.diff(weights)
        assert np.all(diffs < 0), (
            "W(p,1) should decrease for p > e² ≈ 7.39"
        )

    def test_riemann_zeros_are_known(self):
        """Check the hard-coded Riemann zeros against known values."""
        assert len(RIEMANN_ZEROS) == 30
        assert abs(RIEMANN_ZEROS[0] - 14.134725) < 1e-4
        assert abs(RIEMANN_ZEROS[1] - 21.022040) < 1e-4

    def test_trace_result_parameters_complete(self):
        formula = ExactTraceFormula(n_primes=5, k_max=2)
        t = np.linspace(0.5, 3.0, 10)
        result = formula.compute(t)
        for key in ("n_primes", "k_max", "smoothing_sigma", "doi",
                    "f0_qcal", "c_coherence"):
            assert key in result.parameters

    def test_distributional_kernel_integral_against_constant(self):
        """Integral of K(t) against 1 over [0, T] equals total weight."""
        kernel = DistributionalTraceKernel(n_primes=5, k_max=2, smoothing_sigma=0.1)
        total_weight = sum(amplitude for amplitude, _, _, _ in kernel._orbits)
        T = max(length for _, length, _, _ in kernel._orbits) + 1.0
        t = np.linspace(0.0, T, 2000)
        dt = float(t[1] - t[0])
        K = kernel.evaluate(t)
        integral = float(np.sum(K) * dt)
        # Integral of Σ_pk amp * Gaussian ≈ Σ_pk amp (each Gaussian ≈1 if window wide)
        assert abs(integral - total_weight) / (total_weight + 1e-30) < 0.05


# ---------------------------------------------------------------------------
# NormalTransverseSpace
# ---------------------------------------------------------------------------

class TestNormalTransverseSpace:
    """Tests for NormalTransverseSpace."""

    def setup_method(self):
        self.nts = NormalTransverseSpace(k_max=3)

    def test_initialization_defaults(self):
        nts = NormalTransverseSpace()
        assert len(nts.primes) == 10
        assert nts.k_max == 5

    def test_initialization_custom(self):
        nts = NormalTransverseSpace(k_max=2)
        assert nts.k_max == 2

    def test_check_norm_constraint_satisfied(self):
        """A vector summing to 0 passes the norm constraint."""
        log_abs = np.array([math.log(2.0), -math.log(2.0), 0.0, 0.0])
        assert self.nts.check_norm_constraint(log_abs) is True

    def test_check_norm_constraint_violated(self):
        """A vector not summing to 0 fails the constraint."""
        log_abs = np.array([1.0, 0.5, 0.0])
        assert self.nts.check_norm_constraint(log_abs) is False

    def test_check_norm_constraint_zero_vector(self):
        """The zero vector satisfies the constraint trivially."""
        assert self.nts.check_norm_constraint(np.zeros(5)) is True

    def test_build_constrained_sample_norm(self):
        """build_constrained_sample produces a vector summing to 0."""
        for p in [2.0, 3.0, 5.0]:
            for k in [1, 2, 3]:
                sample = self.nts.build_constrained_sample(p, k)
                assert self.nts.check_norm_constraint(sample), (
                    f"Norm constraint violated for p={p}, k={k}"
                )

    def test_build_constrained_sample_real_place(self):
        """Real-place entry equals k log p."""
        p, k = 3.0, 2
        sample = self.nts.build_constrained_sample(p, k)
        assert abs(sample[0] - k * math.log(p)) < 1e-12

    def test_build_constrained_sample_padic_compensation(self):
        """p-adic entry equals −k log p."""
        # Use p=2 which is the first prime; its index is 0 in self.primes
        nts = NormalTransverseSpace(primes=_sieve_primes(5), k_max=2)
        sample = nts.build_constrained_sample(2.0, 1)
        # Real place: log 2; p-adic (index 1 in sample) : -log 2
        assert abs(sample[0] - math.log(2.0)) < 1e-12
        assert abs(sample[1] + math.log(2.0)) < 1e-12

    def test_build_constrained_sample_raises_for_unknown_prime(self):
        """ValueError raised when p is not in self.primes."""
        nts = NormalTransverseSpace(primes=_sieve_primes(3), k_max=2)  # primes: 2,3,5
        with pytest.raises(ValueError, match="not in self.primes"):
            nts.build_constrained_sample(7.0, 1)  # 7 is not in [2,3,5]

    def test_verify_norm_constraint_for_orbits(self):
        """Norm constraint holds for all configured (p, k) orbits."""
        assert self.nts.verify_norm_constraint_for_orbits() is True

    def test_transversal_dimension(self):
        """Transversal dimension = n_primes − 1."""
        for n in [5, 10, 20]:
            nts = NormalTransverseSpace(primes=_sieve_primes(n))
            assert nts.transversal_dimension() == n - 1

    def test_summary_keys(self):
        """summary() returns all expected keys."""
        s = self.nts.summary()
        for key in ("definition", "compact", "norm_constraint_ok",
                    "transversal_dimension", "n_primes"):
            assert key in s

    def test_summary_compact(self):
        """Σ is compact — always True."""
        assert self.nts.summary()["compact"] is True

    def test_summary_norm_constraint_ok(self):
        assert self.nts.summary()["norm_constraint_ok"] is True

    def test_summary_definition_contains_kernel(self):
        """Definition string references the norm kernel."""
        defn = self.nts.summary()["definition"]
        assert "log" in defn and "0" in defn


# ---------------------------------------------------------------------------
# ArchimedeanContribution (Block C)
# ---------------------------------------------------------------------------

class TestArchimedeanContribution:
    """Tests for ArchimedeanContribution."""

    def setup_method(self):
        self.arch = ArchimedeanContribution(precision=25)

    def test_initialization(self):
        arch = ArchimedeanContribution(precision=30)
        assert arch.precision == 30

    def test_mellin_gamma_factor_positive_real_axis(self):
        """W_∞(σ) = π^{−σ/2} Γ(σ/2) is real and positive for real σ > 0."""
        for sigma in [0.5, 1.0, 1.5, 2.0, 3.0]:
            gf = self.arch.mellin_gamma_factor(complex(sigma, 0.0))
            assert abs(gf.imag) < 1e-10, f"Im(W_∞({sigma})) ≠ 0"
            assert gf.real > 0.0, f"W_∞({sigma}) ≤ 0"

    def test_mellin_gamma_factor_known_value(self):
        """W_∞(2) = π^{−1} Γ(1) = 1/π."""
        gf = self.arch.mellin_gamma_factor(complex(2.0, 0.0))
        expected = 1.0 / math.pi
        assert abs(gf.real - expected) < 1e-10

    def test_mellin_gamma_factor_finite_on_critical_line(self):
        """W_∞(1/2 + it) is finite and nonzero on the critical line."""
        for t in [1.0, 5.0, 14.0, 21.0]:
            gf = self.arch.mellin_gamma_factor(complex(0.5, t))
            assert np.isfinite(abs(gf))
            assert abs(gf) > 0.0

    def test_nodo_zero_factor_at_critical_line(self):
        """½ s(s−1) at s = 1/2 + it is complex for t ≠ 0."""
        s = complex(0.5, 14.0)
        z0 = self.arch.nodo_zero_factor(s)
        expected = 0.5 * s * (s - 1.0)
        assert abs(z0 - expected) < 1e-12

    def test_nodo_zero_factor_at_s_half_real(self):
        """½ × (1/2) × (−1/2) = −1/8."""
        z0 = self.arch.nodo_zero_factor(complex(0.5, 0.0))
        assert abs(z0.real - (-1.0 / 8.0)) < 1e-12
        assert abs(z0.imag) < 1e-12

    def test_nodo_zero_factor_at_s_0_and_1(self):
        """½ s(s−1) vanishes at s = 0 and s = 1."""
        assert abs(self.arch.nodo_zero_factor(complex(0.0, 0.0))) < 1e-12
        assert abs(self.arch.nodo_zero_factor(complex(1.0, 0.0))) < 1e-12

    def test_full_archimedean_factor_equals_product(self):
        """Δ_∞(s) = nodo_zero × mellin_gamma."""
        for s in [complex(0.5, 5.0), complex(2.0, 0.0), complex(0.3, 10.0)]:
            delta = self.arch.full_archimedean_factor(s)
            expected = (
                self.arch.nodo_zero_factor(s)
                * self.arch.mellin_gamma_factor(s)
            )
            assert abs(delta - expected) < 1e-10

    def test_verify_gamma_factor_real_on_critical_line(self):
        """W_∞ is finite and positive on the critical line."""
        assert self.arch.verify_gamma_factor_real_on_critical_line() is True

    def test_verify_functional_equation_symmetry(self):
        """Δ_∞ functional symmetry check passes."""
        assert self.arch.verify_functional_equation_symmetry() is True

    def test_summary_keys(self):
        """summary() returns all expected keys."""
        s = self.arch.summary()
        for key in ("gamma_factor_ok", "functional_symmetry_ok",
                    "nodo_zero_at_s_half", "delta_inf_at_s_2"):
            assert key in s

    def test_summary_checks_pass(self):
        s = self.arch.summary()
        assert s["gamma_factor_ok"] is True
        assert s["functional_symmetry_ok"] is True

    def test_mellin_gamma_factor_consistency_with_spectral_id(self):
        """W_∞(s) agrees with SpectralIdentification.gamma_factor(s)."""
        si = SpectralIdentification(n_primes=5, k_max=2)
        for s in [complex(0.5, 0.0), complex(1.0, 0.0), complex(2.0, 0.0)]:
            w_inf = self.arch.mellin_gamma_factor(s)
            gf_si = si.gamma_factor(s)
            assert abs(w_inf - gf_si) < 1e-8, (
                f"W_∞({s}) = {w_inf}, gamma_factor({s}) = {gf_si}"
            )
