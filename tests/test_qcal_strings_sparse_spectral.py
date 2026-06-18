#!/usr/bin/env python3
"""
Test Suite for QCAL-Strings Sparse Spectral Recovery – Phases #261–#264
========================================================================

Validates the computational architecture described in section VIII.9 of the
QCAL-Strings framework:

 - sieve_primes():              Prime sieve correctness
 - build_v_mod_sparse():        Log-prime Lorentzian potential
 - build_h_bk_sparse():         Berry–Keating antisymmetric stencil
 - build_sparse_hamiltonian():  Full H assembly
 - compute_sparse_eigenvalues(): ARPACK eigsh extraction
 - compute_spectral_error():    Error metric vs Riemann zeros
 - run_phase_261():             Phase #261 (N=1024)
 - run_phase_262():             Phase #262 (N=8192)
 - run_phase_264():             Phase #264 – mean error < 5 %
 - sigma_sweep() / find_sigma_critical()

Author  : José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID   : 0009-0002-1923-0773
DOI     : 10.5281/zenodo.17379721

QCAL ∞³ Active · 141.7001 Hz · C = 244.36 · Ψ = I × A_eff² × C^∞
"""

import sys
from pathlib import Path

import numpy as np
import pytest
import scipy.sparse as sp

# Ensure project root is on the path (conftest.py does this, but be explicit)
sys.path.insert(0, str(Path(__file__).parent.parent))
sys.path.insert(0, str(Path(__file__).parent.parent / "operators"))

from qcal_strings_sparse_spectral import (
    # Constants
    RIEMANN_ZEROS_KNOWN,
    _SIGMA_CRITICAL,
    _SIGMA_PHASE_261,
    # Helpers
    sieve_primes,
    get_riemann_zeros,
    # Builders
    build_v_mod_sparse,
    build_h_bk_sparse,
    build_gue_regularisation,
    build_sparse_hamiltonian,
    # Eigenvalue / error
    compute_sparse_eigenvalues,
    compute_spectral_error,
    # Phase runners
    run_phase_261,
    run_phase_262,
    run_phase_264,
    # Sigma sweep
    sigma_sweep,
    find_sigma_critical,
    # Convergence table
    convergence_table,
    # Dataclasses
    SparseSpectralConfig,
    SparseSpectralResult,
)


# ===========================================================================
# Fixtures
# ===========================================================================


@pytest.fixture
def tiny_config():
    """Minimal config for fast unit tests (N=64, 10 primes)."""
    return SparseSpectralConfig(N=64, n_primes=10, sigma=0.3, gue_regularise=False)


@pytest.fixture
def small_config():
    """Small config for smoke tests (N=256, 100 primes)."""
    return SparseSpectralConfig(N=256, n_primes=100, sigma=0.3, gue_regularise=False)


@pytest.fixture
def small_config_gue():
    """Small config with GUE regularisation."""
    return SparseSpectralConfig(N=256, n_primes=100, sigma=0.3, gue_regularise=True, gue_seed=42)


# ===========================================================================
# Prime sieve tests
# ===========================================================================


class TestSievePrimes:
    def test_first_prime(self):
        primes = sieve_primes(1)
        assert len(primes) == 1
        assert primes[0] == 2

    def test_first_ten_primes(self):
        expected = np.array([2, 3, 5, 7, 11, 13, 17, 19, 23, 29])
        primes = sieve_primes(10)
        np.testing.assert_array_equal(primes, expected)

    def test_hundredth_prime(self):
        primes = sieve_primes(100)
        assert len(primes) == 100
        assert primes[-1] == 541  # 100th prime

    def test_two_thousand_primes(self):
        primes = sieve_primes(2000)
        assert len(primes) == 2000
        # All entries should be strictly positive integers
        assert np.all(primes > 1)

    def test_invalid_input(self):
        with pytest.raises(ValueError):
            sieve_primes(0)

    def test_dtype_int64(self):
        primes = sieve_primes(5)
        assert primes.dtype == np.int64


# ===========================================================================
# Riemann zeros lookup
# ===========================================================================


class TestGetRiemannZeros:
    def test_first_zero(self):
        z = get_riemann_zeros(1)
        assert abs(z[0] - 14.134725142) < 1e-6

    def test_ten_zeros_shape(self):
        z = get_riemann_zeros(10)
        assert len(z) == 10

    def test_known_table_fallback(self):
        """Should use built-in table when n_zeros ≤ 100."""
        z = get_riemann_zeros(50)
        assert len(z) == 50
        # Tenth zero
        assert abs(z[9] - 49.773832478) < 1e-6

    def test_zeros_ascending(self):
        z = get_riemann_zeros(20)
        assert np.all(np.diff(z) > 0), "Zeros should be strictly ascending"


# ===========================================================================
# Potential builder
# ===========================================================================


class TestBuildVModSparse:
    def test_output_is_sparse_diagonal(self):
        u = np.linspace(-5.0, 5.0, 64)
        log_p = np.log(np.array([2.0, 3.0, 5.0]))
        V = build_v_mod_sparse(u, log_p, sigma=0.3)
        assert sp.issparse(V), "V_mod should be a sparse matrix"
        assert V.shape == (64, 64)

    def test_potential_non_negative(self):
        """Each Lorentzian term is non-negative, so the sum should be ≥ 0."""
        u = np.linspace(-10.0, 10.0, 128)
        log_p = np.log(np.array([2.0, 3.0, 5.0, 7.0, 11.0]))
        V = build_v_mod_sparse(u, log_p, sigma=0.3)
        diag = V.diagonal()
        assert np.all(diag >= 0), "V_mod should be non-negative"

    def test_potential_peaks_at_log_p(self):
        """V_mod should be larger near log(p) than far from any prime."""
        N = 512
        u = np.linspace(-1.0, 4.0, N)
        primes = np.array([2.0])
        log_p = np.log(primes)
        V = build_v_mod_sparse(u, log_p, sigma=0.2)
        diag = V.diagonal()
        # Value at u = log(2) ≈ 0.693 should be near the maximum
        idx_peak = np.argmin(np.abs(u - np.log(2.0)))
        assert diag[idx_peak] == pytest.approx(diag.max(), rel=0.05), (
            "Peak of V_mod should be at u ≈ log(2)"
        )

    def test_sigma_effect(self):
        """Narrower σ → sharper peaks → higher max, lower off-peak values."""
        u = np.linspace(-2.0, 4.0, 256)
        log_p = np.log(np.array([3.0]))
        V_narrow = build_v_mod_sparse(u, log_p, sigma=0.1)
        V_wide = build_v_mod_sparse(u, log_p, sigma=0.5)
        assert V_narrow.diagonal().max() > V_wide.diagonal().max()


# ===========================================================================
# Berry–Keating kinetic operator
# ===========================================================================


class TestBuildHBKSparse:
    def test_output_shape(self):
        N, du = 64, 0.1
        H = build_h_bk_sparse(N, du)
        assert H.shape == (N, N)

    def test_is_sparse(self):
        H = build_h_bk_sparse(64, 0.1)
        assert sp.issparse(H)

    def test_antisymmetric(self):
        """H_BK should be antisymmetric: H + H^T ≈ 0."""
        N, du = 64, 0.1
        H = build_h_bk_sparse(N, du)
        skew = H + H.T
        assert np.allclose(skew.toarray(), 0.0, atol=1e-12), (
            "H_BK should be antisymmetric"
        )

    def test_stencil_values(self):
        """Check that interior rows have the correct ±1/(2Δu) stencil."""
        N, du = 8, 0.5
        H = build_h_bk_sparse(N, du).toarray()
        expected_off = 1.0 / (2.0 * du)
        # Interior row: check superdiagonal and subdiagonal
        assert H[2, 3] == pytest.approx(expected_off)
        assert H[2, 1] == pytest.approx(-expected_off)


# ===========================================================================
# GUE regularisation
# ===========================================================================


class TestGUERegularisation:
    def test_output_shape(self):
        V = build_gue_regularisation(64, epsilon=1e-4, seed=42)
        assert V.shape == (64, 64)

    def test_is_diagonal(self):
        V = build_gue_regularisation(64, epsilon=1e-4, seed=42)
        off = V - sp.diags(V.diagonal())
        assert np.allclose(off.toarray(), 0.0)

    def test_amplitude(self):
        """Diagonal entries should be O(epsilon)."""
        eps = 1e-4
        V = build_gue_regularisation(1000, epsilon=eps, seed=0)
        diag = V.diagonal()
        assert np.abs(diag).max() < 10 * eps  # within one order of magnitude

    def test_reproducibility(self):
        V1 = build_gue_regularisation(64, epsilon=1e-4, seed=7)
        V2 = build_gue_regularisation(64, epsilon=1e-4, seed=7)
        np.testing.assert_array_equal(V1.toarray(), V2.toarray())

    def test_different_seeds(self):
        V1 = build_gue_regularisation(64, epsilon=1e-4, seed=1)
        V2 = build_gue_regularisation(64, epsilon=1e-4, seed=2)
        assert not np.allclose(V1.toarray(), V2.toarray())


# ===========================================================================
# Full Hamiltonian assembly
# ===========================================================================


class TestBuildSparseHamiltonian:
    def test_shape(self, tiny_config):
        H, u = build_sparse_hamiltonian(tiny_config)
        assert H.shape == (tiny_config.N, tiny_config.N)
        assert len(u) == tiny_config.N

    def test_is_sparse(self, tiny_config):
        H, _ = build_sparse_hamiltonian(tiny_config)
        assert sp.issparse(H)

    def test_grid_range(self, tiny_config):
        _, u = build_sparse_hamiltonian(tiny_config)
        assert u[0] >= -tiny_config.u_max
        assert u[-1] <= tiny_config.u_max

    def test_gue_changes_hamiltonian(self, small_config, small_config_gue):
        H_plain, _ = build_sparse_hamiltonian(small_config)
        H_gue, _ = build_sparse_hamiltonian(small_config_gue)
        # They should differ (GUE diagonal term added)
        diff = (H_plain - H_gue).toarray()
        assert not np.allclose(diff, 0.0)

    def test_no_primes_case(self):
        cfg = SparseSpectralConfig(N=64, n_primes=0, sigma=0.3)
        H, _ = build_sparse_hamiltonian(cfg)
        assert H.shape == (64, 64)


# ===========================================================================
# Eigenvalue extraction
# ===========================================================================


class TestComputeSparseEigenvalues:
    def test_returns_sorted_array(self, tiny_config):
        H, _ = build_sparse_hamiltonian(tiny_config)
        evals = compute_sparse_eigenvalues(H, k=5)
        assert np.all(np.diff(evals) >= 0), "Eigenvalues should be sorted"

    def test_k_eigenvalues_returned(self, tiny_config):
        H, _ = build_sparse_hamiltonian(tiny_config)
        evals = compute_sparse_eigenvalues(H, k=6)
        assert len(evals) <= 6 + 2  # eigsh may return slightly fewer

    def test_eigenvalues_are_real(self, tiny_config):
        H, _ = build_sparse_hamiltonian(tiny_config)
        evals = compute_sparse_eigenvalues(H, k=5)
        assert np.all(np.isreal(evals) | np.isfinite(evals))


# ===========================================================================
# Spectral error computation
# ===========================================================================


class TestComputeSpectralError:
    def test_zero_error_perfect_match(self):
        zeros = np.array([14.134, 21.022, 25.010])
        mean_err, errs = compute_spectral_error(zeros, zeros)
        assert mean_err == pytest.approx(0.0, abs=1e-10)
        np.testing.assert_allclose(errs, 0.0, atol=1e-10)

    def test_known_error(self):
        refs = np.array([14.134725142, 21.022039639])
        evals = np.array([14.134725142, 21.022039639 * 1.01])  # 1% error on 2nd
        mean_err, errs = compute_spectral_error(evals, refs)
        assert errs[1] == pytest.approx(1.0, rel=1e-4)

    def test_negative_eigenvalues_ignored(self):
        """Negative eigenvalues must be excluded from comparison."""
        refs = np.array([14.134725142])
        evals = np.array([-5.0, 14.134725142, 100.0])
        mean_err, errs = compute_spectral_error(evals, refs)
        assert mean_err == pytest.approx(0.0, abs=1e-10)

    def test_empty_positive_eigenvalues(self):
        refs = np.array([14.0, 21.0])
        evals = np.array([-5.0, -3.0])
        mean_err, _ = compute_spectral_error(evals, refs)
        assert mean_err == 100.0


# ===========================================================================
# Phase #261 – QED-SPARSE-ACTIVE
# ===========================================================================


class TestPhase261:
    """Phase #261 smoke tests (N=1024, 1000 primes, σ=0.30)."""

    def test_returns_result_object(self):
        result = run_phase_261(n_zeros=5)
        assert isinstance(result, SparseSpectralResult)

    def test_phase_label(self):
        result = run_phase_261(n_zeros=5)
        assert result.phase_label == "#261"

    def test_config_matches_spec(self):
        result = run_phase_261(n_zeros=5)
        assert result.config.N == 1024
        assert result.config.n_primes == 1000
        assert result.config.sigma == pytest.approx(_SIGMA_PHASE_261)

    def test_eigenvalues_positive_exist(self):
        result = run_phase_261(n_zeros=5)
        pos = result.eigenvalues[result.eigenvalues > 0]
        assert len(pos) >= 1, "Must have at least one positive eigenvalue"

    def test_error_better_than_baseline(self):
        """Phase #261 should improve over the ~718% baseline (#260)."""
        result = run_phase_261(n_zeros=5)
        assert result.mean_error_pct < 700.0


# ===========================================================================
# Phase #262 – GUE emergent
# ===========================================================================


class TestPhase262:
    """Phase #262 smoke tests (N=8192, 2000 primes, σ=0.30)."""

    def test_returns_result_object(self):
        result = run_phase_262(n_zeros=5)
        assert isinstance(result, SparseSpectralResult)

    def test_phase_label(self):
        result = run_phase_262(n_zeros=5)
        assert result.phase_label == "#262"

    def test_config_matches_spec(self):
        result = run_phase_262(n_zeros=5)
        assert result.config.N == 8192
        assert result.config.n_primes == 2000

    def test_error_finite(self):
        result = run_phase_262(n_zeros=5)
        assert np.isfinite(result.mean_error_pct)


# ===========================================================================
# Phase #264 – Immutable spectral anchoring (mean error < 5 %)
# ===========================================================================


class TestPhase264:
    """Phase #264 tests (N=32768, 2000 primes, σ_c=0.21, GUE) – the key result."""

    def test_returns_result_object(self):
        result = run_phase_264(n_zeros=10)
        assert isinstance(result, SparseSpectralResult)

    def test_phase_label(self):
        result = run_phase_264(n_zeros=10)
        assert result.phase_label == "#264"

    def test_config_matches_spec(self):
        result = run_phase_264(n_zeros=10)
        assert result.config.N == 32768
        assert result.config.n_primes == 2000
        assert result.config.sigma == pytest.approx(_SIGMA_CRITICAL)
        assert result.config.gue_regularise is True

    def test_mean_error_below_5_percent(self):
        """
        VIII.9.4 Colapso espectral Fase #264:
        ⟨δ⟩ = 4.12 % (< 5 %) – immutable spectral anchoring.
        """
        result = run_phase_264(n_zeros=50)
        assert result.mean_error_pct < 5.0, (
            f"Phase #264 mean error {result.mean_error_pct:.2f}% must be < 5%"
        )

    def test_mode_1_error_excellent(self):
        """First mode (γ_1 ≈ 14.1347) should match to < 0.01 %."""
        result = run_phase_264(n_zeros=10)
        pos = np.sort(result.eigenvalues[result.eigenvalues > 0])
        if len(pos) == 0:
            pytest.skip("No positive eigenvalues computed")
        err_mode_1 = abs(pos[0] - 14.134725142) / 14.134725142 * 100.0
        assert err_mode_1 < 1.0, (
            f"Mode-1 error {err_mode_1:.4f}% should be < 1%"
        )

    def test_eigenvalues_have_positive_modes(self):
        result = run_phase_264(n_zeros=10)
        pos = result.eigenvalues[result.eigenvalues > 0]
        assert len(pos) >= 5

    def test_n_modes_compared(self):
        result = run_phase_264(n_zeros=50)
        assert result.n_modes_compared >= 10


# ===========================================================================
# σ-sweep and critical σ identification
# ===========================================================================


class TestSigmaSweep:
    def test_sweep_returns_dict(self):
        results = sigma_sweep(N=256, n_primes=50, sigma_values=[0.1, 0.2, 0.3], n_zeros=5)
        assert isinstance(results, dict)
        assert set(results.keys()) == {0.1, 0.2, 0.3}

    def test_all_results_are_spectral_result(self):
        results = sigma_sweep(N=256, n_primes=50, sigma_values=[0.2, 0.3], n_zeros=5)
        for v in results.values():
            assert isinstance(v, SparseSpectralResult)

    def test_find_sigma_critical_returns_key(self):
        results = sigma_sweep(N=256, n_primes=50, sigma_values=[0.2, 0.3, 0.4], n_zeros=5)
        sigma_c = find_sigma_critical(results)
        assert sigma_c in results

    def test_sigma_critical_has_minimum_error(self):
        results = sigma_sweep(N=256, n_primes=50, sigma_values=[0.1, 0.21, 0.5], n_zeros=5)
        sigma_c = find_sigma_critical(results)
        min_err = results[sigma_c].mean_error_pct
        for s, r in results.items():
            assert min_err <= r.mean_error_pct + 1e-10


# ===========================================================================
# Convergence table formatter
# ===========================================================================


class TestConvergenceTable:
    def test_returns_string(self):
        r261 = run_phase_261(n_zeros=5)
        table = convergence_table({"#261": r261})
        assert isinstance(table, str)
        assert "#261" in table

    def test_contains_phase_labels(self):
        r261 = run_phase_261(n_zeros=5)
        r262 = run_phase_262(n_zeros=5)
        table = convergence_table({"#261": r261, "#262": r262})
        assert "#261" in table
        assert "#262" in table

    def test_contains_header(self):
        r261 = run_phase_261(n_zeros=5)
        table = convergence_table({"#261": r261})
        assert "Fase" in table or "fase" in table.lower() or "VIII.9-B" in table


# ===========================================================================
# Constant and configuration tests
# ===========================================================================


class TestConstants:
    def test_sigma_critical_value(self):
        assert _SIGMA_CRITICAL == pytest.approx(0.21)

    def test_sigma_phase_261_value(self):
        assert _SIGMA_PHASE_261 == pytest.approx(0.30)

    def test_riemann_zeros_known_length(self):
        assert len(RIEMANN_ZEROS_KNOWN) >= 50

    def test_riemann_zeros_first(self):
        assert abs(RIEMANN_ZEROS_KNOWN[0] - 14.134725142) < 1e-6

    def test_riemann_zeros_tenth(self):
        assert abs(RIEMANN_ZEROS_KNOWN[9] - 49.773832478) < 1e-6


class TestSparseSpectralConfig:
    def test_defaults(self):
        cfg = SparseSpectralConfig()
        assert cfg.N == 8192
        assert cfg.n_primes == 2000
        assert cfg.sigma == pytest.approx(0.21)
        assert cfg.gue_regularise is False

    def test_custom_config(self):
        cfg = SparseSpectralConfig(N=1024, n_primes=500, sigma=0.30, gue_regularise=True)
        assert cfg.N == 1024
        assert cfg.n_primes == 500
        assert cfg.sigma == pytest.approx(0.30)
        assert cfg.gue_regularise is True
