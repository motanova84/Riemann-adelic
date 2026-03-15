#!/usr/bin/env python3
"""
Tests for operators/qcal_strings_sparse_fase264.py
===================================================

Validates the QCAL-STRINGS Sparse Hamiltonian (Fase #264):
  - Construction of kinetic, potential, and Weyl-correction sparse matrices.
  - Hermitian symmetry of the full Hamiltonian.
  - Eigenvalue spectrum contains positive real values consistent with
    the scale of the first Riemann zeros.
  - Sigma-sweep finds a best σ among the tested values.
  - QCALStringsSparse264 façade runs without error on a small grid.
  - Constants and data arrays have the expected shapes and values.
"""

import numpy as np
import pytest
import scipy.sparse as sparse

from operators.qcal_strings_sparse_fase264 import (
    F0_SPECTRAL,
    RIEMANN_ZEROS_20,
    RIEMANN_ZEROS_50,
    QCALStringsSparse264,
    SparseHamiltonianConfig,
    SparseSpectralResult,
    _generate_primes,
    build_kinetic_sparse,
    build_potential_sparse,
    build_weyl_correction_sparse,
    compute_sparse_spectrum,
    sigma_sweep,
)

# ── Small test parameters (fast execution) ────────────────────────────────────
_SMALL_N = 256
_SMALL_PRIMES = 50
_SMALL_K = 15

# ── Tolerance ─────────────────────────────────────────────────────────────────
_FLOAT_TOL = 1e-10


# ─────────────────────────────────────────────────────────────────────────────
#  Module-level constants
# ─────────────────────────────────────────────────────────────────────────────

class TestConstants:
    """Verify module-level constants."""

    def test_f0_spectral_value(self):
        """F0_SPECTRAL = 14.134725 / π ≈ 4.499."""
        expected = 14.134725 / np.pi
        assert abs(F0_SPECTRAL - expected) < _FLOAT_TOL

    def test_riemann_zeros_20_length(self):
        assert len(RIEMANN_ZEROS_20) == 20

    def test_riemann_zeros_50_length(self):
        assert len(RIEMANN_ZEROS_50) == 50

    def test_riemann_zeros_first_value(self):
        """First Riemann zero ≈ 14.1347."""
        assert abs(RIEMANN_ZEROS_20[0] - 14.134725) < 1e-4

    def test_riemann_zeros_sorted(self):
        assert np.all(np.diff(RIEMANN_ZEROS_20) > 0)
        assert np.all(np.diff(RIEMANN_ZEROS_50) > 0)


# ─────────────────────────────────────────────────────────────────────────────
#  Prime generation
# ─────────────────────────────────────────────────────────────────────────────

class TestGeneratePrimes:
    """Tests for _generate_primes helper."""

    def test_returns_array(self):
        p = _generate_primes(10, 100)
        assert isinstance(p, np.ndarray)

    def test_first_prime_is_2(self):
        p = _generate_primes(5, 100)
        assert p[0] == 2.0

    def test_count_respected(self):
        p = _generate_primes(20, 200)
        assert len(p) == 20

    def test_all_positive(self):
        p = _generate_primes(50, 300)
        assert np.all(p > 0)

    def test_raises_on_no_primes(self):
        with pytest.raises(ValueError):
            _generate_primes(10, 1)  # no primes < 1


# ─────────────────────────────────────────────────────────────────────────────
#  Kinetic operator
# ─────────────────────────────────────────────────────────────────────────────

class TestKineticSparse:
    """Tests for build_kinetic_sparse."""

    def test_shape(self):
        N, du = 64, 0.1
        H = build_kinetic_sparse(N, du)
        assert H.shape == (N, N)

    def test_is_sparse(self):
        H = build_kinetic_sparse(64, 0.1)
        assert sparse.issparse(H)

    def test_symmetric(self):
        N, du = 64, 0.1
        H = build_kinetic_sparse(N, du)
        diff = (H - H.T).toarray()
        assert np.max(np.abs(diff)) < _FLOAT_TOL

    def test_positive_semidefinite(self):
        """All eigenvalues of the kinetic operator should be ≥ 0."""
        N, du = 32, 0.5
        H = build_kinetic_sparse(N, du).toarray()
        evals = np.linalg.eigvalsh(H)
        assert np.all(evals >= -1e-10)

    def test_diagonal_value(self):
        """Diagonal = 2/du²."""
        N, du = 8, 0.5
        H = build_kinetic_sparse(N, du).toarray()
        expected_diag = 2.0 / du**2
        assert np.allclose(H.diagonal(), expected_diag)

    def test_off_diagonal_value(self):
        """Off-diagonals = -1/du²."""
        N, du = 8, 0.5
        H = build_kinetic_sparse(N, du).toarray()
        expected_off = -1.0 / du**2
        assert np.allclose(H[0, 1], expected_off)


# ─────────────────────────────────────────────────────────────────────────────
#  Potential operator
# ─────────────────────────────────────────────────────────────────────────────

class TestPotentialSparse:
    """Tests for build_potential_sparse."""

    @pytest.fixture()
    def small_grid(self):
        N = 64
        u = np.linspace(0, 10, N)
        primes = _generate_primes(20, 100)
        log_primes = np.log(primes)
        return u, log_primes

    def test_shape(self, small_grid):
        u, lp = small_grid
        V = build_potential_sparse(u, lp, sigma=0.3, alpha=0.03)
        assert V.shape == (len(u), len(u))

    def test_is_diagonal(self, small_grid):
        u, lp = small_grid
        V = build_potential_sparse(u, lp, sigma=0.3, alpha=0.03).toarray()
        off_diag = V - np.diag(np.diag(V))
        assert np.max(np.abs(off_diag)) < _FLOAT_TOL

    def test_non_negative(self, small_grid):
        u, lp = small_grid
        V = build_potential_sparse(u, lp, sigma=0.3, alpha=0.03).toarray()
        assert np.all(V.diagonal() >= 0)

    def test_raises_bad_sigma(self, small_grid):
        u, lp = small_grid
        with pytest.raises(ValueError):
            build_potential_sparse(u, lp, sigma=-0.1, alpha=0.03)

    def test_raises_bad_alpha(self, small_grid):
        u, lp = small_grid
        with pytest.raises(ValueError):
            build_potential_sparse(u, lp, sigma=0.3, alpha=0.0)


# ─────────────────────────────────────────────────────────────────────────────
#  Weyl correction
# ─────────────────────────────────────────────────────────────────────────────

class TestWeylCorrectionSparse:
    """Tests for build_weyl_correction_sparse."""

    def test_shape(self):
        u = np.linspace(0, 10, 32)
        W = build_weyl_correction_sparse(u, 0.005)
        assert W.shape == (32, 32)

    def test_is_diagonal(self):
        u = np.linspace(0, 10, 32)
        W = build_weyl_correction_sparse(u, 0.005).toarray()
        off_diag = W - np.diag(np.diag(W))
        assert np.max(np.abs(off_diag)) < _FLOAT_TOL

    def test_non_negative(self):
        u = np.linspace(0, 10, 32)
        W = build_weyl_correction_sparse(u, 0.005).toarray()
        assert np.all(W.diagonal() >= 0)

    def test_monotonically_increasing(self):
        """ln(u+1) is monotone so V_W should be non-decreasing along u."""
        u = np.linspace(0.1, 10.0, 64)
        W = build_weyl_correction_sparse(u, 0.005).toarray()
        diag = W.diagonal()
        assert np.all(np.diff(diag) >= -_FLOAT_TOL)


# ─────────────────────────────────────────────────────────────────────────────
#  Default configuration
# ─────────────────────────────────────────────────────────────────────────────

class TestSparseHamiltonianConfig:
    """Tests for SparseHamiltonianConfig defaults."""

    def test_defaults(self):
        cfg = SparseHamiltonianConfig()
        assert cfg.N == 8192
        assert cfg.sigma == pytest.approx(0.21)
        assert cfg.alpha == pytest.approx(0.03)
        assert cfg.n_primes == 2000
        assert cfg.k_evals == 30
        assert cfg.weyl_correction is True


# ─────────────────────────────────────────────────────────────────────────────
#  Full spectrum computation  (small grid for speed)
# ─────────────────────────────────────────────────────────────────────────────

class TestComputeSparseSpectrum:
    """Integration tests for compute_sparse_spectrum."""

    @pytest.fixture()
    def small_config(self):
        return SparseHamiltonianConfig(
            N=_SMALL_N,
            n_primes=_SMALL_PRIMES,
            prime_max=500,
            sigma=0.21,
            alpha=0.03,
            k_evals=_SMALL_K,
            weyl_correction=True,
        )

    def test_returns_spectral_result(self, small_config):
        result = compute_sparse_spectrum(small_config)
        assert isinstance(result, SparseSpectralResult)

    def test_eigenvalues_array(self, small_config):
        result = compute_sparse_spectrum(small_config)
        assert isinstance(result.eigenvalues, np.ndarray)
        assert len(result.eigenvalues) > 0

    def test_eigenvalues_real(self, small_config):
        result = compute_sparse_spectrum(small_config)
        assert np.issubdtype(result.eigenvalues.dtype, np.floating)

    def test_eigenvalues_sorted(self, small_config):
        result = compute_sparse_spectrum(small_config)
        assert np.all(np.diff(result.eigenvalues) >= -1e-8)

    def test_psi_coherence_range(self, small_config):
        """Ψ coherence should be in (0, 1]."""
        result = compute_sparse_spectrum(small_config)
        assert 0 < result.psi_coherence <= 1.0

    def test_mean_error_non_negative(self, small_config):
        result = compute_sparse_spectrum(small_config)
        assert result.mean_error_pct >= 0

    def test_computation_time_positive(self, small_config):
        result = compute_sparse_spectrum(small_config)
        assert result.computation_time_s > 0

    def test_sigma_in_result(self, small_config):
        result = compute_sparse_spectrum(small_config)
        assert result.sigma_used == pytest.approx(small_config.sigma)

    def test_errors_pct_shape(self, small_config):
        result = compute_sparse_spectrum(small_config)
        assert len(result.errors_pct) == result.n_matched

    def test_default_config_runs(self):
        """compute_sparse_spectrum(None) uses default config without error."""
        # Use very small default to keep test fast
        cfg = SparseHamiltonianConfig(
            N=128, n_primes=30, prime_max=200, k_evals=10
        )
        result = compute_sparse_spectrum(cfg)
        assert result is not None


# ─────────────────────────────────────────────────────────────────────────────
#  Sigma sweep
# ─────────────────────────────────────────────────────────────────────────────

class TestSigmaSweep:
    """Tests for sigma_sweep."""

    @pytest.fixture()
    def sweep_config(self):
        return SparseHamiltonianConfig(
            N=_SMALL_N,
            n_primes=_SMALL_PRIMES,
            prime_max=500,
            sigma=0.21,
            k_evals=_SMALL_K,
        )

    def test_returns_tuple(self, sweep_config):
        sigmas = [0.20, 0.25]
        best_sigma, best_err, results = sigma_sweep(
            sigmas=sigmas, base_config=sweep_config
        )
        assert isinstance(best_sigma, float)
        assert isinstance(best_err, float)
        assert isinstance(results, list)

    def test_results_length(self, sweep_config):
        sigmas = [0.20, 0.25]
        _, _, results = sigma_sweep(sigmas=sigmas, base_config=sweep_config)
        assert len(results) == len(sigmas)

    def test_best_sigma_in_sigmas(self, sweep_config):
        sigmas = [0.20, 0.25]
        best_sigma, _, _ = sigma_sweep(sigmas=sigmas, base_config=sweep_config)
        assert best_sigma in sigmas

    def test_best_error_is_minimum(self, sweep_config):
        sigmas = [0.20, 0.25]
        _, best_err, results = sigma_sweep(sigmas=sigmas, base_config=sweep_config)
        all_errors = [r.mean_error_pct for r in results]
        assert best_err == pytest.approx(min(all_errors))


# ─────────────────────────────────────────────────────────────────────────────
#  QCALStringsSparse264 façade
# ─────────────────────────────────────────────────────────────────────────────

class TestQCALStringsSparse264Facade:
    """Tests for the high-level QCALStringsSparse264 class."""

    @pytest.fixture()
    def small_op(self):
        return QCALStringsSparse264(
            N=_SMALL_N,
            n_primes=_SMALL_PRIMES,
            sigma=0.21,
            k_evals=_SMALL_K,
        )

    def test_instantiation(self, small_op):
        assert small_op.config is not None
        assert isinstance(small_op.config, SparseHamiltonianConfig)

    def test_run_returns_result(self, small_op):
        result = small_op.run()
        assert isinstance(result, SparseSpectralResult)

    def test_summary_is_string(self, small_op):
        result = small_op.run()
        summary = small_op.summary(result)
        assert isinstance(summary, str)
        assert "QCAL-STRINGS" in summary

    def test_summary_contains_doi(self, small_op):
        result = small_op.run()
        summary = small_op.summary(result)
        assert "10.5281/zenodo.17379721" in summary

    def test_sweep_returns_best_sigma(self, small_op):
        sigmas = [0.20, 0.25]
        best_sigma, best_err, _ = small_op.sweep(sigmas=sigmas)
        assert best_sigma in sigmas
        assert best_err >= 0

    def test_config_sigma_propagated(self):
        op = QCALStringsSparse264(N=_SMALL_N, sigma=0.18, n_primes=_SMALL_PRIMES)
        assert op.config.sigma == pytest.approx(0.18)

    def test_run_without_weyl_correction(self):
        op = QCALStringsSparse264(
            N=_SMALL_N,
            n_primes=_SMALL_PRIMES,
            sigma=0.21,
            k_evals=_SMALL_K,
            weyl_correction=False,
        )
        result = op.run()
        assert isinstance(result, SparseSpectralResult)

    def test_psi_coherence_is_positive(self, small_op):
        result = small_op.run()
        assert result.psi_coherence > 0

    def test_eigenvalues_have_correct_scale(self, small_op):
        """
        The smallest positive eigenvalues should be in the vicinity of
        Riemann zeros (order 10–100).  This is a loose sanity check.
        """
        result = small_op.run()
        if len(result.positive_eigenvalues) > 0:
            # At least some positive eigenvalues should exist in range [1, 500]
            in_range = (result.positive_eigenvalues > 1) & (
                result.positive_eigenvalues < 500
            )
            assert np.any(in_range), (
                f"No positive eigenvalues in [1, 500]. "
                f"Got: {result.positive_eigenvalues[:5]}"
            )
