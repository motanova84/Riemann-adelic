#!/usr/bin/env python3
"""
Tests for Phase #264 Sparse Spectral Hamiltonian — Riemann Zero Anchoring
==========================================================================

Validates:
1. Module constants (SIGMA_CRITICAL, N_FULL, N_PRIMES_264, …)
2. _sieve_primes() — prime generation correctness
3. get_riemann_zeros() — reference zeros retrieval
4. v_mod_sparse() — sparse Lorentzian potential construction
5. h_bk_sparse() — sparse kinetic operator construction
6. v_corrections_sparse() — GUE correction operator
7. build_phase264_hamiltonian() — full operator assembly
8. SpectralAnchoringResult — dataclass semantics
9. compute_spectral_anchoring() — eigenvalue recovery & error metrics
10. sweep_sigma() — σ-sweep utility

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
QCAL ∞³ Active · 141.7001 Hz · C = 244.36
DOI: 10.5281/zenodo.17379721
"""

import importlib.util
import os

import numpy as np
import pytest
import scipy.sparse as sp

# ---------------------------------------------------------------------------
# Import the module under test using importlib (avoids sys.path side-effects)
# ---------------------------------------------------------------------------
_MOD_PATH = os.path.join(
    os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
    "operators",
    "phase_264_sparse_spectral.py",
)
_spec = importlib.util.spec_from_file_location("phase_264_sparse_spectral", _MOD_PATH)
_mod = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_mod)

# Public names
SIGMA_CRITICAL = _mod.SIGMA_CRITICAL
N_FULL = _mod.N_FULL
N_PRIMES_264 = _mod.N_PRIMES_264
K_MODES_264 = _mod.K_MODES_264
MEAN_ERROR_264 = _mod.MEAN_ERROR_264
ANCHOR_THRESHOLD = _mod.ANCHOR_THRESHOLD
F0_264 = _mod.F0_264

_sieve_primes = _mod._sieve_primes
get_riemann_zeros = _mod.get_riemann_zeros
v_mod_sparse = _mod.v_mod_sparse
h_bk_sparse = _mod.h_bk_sparse
v_corrections_sparse = _mod.v_corrections_sparse
build_phase264_hamiltonian = _mod.build_phase264_hamiltonian
compute_spectral_anchoring = _mod.compute_spectral_anchoring
sweep_sigma = _mod.sweep_sigma
SpectralAnchoringResult = _mod.SpectralAnchoringResult


# ===========================================================================
# Constants
# ===========================================================================

class TestConstants:
    """Verify module-level constants match the Phase #264 specification."""

    def test_sigma_critical_value(self):
        """SIGMA_CRITICAL must be 0.21."""
        assert SIGMA_CRITICAL == pytest.approx(0.21, rel=1e-6)

    def test_n_full_value(self):
        """Full-scale grid size must be 32 768."""
        assert N_FULL == 32_768

    def test_n_primes_264(self):
        """Number of primes in full run must be 2 000."""
        assert N_PRIMES_264 == 2_000

    def test_k_modes_264(self):
        """Number of extracted modes must be 50."""
        assert K_MODES_264 == 50

    def test_mean_error_264(self):
        """Documented mean error must be 4.12 % (0.0412)."""
        assert MEAN_ERROR_264 == pytest.approx(0.0412, rel=1e-4)

    def test_anchor_threshold(self):
        """Anchor threshold must be 0.001 (0.1 %)."""
        assert ANCHOR_THRESHOLD == pytest.approx(0.001, rel=1e-6)

    def test_f0_264(self):
        """F0_264 must equal 141.7001."""
        assert F0_264 == pytest.approx(141.7001, rel=1e-6)


# ===========================================================================
# Prime sieve
# ===========================================================================

class TestSievePrimes:
    """Tests for _sieve_primes()."""

    def test_first_five_primes(self):
        """First five primes must be [2, 3, 5, 7, 11]."""
        primes = _sieve_primes(5)
        np.testing.assert_array_equal(primes, [2.0, 3.0, 5.0, 7.0, 11.0])

    def test_length(self):
        """Return array must have exactly n_primes elements."""
        for n in (1, 10, 50, 100):
            assert len(_sieve_primes(n)) == n

    def test_all_prime(self):
        """All returned values must be prime."""
        primes = _sieve_primes(30)
        for p in primes.astype(int):
            assert all(p % d != 0 for d in range(2, p)), f"{p} is not prime"

    def test_sorted_ascending(self):
        """Primes must be in ascending order."""
        primes = _sieve_primes(20)
        assert np.all(primes[1:] > primes[:-1])

    def test_invalid_n_raises(self):
        """Non-positive or non-integer n_primes must raise ValueError."""
        with pytest.raises(ValueError):
            _sieve_primes(0)
        with pytest.raises(ValueError):
            _sieve_primes(-3)
        with pytest.raises(ValueError):
            _sieve_primes(3.5)  # type: ignore[arg-type]


# ===========================================================================
# Riemann zeros
# ===========================================================================

class TestGetRiemannZeros:
    """Tests for get_riemann_zeros()."""

    def test_first_zero(self):
        """First zero must be ≈ 14.134725."""
        zeros = get_riemann_zeros(1)
        assert zeros[0] == pytest.approx(14.134725, rel=1e-4)

    def test_length(self):
        """Output array must have n_zeros elements."""
        for n in (1, 5, 10, 25, 50):
            assert len(get_riemann_zeros(n)) == n

    def test_sorted_ascending(self):
        """Zeros must be in ascending order."""
        zeros = get_riemann_zeros(20)
        assert np.all(zeros[1:] > zeros[:-1])

    def test_all_positive(self):
        """All zeros must be positive."""
        zeros = get_riemann_zeros(50)
        assert np.all(zeros > 0.0)

    def test_invalid_n_raises(self):
        """n_zeros < 1 must raise ValueError."""
        with pytest.raises(ValueError):
            get_riemann_zeros(0)

    def test_beyond_table_continues(self):
        """Should not crash when requesting more than 50 zeros."""
        zeros = get_riemann_zeros(60)
        assert len(zeros) == 60
        assert zeros[59] > zeros[49]


# ===========================================================================
# v_mod_sparse
# ===========================================================================

class TestVModSparse:
    """Tests for v_mod_sparse()."""

    def _log_primes(self, n: int = 5) -> np.ndarray:
        return np.log(_sieve_primes(n))

    def test_output_type(self):
        """Return type must be a scipy sparse matrix."""
        V = v_mod_sparse(16, self._log_primes())
        assert sp.issparse(V)

    def test_output_shape(self):
        """Sparse matrix shape must be (N, N)."""
        N = 32
        V = v_mod_sparse(N, self._log_primes())
        assert V.shape == (N, N)

    def test_diagonal_only(self):
        """Only diagonal entries must be non-zero."""
        N = 16
        V = v_mod_sparse(N, self._log_primes()).toarray()
        off_diag_sum = np.sum(np.abs(V - np.diag(np.diag(V))))
        assert off_diag_sum == pytest.approx(0.0, abs=1e-15)

    def test_diagonal_positive(self):
        """Diagonal entries must be strictly positive (Lorentzian sum)."""
        N = 32
        V = v_mod_sparse(N, self._log_primes())
        diag = V.diagonal()
        assert np.all(diag > 0.0)

    def test_larger_sigma_flatter_peaks(self):
        """Larger σ produces broader peaks — minimum value must be higher."""
        N = 64
        lp = self._log_primes(3)
        V_narrow = v_mod_sparse(N, lp, sigma=0.05).diagonal()
        V_wide = v_mod_sparse(N, lp, sigma=2.0).diagonal()
        # With narrow σ, most grid points are far from any prime → near-zero floor.
        # With wide σ, overlapping tails keep the floor well above zero.
        assert V_wide.min() > V_narrow.min()

    def test_invalid_N_raises(self):
        """N < 2 must raise ValueError."""
        with pytest.raises(ValueError, match="N"):
            v_mod_sparse(1, self._log_primes())

    def test_invalid_sigma_raises(self):
        """sigma ≤ 0 must raise ValueError."""
        with pytest.raises(ValueError, match="sigma"):
            v_mod_sparse(16, self._log_primes(), sigma=0.0)
        with pytest.raises(ValueError, match="sigma"):
            v_mod_sparse(16, self._log_primes(), sigma=-1.0)

    def test_empty_log_primes_raises(self):
        """Empty log_primes must raise ValueError."""
        with pytest.raises(ValueError, match="log_primes"):
            v_mod_sparse(16, np.array([]))

    def test_zero_log_prime_raises(self):
        """Non-positive log_primes must raise ValueError."""
        with pytest.raises(ValueError, match="log_primes"):
            v_mod_sparse(16, np.array([0.0, 1.0]))

    def test_negative_log_prime_raises(self):
        """Negative log_primes values must raise ValueError."""
        with pytest.raises(ValueError, match="log_primes"):
            v_mod_sparse(16, np.array([-1.0, 0.5]))


# ===========================================================================
# h_bk_sparse
# ===========================================================================

class TestHBKSparse:
    """Tests for h_bk_sparse()."""

    def test_output_type_is_sparse(self):
        """Return type must be a scipy sparse matrix."""
        H = h_bk_sparse(16)
        assert sp.issparse(H)

    def test_output_shape(self):
        """Shape must be (N, N)."""
        N = 32
        assert h_bk_sparse(N).shape == (N, N)

    def test_symmetric(self):
        """The kinetic matrix must be symmetric."""
        N = 32
        H = h_bk_sparse(N).toarray()
        np.testing.assert_allclose(H, H.T, atol=1e-15)

    def test_tridiagonal(self):
        """Only main diagonal and first off-diagonals must be non-zero."""
        N = 8
        H = h_bk_sparse(N).toarray()
        for i in range(N):
            for j in range(N):
                if abs(i - j) > 1:
                    assert H[i, j] == pytest.approx(0.0, abs=1e-15), (
                        f"Non-tridiagonal entry H[{i},{j}] = {H[i,j]}"
                    )

    def test_positive_diagonal(self):
        """Main diagonal must be positive (standard Laplacian sign)."""
        H = h_bk_sparse(16).toarray()
        assert np.all(np.diag(H) > 0.0)

    def test_negative_off_diagonal(self):
        """Off-diagonal entries must be negative."""
        H = h_bk_sparse(16).toarray()
        for i in range(15):
            assert H[i, i + 1] < 0.0

    def test_invalid_N_raises(self):
        """N < 3 must raise ValueError."""
        with pytest.raises(ValueError, match="N"):
            h_bk_sparse(2)

    def test_invalid_grid_raises(self):
        """u_min ≥ u_max must raise ValueError."""
        with pytest.raises(ValueError):
            h_bk_sparse(16, u_min=5.0, u_max=1.0)


# ===========================================================================
# v_corrections_sparse
# ===========================================================================

class TestVCorrectionsSparse:
    """Tests for v_corrections_sparse()."""

    def test_output_type(self):
        """Return type must be sparse."""
        V = v_corrections_sparse(16)
        assert sp.issparse(V)

    def test_shape(self):
        """Shape must be (N, N)."""
        N = 20
        V = v_corrections_sparse(N)
        assert V.shape == (N, N)

    def test_diagonal_only(self):
        """Matrix must be diagonal (only main diagonal non-zero)."""
        N = 16
        V = v_corrections_sparse(N).toarray()
        off = np.sum(np.abs(V - np.diag(np.diag(V))))
        assert off == pytest.approx(0.0, abs=1e-15)

    def test_zero_amplitude_gives_zero(self):
        """amplitude=0 must give a matrix with all-zero values."""
        V = v_corrections_sparse(16, amplitude=0.0)
        # dia_matrix may still store zeros structurally; check values are zero.
        np.testing.assert_allclose(V.toarray(), 0.0, atol=1e-15)

    def test_diagonal_nonnegative(self):
        """Diagonal values must be ≥ 0 for positive amplitude."""
        V = v_corrections_sparse(32, amplitude=0.05)
        assert np.all(V.diagonal() >= 0.0)

    def test_invalid_N_raises(self):
        with pytest.raises(ValueError, match="N"):
            v_corrections_sparse(1)

    def test_negative_amplitude_raises(self):
        with pytest.raises(ValueError, match="amplitude"):
            v_corrections_sparse(16, amplitude=-0.1)


# ===========================================================================
# build_phase264_hamiltonian
# ===========================================================================

class TestBuildPhase264Hamiltonian:
    """Tests for build_phase264_hamiltonian()."""

    def test_output_is_sparse(self):
        """Return type must be a sparse matrix."""
        H = build_phase264_hamiltonian(N=16, n_primes=5)
        assert sp.issparse(H)

    def test_shape(self):
        """Shape must be (N, N)."""
        N = 32
        H = build_phase264_hamiltonian(N=N, n_primes=5)
        assert H.shape == (N, N)

    def test_symmetric(self):
        """Hamiltonian must be symmetric (Hermitian in real case)."""
        N = 16
        H = build_phase264_hamiltonian(N=N, n_primes=5).toarray()
        np.testing.assert_allclose(H, H.T, atol=1e-10)

    def test_sparse_format(self):
        """Return format should be CSR for efficient arithmetic."""
        H = build_phase264_hamiltonian(N=16, n_primes=5)
        assert H.format == "csr"

    def test_real_entries(self):
        """All entries must be real (no imaginary parts)."""
        H = build_phase264_hamiltonian(N=16, n_primes=5).toarray()
        assert np.all(np.isreal(H))

    def test_finite_entries(self):
        """All entries must be finite."""
        H = build_phase264_hamiltonian(N=32, n_primes=10).toarray()
        assert np.all(np.isfinite(H))

    def test_scaled_by_f0(self):
        """Doubling f0 must double the norm of H."""
        H1 = build_phase264_hamiltonian(N=16, n_primes=5, f0=1.0)
        H2 = build_phase264_hamiltonian(N=16, n_primes=5, f0=2.0)
        norm1 = np.linalg.norm(H1.toarray())
        norm2 = np.linalg.norm(H2.toarray())
        assert norm2 == pytest.approx(2.0 * norm1, rel=1e-9)

    def test_more_primes_different_spectrum(self):
        """Using more primes must change the diagonal potential."""
        H_few = build_phase264_hamiltonian(N=32, n_primes=5).toarray()
        H_more = build_phase264_hamiltonian(N=32, n_primes=20).toarray()
        assert not np.allclose(H_few, H_more)


# ===========================================================================
# SpectralAnchoringResult
# ===========================================================================

class TestSpectralAnchoringResult:
    """Tests for the SpectralAnchoringResult dataclass."""

    def _make_result(self, n: int = 5) -> SpectralAnchoringResult:
        evals = np.array([14.13, 21.02, 25.01, 30.42, 32.94])[:n]
        zeros = np.array([14.134725, 21.022040, 25.010858, 30.424876, 32.935062])[:n]
        rel_err = np.abs(evals - zeros) / np.abs(zeros)
        anchored = np.where(rel_err < ANCHOR_THRESHOLD)[0]
        return SpectralAnchoringResult(
            eigenvalues=evals,
            riemann_zeros=zeros,
            relative_errors=rel_err,
            mean_error=float(np.mean(rel_err)),
            anchored_modes=anchored,
            n_anchored=int(len(anchored)),
            sigma=0.21,
            N=512,
            n_primes=50,
            k_modes=n,
        )

    def test_mean_error_computed(self):
        """mean_error must be the mean of relative_errors."""
        r = self._make_result()
        assert r.mean_error == pytest.approx(float(np.mean(r.relative_errors)), rel=1e-9)

    def test_is_anchored_true_when_modes_exist(self):
        """is_anchored must be True when n_anchored > 0."""
        r = self._make_result()
        assert r.is_anchored == (r.n_anchored > 0)

    def test_as_dict_keys(self):
        """as_dict() must return all expected keys."""
        r = self._make_result()
        d = r.as_dict()
        expected_keys = {
            "eigenvalues", "riemann_zeros", "relative_errors", "mean_error",
            "anchored_modes", "n_anchored", "sigma", "N", "n_primes", "k_modes",
        }
        assert set(d.keys()) == expected_keys

    def test_as_dict_serialisable(self):
        """as_dict() output must be JSON-serialisable."""
        import json
        r = self._make_result()
        json_str = json.dumps(r.as_dict())
        assert isinstance(json_str, str)


# ===========================================================================
# compute_spectral_anchoring
# ===========================================================================

class TestComputeSpectralAnchoring:
    """Tests for compute_spectral_anchoring()."""

    def test_returns_result(self):
        """Function must return a SpectralAnchoringResult."""
        result = compute_spectral_anchoring(N=32, n_primes=5, k_modes=5)
        assert isinstance(result, SpectralAnchoringResult)

    def test_eigenvalues_length(self):
        """eigenvalues must have k_modes entries."""
        k = 5
        result = compute_spectral_anchoring(N=32, n_primes=5, k_modes=k)
        assert len(result.eigenvalues) == k

    def test_riemann_zeros_length(self):
        """riemann_zeros must match k_modes in length."""
        k = 6
        result = compute_spectral_anchoring(N=40, n_primes=5, k_modes=k)
        assert len(result.riemann_zeros) == k

    def test_relative_errors_positive(self):
        """All relative errors must be non-negative."""
        result = compute_spectral_anchoring(N=32, n_primes=5, k_modes=5)
        assert np.all(result.relative_errors >= 0.0)

    def test_mean_error_finite(self):
        """Mean error must be a finite positive float."""
        result = compute_spectral_anchoring(N=32, n_primes=5, k_modes=5)
        assert np.isfinite(result.mean_error)
        assert result.mean_error >= 0.0

    def test_stored_params(self):
        """Result must record the parameters used."""
        N, n_p, k = 32, 8, 5
        result = compute_spectral_anchoring(N=N, n_primes=n_p, k_modes=k)
        assert result.N == N
        assert result.n_primes == n_p
        assert result.k_modes == k
        assert result.sigma == pytest.approx(SIGMA_CRITICAL, rel=1e-6)

    def test_k_modes_too_large_raises(self):
        """k_modes ≥ N − 2 must raise ValueError."""
        with pytest.raises(ValueError, match="k_modes"):
            compute_spectral_anchoring(N=10, n_primes=5, k_modes=9)

    def test_eigenvalues_sorted(self):
        """Eigenvalues must be returned in ascending order."""
        result = compute_spectral_anchoring(N=32, n_primes=5, k_modes=6)
        assert np.all(result.eigenvalues[1:] >= result.eigenvalues[:-1])

    def test_reasonable_error_moderate_N(self):
        """With moderate N and n_primes, mean error should be less than 80 %."""
        result = compute_spectral_anchoring(N=128, n_primes=20, k_modes=8)
        assert result.mean_error < 0.80

    def test_anchored_modes_subset_of_all(self):
        """All anchored mode indices must be valid (in range [0, k_modes))."""
        result = compute_spectral_anchoring(N=64, n_primes=10, k_modes=8)
        for idx in result.anchored_modes:
            assert 0 <= idx < result.k_modes


# ===========================================================================
# sweep_sigma
# ===========================================================================

class TestSweepSigma:
    """Tests for sweep_sigma()."""

    def test_returns_dict_with_correct_keys(self):
        """Return value must have 'sigma' and 'mean_error' keys."""
        sigmas = np.array([0.1, 0.2, 0.3])
        result = sweep_sigma(sigmas, N=16, n_primes=5, k_modes=4)
        assert "sigma" in result
        assert "mean_error" in result

    def test_output_lengths_match_input(self):
        """Output arrays must have the same length as sigma_values."""
        sigmas = np.linspace(0.1, 0.5, 4)
        result = sweep_sigma(sigmas, N=16, n_primes=5, k_modes=4)
        assert len(result["sigma"]) == len(sigmas)
        assert len(result["mean_error"]) == len(sigmas)

    def test_sigma_values_preserved(self):
        """Output sigma values must match input."""
        sigmas = np.array([0.15, 0.25, 0.35])
        result = sweep_sigma(sigmas, N=16, n_primes=5, k_modes=4)
        np.testing.assert_allclose(result["sigma"], sigmas)

    def test_errors_are_finite_or_nan(self):
        """Each error entry must be either finite or NaN (no Inf)."""
        sigmas = np.array([0.1, 0.2, 0.5])
        result = sweep_sigma(sigmas, N=16, n_primes=5, k_modes=4)
        for e in result["mean_error"]:
            assert np.isnan(e) or np.isfinite(e)
            if not np.isnan(e):
                assert not np.isinf(e)
