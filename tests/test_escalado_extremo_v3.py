#!/usr/bin/env python3
"""
Tests for ESCALADO EXTREMO v3.0
================================

Tests de la criba de primos, construcción del Hamiltoniano sparse,
alineación espectral, barrido paralelo reducido y funciones de
visualización para el módulo operators/escalado_extremo_v3.py.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Framework
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add repository root to path
repo_root = Path(__file__).parent.parent
sys.path.insert(0, str(repo_root))

from operators.escalado_extremo_v3 import (
    segmented_sieve,
    build_hamiltonian,
    compute_single,
    ejecutar_escalado_extremo,
    plot_gue_purified,
    plot_error_map,
    decreto_dilmun_v3,
    EscaladoResult,
)


# ──────────────────────────────────────────────────────────────────────────────
# Criba segmentada
# ──────────────────────────────────────────────────────────────────────────────

class TestSegmentedSieve:
    """Tests for segmented_sieve()."""

    def test_small_primes(self):
        primes = segmented_sieve(20)
        assert list(primes) == [2, 3, 5, 7, 11, 13, 17, 19]

    def test_first_prime_is_two(self):
        primes = segmented_sieve(10)
        assert primes[0] == 2

    def test_empty_below_two(self):
        assert len(segmented_sieve(1)) == 0
        assert len(segmented_sieve(0)) == 0

    def test_limit_inclusive(self):
        # 97 is prime; should be included when limit=97
        primes = segmented_sieve(97)
        assert 97 in primes

    def test_no_composites(self):
        primes = segmented_sieve(50)
        for p in primes:
            if p < 2:
                pytest.fail(f"Non-prime {p} returned")
            for d in range(2, int(p ** 0.5) + 1):
                assert p % d != 0, f"{p} is not prime"

    def test_count_100(self):
        # There are 25 primes ≤ 100
        primes = segmented_sieve(100)
        assert len(primes) == 25

    def test_consistency(self):
        assert list(segmented_sieve(50)) == list(segmented_sieve(50))


# ──────────────────────────────────────────────────────────────────────────────
# Construcción del Hamiltoniano
# ──────────────────────────────────────────────────────────────────────────────

class TestBuildHamiltonian:
    """Tests for build_hamiltonian()."""

    @pytest.fixture
    def small_primes(self):
        return segmented_sieve(20)  # [2, 3, 5, 7, 11, 13, 17, 19]

    def test_returns_sparse_matrix(self, small_primes):
        import scipy.sparse as sp
        H = build_hamiltonian(0.3, 0.01, small_primes, n_basis=64, L=10.0)
        assert sp.issparse(H)

    def test_correct_shape(self, small_primes):
        n = 128
        H = build_hamiltonian(0.3, 0.01, small_primes, n_basis=n, L=10.0)
        assert H.shape == (n, n)

    def test_symmetry(self, small_primes):
        """Hamiltonian should be symmetric (H = H^T)."""
        H = build_hamiltonian(0.3, 0.01, small_primes, n_basis=64, L=10.0)
        diff = (H - H.T).toarray()
        assert np.max(np.abs(diff)) < 1e-10

    def test_diagonal_real(self, small_primes):
        H = build_hamiltonian(0.3, 0.01, small_primes, n_basis=64, L=10.0)
        diag = H.diagonal()
        assert np.all(np.isreal(diag))

    def test_finite_entries(self, small_primes):
        H = build_hamiltonian(0.3, 0.01, small_primes, n_basis=64, L=10.0)
        data = H.toarray()
        assert np.all(np.isfinite(data))

    def test_confinement_increases_diagonal(self, small_primes):
        """Higher α should produce larger diagonal entries."""
        H_low = build_hamiltonian(0.3, 0.001, small_primes, n_basis=64, L=10.0)
        H_high = build_hamiltonian(0.3, 1.0, small_primes, n_basis=64, L=10.0)
        # Mean absolute diagonal should be larger for higher alpha
        mean_low = np.mean(np.abs(H_low.diagonal()))
        mean_high = np.mean(np.abs(H_high.diagonal()))
        assert mean_high > mean_low


# ──────────────────────────────────────────────────────────────────────────────
# Compute single (eigenvalores)
# ──────────────────────────────────────────────────────────────────────────────

class TestComputeSingle:
    """Tests for compute_single()."""

    @pytest.fixture
    def small_primes(self):
        return segmented_sieve(30)

    def test_returns_tuple(self, small_primes):
        result = compute_single((0.3, 0.01), small_primes, n_basis=64, L=10.0, k_max=3, n_ev=10)
        assert len(result) == 3

    def test_evals_positive(self, small_primes):
        evals, eps, alpha = compute_single(
            (0.3, 0.01), small_primes, n_basis=64, L=10.0, k_max=3, n_ev=10
        )
        assert np.all(evals > 0.01)

    def test_evals_sorted(self, small_primes):
        evals, _, _ = compute_single(
            (0.3, 0.01), small_primes, n_basis=64, L=10.0, k_max=3, n_ev=10
        )
        assert np.all(np.diff(evals) >= 0)

    def test_params_returned(self, small_primes):
        eps, alpha = 0.35, 0.015
        _, ret_eps, ret_alpha = compute_single(
            (eps, alpha), small_primes, n_basis=64, L=10.0, k_max=3, n_ev=10
        )
        assert ret_eps == eps
        assert ret_alpha == alpha


# ──────────────────────────────────────────────────────────────────────────────
# Barrido extremo reducido
# ──────────────────────────────────────────────────────────────────────────────

class TestEjecucionEscalado:
    """Tests for ejecutar_escalado_extremo() with tiny params."""

    def test_returns_escalado_result(self):
        result = ejecutar_escalado_extremo(
            n_basis=64,
            L=10.0,
            primes_limit=20,
            k_max=2,
            n_ev=10,
            n_ceros_align=5,
            eps_range=np.array([0.3]),
            alpha_range=np.array([0.01]),
            n_jobs=1,
        )
        assert isinstance(result, EscaladoResult)

    def test_best_corr_is_float(self):
        result = ejecutar_escalado_extremo(
            n_basis=64,
            L=10.0,
            primes_limit=20,
            k_max=2,
            n_ev=10,
            n_ceros_align=5,
            eps_range=np.linspace(0.28, 0.38, 2),
            alpha_range=np.linspace(0.009, 0.015, 2),
            n_jobs=1,
        )
        assert isinstance(result.best_corr, float)

    def test_best_evals_nonempty(self):
        result = ejecutar_escalado_extremo(
            n_basis=64,
            L=10.0,
            primes_limit=20,
            k_max=2,
            n_ev=10,
            n_ceros_align=5,
            eps_range=np.array([0.3]),
            alpha_range=np.array([0.01]),
            n_jobs=1,
        )
        assert len(result.best_evals) > 0

    def test_elapsed_nonnegative(self):
        result = ejecutar_escalado_extremo(
            n_basis=64,
            L=10.0,
            primes_limit=20,
            k_max=2,
            n_ev=10,
            n_ceros_align=5,
            eps_range=np.array([0.3]),
            alpha_range=np.array([0.01]),
            n_jobs=1,
        )
        assert result.elapsed_minutes >= 0.0


# ──────────────────────────────────────────────────────────────────────────────
# Visualizaciones (smoke tests)
# ──────────────────────────────────────────────────────────────────────────────

class TestVisualizations:
    """Smoke tests for plotting functions (no display)."""

    @pytest.fixture
    def synthetic_evals(self):
        """Synthetic eigenvalues with GUE-like spacing."""
        rng = np.random.default_rng(42)
        vals = np.sort(np.cumsum(rng.exponential(1.0, 200))) + 55
        return vals

    def test_plot_gue_returns_figure(self, synthetic_evals):
        import matplotlib.pyplot as plt
        fig = plot_gue_purified(synthetic_evals, show=False)
        assert fig is not None
        plt.close("all")

    def test_plot_gue_no_display(self, synthetic_evals):
        import matplotlib.pyplot as plt
        # Should not raise even without display
        fig = plot_gue_purified(synthetic_evals, t_min=55.0, t_max=200.0, show=False)
        plt.close("all")

    def test_plot_error_map_returns_figure(self, synthetic_evals):
        import matplotlib.pyplot as plt
        fig = plot_error_map(synthetic_evals, n_ceros=20, show=False)
        assert fig is not None
        plt.close("all")

    def test_plot_gue_empty_window_raises(self):
        evals = np.array([1.0, 2.0, 3.0])
        with pytest.raises(ValueError):
            plot_gue_purified(evals, t_min=1000.0, t_max=2000.0, show=False)


# ──────────────────────────────────────────────────────────────────────────────
# Decreto Dilmun v3
# ──────────────────────────────────────────────────────────────────────────────

class TestDecretoDilmun:
    """Tests for decreto_dilmun_v3()."""

    def test_returns_string(self):
        result = EscaladoResult(
            best_evals=np.array([1.0, 2.0]),
            best_eps=0.3,
            best_alpha=0.01,
            best_corr=0.99,
            elapsed_minutes=0.1,
        )
        ret = decreto_dilmun_v3(result)
        assert isinstance(ret, str)
        assert "Ziusudra" in ret
        assert ret == "Ziusudra 2026: Operador Indispensable registrado en Dilmun."

    def test_dilmun_message(self, capsys):
        result = EscaladoResult(
            best_evals=np.array([1.0, 2.0]),
            best_eps=0.3,
            best_alpha=0.01,
            best_corr=0.9987,
            elapsed_minutes=0.1,
        )
        decreto_dilmun_v3(result)
        captured = capsys.readouterr()
        assert "DECRETO" in captured.out
        assert "0.9987" in captured.out
