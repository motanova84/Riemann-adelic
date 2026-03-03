#!/usr/bin/env python3
"""
Tests for operators/riemann_operator_H_corrected.py

Validates:
 1. Prime sieve helper
 2. V_osc^σ Gauss-filter regularisation (L²_loc bound, positivity of σ)
 3. V_Abel potential properties
 4. Hamiltonian construction (symmetry, shape)
 5. Kato-Rellich relative-bound check
 6. Spectral zeta / determinant
 7. Heat-kernel trace properties
 8. RiemannOperatorHCorrected class interface
 9. regularizar_potencial_soberano top-level function

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
DOI: 10.5281/zenodo.17379721
"""

import sys
import os
import pytest
import numpy as np

# Ensure operators package is importable from the repo root
REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, REPO_ROOT)

from operators.riemann_operator_H_corrected import (
    _sieve_primes,
    v_abel,
    v_osc_regularized,
    l2loc_bound,
    build_hamiltonian,
    kato_rellich_bound,
    spectral_zeta,
    heat_kernel_trace,
    fit_heat_asymptotic,
    regularizar_potencial_soberano,
    RiemannOperatorHCorrected,
    SpectralZetaData,
    RegularizationResult,
    EPSILON_OSC,
)
from scipy.linalg import eigh


# ---------------------------------------------------------------------------
# 1. Prime sieve
# ---------------------------------------------------------------------------

class TestSievePrimes:
    def test_small_primes(self):
        primes = _sieve_primes(10)
        assert primes == [2, 3, 5, 7]

    def test_empty_below_two(self):
        assert _sieve_primes(1) == []
        assert _sieve_primes(0) == []

    def test_includes_100(self):
        primes = _sieve_primes(100)
        assert len(primes) == 25   # 25 primes ≤ 100
        assert 97 in primes
        assert 98 not in primes

    def test_all_primes(self):
        primes = _sieve_primes(50)
        # Verify primality with trial division
        for p in primes:
            assert all(p % d != 0 for d in range(2, int(p ** 0.5) + 1)), \
                f"{p} is not prime"


# ---------------------------------------------------------------------------
# 2. V_osc regularisation
# ---------------------------------------------------------------------------

class TestVoscRegularized:
    def test_sigma_positive_required(self):
        x = np.array([1.0, 2.0])
        with pytest.raises(ValueError):
            v_osc_regularized(x, sigma=0.0)
        with pytest.raises(ValueError):
            v_osc_regularized(x, sigma=-0.1)

    def test_output_shape(self):
        x = np.linspace(0, 10, 50)
        v = v_osc_regularized(x, sigma=0.1, p_max=50)
        assert v.shape == x.shape

    def test_l2loc_bound_decreases_with_sigma(self):
        """Larger σ → stronger cutoff → smaller norm bound."""
        b1 = l2loc_bound(sigma=0.01, R=10.0, p_max=100)
        b2 = l2loc_bound(sigma=0.1, R=10.0, p_max=100)
        assert b2 < b1

    def test_l2loc_bound_positive(self):
        b = l2loc_bound(sigma=0.05, R=10.0, p_max=100)
        assert b > 0.0

    def test_real_values(self):
        x = np.linspace(-5, 5, 30)
        v = v_osc_regularized(x, sigma=0.05, p_max=50)
        assert np.all(np.isfinite(v))
        assert np.isrealobj(v)

    def test_phases_shift_values(self):
        """Non-zero phases should change the potential values."""
        x = np.linspace(0, 5, 20)
        primes = _sieve_primes(30)
        phases_zero = np.zeros(len(primes))
        phases_pi = np.full(len(primes), np.pi)
        v0 = v_osc_regularized(x, sigma=0.05, primes=primes, phases=phases_zero)
        vpi = v_osc_regularized(x, sigma=0.05, primes=primes, phases=phases_pi)
        assert not np.allclose(v0, vpi)

    def test_sigma_zero_limit_larger_values(self):
        """Very small σ should give larger potential than larger σ."""
        x = np.array([1.0, 2.0, 3.0])
        v_small = v_osc_regularized(x, sigma=1e-4, p_max=50)
        v_large = v_osc_regularized(x, sigma=1.0, p_max=50)
        assert np.max(np.abs(v_small)) >= np.max(np.abs(v_large))


# ---------------------------------------------------------------------------
# 3. V_Abel potential
# ---------------------------------------------------------------------------

class TestVAbel:
    def test_output_shape(self):
        x = np.linspace(-10, 10, 100)
        v = v_abel(x)
        assert v.shape == x.shape

    def test_non_negative(self):
        x = np.linspace(0.1, 20, 100)
        v = v_abel(x)
        assert np.all(v >= 0.0)

    def test_grows_with_x(self):
        """Background potential should be larger at larger |x|."""
        x = np.array([1.0, 5.0, 10.0, 20.0])
        v = v_abel(x)
        # Check endpoint comparison (potential grows as |x| → ∞)
        assert v[-1] > v[0]

    def test_even_symmetry(self):
        """v_abel is defined on |x|, so v(x) = v(-x)."""
        x_pos = np.array([1.0, 3.0, 7.0])
        assert np.allclose(v_abel(x_pos), v_abel(-x_pos), rtol=1e-10)

    def test_finite(self):
        x = np.linspace(-15, 15, 200)
        assert np.all(np.isfinite(v_abel(x)))


# ---------------------------------------------------------------------------
# 4. Hamiltonian construction
# ---------------------------------------------------------------------------

class TestBuildHamiltonian:
    def test_shape(self):
        H, x = build_hamiltonian(n_grid=50, p_max=30)
        assert H.shape == (50, 50)
        assert x.shape == (50,)

    def test_symmetric(self):
        H, _ = build_hamiltonian(n_grid=60, sigma=0.05, p_max=30)
        assert np.allclose(H, H.T, atol=1e-12)

    def test_real(self):
        H, _ = build_hamiltonian(n_grid=40, p_max=20)
        assert np.isrealobj(H)

    def test_eigenvalues_increase(self):
        """Eigenvalues should be ordered (eigh returns sorted)."""
        H, _ = build_hamiltonian(n_grid=40, p_max=20)
        eigs = eigh(H, eigvals_only=True)
        assert np.all(np.diff(eigs) >= 0)

    def test_positive_eigenvalues(self):
        """Background potential dominates; lowest eigenvalues should be positive."""
        H, _ = build_hamiltonian(n_grid=60, sigma=0.05, epsilon=0.01, p_max=50)
        eigs = eigh(H, eigvals_only=True)
        # At least the ground state should be positive for strong V_Abel
        assert eigs[0] > 0.0

    def test_epsilon_zero_no_osc(self):
        """With ε=0 the Hamiltonian is purely H₀ = -Δ + V_Abel."""
        H_full, _ = build_hamiltonian(n_grid=40, epsilon=0.0, p_max=20)
        H_zero, _ = build_hamiltonian(n_grid=40, epsilon=0.0, sigma=1.0, p_max=20)
        # Both should be identical because ε=0 suppresses oscillatory term
        assert np.allclose(H_full, H_zero, atol=1e-12)


# ---------------------------------------------------------------------------
# 5. Kato-Rellich
# ---------------------------------------------------------------------------

class TestKatoRellich:
    def test_returns_dict_keys(self):
        result = kato_rellich_bound(sigma=0.1, p_max=50, n_grid=40)
        for key in ("kato_a", "lambda1_H0", "l2_norm_vosc", "satisfied"):
            assert key in result

    def test_satisfied_for_small_epsilon(self):
        """Small ε should satisfy Kato-Rellich with a < 1."""
        result = kato_rellich_bound(
            sigma=0.05, p_max=100, n_grid=50, epsilon=0.01
        )
        assert result["satisfied"]
        assert result["kato_a"] < 1.0

    def test_larger_sigma_more_stable(self):
        """Larger σ means smaller V_osc norm, so kato_a should decrease."""
        r1 = kato_rellich_bound(sigma=0.01, p_max=100, n_grid=40, epsilon=0.05)
        r2 = kato_rellich_bound(sigma=1.0, p_max=100, n_grid=40, epsilon=0.05)
        assert r2["kato_a"] < r1["kato_a"]

    def test_lambda1_positive(self):
        result = kato_rellich_bound(sigma=0.1, p_max=50, n_grid=50)
        assert result["lambda1_H0"] > 0.0


# ---------------------------------------------------------------------------
# 6. Spectral zeta / determinant
# ---------------------------------------------------------------------------

class TestSpectralZeta:
    def _sample_eigs(self, n: int = 40) -> np.ndarray:
        H, _ = build_hamiltonian(n_grid=n, sigma=0.1, p_max=50)
        return eigh(H, eigvals_only=True)

    def test_returns_dataclass(self):
        eigs = self._sample_eigs()
        result = spectral_zeta(eigs)
        assert isinstance(result, SpectralZetaData)

    def test_log_det_finite(self):
        eigs = self._sample_eigs()
        result = spectral_zeta(eigs)
        assert np.isfinite(result.log_determinant)

    def test_log_det_equals_neg_zeta_prime(self):
        eigs = self._sample_eigs()
        result = spectral_zeta(eigs)
        assert np.isclose(result.log_determinant, -result.zeta_prime_0, atol=1e-10)

    def test_empty_eigenvalues(self):
        empty = np.array([])
        result = spectral_zeta(empty)
        assert result.log_determinant == 0.0
        assert result.zeta_prime_0 == 0.0

    def test_positive_eigenvalues_only(self):
        """Spectral zeta uses only positive eigenvalues."""
        eigs_mixed = np.array([-1.0, 0.5, 1.0, 2.0, 3.0])
        result = spectral_zeta(eigs_mixed)
        # Should not raise; negative eigs are filtered
        assert np.isfinite(result.log_determinant)
        assert len(result.eigenvalues) == 4  # Only positives used


# ---------------------------------------------------------------------------
# 7. Heat-kernel trace
# ---------------------------------------------------------------------------

class TestHeatKernelTrace:
    def _sample_eigs(self, n: int = 50) -> np.ndarray:
        H, _ = build_hamiltonian(n_grid=n, sigma=0.1, p_max=50)
        return eigh(H, eigvals_only=True)

    def test_shape(self):
        eigs = self._sample_eigs()
        t_vals = np.logspace(-2, 1, 30)
        t_out, tr_out = heat_kernel_trace(eigs, t_values=t_vals)
        assert t_out.shape == tr_out.shape == (30,)

    def test_decreasing_in_t(self):
        """Tr(e^{-tH}) should decrease monotonically for positive spectrum."""
        eigs = np.array([1.0, 2.0, 3.0, 5.0])
        t_vals = np.array([0.1, 0.5, 1.0, 2.0, 5.0])
        _, tr = heat_kernel_trace(eigs, t_values=t_vals)
        assert np.all(np.diff(tr) <= 0)

    def test_t_zero_limit(self):
        """Tr → number of positive eigenvalues as t → 0+."""
        eigs = np.array([0.1, 0.5, 1.0, 2.0])  # all positive
        t_vals = np.array([1e-6])
        _, tr = heat_kernel_trace(eigs, t_values=t_vals)
        assert abs(tr[0] - 4.0) < 0.01

    def test_default_t_values(self):
        eigs = self._sample_eigs()
        t_out, tr_out = heat_kernel_trace(eigs)
        assert len(t_out) == 80
        assert np.all(np.isfinite(tr_out))

    def test_asymptotic_fit_three_coeffs(self):
        eigs = self._sample_eigs()
        t_vals, tr_vals = heat_kernel_trace(eigs)
        coeffs = fit_heat_asymptotic(t_vals, tr_vals)
        assert coeffs.shape == (3,)
        assert np.all(np.isfinite(coeffs))


# ---------------------------------------------------------------------------
# 8. RiemannOperatorHCorrected class
# ---------------------------------------------------------------------------

class TestRiemannOperatorHCorrected:
    def test_invalid_sigma(self):
        with pytest.raises(ValueError):
            RiemannOperatorHCorrected(sigma=0.0)
        with pytest.raises(ValueError):
            RiemannOperatorHCorrected(sigma=-0.05)

    def test_build_returns_self(self):
        op = RiemannOperatorHCorrected(sigma=0.1, n_grid=40, p_max=30)
        result = op.build()
        assert result is op

    def test_hamiltonian_symmetric(self):
        op = RiemannOperatorHCorrected(sigma=0.05, n_grid=50, p_max=50)
        assert op.is_self_adjoint()

    def test_eigenvalues_sorted(self):
        op = RiemannOperatorHCorrected(sigma=0.1, n_grid=40, p_max=30)
        eigs = op.eigenvalues()
        assert np.all(np.diff(eigs) >= 0)

    def test_kato_rellich_method(self):
        op = RiemannOperatorHCorrected(sigma=0.1, epsilon=0.01, n_grid=40, p_max=50)
        kr = op.kato_rellich()
        assert "satisfied" in kr
        assert kr["satisfied"]

    def test_spectral_determinant_method(self):
        op = RiemannOperatorHCorrected(sigma=0.1, n_grid=40, p_max=30)
        sz = op.spectral_determinant()
        assert isinstance(sz, SpectralZetaData)
        assert np.isfinite(sz.log_determinant)

    def test_heat_kernel_method(self):
        op = RiemannOperatorHCorrected(sigma=0.1, n_grid=40, p_max=30)
        t_vals, tr_vals = op.heat_kernel()
        assert len(t_vals) == 80
        assert np.all(np.isfinite(tr_vals))

    def test_validate_returns_result(self):
        op = RiemannOperatorHCorrected(sigma=0.1, epsilon=0.01, n_grid=40, p_max=50)
        res = op.validate()
        assert isinstance(res, RegularizationResult)
        assert res.sigma == 0.1
        assert res.n_primes > 0
        assert res.l2loc_bound > 0.0
        assert np.isfinite(res.log_determinant)
        assert isinstance(res.status, str)

    def test_validate_status_positive(self):
        """Small ε should produce satisfied Kato-Rellich → positive status."""
        op = RiemannOperatorHCorrected(sigma=0.1, epsilon=0.01, n_grid=40, p_max=50)
        res = op.validate()
        assert res.kato_rellich_satisfied
        assert "✅" in res.status

    def test_h_matrix_shape(self):
        op = RiemannOperatorHCorrected(sigma=0.05, n_grid=60, p_max=50)
        assert op.H.shape == (60, 60)

    def test_x_grid_length(self):
        op = RiemannOperatorHCorrected(sigma=0.05, n_grid=60, p_max=50)
        assert len(op.x) == 60


# ---------------------------------------------------------------------------
# 9. regularizar_potencial_soberano top-level function
# ---------------------------------------------------------------------------

class TestRegularizarPotencialSoberano:
    def test_returns_string(self, capsys):
        result = regularizar_potencial_soberano(sigma=0.2)
        assert isinstance(result, str)

    def test_status_message(self):
        result = regularizar_potencial_soberano(sigma=0.1)
        assert "Coherencia de Distribución Alcanzada" in result

    def test_output_contains_key_steps(self, capsys):
        regularizar_potencial_soberano(sigma=0.15)
        captured = capsys.readouterr()
        assert "REGULARIZACIÓN ESTRUCTURAL" in captured.out
        assert "Kato-Rellich" in captured.out
        assert "determinante" in captured.out.lower()

    def test_different_sigma_values(self):
        for sigma in [0.05, 0.1, 0.5]:
            result = regularizar_potencial_soberano(sigma=sigma)
            assert "OPERACIÓN" in result
