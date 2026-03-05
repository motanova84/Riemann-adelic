#!/usr/bin/env python3
"""
Test Suite: Regularización KAIROS — Exponential Cutoff Regularization

Tests for operators/regularizacion_kairos.py

Validates:
1. PotencialRegularizado construction and basic properties
2. Absolute convergence of the regularized series
3. L²_loc membership of V_osc^σ
4. Kato-Rellich self-adjointness conditions
5. Behavior of the σ → 0 limit study function
6. Matrix construction and eigenvalue computation

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: March 2026
QCAL ∞³ Active
"""

import math
import sys
from pathlib import Path

import numpy as np
import pytest

# Ensure repository root is importable
sys.path.insert(0, str(Path(__file__).parent.parent))

from operators.regularizacion_kairos import (  # noqa: E402
    C_ABEL,
    F0,
    PHI,
    SIGMA_DEFAULT,
    TWO_PI,
    PotencialRegularizado,
    estudio_limite_sigma,
    regularizar_potencial_soberano,
)


# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

class TestConstants:
    """Verify module-level physical and mathematical constants."""

    def test_two_pi(self):
        assert abs(TWO_PI - 2.0 * math.pi) < 1e-12

    def test_c_abel(self):
        expected = 1.0 - 2.0 * math.log(2.0)
        assert abs(C_ABEL - expected) < 1e-12

    def test_f0(self):
        assert F0 == 141.7001

    def test_sigma_default(self):
        assert SIGMA_DEFAULT > 0

    def test_phi(self):
        assert abs(PHI - 1.618033988749895) < 1e-12


# ---------------------------------------------------------------------------
# Initialization & validation
# ---------------------------------------------------------------------------

class TestPotencialRegularizadoInit:
    """Test construction of PotencialRegularizado."""

    def test_default_construction(self):
        pot = PotencialRegularizado(num_primos=20, sigma=0.1, N=50)
        assert pot.num_primos == 20
        assert pot.sigma == 0.1
        assert pot.N == 50
        assert len(pot.x_grid) == 50

    def test_grid_spacing(self):
        pot = PotencialRegularizado(num_primos=10, sigma=0.1, x_max=10.0, N=100)
        assert abs(pot.h - 10.0 / 101) < 1e-12

    def test_primes_generated(self):
        pot = PotencialRegularizado(num_primos=10, sigma=0.1, N=50)
        assert len(pot.primos) == 10
        assert pot.primos[0] == 2.0
        assert pot.primos[1] == 3.0
        assert pot.primos[2] == 5.0

    def test_zero_primos(self):
        """When num_primos=0, V_osc should be zero everywhere."""
        pot = PotencialRegularizado(num_primos=0, sigma=0.1, N=50)
        assert np.allclose(pot.V_osc_vals, 0.0)

    def test_invalid_sigma_raises(self):
        with pytest.raises(ValueError):
            PotencialRegularizado(num_primos=10, sigma=0.0, N=50)

    def test_invalid_sigma_negative_raises(self):
        with pytest.raises(ValueError):
            PotencialRegularizado(num_primos=10, sigma=-0.1, N=50)

    def test_invalid_N_raises(self):
        with pytest.raises(ValueError):
            PotencialRegularizado(num_primos=10, sigma=0.1, N=0)

    def test_invalid_x_max_raises(self):
        with pytest.raises(ValueError):
            PotencialRegularizado(num_primos=10, sigma=0.1, x_max=0.0, N=50)

    def test_invalid_num_primos_raises(self):
        with pytest.raises(ValueError):
            PotencialRegularizado(num_primos=-1, sigma=0.1, N=50)

    def test_maslov_phases(self):
        pot = PotencialRegularizado(num_primos=5, sigma=0.1, fase_phi="maslov", N=10)
        assert np.allclose(pot.fases, -math.pi / 4)

    def test_cero_phases(self):
        pot = PotencialRegularizado(num_primos=5, sigma=0.1, fase_phi="cero", N=10)
        assert np.allclose(pot.fases, 0.0)

    def test_densidad_phases_shape(self):
        pot = PotencialRegularizado(num_primos=5, sigma=0.1, fase_phi="densidad", N=10)
        assert pot.fases.shape == (5,)

    def test_unknown_fase_defaults_to_zero(self):
        pot = PotencialRegularizado(num_primos=5, sigma=0.1, fase_phi="unknown", N=10)
        assert np.allclose(pot.fases, 0.0)


# ---------------------------------------------------------------------------
# Exponential cutoff factor
# ---------------------------------------------------------------------------

class TestExponentialCutoff:
    """Verify properties of the exponential cutoff exp(-σ(log p)²)."""

    def test_cutoff_positive(self):
        pot = PotencialRegularizado(num_primos=50, sigma=0.1, N=50)
        assert np.all(pot.factor_corte > 0)

    def test_cutoff_at_most_one(self):
        pot = PotencialRegularizado(num_primos=50, sigma=0.1, N=50)
        assert np.all(pot.factor_corte <= 1.0)

    def test_cutoff_decreasing_in_p(self):
        """Larger primes should have smaller cutoff factors."""
        pot = PotencialRegularizado(num_primos=50, sigma=0.1, N=50)
        # The cutoff exp(-σ(log p)²) is monotone decreasing in p
        assert np.all(np.diff(pot.factor_corte) <= 0)

    def test_larger_sigma_smaller_cutoff(self):
        """A larger σ should suppress higher primes more aggressively."""
        pot1 = PotencialRegularizado(num_primos=50, sigma=0.01, N=50)
        pot2 = PotencialRegularizado(num_primos=50, sigma=0.1, N=50)
        # For large primes, pot2.factor_corte < pot1.factor_corte
        assert np.all(pot2.factor_corte[10:] <= pot1.factor_corte[10:])

    def test_sigma_limit_identity(self):
        """As σ → 0, factor_corte → 1 for every prime."""
        pot = PotencialRegularizado(num_primos=10, sigma=1e-8, N=20)
        assert np.allclose(pot.factor_corte, 1.0, atol=1e-5)


# ---------------------------------------------------------------------------
# Absolute convergence
# ---------------------------------------------------------------------------

class TestAbsoluteConvergence:
    """Verify that the regularized series converges absolutely."""

    def test_suma_corte_absoluta_finite(self):
        pot = PotencialRegularizado(num_primos=200, sigma=0.01, N=50)
        S = pot.suma_corte_absoluta()
        assert math.isfinite(S)
        assert S > 0

    def test_suma_corte_decreases_with_sigma(self):
        """Larger σ → smaller absolute sum (more suppression)."""
        S1 = PotencialRegularizado(num_primos=100, sigma=0.01, N=50).suma_corte_absoluta()
        S2 = PotencialRegularizado(num_primos=100, sigma=0.1, N=50).suma_corte_absoluta()
        assert S2 < S1

    def test_v_osc_bounded_by_sum(self):
        """The pointwise absolute value of V_osc^σ ≤ Σ (log p)/√p · exp(-σ(log p)²)."""
        pot = PotencialRegularizado(num_primos=100, sigma=0.05, N=200)
        S = pot.suma_corte_absoluta()
        assert np.all(np.abs(pot.V_osc_vals) <= S + 1e-10)

    def test_zero_primos_sum_zero(self):
        pot = PotencialRegularizado(num_primos=0, sigma=0.1, N=20)
        assert pot.suma_corte_absoluta() == 0.0


# ---------------------------------------------------------------------------
# L²_loc membership
# ---------------------------------------------------------------------------

class TestL2locMembership:
    """Verify that V_osc^σ belongs to L²_loc(ℝ)."""

    def test_l2_norm_finite(self):
        pot = PotencialRegularizado(num_primos=100, sigma=0.05, N=200)
        norma = pot.norma_L2_acotada(R=10.0)
        assert math.isfinite(norma)
        assert norma >= 0

    def test_l2_norm_non_negative(self):
        pot = PotencialRegularizado(num_primos=50, sigma=0.1, N=100)
        assert pot.norma_L2_local((0.0, pot.x_max)) >= 0.0

    def test_l2_norm_increases_with_interval(self):
        """Norm over a larger interval should be ≥ norm over a smaller one."""
        pot = PotencialRegularizado(num_primos=100, sigma=0.05, N=500)
        n5 = pot.norma_L2_local((0.0, 5.0))
        n10 = pot.norma_L2_local((0.0, 10.0))
        assert n10 >= n5

    def test_l2_norm_l2loc_bound(self):
        """‖V_osc^σ‖_{L²(K)} ≤ √|K| · Σ (log p)/√p · exp(-σ(log p)²)."""
        pot = PotencialRegularizado(num_primos=100, sigma=0.1, N=200)
        R = 10.0
        S = pot.suma_corte_absoluta()
        norma = pot.norma_L2_acotada(R)
        # |K| = 2R (but our domain is [0, x_max], so |K| ≤ x_max)
        upper = math.sqrt(pot.x_max) * S
        assert norma <= upper + 1e-6

    def test_empty_interval_returns_zero(self):
        pot = PotencialRegularizado(num_primos=20, sigma=0.1, N=100)
        # Interval outside the grid
        norma = pot.norma_L2_local((1000.0, 2000.0))
        assert norma == 0.0


# ---------------------------------------------------------------------------
# Kato-Rellich self-adjointness
# ---------------------------------------------------------------------------

class TestKatoRellich:
    """Verify Kato-Rellich self-adjointness conditions."""

    def test_autoadjoint_returns_true(self):
        pot = PotencialRegularizado(num_primos=50, sigma=0.05, N=100)
        result = pot.estimacion_autoadjunta()
        assert result["autoadjunto"] is True

    def test_kato_condition_a_lt_1(self):
        pot = PotencialRegularizado(num_primos=50, sigma=0.05, N=100)
        result = pot.estimacion_autoadjunta()
        assert result["condicion_kato"] is True
        assert result["a_constante"] < 1.0

    def test_a_is_zero_for_bounded_potential(self):
        """For a bounded V, the Kato constant a must be 0."""
        pot = PotencialRegularizado(num_primos=50, sigma=0.05, N=100)
        result = pot.estimacion_autoadjunta()
        assert result["a_constante"] == 0.0

    def test_b_equals_v_max(self):
        pot = PotencialRegularizado(num_primos=50, sigma=0.05, N=100)
        result = pot.estimacion_autoadjunta()
        v_max_direct = float(np.max(np.abs(pot.V_osc_vals)))
        assert abs(result["b_constante"] - v_max_direct) < 1e-10

    def test_v_max_finite(self):
        pot = PotencialRegularizado(num_primos=200, sigma=0.01, N=100)
        result = pot.estimacion_autoadjunta()
        assert math.isfinite(result["V_max"])

    def test_v_max_bounded_by_absolute_sum(self):
        """‖V_osc^σ‖_∞ ≤ Σ (log p)/√p · exp(-σ(log p)²)."""
        pot = PotencialRegularizado(num_primos=100, sigma=0.05, N=100)
        result = pot.estimacion_autoadjunta()
        S = pot.suma_corte_absoluta()
        assert result["V_max"] <= S + 1e-10


# ---------------------------------------------------------------------------
# Matrix construction and eigenvalues
# ---------------------------------------------------------------------------

class TestMatrixAndEigenvalues:
    """Test finite-difference matrix and spectral computation."""

    def test_matrix_shape(self):
        N = 50
        pot = PotencialRegularizado(num_primos=20, sigma=0.1, N=N)
        H = pot.construir_matriz()
        assert H.shape == (N, N)

    def test_matrix_symmetric(self):
        N = 30
        pot = PotencialRegularizado(num_primos=10, sigma=0.1, N=N)
        H = pot.construir_matriz()
        diff = (H - H.T).toarray()
        assert np.allclose(diff, 0.0, atol=1e-12)

    def test_eigenvalues_real(self):
        pot = PotencialRegularizado(num_primos=20, sigma=0.1, N=50)
        evals = pot.calcular_autovalores(k=5)
        assert np.all(np.isreal(evals))

    def test_eigenvalues_positive(self):
        """Eigenvalues of H_σ should be positive (V_smooth dominates at large x)."""
        pot = PotencialRegularizado(num_primos=20, sigma=0.1, N=100)
        evals = pot.calcular_autovalores(k=5)
        assert np.all(evals > 0)

    def test_eigenvalues_sorted(self):
        pot = PotencialRegularizado(num_primos=20, sigma=0.1, N=100)
        evals = pot.calcular_autovalores(k=10)
        assert np.all(np.diff(evals) >= 0)

    def test_heat_trace_positive(self):
        pot = PotencialRegularizado(num_primos=20, sigma=0.1, N=100)
        tr = pot.traza_calor(t=0.1, n_max=10)
        assert tr > 0

    def test_heat_trace_decreasing_in_t(self):
        """Tr(e^{-tH}) should be decreasing in t for t > 0."""
        pot = PotencialRegularizado(num_primos=20, sigma=0.1, N=100)
        tr1 = pot.traza_calor(t=0.05, n_max=10)
        tr2 = pot.traza_calor(t=0.1, n_max=10)
        assert tr1 >= tr2


# ---------------------------------------------------------------------------
# V_smooth (Wu-Sprung)
# ---------------------------------------------------------------------------

class TestVSmooth:
    """Test the smooth Wu-Sprung potential."""

    def test_v_smooth_non_negative(self):
        pot = PotencialRegularizado(num_primos=10, sigma=0.1, N=100)
        assert np.all(pot.V_smooth_vals >= 0)

    def test_v_smooth_increasing(self):
        """V_smooth should be monotone non-decreasing (it grows with x)."""
        pot = PotencialRegularizado(num_primos=10, sigma=0.1, N=200)
        assert np.all(np.diff(pot.V_smooth_vals) >= 0)

    def test_v_smooth_at_origin(self):
        """V_smooth(x → 0) ≈ 9.25 (minimum of the Wu-Sprung potential)."""
        pot = PotencialRegularizado(num_primos=5, sigma=0.1, N=100)
        # First grid point is close to 0
        assert pot.V_smooth_vals[0] >= 9.2


# ---------------------------------------------------------------------------
# regularizar_potencial_soberano
# ---------------------------------------------------------------------------

class TestRegularizarPotencialSoberano:
    """Integration test for the main regularization function."""

    def test_returns_dict(self):
        result = regularizar_potencial_soberano(
            sigma=0.1, num_primos=50, x_max=10.0, N=100, verbose=False
        )
        assert isinstance(result, dict)

    def test_required_keys(self):
        result = regularizar_potencial_soberano(
            sigma=0.1, num_primos=50, x_max=10.0, N=100, verbose=False
        )
        for key in [
            "sigma",
            "num_primos",
            "norma_L2_R10",
            "norma_L2_R20",
            "autoadjunto",
            "V_max",
            "trazas_calor",
            "autovalores",
            "sello",
        ]:
            assert key in result, f"Missing key: {key}"

    def test_sello(self):
        result = regularizar_potencial_soberano(
            sigma=0.1, num_primos=50, x_max=10.0, N=100, verbose=False
        )
        assert result["sello"] == "∴𓂀Ω∞³Φ"

    def test_autoadjunto(self):
        result = regularizar_potencial_soberano(
            sigma=0.1, num_primos=50, x_max=10.0, N=100, verbose=False
        )
        assert result["autoadjunto"] is True

    def test_normas_finite(self):
        result = regularizar_potencial_soberano(
            sigma=0.1, num_primos=50, x_max=10.0, N=100, verbose=False
        )
        assert math.isfinite(result["norma_L2_R10"])
        assert math.isfinite(result["norma_L2_R20"])

    def test_eigenvalues_list(self):
        result = regularizar_potencial_soberano(
            sigma=0.1, num_primos=50, x_max=10.0, N=100, verbose=False
        )
        assert isinstance(result["autovalores"], list)
        assert len(result["autovalores"]) == 10

    def test_heat_traces_keys(self):
        result = regularizar_potencial_soberano(
            sigma=0.1, num_primos=50, x_max=10.0, N=100, verbose=False
        )
        for t in [0.1, 0.05, 0.01]:
            assert t in result["trazas_calor"]


# ---------------------------------------------------------------------------
# estudio_limite_sigma
# ---------------------------------------------------------------------------

class TestEstudioLimiteSigma:
    """Test the σ → 0 limit study function."""

    def test_returns_dict(self):
        result = estudio_limite_sigma(
            lista_sigma=[0.1, 0.01], num_primos=50, verbose=False
        )
        assert isinstance(result, dict)

    def test_keys_are_sigma_values(self):
        sigmas = [0.1, 0.01]
        result = estudio_limite_sigma(
            lista_sigma=sigmas, num_primos=50, verbose=False
        )
        for s in sigmas:
            assert s in result

    def test_sub_dict_keys(self):
        result = estudio_limite_sigma(
            lista_sigma=[0.1], num_primos=50, verbose=False
        )
        sub = result[0.1]
        assert "norma_L2_R10" in sub
        assert "V_max" in sub
        assert "autoadjunto" in sub

    def test_v_max_increases_as_sigma_decreases(self):
        """Smaller σ means less suppression → larger V_max."""
        result = estudio_limite_sigma(
            lista_sigma=[0.5, 0.1, 0.01], num_primos=100, verbose=False
        )
        assert result[0.1]["V_max"] >= result[0.5]["V_max"]
        assert result[0.01]["V_max"] >= result[0.1]["V_max"]

    def test_default_sigmas(self):
        result = estudio_limite_sigma(num_primos=50, verbose=False)
        assert len(result) == 5
