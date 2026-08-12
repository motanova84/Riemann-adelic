#!/usr/bin/env python3
"""
Tests for simulate_espectral_completo - Spectral Simulation Module.

Validates:
1. Prime generation via Sieve of Eratosthenes
2. Phase strategies (maslov, cero, densidad, optimizada)
3. Wu-Sprung potential inversion (V_smooth)
4. Oscillatory potential (V_osc)
5. Hamiltonian matrix construction
6. Eigenvalue computation
7. Comparison with Riemann zeros
8. Spectral rigidity calculation
9. Full simulation pipeline
"""

import pytest
import numpy as np
import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from simulate_espectral_completo import (
    PotencialEspectralCompleto,
    ResultadoSimulacion,
    simular_ceros_riemann,
    TWO_PI,
    C_ABEL,
    F0,
    F_AMOR,
    PHI,
    V_MIN,
)


# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

FLOAT_TOL = 1e-10


# ---------------------------------------------------------------------------
# TestConstants
# ---------------------------------------------------------------------------

class TestConstants:
    """Test module-level physical and numerical constants."""

    def test_two_pi(self):
        assert abs(TWO_PI - 2.0 * math.pi) < FLOAT_TOL

    def test_c_abel(self):
        expected = 1.0 - 2.0 * math.log(2.0)
        assert abs(C_ABEL - expected) < FLOAT_TOL

    def test_f0_frequency(self):
        assert F0 == 141.7001

    def test_f_amor_frequency(self):
        assert F_AMOR == 888.0

    def test_phi_golden_ratio(self):
        assert abs(PHI - 1.618033988749895) < FLOAT_TOL

    def test_v_min_constant(self):
        assert V_MIN == 9.25


# ---------------------------------------------------------------------------
# TestPrimeGeneration
# ---------------------------------------------------------------------------

class TestPrimeGeneration:
    """Test Sieve of Eratosthenes prime generation."""

    def setup_method(self):
        # Use small N to keep tests fast
        self.pot = PotencialEspectralCompleto(x_max=5.0, N=50, num_primos=10)

    def test_correct_count(self):
        primos = self.pot._generar_primos(10)
        assert len(primos) == 10

    def test_first_primes(self):
        primos = self.pot._generar_primos(5)
        np.testing.assert_array_equal(primos, [2, 3, 5, 7, 11])

    def test_zero_primes(self):
        primos = self.pot._generar_primos(0)
        assert len(primos) == 0

    def test_primes_are_positive(self):
        primos = self.pot._generar_primos(20)
        assert np.all(primos > 0)

    def test_primes_are_integer_values(self):
        primos = self.pot._generar_primos(20)
        assert np.all(primos == np.floor(primos))


# ---------------------------------------------------------------------------
# TestPhaseStrategies
# ---------------------------------------------------------------------------

class TestPhaseStrategies:
    """Test phase calculation strategies."""

    def _make_pot(self, fase_phi):
        return PotencialEspectralCompleto(
            x_max=5.0, N=50, num_primos=5, fase_phi=fase_phi
        )

    def test_maslov_phase(self):
        pot = self._make_pot("maslov")
        expected = -math.pi / 4
        assert np.allclose(pot.fases, expected)

    def test_cero_phase(self):
        pot = self._make_pot("cero")
        assert np.allclose(pot.fases, 0.0)

    def test_densidad_phase_shape(self):
        pot = self._make_pot("densidad")
        assert pot.fases.shape == (5,)

    def test_optimizada_phase_range(self):
        pot = self._make_pot("optimizada")
        assert np.all(pot.fases >= -math.pi)
        assert np.all(pot.fases <= math.pi)

    def test_unknown_phase_raises(self):
        with pytest.raises(ValueError):
            PotencialEspectralCompleto(
                x_max=5.0, N=50, num_primos=5, fase_phi="unknown_strategy"
            )


# ---------------------------------------------------------------------------
# TestVSmooth
# ---------------------------------------------------------------------------

class TestVSmooth:
    """Test Wu-Sprung smooth potential."""

    def setup_method(self):
        self.pot = PotencialEspectralCompleto(x_max=5.0, N=100, num_primos=5)

    def test_v_of_x_zero(self):
        """V(0) should return just above V_MIN."""
        v = self.pot._V_of_x(0.0)
        assert v >= V_MIN

    def test_v_smooth_shape(self):
        assert self.pot.V_smooth_vals.shape == (100,)

    def test_v_smooth_increasing(self):
        """V_smooth should be approximately non-decreasing (Wu-Sprung is monotone)."""
        diffs = np.diff(self.pot.V_smooth_vals)
        assert np.all(diffs >= -1e-6), "V_smooth should be approximately non-decreasing"

    def test_x_of_v_below_vmin(self):
        """x(V) for V <= 9.25 should return 0."""
        x = self.pot._x_of_V(9.0)
        assert x == 0.0

    def test_x_of_v_positive(self):
        x = self.pot._x_of_V(100.0)
        assert x > 0


# ---------------------------------------------------------------------------
# TestVOsc
# ---------------------------------------------------------------------------

class TestVOsc:
    """Test oscillatory prime potential."""

    def test_v_osc_shape(self):
        pot = PotencialEspectralCompleto(x_max=5.0, N=50, num_primos=5)
        assert pot.V_osc_vals.shape == (50,)

    def test_v_osc_zero_primes(self):
        pot = PotencialEspectralCompleto(x_max=5.0, N=50, num_primos=0)
        assert np.allclose(pot.V_osc_vals, 0.0)

    def test_v_osc_no_phases(self):
        pot = PotencialEspectralCompleto(
            x_max=5.0, N=50, num_primos=5, incluir_fases=False
        )
        assert pot.V_osc_vals.shape == (50,)

    def test_v_total_equals_sum(self):
        pot = PotencialEspectralCompleto(x_max=5.0, N=50, num_primos=5)
        np.testing.assert_allclose(
            pot.V_total_vals,
            pot.V_smooth_vals + pot.V_osc_vals,
        )


# ---------------------------------------------------------------------------
# TestMatrixConstruction
# ---------------------------------------------------------------------------

class TestMatrixConstruction:
    """Test Hamiltonian matrix construction."""

    def setup_method(self):
        self.pot = PotencialEspectralCompleto(x_max=5.0, N=50, num_primos=5)

    def test_matrix_shape(self):
        H = self.pot.construir_matriz()
        assert H.shape == (50, 50)

    def test_matrix_symmetric(self):
        H = self.pot.construir_matriz()
        diff = H - H.T
        assert abs(diff).max() < 1e-12

    def test_matrix_sparse(self):
        from scipy.sparse import issparse
        H = self.pot.construir_matriz()
        assert issparse(H)

    def test_diagonal_positive(self):
        H = self.pot.construir_matriz()
        diag = H.diagonal()
        assert np.all(diag > 0)


# ---------------------------------------------------------------------------
# TestEigenvalues
# ---------------------------------------------------------------------------

class TestEigenvalues:
    """Test eigenvalue computation."""

    def setup_method(self):
        self.pot = PotencialEspectralCompleto(x_max=5.0, N=100, num_primos=5)

    def test_eigenvalues_sorted(self):
        evals = self.pot.calcular_autovalores(k=5)
        assert np.all(np.diff(evals) >= 0)

    def test_eigenvalues_count(self):
        evals = self.pot.calcular_autovalores(k=5)
        assert len(evals) == 5

    def test_eigenvalues_positive(self):
        evals = self.pot.calcular_autovalores(k=5)
        assert np.all(evals > 0)


# ---------------------------------------------------------------------------
# TestSpectralRigidity
# ---------------------------------------------------------------------------

class TestSpectralRigidity:
    """Test spectral rigidity calculation."""

    def setup_method(self):
        self.pot = PotencialEspectralCompleto(x_max=5.0, N=50, num_primos=5)

    def test_rigidity_too_few_evals(self):
        evals = np.array([1.0, 2.0, 3.0])  # fewer than 10
        rigidity = self.pot.rigidez_espectral(evals)
        assert rigidity == 0.0

    def test_rigidity_non_negative(self):
        evals = np.linspace(1.0, 50.0, 20)
        rigidity = self.pot.rigidez_espectral(evals)
        assert rigidity >= 0.0

    def test_rigidity_uniform_spacing(self):
        """Uniformly spaced eigenvalues → variance 0."""
        evals = np.linspace(1.0, 100.0, 20)
        rigidity = self.pot.rigidez_espectral(evals)
        assert rigidity < 1e-10


# ---------------------------------------------------------------------------
# TestComparacionCeros
# ---------------------------------------------------------------------------

class TestComparacionCeros:
    """Test comparison with Riemann zeros."""

    def setup_method(self):
        self.pot = PotencialEspectralCompleto(x_max=5.0, N=100, num_primos=5)

    def test_comparison_keys(self):
        evals = np.linspace(14.0, 80.0, 20)
        result = self.pot.comparar_con_ceros(evals)
        for key in ["error_medio", "error_max", "correlacion", "rigidez_espectral",
                    "autovalores", "ceros_referencia", "errores_abs",
                    "n_comparados", "fase_phi"]:
            assert key in result

    def test_error_medio_non_negative(self):
        evals = np.linspace(14.0, 80.0, 20)
        result = self.pot.comparar_con_ceros(evals)
        assert result["error_medio"] >= 0.0

    def test_correlacion_range(self):
        evals = np.linspace(14.0, 80.0, 20)
        result = self.pot.comparar_con_ceros(evals)
        assert -1.0 <= result["correlacion"] <= 1.0

    def test_custom_zeros_reference(self):
        evals = np.array([14.13, 21.02])
        ceros = [14.134725, 21.022039]
        result = self.pot.comparar_con_ceros(evals, ceros_ref=ceros)
        assert result["n_comparados"] == 2

    def test_errores_shape(self):
        evals = np.linspace(14.0, 50.0, 10)
        result = self.pot.comparar_con_ceros(evals)
        assert len(result["errores_abs"]) == result["n_comparados"]


# ---------------------------------------------------------------------------
# TestSimulacion (integration, small parameters)
# ---------------------------------------------------------------------------

class TestSimulacion:
    """Integration tests for the full simulation pipeline."""

    @pytest.mark.slow
    def test_simular_returns_resultado(self):
        pot = PotencialEspectralCompleto(x_max=5.0, N=100, num_primos=5)
        resultado = pot.simular(k=5, verbose=False)
        assert isinstance(resultado, ResultadoSimulacion)

    @pytest.mark.slow
    def test_simular_sello(self):
        pot = PotencialEspectralCompleto(x_max=5.0, N=100, num_primos=5)
        resultado = pot.simular(k=5, verbose=False)
        assert resultado.sello == "∴𓂀Ω∞³Φ"

    @pytest.mark.slow
    def test_simular_num_primos_usados(self):
        pot = PotencialEspectralCompleto(x_max=5.0, N=100, num_primos=5)
        resultado = pot.simular(k=5, verbose=False)
        assert resultado.num_primos_usados == 5

    @pytest.mark.slow
    def test_simular_tiempo_positivo(self):
        pot = PotencialEspectralCompleto(x_max=5.0, N=100, num_primos=5)
        resultado = pot.simular(k=5, verbose=False)
        assert resultado.tiempo_calculo >= 0.0

    @pytest.mark.slow
    def test_simular_ceros_riemann_small(self):
        resultado = simular_ceros_riemann(
            num_primos=5,
            N=100,
            x_max=5.0,
            k=5,
            fase_phi="maslov",
            verbose=False,
        )
        assert isinstance(resultado, ResultadoSimulacion)
        assert resultado.error_medio >= 0.0
        assert resultado.num_primos_usados == 5
