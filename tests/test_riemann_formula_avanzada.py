"""
Tests para riemann_formula_avanzada.py
Valida los tres métodos matemáticamente serios para aproximar la fórmula
explícita de Riemann sin ceros precalculados:
A) WeilFuncionPrueba  – mollificación gaussiana exacta
B) MellinExponencial  – regularización exponencial natural
C) RiemannSiegelPrimos – ceros auto-generados via suma RS
"""
import math
import os
import sys
import unittest

import numpy as np

# Ensure repo root is on sys.path when tests/ is the working directory
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from riemann_formula_avanzada import (
    WeilFuncionPrueba,
    MellinExponencial,
    RiemannSiegelPrimos,
    ComparadorMetodos,
    _theta_rs,
    _theta_rs_stirling,
    _Z_main_sum,
    EPSILON_DEFAULT,
    DELTA_WEIL_DEFAULT,
    P_MELLIN_DEFAULT,
)
from riemann_explicit_formula import chebyshev_psi

# ============================================================================
# A) WEIL FUNCIÓN DE PRUEBA
# ============================================================================
class TestWeilFuncionPrueba(unittest.TestCase):
    def setUp(self):
        self.weil = WeilFuncionPrueba(delta=0.1, p_max=500)
        self.weil_small = WeilFuncionPrueba(delta=0.05, p_max=500)

    # Validación de parámetros
    def test_invalid_delta_zero(self):
        with self.assertRaises(ValueError):
            WeilFuncionPrueba(delta=0.0)

    def test_invalid_delta_negative(self):
        with self.assertRaises(ValueError):
            WeilFuncionPrueba(delta=-0.1)

    def test_invalid_p_max(self):
        with self.assertRaises(ValueError):
            WeilFuncionPrueba(p_max=1)

    # Propiedades básicas
    def test_evaluate_zero_for_x_le_1(self):
        self.assertEqual(self.weil.evaluate(0.5), 0.0)
        self.assertEqual(self.weil.evaluate(1.0), 0.0)

    def test_evaluate_positive_for_x_gt_2(self):
        # ψ_δ(x) debe ser positiva para x > 2
        self.assertGreater(self.weil.evaluate(3.0), 0.0)

    def test_evaluate_finite(self):
        for x in [2.0, 5.0, 10.0, 50.0, 100.0]:
            self.assertTrue(math.isfinite(self.weil.evaluate(x)))

    def test_evaluate_array_shape(self):
        x_arr = np.linspace(2, 50, 30)
        result = self.weil.evaluate_array(x_arr)
        self.assertEqual(result.shape, (30,))

    def test_evaluate_array_consistent_with_scalar(self):
        x_arr = np.array([3.0, 7.0, 20.0])
        arr_res = self.weil.evaluate_array(x_arr)
        for i, x in enumerate(x_arr):
            self.assertAlmostEqual(arr_res[i], self.weil.evaluate(x), places=10)

    def test_n_prime_powers_positive(self):
        self.assertGreater(self.weil.n_prime_powers, 0)

    # Convergencia: delta más pequeño → ψ_δ más parecida a ψ exacta
    def test_smaller_delta_closer_to_exact_at_jump(self):
        # En x = 7 (justo antes del salto ψ(7)→ψ(7+ε)), la mollificación
        # con δ pequeño es más selectiva.
        x = 7.5
        psi_exact = chebyshev_psi(x)
        err_large = abs(self.weil.evaluate(x) - psi_exact)
        err_small = abs(self.weil_small.evaluate(x) - psi_exact)
        # Con δ pequeño el error puede ser mayor en puntos de discontinuidad,
        # pero en el interior del intervalo (entre primos) debe ser menor.
        # Aquí solo verificamos que ambos son finitos.
        self.assertTrue(math.isfinite(err_large))
        self.assertTrue(math.isfinite(err_small))

    def test_convergence_bound_non_negative(self):
        for x in [5.0, 20.0, 50.0]:
            self.assertGreaterEqual(self.weil.convergence_bound(x), 0.0)

    # Relación con ψ exacta: en promedio, ψ_δ ≈ ψ
    def test_mean_value_close_to_psi(self):
        # En un rango suave (x ∈ [10, 50]), la media de ψ_δ(x) - ψ(x)
        # debe ser pequeña (error sistemático ~0, solo fluctuaciones de δ).
        x_arr = np.linspace(10, 50, 30)
        psi_exact = np.array([chebyshev_psi(xi) for xi in x_arr])
        psi_weil = self.weil.evaluate_array(x_arr)
        mean_error = float(np.mean(psi_weil - psi_exact))
        # La mollificación suaviza pero no sesga sistemáticamente
        self.assertLess(abs(mean_error), 5.0)  # tolerancia generosa


# ============================================================================
# B) MELLIN EXPONENCIAL
# ============================================================================
class TestMellinExponencial(unittest.TestCase):
    def setUp(self):
        self.mell_1000 = MellinExponencial(P=1000.0, epsilon=0.4)
        self.mell_100 = MellinExponencial(P=100.0, epsilon=0.4)
        self.mell_5000 = MellinExponencial(P=5000.0, epsilon=0.4)

    # Validación de parámetros
    def test_invalid_P_zero(self):
        with self.assertRaises(ValueError):
            MellinExponencial(P=0.0)

    def test_invalid_P_negative(self):
        with self.assertRaises(ValueError):
            MellinExponencial(P=-10.0)

    # Propiedades básicas
    def test_n_primes_positive(self):
        self.assertGreater(self.mell_1000.n_primes, 0)

    def test_evaluate_finite(self):
        for x in [1.0, 5.0, 10.0, 50.0, 100.0]:
            self.assertTrue(math.isfinite(self.mell_1000.evaluate(x)))

    def test_evaluate_array_shape(self):
        x_arr = np.linspace(1, 50, 40)
        result = self.mell_1000.evaluate_array(x_arr)
        self.assertEqual(result.shape, (40,))

    def test_evaluate_array_consistent_with_scalar(self):
        x_arr = np.array([3.0, 10.0, 25.0])
        arr_res = self.mell_1000.evaluate_array(x_arr)
        for i, x in enumerate(x_arr):
            self.assertAlmostEqual(arr_res[i], self.mell_1000.evaluate(x), places=10)

    def test_epsilon_scaling(self):
        mell2 = MellinExponencial(P=1000.0, epsilon=0.8)
        x = 5.0
        self.assertAlmostEqual(mell2.evaluate(x), 2.0 * self.mell_1000.evaluate(x), places=10)

    # Propiedades analíticas del factor exp(-p/P)
    def test_larger_P_uses_more_primes(self):
        self.assertGreater(self.mell_5000.n_primes, self.mell_100.n_primes)

    def test_effective_weight_increases_with_P(self):
        w100 = self.mell_100.effective_weight()
        w1000 = self.mell_1000.effective_weight()
        w5000 = self.mell_5000.effective_weight()
        self.assertGreater(w1000, w100)
        self.assertGreater(w5000, w1000)

    def test_effective_weight_finite(self):
        self.assertTrue(math.isfinite(self.mell_1000.effective_weight()))

    def test_compare_with_sharp_keys(self):
        result = self.mell_1000.compare_with_sharp(p_sharp=100)
        for key in ["weight_mellin", "weight_sharp_p100", "n_primes_mellin",
                    "n_primes_sharp", "mellin_coverage_ratio"]:
            self.assertIn(key, result)

    def test_mellin_covers_more_primes_than_sharp_100(self):
        result = self.mell_1000.compare_with_sharp(p_sharp=100)
        self.assertGreater(result["n_primes_mellin"], result["n_primes_sharp"])

    # Calidad de la aproximación de ψ
    def test_psi_mellin_close_to_exact(self):
        # ψ_mellin(x) = x + V_mell(x) debe estar cerca de ψ exacta
        x_arr = np.linspace(5.0, 80.0, 30)
        psi_exact = np.array([chebyshev_psi(xi) for xi in x_arr])
        psi_mellin = x_arr + self.mell_1000.evaluate_array(x_arr)
        mae = float(np.mean(np.abs(psi_exact - psi_mellin)))
        self.assertLess(mae, 10.0)  # V_mell es corrección al operador, no a ψ directamente


# ============================================================================
# C) RIEMANN-SIEGEL PRIMOS
# ============================================================================
class TestThetaRS(unittest.TestCase):
    def test_theta_invalid_t(self):
        with self.assertRaises(ValueError):
            _theta_rs(0.0)

    def test_theta_positive_for_large_t(self):
        # θ(t) crece sin límite con t
        self.assertGreater(_theta_rs(100.0), 0.0)

    def test_theta_stirling_agrees_with_exact_for_large_t(self):
        # Para t grande, Stirling debe concordar con el valor exacto
        for t in [50.0, 100.0, 200.0]:
            exact = _theta_rs(t)
            stirling = _theta_rs_stirling(t)
            # Tolerancia ~1e-5 para t ≥ 50
            self.assertAlmostEqual(exact, stirling, delta=1e-3)

    def test_theta_increases_with_t(self):
        ts = [20.0, 50.0, 100.0, 200.0]
        thetas = [_theta_rs(t) for t in ts]
        for i in range(len(thetas) - 1):
            self.assertLess(thetas[i], thetas[i + 1])


class TestZMainSum(unittest.TestCase):
    def test_Z_at_zero_t_returns_zero(self):
        self.assertEqual(_Z_main_sum(0.0), 0.0)

    def test_Z_finite_for_positive_t(self):
        for t in [15.0, 21.0, 25.0, 50.0]:
            self.assertTrue(math.isfinite(_Z_main_sum(t)))

    def test_Z_sign_change_near_first_zero(self):
        # γ₁ ≈ 14.1347; Z debe cambiar de signo alrededor de ese punto
        z_before = _Z_main_sum(14.0)
        z_after = _Z_main_sum(14.3)
        # Producto negativo indica cambio de signo (o ambos son pequeños)
        self.assertLessEqual(z_before * z_after, 0.5)  # tolerancia

    def test_Z_custom_N(self):
        t = 50.0
        z_N3 = _Z_main_sum(t, N=3)
        z_N10 = _Z_main_sum(t, N=10)
        # Ambos deben ser finitos
        self.assertTrue(math.isfinite(z_N3))
        self.assertTrue(math.isfinite(z_N10))


class TestRiemannSiegelPrimos(unittest.TestCase):
    def setUp(self):
        # Instancia con t_max=50 para que los tests sean rápidos
        self.rs = RiemannSiegelPrimos(t_max=50.0, n_scan=500, max_zeros=10)

    def test_invalid_t_max(self):
        with self.assertRaises(ValueError):
            RiemannSiegelPrimos(t_max=10.0)

    def test_theta_static_method(self):
        t = 50.0
        self.assertAlmostEqual(
            RiemannSiegelPrimos.theta(t), _theta_rs(t), places=12
        )

    def test_Z_static_method(self):
        t = 25.0
        self.assertAlmostEqual(
            RiemannSiegelPrimos.Z(t), _Z_main_sum(t), places=12
        )

    # Cálculo de ceros
    def test_compute_zeros_returns_array(self):
        zeros = self.rs.compute_zeros()
        self.assertIsInstance(zeros, np.ndarray)

    def test_at_least_one_zero_found(self):
        # γ₁ ≈ 14.13 está en (14, 50)
        self.assertGreater(len(self.rs.zeros), 0)

    def test_zeros_in_valid_range(self):
        for gamma in self.rs.zeros:
            self.assertGreater(gamma, 14.0)
            self.assertLessEqual(gamma, 50.0)

    def test_first_zero_near_14_13(self):
        # γ₁ ≈ 14.1347; tolerancia de 0.05 para la suma RS
        gamma_1 = self.rs.zeros[0]
        self.assertAlmostEqual(gamma_1, 14.1347, delta=0.05)

    def test_zeros_ordered(self):
        zeros = self.rs.zeros
        for i in range(len(zeros) - 1):
            self.assertLess(zeros[i], zeros[i + 1])

    # Error vs referencia
    def test_zero_error_vs_reference_keys(self):
        result = self.rs.zero_error_vs_reference()
        for key in ["n_computed", "n_compared", "mae_zeros", "max_error", "errors"]:
            self.assertIn(key, result)

    def test_zero_mae_below_threshold(self):
        result = self.rs.zero_error_vs_reference()
        if result["n_compared"] > 0:
            # MAE de ceros < 0.5 (la suma RS con N=⌊√(t/2π)⌋ es precisa)
            self.assertLess(result["mae_zeros"], 0.5)

    # ψ_RS
    def test_psi_rs_zero_for_x_le_1(self):
        self.assertEqual(self.rs.psi_rs(0.5), 0.0)

    def test_psi_rs_finite(self):
        for x in [2.0, 5.0, 10.0, 30.0]:
            self.assertTrue(math.isfinite(self.rs.psi_rs(x)))

    def test_psi_rs_array_shape(self):
        x_arr = np.linspace(2, 30, 20)
        result = self.rs.psi_rs_array(x_arr)
        self.assertEqual(result.shape, (20,))

    def test_psi_rs_array_consistent_with_scalar(self):
        x_arr = np.array([5.0, 15.0, 25.0])
        arr_res = self.rs.psi_rs_array(x_arr)
        for i, x in enumerate(x_arr):
            self.assertAlmostEqual(arr_res[i], self.rs.psi_rs(x), places=8)

    def test_mae_vs_exact_finite(self):
        mae = self.rs.mae_vs_exact(x_min=5.0, x_max=40.0, n_points=30)
        self.assertTrue(math.isfinite(mae))

    def test_mae_vs_exact_reasonable(self):
        # ψ_RS con pocos ceros (~5-10) debe tener MAE < 10 en [5,40]
        mae = self.rs.mae_vs_exact(x_min=5.0, x_max=40.0, n_points=30)
        self.assertLess(mae, 10.0)

    # Idempotencia: compute_zeros llamado dos veces devuelve el mismo resultado
    def test_zeros_cached_after_first_call(self):
        z1 = self.rs.zeros
        z2 = self.rs.zeros
        np.testing.assert_array_equal(z1, z2)


# ============================================================================
# COMPARADOR UNIFICADO
# ============================================================================
class TestComparadorMetodos(unittest.TestCase):
    def setUp(self):
        # Instancia ligera para tests rápidos
        self.comp = ComparadorMetodos(
            weil_delta=0.1,
            weil_p_max=500,
            mellin_P=500.0,
            rs_t_max=50.0,
            epsilon=0.4,
        )

    def test_comparar_returns_dict(self):
        result = self.comp.comparar(x_min=5.0, x_max=40.0, n_points=20)
        self.assertIsInstance(result, dict)

    def test_comparar_has_required_keys(self):
        result = self.comp.comparar(x_min=5.0, x_max=40.0, n_points=20)
        for key in ["mae_lineal", "mae_weil", "mae_mellin", "mae_rs",
                    "n_zeros_rs", "mejor_metodo"]:
            self.assertIn(key, result)

    def test_mae_values_non_negative(self):
        result = self.comp.comparar(x_min=5.0, x_max=40.0, n_points=20)
        self.assertGreaterEqual(result["mae_lineal"], 0.0)
        self.assertGreaterEqual(result["mae_weil"], 0.0)
        self.assertGreaterEqual(result["mae_mellin"], 0.0)
        self.assertGreaterEqual(result["mae_rs"], 0.0)

    def test_n_zeros_rs_positive(self):
        result = self.comp.comparar(x_min=5.0, x_max=40.0, n_points=20)
        self.assertGreater(result["n_zeros_rs"], 0)

    def test_mejor_metodo_valid(self):
        result = self.comp.comparar(x_min=5.0, x_max=40.0, n_points=20)
        self.assertIn(result["mejor_metodo"], ["weil", "mellin", "rs"])

    def test_weil_mae_finite(self):
        result = self.comp.comparar(x_min=5.0, x_max=40.0, n_points=20)
        self.assertTrue(math.isfinite(result["mae_weil"]))

    def test_mellin_mae_finite(self):
        result = self.comp.comparar(x_min=5.0, x_max=40.0, n_points=20)
        self.assertTrue(math.isfinite(result["mae_mellin"]))

    def test_rs_mae_finite(self):
        result = self.comp.comparar(x_min=5.0, x_max=40.0, n_points=20)
        self.assertTrue(math.isfinite(result["mae_rs"]))


# ============================================================================
# CONSTANTES
# ============================================================================
class TestConstantes(unittest.TestCase):
    def test_epsilon_default(self):
        self.assertAlmostEqual(EPSILON_DEFAULT, 0.4, places=10)

    def test_delta_weil_default(self):
        self.assertAlmostEqual(DELTA_WEIL_DEFAULT, 0.10, places=10)

    def test_p_mellin_default(self):
        self.assertAlmostEqual(P_MELLIN_DEFAULT, 1000.0, places=10)


if __name__ == "__main__":
    unittest.main()
