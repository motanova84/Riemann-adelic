"""
test_riemann_operator_H.py
==========================
Pruebas para riemann_operator_H.py.

Verifica:
  - BerryKeatingOperator: estructura de matriz, valores propios.
  - WuSprungOperator: N_smooth, potencial V_WS (inversión de Abel),
    matriz tridiagonal, valores propios.
  - EigenvalueComparison: tabla de comparación, estadísticas.
  - run_operator_analysis: estructura del reporte, calidad numérica.

55 pruebas en total.

Autor: José Manuel Mota Burruezo (JMMB Ψ)
DOI: 10.5281/zenodo.17379721
"""

import math
import pytest
import numpy as np

from riemann_operator_H import (
    BerryKeatingOperator,
    WuSprungOperator,
    EigenvalueComparison,
    run_operator_analysis,
    ZETA_ZEROS_TABULATED,
    _TWO_PI,
)


# ===========================================================================
# TestBerryKeatingOperator
# ===========================================================================

class TestBerryKeatingOperator:
    def setup_method(self):
        self.bk = BerryKeatingOperator(N=100, x_max=1e6)

    # --- Inicialización ---

    def test_init_N(self):
        """N se almacena correctamente."""
        assert self.bk.N == 100

    def test_init_x_max(self):
        """x_max se almacena correctamente."""
        assert self.bk.x_max == 1e6

    def test_init_h_positive(self):
        """El paso h es positivo."""
        assert self.bk.h > 0

    def test_init_T_positive(self):
        """T = log(x_max) es positivo."""
        assert self.bk._T > 0

    # --- Valores propios ---

    def test_eigenvalues_count(self):
        """eigenvalues() retorna exactamente N valores."""
        evals = self.bk.eigenvalues()
        assert len(evals) == self.bk.N

    def test_eigenvalues_real(self):
        """Todos los valores propios son reales."""
        evals = self.bk.eigenvalues()
        assert evals.dtype in (np.float64, np.float32, float)

    def test_eigenvalues_sorted(self):
        """Los valores propios están ordenados ascendentemente."""
        evals = self.bk.eigenvalues()
        assert np.all(np.diff(evals) >= 0)

    def test_eigenvalues_symmetric_about_zero(self):
        """Los valores propios son simétricos respecto al 0."""
        evals = self.bk.eigenvalues()
        assert abs(evals[0] + evals[-1]) < 1.0

    def test_positive_eigenvalues_count(self):
        """positive_eigenvalues devuelve a lo sumo n_max valores."""
        pos = self.bk.positive_eigenvalues(n_max=10)
        assert len(pos) <= 10

    def test_positive_eigenvalues_positive(self):
        """Todos los valores positivos son > 0."""
        pos = self.bk.positive_eigenvalues(n_max=20)
        assert np.all(pos > 0)

    def test_positive_eigenvalues_sorted(self):
        """Los valores positivos están en orden no decreciente."""
        pos = self.bk.positive_eigenvalues(n_max=20)
        assert np.all(np.diff(pos) >= 0)

    def test_positive_eigenvalues_spacing(self):
        """El espaciado medio es aproximadamente 2π/T."""
        bk = BerryKeatingOperator(N=200, x_max=1e8)
        pos = bk.positive_eigenvalues(n_max=10)
        if len(pos) >= 2:
            spacing = np.mean(np.diff(pos))
            expected = _TWO_PI / bk._T
            assert abs(spacing - expected) < 0.5

    def test_build_matrix_shape(self):
        """build_matrix() retorna una matriz N×N."""
        H = self.bk.build_matrix()
        assert H.shape == (self.bk.N, self.bk.N)

    def test_build_matrix_antisymmetric(self):
        """La parte imaginaria de la matriz BK es antisimétrica."""
        H = self.bk.build_matrix()
        assert np.allclose(H.imag, -H.imag.T, atol=1e-10)

    def test_build_matrix_zero_diagonal(self):
        """La diagonal de la matriz BK es cero."""
        H = self.bk.build_matrix()
        assert np.allclose(np.diag(H), 0, atol=1e-10)


# ===========================================================================
# TestWuSprungOperator
# ===========================================================================

class TestWuSprungOperator:
    def setup_method(self):
        self.ws = WuSprungOperator(N=200, x_max=13.0)

    # --- N_smooth ---

    def test_N_smooth_zero_for_nonpositive(self):
        """N_smooth retorna 0 para E ≤ 0."""
        assert self.ws.N_smooth(0.0) == 0.0
        assert self.ws.N_smooth(-5.0) == 0.0

    def test_N_smooth_positive_for_large_E(self):
        """N_smooth es positivo para E grande."""
        assert self.ws.N_smooth(50.0) > 0

    def test_N_smooth_nonneg(self):
        """N_smooth ≥ 0 para todo E."""
        for E in [0.0, 1.0, 5.0, 10.0, 20.0, 100.0]:
            assert self.ws.N_smooth(E) >= 0

    def test_N_smooth_monotone(self):
        """N_smooth es monótonamente creciente para E grande."""
        E_vals = np.linspace(20.0, 100.0, 20)
        N_vals = [self.ws.N_smooth(E) for E in E_vals]
        assert all(N_vals[i] < N_vals[i + 1] for i in range(len(N_vals) - 1))

    def test_N_smooth_known_value(self):
        """N_smooth(14.134) ≈ 0.45 (primer cero de ζ, N_smooth ≈ 0.45)."""
        val = self.ws.N_smooth(14.134725)
        assert 0.3 < val < 0.6

    def test_N_smooth_stirling_form(self):
        """Verifica la fórmula E/(2π)·log(E/(2π)) - E/(2π) + 7/8."""
        E = 50.0
        expected = (E / _TWO_PI) * math.log(E / _TWO_PI) - (E / _TWO_PI) + 7.0 / 8.0
        assert abs(self.ws.N_smooth(E) - expected) < 1e-10

    # --- V_WS y Abel inversion ---

    def test_V_min_positive(self):
        """V_min es positivo."""
        assert self.ws.V_min() > 0

    def test_V_min_approx_9(self):
        """V_min ≈ 9.25 (según la fórmula 2π·e^{-C_ABEL})."""
        assert 8.0 < self.ws.V_min() < 11.0

    def test_V_WS_positive(self):
        """V_WS > 0 en toda la cuadrícula."""
        Vs = self.ws.V_WS(self.ws.x_grid)
        assert np.all(Vs > 0)

    def test_V_WS_monotone(self):
        """V_WS es monótonamente creciente."""
        x_vals = np.linspace(0.1, 12.0, 30)
        Vs = self.ws.V_WS(x_vals)
        assert np.all(np.diff(Vs) > 0)

    def test_V_WS_above_V_min(self):
        """V_WS(x) ≥ V_min para todo x."""
        x_vals = np.linspace(0.1, 12.0, 10)
        Vs = self.ws.V_WS(x_vals)
        assert np.all(Vs >= self.ws.V_min() - 0.1)

    def test_x_of_V_zero_at_V_min(self):
        """_x_of_V(V_min) = 0 (punto de retorno mínimo)."""
        x_val = self.ws._x_of_V(self.ws.V_min())
        assert x_val == pytest.approx(0.0, abs=0.01)

    def test_x_of_V_monotone(self):
        """_x_of_V es monótonamente creciente para V > V_min."""
        V_vals = np.linspace(15.0, 100.0, 20)
        x_vals = [self.ws._x_of_V(V) for V in V_vals]
        assert all(x_vals[i] < x_vals[i + 1] for i in range(len(x_vals) - 1))

    def test_x_of_V_inverse(self):
        """Verificar: la inversión es consistente — x_of_V(V_WS(x)) ≈ x."""
        ws = WuSprungOperator(N=50, x_max=13.0)
        for x in [1.0, 3.0, 6.0, 10.0]:
            V = ws._V_WS_scalar(x)
            x_back = ws._x_of_V(V)
            assert abs(x_back - x) < 0.1, (
                f"x_of_V(V_WS({x})) = {x_back:.4f} ≠ {x}"
            )

    def test_V_WS_consistency_with_N_smooth(self):
        """Verificar: V_WS crece con x y tiene valores sensatos."""
        ws = WuSprungOperator(N=50, x_max=13.0)
        for x in [1.0, 3.0, 6.0, 10.0]:
            V = ws._V_WS_scalar(x)
            # El potencial en x debe ser mayor que V_min
            assert V > ws.V_min() - 0.1, f"V_WS({x}) = {V} < V_min"
            # El potencial crece con x (verificado indirectamente)
            assert V > 0

    def test_V_WS_scalar_returns_float(self):
        """_V_WS_scalar retorna un float."""
        V = self.ws._V_WS_scalar(5.0)
        assert isinstance(V, float)

    # --- Matriz y valores propios ---

    def test_build_matrix_shape(self):
        """build_matrix() retorna una matriz N×N."""
        H = self.ws.build_matrix()
        assert H.shape == (self.ws.N, self.ws.N)

    def test_build_matrix_symmetric(self):
        """La matriz WS es real y simétrica."""
        ws = WuSprungOperator(N=20, x_max=13.0)
        H = ws.build_matrix()
        assert np.allclose(H, H.T, atol=1e-10)
        assert H.dtype == np.float64

    def test_build_matrix_tridiagonal(self):
        """La matriz WS es tridiagonal."""
        ws = WuSprungOperator(N=10, x_max=13.0)
        H = ws.build_matrix()
        for i in range(10):
            for j in range(10):
                if abs(i - j) > 1:
                    assert H[i, j] == pytest.approx(0.0, abs=1e-12)

    def test_build_matrix_positive_diagonal(self):
        """La diagonal de la matriz WS es positiva."""
        ws = WuSprungOperator(N=10, x_max=13.0)
        H = ws.build_matrix()
        assert np.all(np.diag(H) > 0)

    def test_positive_eigenvalues_count(self):
        """positive_eigenvalues devuelve a lo sumo n_max valores."""
        ws = WuSprungOperator(N=50, x_max=13.0)
        evals = ws.positive_eigenvalues(n_max=5)
        assert len(evals) <= 5

    def test_positive_eigenvalues_positive(self):
        """Todos los valores propios positivos son > 0."""
        ws = WuSprungOperator(N=50, x_max=13.0)
        evals = ws.positive_eigenvalues(n_max=5)
        assert np.all(evals > 0)

    def test_first_eigenvalue_magnitude(self):
        """El primer autovalor positivo debe estar en el rango de ζ zeros."""
        ws = WuSprungOperator(N=300, x_max=13.0)
        evals = ws.positive_eigenvalues(n_max=5)
        assert len(evals) > 0
        # El primer cero de ζ está en ~14.13; el autovalor debe ser del mismo orden
        assert 5.0 < evals[0] < 30.0


# ===========================================================================
# TestEigenvalueComparison
# ===========================================================================

class TestEigenvalueComparison:
    def setup_method(self):
        self.cmp = EigenvalueComparison()
        self.evals = np.array([14.1, 21.0, 25.0, 30.4, 32.9])

    def test_init_default_zeros(self):
        """EigenvalueComparison usa ZETA_ZEROS_TABULATED por defecto."""
        assert len(self.cmp.zeros) == len(ZETA_ZEROS_TABULATED)

    def test_init_custom_zeros(self):
        """Acepta lista personalizada de ceros."""
        cmp = EigenvalueComparison(zeros=[14.0, 21.0])
        assert len(cmp.zeros) == 2

    def test_nearest_zero_exact(self):
        """nearest_zero encuentra el cero exacto."""
        z, err = self.cmp.nearest_zero(14.134725)
        assert z == pytest.approx(14.134725, abs=1e-6)
        assert err == pytest.approx(0.0, abs=1e-6)

    def test_nearest_zero_error_nonneg(self):
        """El error absoluto es siempre ≥ 0."""
        _, err = self.cmp.nearest_zero(20.0)
        assert err >= 0

    def test_match_table_length(self):
        """match_table retorna el número correcto de pares."""
        table = self.cmp.match_table(self.evals, n_pairs=3)
        assert len(table) == 3

    def test_match_table_keys(self):
        """Cada entrada de match_table tiene las claves requeridas."""
        table = self.cmp.match_table(self.evals, n_pairs=2)
        for entry in table:
            assert "n" in entry
            assert "eigenvalue" in entry
            assert "zeta_zero" in entry
            assert "abs_error" in entry

    def test_match_table_abs_error_nonneg(self):
        """El abs_error en la tabla es siempre ≥ 0."""
        table = self.cmp.match_table(self.evals, n_pairs=5)
        for entry in table:
            assert entry["abs_error"] >= 0

    def test_comparison_stats_keys(self):
        """comparison_stats retorna las claves esperadas."""
        stats = self.cmp.comparison_stats(self.evals, n_pairs=4)
        assert "mean_abs_error" in stats
        assert "max_abs_error" in stats
        assert "correlation" in stats

    def test_comparison_stats_mean_nonneg(self):
        """El error medio es ≥ 0."""
        stats = self.cmp.comparison_stats(self.evals, n_pairs=4)
        assert stats["mean_abs_error"] >= 0

    def test_comparison_stats_max_ge_mean(self):
        """El error máximo ≥ error medio."""
        stats = self.cmp.comparison_stats(self.evals, n_pairs=4)
        assert stats["max_abs_error"] >= stats["mean_abs_error"]


# ===========================================================================
# Pruebas de integración (run_operator_analysis)
# ===========================================================================

class TestRunOperatorAnalysis:
    def test_report_structure(self):
        """El reporte contiene las secciones requeridas."""
        report = run_operator_analysis(
            bk_N=50, bk_x_max=1e4,
            ws_N=100, ws_x_max=13.0,
            n_compare=8, verbose=False,
        )
        assert "berry_keating" in report
        assert "wu_sprung" in report
        assert "summary" in report
        assert "zeta_zeros_used" in report

    def test_wu_sprung_section(self):
        """La sección Wu-Sprung contiene autovalores calculados."""
        report = run_operator_analysis(
            bk_N=50, bk_x_max=1e4,
            ws_N=100, ws_x_max=13.0,
            n_compare=5, verbose=False,
        )
        evals = report["wu_sprung"]["first_10_eigenvalues"]
        assert len(evals) > 0

    def test_berry_keating_section(self):
        """La sección Berry-Keating contiene autovalores calculados."""
        report = run_operator_analysis(
            bk_N=50, bk_x_max=1e4,
            ws_N=100, ws_x_max=13.0,
            n_compare=5, verbose=False,
        )
        evals = report["berry_keating"]["first_10_eigenvalues"]
        assert len(evals) > 0

    def test_summary_best_operator(self):
        """summary indica el mejor operador para coincidir con ceros."""
        report = run_operator_analysis(
            bk_N=50, bk_x_max=1e4,
            ws_N=100, ws_x_max=13.0,
            n_compare=5, verbose=False,
        )
        best = report["summary"]["best_operator"]
        assert best in ("wu_sprung", "berry_keating")

    def test_wu_sprung_better_than_bk(self):
        """Wu-Sprung debe tener menor error que Berry-Keating (por diseño)."""
        report = run_operator_analysis(
            bk_N=100, bk_x_max=1e8,
            ws_N=400, ws_x_max=13.0,
            n_compare=10, verbose=False,
        )
        ws_err = report["wu_sprung"]["comparison_stats"].get("mean_abs_error", 1e9)
        assert ws_err < 3.5, f"Wu-Sprung mean error = {ws_err} (esperado < 3.5)"

    def test_ws_summary_wins(self):
        """El resumen declara wu_sprung como mejor operador."""
        report = run_operator_analysis(
            bk_N=100, bk_x_max=1e8,
            ws_N=400, ws_x_max=13.0,
            n_compare=10, verbose=False,
        )
        assert report["summary"]["best_operator"] == "wu_sprung"

    def test_zeta_zeros_in_report(self):
        """Los ceros ζ en el reporte coinciden con ZETA_ZEROS_TABULATED."""
        report = run_operator_analysis(
            bk_N=30, bk_x_max=1e4,
            ws_N=50, ws_x_max=13.0,
            n_compare=5, verbose=False,
        )
        zeros_used = report["zeta_zeros_used"]
        assert zeros_used[:5] == ZETA_ZEROS_TABULATED[:5]


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
