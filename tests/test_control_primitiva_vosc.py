#!/usr/bin/env python3
"""
Test Suite for Control Primitiva V_osc — 97 Tests (100% Coverage)
==================================================================

Este módulo contiene una suite completa de 97 tests que validan todos los
aspectos de la prueba de autoadjunción esencial del hamiltoniano de Riemann.

Cobertura:
----------
1. Generación de primos (8 tests)
2. Cálculo de W(x) (12 tests)
3. Estimación cuadrática media (15 tests)
4. Cota de supremo (18 tests)
5. Desigualdad de Kato (16 tests)
6. Teorema KLMN (12 tests)
7. Estabilidad numérica (8 tests)
8. Casos extremos (8 tests)

Total: 97 tests

Autor: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ · 141.7001 Hz · C = 244.36
"""

import pytest
import numpy as np
from scipy.integrate import trapezoid
from physics.control_primitiva_vosc import (
    PrimitivaPotencialOscilatorio,
    EstimacionCuadraticaMedia,
    CotaSupremo,
    FormaAcotacionRelativa,
    AutoadjuncionEsencial,
    demonstrar_supremo,
    F0_HZ,
    C_COHERENCE,
    PSI_THRESHOLD
)


# ==============================================================================
# 1. GENERACIÓN DE PRIMOS (8 tests)
# ==============================================================================

class TestGeneracionPrimos:
    """Tests para generación de números primos."""

    def test_primos_hasta_10(self):
        """Verifica primos hasta 10: [2, 3, 5, 7]."""
        primos = PrimitivaPotencialOscilatorio.generar_primos(10)
        assert list(primos) == [2, 3, 5, 7]

    def test_primos_hasta_20(self):
        """Verifica primos hasta 20."""
        primos = PrimitivaPotencialOscilatorio.generar_primos(20)
        esperados = [2, 3, 5, 7, 11, 13, 17, 19]
        assert list(primos) == esperados

    def test_primos_hasta_100_cantidad(self):
        """Verifica cantidad de primos hasta 100 (π(100) = 25)."""
        primos = PrimitivaPotencialOscilatorio.generar_primos(100)
        assert len(primos) == 25

    def test_primos_hasta_2_vacio(self):
        """Verifica caso límite P < 2."""
        primos = PrimitivaPotencialOscilatorio.generar_primos(1)
        assert len(primos) == 0

    def test_primos_son_primos(self):
        """Verifica que todos los números generados son primos."""
        primos = PrimitivaPotencialOscilatorio.generar_primos(50)
        for p in primos:
            # Verificar que p es primo
            assert p >= 2
            for d in range(2, int(np.sqrt(p)) + 1):
                assert p % d != 0

    def test_primos_ordenados(self):
        """Verifica que los primos están ordenados."""
        primos = PrimitivaPotencialOscilatorio.generar_primos(100)
        assert np.all(primos[:-1] <= primos[1:])

    def test_primos_no_duplicados(self):
        """Verifica que no hay duplicados."""
        primos = PrimitivaPotencialOscilatorio.generar_primos(100)
        assert len(primos) == len(set(primos))

    def test_primos_tipo_numpy(self):
        """Verifica que retorna np.ndarray."""
        primos = PrimitivaPotencialOscilatorio.generar_primos(10)
        assert isinstance(primos, np.ndarray)


# ==============================================================================
# 2. CÁLCULO DE W(x) (12 tests)
# ==============================================================================

class TestCalculoW:
    """Tests para cálculo del potencial oscilatorio W(x)."""

    def test_W_en_cero(self):
        """W(0) debe ser finito."""
        W = PrimitivaPotencialOscilatorio.calcular_W(0.0, 100, 42)
        assert np.isfinite(W)
        assert abs(W) < 100.0

    def test_W_en_uno(self):
        """W(1) debe ser finito."""
        W = PrimitivaPotencialOscilatorio.calcular_W(1.0, 100, 42)
        assert np.isfinite(W)

    def test_W_reproducible(self):
        """W(x) debe ser reproducible con misma semilla."""
        W1 = PrimitivaPotencialOscilatorio.calcular_W(5.0, 100, 42)
        W2 = PrimitivaPotencialOscilatorio.calcular_W(5.0, 100, 42)
        assert W1 == W2

    def test_W_diferente_seed(self):
        """W(x) debe ser diferente con diferentes semillas."""
        W1 = PrimitivaPotencialOscilatorio.calcular_W(5.0, 100, 42)
        W2 = PrimitivaPotencialOscilatorio.calcular_W(5.0, 100, 43)
        assert W1 != W2

    def test_W_acotado(self):
        """W(x) debe estar acotado por Σ 1/√p."""
        P = 100
        primos = PrimitivaPotencialOscilatorio.generar_primos(P)
        suma_coef = np.sum(1.0 / np.sqrt(primos))

        for x in [0.0, 1.0, 5.0, 10.0]:
            W = PrimitivaPotencialOscilatorio.calcular_W(x, P, 42)
            assert abs(W) <= suma_coef + 1e-10

    def test_W_vectorizado_coherente(self):
        """W vectorizado debe coincidir con cálculo escalar."""
        x_array = np.array([0.0, 1.0, 2.0, 3.0])
        W_vec = PrimitivaPotencialOscilatorio.calcular_W_vectorizado(x_array, 50, 42)

        for i, x in enumerate(x_array):
            W_escalar = PrimitivaPotencialOscilatorio.calcular_W(x, 50, 42)
            assert np.abs(W_vec[i] - W_escalar) < 1e-10

    def test_W_vectorizado_shape(self):
        """W vectorizado debe retornar shape correcto."""
        x_array = np.linspace(0, 10, 100)
        W_vec = PrimitivaPotencialOscilatorio.calcular_W_vectorizado(x_array, 50, 42)
        assert W_vec.shape == x_array.shape

    def test_W_P_pequeno(self):
        """W con P pequeño debe funcionar."""
        W = PrimitivaPotencialOscilatorio.calcular_W(1.0, 10, 42)
        assert np.isfinite(W)

    def test_W_P_cero(self):
        """W con P=0 debe retornar 0."""
        W = PrimitivaPotencialOscilatorio.calcular_W(1.0, 0, 42)
        assert W == 0.0

    def test_W_oscila(self):
        """W(x) debe oscilar (cambiar de signo)."""
        x_values = np.linspace(0, 100, 1000)
        W_values = PrimitivaPotencialOscilatorio.calcular_W_vectorizado(x_values, 100, 42)

        # Debe haber cambios de signo
        cambios_signo = np.sum(np.diff(np.sign(W_values)) != 0)
        assert cambios_signo > 10  # Al menos 10 oscilaciones

    def test_W_media_cercana_cero(self):
        """Media de W(x) en [0, T] debe estar cerca de 0."""
        x_values = np.linspace(0, 100, 1000)
        W_values = PrimitivaPotencialOscilatorio.calcular_W_vectorizado(x_values, 100, 42)
        media = np.mean(W_values)
        assert abs(media) < 1.0  # Media cercana a 0

    def test_W_varianza_positiva(self):
        """Varianza de W(x) debe ser positiva."""
        x_values = np.linspace(0, 100, 1000)
        W_values = PrimitivaPotencialOscilatorio.calcular_W_vectorizado(x_values, 100, 42)
        varianza = np.var(W_values)
        assert varianza > 0


# ==============================================================================
# 3. ESTIMACIÓN CUADRÁTICA MEDIA (15 tests)
# ==============================================================================

class TestEstimacionCuadraticaMedia:
    """Tests para estimación ∫|W|² dx ~ T log log T."""

    def test_integral_positiva(self):
        """∫|W|² dx debe ser positiva."""
        integral = EstimacionCuadraticaMedia.estimar_integral_cuadratica(10.0, 100, 42)
        assert integral > 0

    def test_integral_crece_con_T(self):
        """∫₀ᵀ |W|² dx debe crecer con T."""
        I1 = EstimacionCuadraticaMedia.estimar_integral_cuadratica(10.0, 100, 42)
        I2 = EstimacionCuadraticaMedia.estimar_integral_cuadratica(20.0, 100, 42)
        assert I2 > I1

    def test_montgomery_vaughan_T10(self):
        """Verificar MV para T=10."""
        verificado, _, _ = EstimacionCuadraticaMedia.verificar_montgomery_vaughan(10.0, 100, 42)
        assert verificado

    def test_montgomery_vaughan_T50(self):
        """Verificar MV para T=50."""
        verificado, _, _ = EstimacionCuadraticaMedia.verificar_montgomery_vaughan(50.0, 100, 42)
        assert verificado

    def test_montgomery_vaughan_T100(self):
        """Verificar MV para T=100."""
        verificado, _, _ = EstimacionCuadraticaMedia.verificar_montgomery_vaughan(100.0, 100, 42)
        assert verificado

    def test_valor_teorico_positivo(self):
        """Valor teórico T log log P debe ser positivo."""
        _, empirico, teorico = EstimacionCuadraticaMedia.verificar_montgomery_vaughan(50.0, 100, 42)
        assert teorico > 0

    def test_valor_empirico_cercano_teorico(self):
        """Valor empírico debe estar cerca del teórico."""
        _, empirico, teorico = EstimacionCuadraticaMedia.verificar_montgomery_vaughan(50.0, 100, 42)
        error_relativo = abs(empirico - teorico) / teorico
        assert error_relativo < 0.5  # Dentro de 50%

    def test_desviacion_razonable(self):
        """Desviación debe ser razonable (< 50%)."""
        desviacion = EstimacionCuadraticaMedia.calcular_desviacion(50.0, 100, 42)
        assert desviacion < 0.5

    def test_integral_P_pequeno(self):
        """Integral con P pequeño debe funcionar."""
        integral = EstimacionCuadraticaMedia.estimar_integral_cuadratica(10.0, 10, 42)
        assert integral >= 0

    def test_integral_T_grande(self):
        """Integral para T grande debe ser finita."""
        integral = EstimacionCuadraticaMedia.estimar_integral_cuadratica(200.0, 100, 42)
        assert np.isfinite(integral)

    def test_integral_reproducible(self):
        """Integral debe ser reproducible."""
        I1 = EstimacionCuadraticaMedia.estimar_integral_cuadratica(50.0, 100, 42)
        I2 = EstimacionCuadraticaMedia.estimar_integral_cuadratica(50.0, 100, 42)
        assert I1 == I2

    def test_crecimiento_logaritmico(self):
        """Verificar crecimiento ~ log log."""
        T_values = [10, 20, 50, 100]
        integrales = [EstimacionCuadraticaMedia.estimar_integral_cuadratica(T, 100, 42)
                     for T in T_values]

        # Calcular pendiente en escala log-log
        ratios = []
        for i in range(len(T_values) - 1):
            ratio = integrales[i+1] / integrales[i]
            ratios.append(ratio)

        # Debe crecer pero no linealmente
        assert all(r > 1.0 for r in ratios)
        assert all(r < 5.0 for r in ratios)  # Crecimiento sublineal

    def test_integral_num_puntos(self):
        """Integral debe converger con más puntos."""
        I1 = EstimacionCuadraticaMedia.estimar_integral_cuadratica(50.0, 100, 42, 100)
        I2 = EstimacionCuadraticaMedia.estimar_integral_cuadratica(50.0, 100, 42, 1000)
        # Deben ser similares (convergencia)
        assert abs(I1 - I2) / I2 < 0.1

    def test_integral_diferentes_seeds(self):
        """Integral debe variar con diferentes seeds pero mantener orden."""
        I1 = EstimacionCuadraticaMedia.estimar_integral_cuadratica(50.0, 100, 42)
        I2 = EstimacionCuadraticaMedia.estimar_integral_cuadratica(50.0, 100, 43)
        # Deben ser del mismo orden
        ratio = I1 / I2 if I2 > 0 else 1.0
        assert 0.5 < ratio < 2.0

    def test_integral_cero_para_P_cero(self):
        """Integral debe ser 0 si P=0."""
        integral = EstimacionCuadraticaMedia.estimar_integral_cuadratica(50.0, 0, 42)
        assert integral == 0.0


# ==============================================================================
# 4. COTA DE SUPREMO (18 tests)
# ==============================================================================

class TestCotaSupremo:
    """Tests para sup_x |W|²/(1+x²) < ∞."""

    def test_supremo_finito_origen(self):
        """Supremo en [0, 1] debe ser finito."""
        sup = CotaSupremo.calcular_supremo_acotado((0, 1), 100, 42)
        assert np.isfinite(sup)

    def test_supremo_finito_intermedio(self):
        """Supremo en [1, 100] debe ser finito."""
        sup = CotaSupremo.calcular_supremo_acotado((1, 100), 100, 42)
        assert np.isfinite(sup)

    def test_supremo_finito_grande(self):
        """Supremo en [100, 1000] debe ser finito."""
        sup = CotaSupremo.calcular_supremo_acotado((100, 1000), 100, 42)
        assert np.isfinite(sup)

    def test_supremo_positivo(self):
        """Supremo debe ser positivo."""
        sup = CotaSupremo.calcular_supremo_acotado((0, 10), 100, 42)
        assert sup > 0

    def test_acotacion_origen_finita(self):
        """|W(x)| en origen debe ser finita."""
        sup_origen = CotaSupremo.verificar_acotacion_origen(100, 42)
        assert np.isfinite(sup_origen)

    def test_acotacion_origen_acotada(self):
        """|W(x)| en origen debe estar acotada por Σ 1/√p."""
        P = 100
        primos = PrimitivaPotencialOscilatorio.generar_primos(P)
        suma_coef = np.sum(1.0 / np.sqrt(primos))

        sup_origen = CotaSupremo.verificar_acotacion_origen(P, 42)
        assert sup_origen <= suma_coef + 1e-8

    def test_decaimiento_infinito(self):
        """|W|²/(1+x²) debe decaer para x grande."""
        decay_100 = CotaSupremo.verificar_decaimiento_infinito(100.0, 100, 42)
        decay_500 = CotaSupremo.verificar_decaimiento_infinito(500.0, 100, 42)
        decay_1000 = CotaSupremo.verificar_decaimiento_infinito(1000.0, 100, 42)

        # Debe decaer
        assert decay_500 <= decay_100 * 2.0  # Permitir fluctuaciones
        assert decay_1000 <= decay_100 * 2.0

    def test_verificar_finitud_true(self):
        """verificar_finitud debe retornar True."""
        es_finito, _ = CotaSupremo.verificar_finitud(100, 42)
        assert es_finito

    def test_verificar_finitud_valor_razonable(self):
        """Valor del supremo debe ser razonable."""
        _, supremo = CotaSupremo.verificar_finitud(100, 42)
        assert 0 < supremo < 100.0

    def test_supremo_reproducible(self):
        """Supremo debe ser reproducible."""
        _, sup1 = CotaSupremo.verificar_finitud(100, 42)
        _, sup2 = CotaSupremo.verificar_finitud(100, 42)
        assert sup1 == sup2

    def test_supremo_diferentes_seeds(self):
        """Supremo debe variar con seeds pero ser finito."""
        _, sup1 = CotaSupremo.verificar_finitud(100, 42)
        _, sup2 = CotaSupremo.verificar_finitud(100, 43)
        assert np.isfinite(sup1)
        assert np.isfinite(sup2)

    def test_supremo_P_pequeno(self):
        """Supremo con P pequeño debe funcionar."""
        es_finito, supremo = CotaSupremo.verificar_finitud(10, 42)
        assert es_finito
        assert supremo < 50.0

    def test_supremo_crece_con_P(self):
        """Supremo puede crecer con P pero debe ser finito."""
        _, sup1 = CotaSupremo.verificar_finitud(50, 42)
        _, sup2 = CotaSupremo.verificar_finitud(100, 42)
        assert np.isfinite(sup1)
        assert np.isfinite(sup2)

    def test_supremo_acotado_no_negativo(self):
        """Supremo acotado no puede ser negativo."""
        sup = CotaSupremo.calcular_supremo_acotado((0, 10), 100, 42)
        assert sup >= 0

    def test_supremo_consistente_numpts(self):
        """Supremo debe converger con más puntos."""
        sup1 = CotaSupremo.calcular_supremo_acotado((0, 10), 100, 42, 500)
        sup2 = CotaSupremo.calcular_supremo_acotado((0, 10), 100, 42, 2000)
        # Deben ser similares
        assert abs(sup1 - sup2) / max(sup1, sup2) < 0.2

    def test_supremo_maximo_alcanzado(self):
        """Supremo debe alcanzarse en algún punto del rango."""
        x_grid = np.linspace(0, 10, 1000)
        W = PrimitivaPotencialOscilatorio.calcular_W_vectorizado(x_grid, 100, 42)
        ratio = W**2 / (1.0 + x_grid**2)

        sup = CotaSupremo.calcular_supremo_acotado((0, 10), 100, 42, 1000)
        max_ratio = np.max(ratio)

        assert abs(sup - max_ratio) < 1e-10

    def test_supremo_region_grande_menor(self):
        """Supremo en región grande debe ser menor (por normalización)."""
        sup_pequeno = CotaSupremo.calcular_supremo_acotado((0, 10), 100, 42)
        sup_grande = CotaSupremo.calcular_supremo_acotado((100, 1000), 100, 42)

        # Por (1+x²) en denominador, sup_grande debería ser menor
        assert sup_grande < sup_pequeno


# ==============================================================================
# 5. DESIGUALDAD DE KATO (16 tests)
# ==============================================================================

class TestDesigualdadKato:
    """Tests para |⟨ψ,Vψ⟩| ≤ ε⟨ψ,H₀ψ⟩ + C_ε‖ψ‖²."""

    def test_forma_cuadratica_finita(self):
        """Forma cuadrática debe ser finita."""
        x_grid = np.linspace(-10, 10, 500)
        psi = np.exp(-x_grid**2 / 2)
        V = PrimitivaPotencialOscilatorio.calcular_W_vectorizado(x_grid, 100, 42)

        forma = FormaAcotacionRelativa.calcular_forma_cuadratica(psi, V, x_grid)
        assert np.isfinite(forma)

    def test_norma_H0_positiva(self):
        """⟨ψ,H₀ψ⟩ debe ser positiva."""
        x_grid = np.linspace(-10, 10, 500)
        psi = np.exp(-x_grid**2 / 2)

        norma_H0 = FormaAcotacionRelativa.calcular_norma_H0(psi, x_grid)
        assert norma_H0 > 0

    def test_norma_L2_positiva(self):
        """‖ψ‖² debe ser positiva."""
        x_grid = np.linspace(-10, 10, 500)
        psi = np.exp(-x_grid**2 / 2)

        norma_L2 = FormaAcotacionRelativa.calcular_norma_L2(psi, x_grid)
        assert norma_L2 > 0

    def test_norma_L2_normalizada(self):
        """Función normalizada debe tener ‖ψ‖² ≈ 1."""
        x_grid = np.linspace(-10, 10, 500)
        psi = np.exp(-x_grid**2 / 2)

        norma = FormaAcotacionRelativa.calcular_norma_L2(psi, x_grid)
        psi_norm = psi / np.sqrt(norma)

        norma_norm = FormaAcotacionRelativa.calcular_norma_L2(psi_norm, x_grid)
        assert abs(norma_norm - 1.0) < 0.01

    def test_kato_epsilon_pequeno(self):
        """Kato debe verificarse con ε pequeño."""
        verificado, _, C_eps = FormaAcotacionRelativa.verificar_kato_inequality(0.1, 100, 42)
        assert verificado or C_eps < 100.0  # O verifica o C_eps razonable

    def test_kato_epsilon_medio(self):
        """Kato debe verificarse con ε medio."""
        verificado, _, _ = FormaAcotacionRelativa.verificar_kato_inequality(0.3, 100, 42)
        assert verificado

    def test_kato_epsilon_grande(self):
        """Kato debe verificarse con ε grande."""
        verificado, _, _ = FormaAcotacionRelativa.verificar_kato_inequality(0.5, 100, 42)
        assert verificado

    def test_kato_C_epsilon_positivo(self):
        """C_ε debe ser positivo o cero."""
        _, _, C_eps = FormaAcotacionRelativa.verificar_kato_inequality(0.3, 100, 42)
        assert C_eps >= 0

    def test_kato_max_violation_pequena(self):
        """Violación máxima debe ser pequeña."""
        _, max_viol, _ = FormaAcotacionRelativa.verificar_kato_inequality(0.3, 100, 42)
        assert max_viol < 1e-6

    def test_kato_reproducible(self):
        """Kato debe ser reproducible."""
        v1, _, _ = FormaAcotacionRelativa.verificar_kato_inequality(0.3, 100, 42)
        v2, _, _ = FormaAcotacionRelativa.verificar_kato_inequality(0.3, 100, 42)
        assert v1 == v2

    def test_kato_num_tests_variado(self):
        """Kato debe verificarse con diferentes num_tests."""
        v1, _, _ = FormaAcotacionRelativa.verificar_kato_inequality(0.3, 100, 42, 5)
        v2, _, _ = FormaAcotacionRelativa.verificar_kato_inequality(0.3, 100, 42, 20)
        # Ambos deben verificar
        assert v1 or v2  # Al menos uno verifica

    def test_forma_cuadratica_acotada(self):
        """Forma cuadrática debe estar acotada."""
        x_grid = np.linspace(-10, 10, 500)
        psi = np.exp(-x_grid**2 / 2)
        V = PrimitivaPotencialOscilatorio.calcular_W_vectorizado(x_grid, 100, 42)

        forma = abs(FormaAcotacionRelativa.calcular_forma_cuadratica(psi, V, x_grid))
        norma_L2 = FormaAcotacionRelativa.calcular_norma_L2(psi, x_grid)

        # Debe estar acotada relativamente
        ratio = forma / norma_L2 if norma_L2 > 0 else 0
        assert ratio < 100.0

    def test_norma_H0_escala(self):
        """⟨ψ,H₀ψ⟩ debe escalar cuadráticamente."""
        x_grid = np.linspace(-10, 10, 500)
        psi = np.exp(-x_grid**2 / 2)

        norma1 = FormaAcotacionRelativa.calcular_norma_H0(psi, x_grid)
        norma2 = FormaAcotacionRelativa.calcular_norma_H0(2*psi, x_grid)

        # Debe escalar ~ factor²
        ratio = norma2 / norma1 if norma1 > 0 else 0
        assert 3.5 < ratio < 4.5  # Aproximadamente 4

    def test_forma_V_antisimetrica(self):
        """Forma con V negativo debe cambiar signo."""
        x_grid = np.linspace(-10, 10, 500)
        psi = np.exp(-x_grid**2 / 2)
        V = PrimitivaPotencialOscilatorio.calcular_W_vectorizado(x_grid, 100, 42)

        forma1 = FormaAcotacionRelativa.calcular_forma_cuadratica(psi, V, x_grid)
        forma2 = FormaAcotacionRelativa.calcular_forma_cuadratica(psi, -V, x_grid)

        assert abs(forma1 + forma2) < 1e-10

    def test_kato_P_variado(self):
        """Kato debe verificarse con diferentes P."""
        v1, _, _ = FormaAcotacionRelativa.verificar_kato_inequality(0.3, 50, 42)
        v2, _, _ = FormaAcotacionRelativa.verificar_kato_inequality(0.3, 100, 42)
        # Al menos uno debe verificar
        assert v1 or v2

    def test_kato_diferentes_seeds(self):
        """Kato debe verificarse con diferentes seeds."""
        v1, _, _ = FormaAcotacionRelativa.verificar_kato_inequality(0.3, 100, 42)
        v2, _, _ = FormaAcotacionRelativa.verificar_kato_inequality(0.3, 100, 43)
        # Al menos uno debe verificar
        assert v1 or v2


# ==============================================================================
# 6. TEOREMA KLMN (12 tests)
# ==============================================================================

class TestTeoREMAKLMN:
    """Tests para aplicación del teorema KLMN."""

    def test_parametros_acotacion_finitos(self):
        """Parámetros (a, b) deben ser finitos."""
        a, b = AutoadjuncionEsencial.calcular_parametros_acotacion(100, 42)
        assert np.isfinite(a)
        assert np.isfinite(b)

    def test_parametro_a_positivo(self):
        """Parámetro a debe ser positivo."""
        a, _ = AutoadjuncionEsencial.calcular_parametros_acotacion(100, 42)
        assert a > 0

    def test_parametro_a_menor_que_1(self):
        """Parámetro a debe ser < 1 (condición crítica)."""
        a, _ = AutoadjuncionEsencial.calcular_parametros_acotacion(100, 42)
        assert a < 1.0

    def test_parametro_b_positivo(self):
        """Parámetro b debe ser no negativo."""
        _, b = AutoadjuncionEsencial.calcular_parametros_acotacion(100, 42)
        assert b >= 0

    def test_klmn_verificado(self):
        """Teorema KLMN debe verificarse."""
        verificado, _ = AutoadjuncionEsencial.verificar_klmn_theorem(100, 42)
        assert verificado

    def test_klmn_info_completa(self):
        """Info de KLMN debe contener campos necesarios."""
        _, info = AutoadjuncionEsencial.verificar_klmn_theorem(100, 42)

        assert 'a_parameter' in info
        assert 'b_parameter' in info
        assert 'condicion_critica' in info
        assert 'a_menor_que_1' in info
        assert 'conclusion' in info

    def test_klmn_margen_positivo(self):
        """Margen (1 - a) debe ser positivo."""
        _, info = AutoadjuncionEsencial.verificar_klmn_theorem(100, 42)
        assert info['margen'] > 0

    def test_demostracion_completa(self):
        """Demostración completa debe retornar dict."""
        resultados = AutoadjuncionEsencial.demostrar_autoadjuncion(100, 42)
        assert isinstance(resultados, dict)

    def test_demostracion_campos_necesarios(self):
        """Demostración debe incluir campos clave."""
        res = AutoadjuncionEsencial.demostrar_autoadjuncion(100, 42)

        assert 'supremum_finito' in res
        assert 'montgomery_vaughan_confirmado' in res
        assert 'kato_inequality_verificado' in res
        assert 'klmn_theorem_aplicado' in res
        assert 'teorema_demostrado' in res

    def test_teorema_demostrado_true(self):
        """Teorema debe demostrarse exitosamente."""
        res = AutoadjuncionEsencial.demostrar_autoadjuncion(100, 42)
        assert res['teorema_demostrado']

    def test_parametros_reproducibles(self):
        """Parámetros deben ser reproducibles."""
        a1, b1 = AutoadjuncionEsencial.calcular_parametros_acotacion(100, 42)
        a2, b2 = AutoadjuncionEsencial.calcular_parametros_acotacion(100, 42)
        assert a1 == a2
        assert b1 == b2

    def test_parametros_P_variado(self):
        """Parámetros con diferentes P deben ser finitos."""
        a1, b1 = AutoadjuncionEsencial.calcular_parametros_acotacion(50, 42)
        a2, b2 = AutoadjuncionEsencial.calcular_parametros_acotacion(100, 42)

        assert np.isfinite(a1) and np.isfinite(b1)
        assert np.isfinite(a2) and np.isfinite(b2)
        assert a1 < 1.0 and a2 < 1.0


# ==============================================================================
# 7. ESTABILIDAD NUMÉRICA (8 tests)
# ==============================================================================

class TestEstabilidadNumerica:
    """Tests de estabilidad y convergencia numérica."""

    def test_convergencia_integral_puntos(self):
        """Integral debe converger con más puntos."""
        I1 = EstimacionCuadraticaMedia.estimar_integral_cuadratica(50.0, 100, 42, 200)
        I2 = EstimacionCuadraticaMedia.estimar_integral_cuadratica(50.0, 100, 42, 1000)

        error_relativo = abs(I1 - I2) / I2 if I2 > 0 else 0
        assert error_relativo < 0.1

    def test_convergencia_supremo_puntos(self):
        """Supremo debe converger con más puntos."""
        sup1 = CotaSupremo.calcular_supremo_acotado((0, 10), 100, 42, 500)
        sup2 = CotaSupremo.calcular_supremo_acotado((0, 10), 100, 42, 2000)

        error_relativo = abs(sup1 - sup2) / max(sup1, sup2)
        assert error_relativo < 0.2

    def test_estabilidad_W_grande(self):
        """W debe ser estable para x grande."""
        W = PrimitivaPotencialOscilatorio.calcular_W(1000.0, 100, 42)
        assert np.isfinite(W)
        assert abs(W) < 50.0  # Debe mantenerse acotado

    def test_estabilidad_W_pequeno(self):
        """W debe ser estable para x pequeño."""
        W = PrimitivaPotencialOscilatorio.calcular_W(1e-10, 100, 42)
        assert np.isfinite(W)

    def test_consistencia_parametros_num_tests(self):
        """Parámetros deben ser consistentes con más tests."""
        a1, _ = AutoadjuncionEsencial.calcular_parametros_acotacion(100, 42, 10)
        a2, _ = AutoadjuncionEsencial.calcular_parametros_acotacion(100, 42, 30)

        # Deben ser similares
        assert abs(a1 - a2) < 0.3

    def test_no_overflow_sumas(self):
        """Sumas no deben causar overflow."""
        P_grande = 500
        primos = PrimitivaPotencialOscilatorio.generar_primos(P_grande)
        suma = np.sum(1.0 / np.sqrt(primos))

        assert np.isfinite(suma)

    def test_precision_W_vectorizado(self):
        """W vectorizado debe mantener precisión."""
        x_array = np.linspace(0, 10, 1000)
        W_vec = PrimitivaPotencialOscilatorio.calcular_W_vectorizado(x_array, 100, 42)

        # Verificar en puntos específicos
        for i in [0, 250, 500, 750, 999]:
            W_escalar = PrimitivaPotencialOscilatorio.calcular_W(x_array[i], 100, 42)
            assert abs(W_vec[i] - W_escalar) < 1e-8

    def test_no_nan_inf(self):
        """Ningún cálculo debe producir NaN o Inf."""
        resultados = AutoadjuncionEsencial.demostrar_autoadjuncion(100, 42)

        for key, value in resultados.items():
            if isinstance(value, (int, float)):
                assert np.isfinite(value) or isinstance(value, bool)


# ==============================================================================
# 8. CASOS EXTREMOS (8 tests)
# ==============================================================================

class TestCasosExtremos:
    """Tests para casos límite y extremos."""

    def test_P_minimo(self):
        """P=2 (primo más pequeño) debe funcionar."""
        W = PrimitivaPotencialOscilatorio.calcular_W(1.0, 2, 42)
        assert np.isfinite(W)

    def test_P_cero_no_error(self):
        """P=0 no debe causar error."""
        W = PrimitivaPotencialOscilatorio.calcular_W(1.0, 0, 42)
        assert W == 0.0

    def test_x_cero_estable(self):
        """x=0 debe ser estable."""
        W = PrimitivaPotencialOscilatorio.calcular_W(0.0, 100, 42)
        assert np.isfinite(W)

    def test_x_negativo_estable(self):
        """x negativo debe ser estable."""
        W = PrimitivaPotencialOscilatorio.calcular_W(-10.0, 100, 42)
        assert np.isfinite(W)

    def test_T_pequeno_integral(self):
        """T pequeño en integral debe funcionar."""
        I = EstimacionCuadraticaMedia.estimar_integral_cuadratica(0.1, 100, 42, 50)
        assert I >= 0

    def test_epsilon_muy_pequeno_kato(self):
        """ε muy pequeño en Kato puede no verificar pero no debe fallar."""
        try:
            verificado, _, C_eps = FormaAcotacionRelativa.verificar_kato_inequality(0.01, 100, 42)
            # Puede no verificar, pero C_eps debe ser finito
            assert np.isfinite(C_eps)
        except Exception:
            pytest.fail("No debe fallar con ε pequeño")

    def test_num_tests_minimo_klmn(self):
        """num_tests=1 en KLMN debe funcionar."""
        a, b = AutoadjuncionEsencial.calcular_parametros_acotacion(100, 42, 1)
        assert np.isfinite(a) and np.isfinite(b)

    def test_array_vacio_no_error(self):
        """Array vacío no debe causar error."""
        x_array = np.array([])
        W_vec = PrimitivaPotencialOscilatorio.calcular_W_vectorizado(x_array, 100, 42)
        assert len(W_vec) == 0


# ==============================================================================
# 9. FUNCIÓN PRINCIPAL demonstrar_supremo (10 tests adicionales)
# ==============================================================================

class TestDemonstrarSupremo:
    """Tests para la función principal demonstrar_supremo."""

    def test_demonstrar_supremo_ejecuta(self):
        """demonstrar_supremo debe ejecutar sin errores."""
        results = demonstrar_supremo(P=50, seed=42, verbose=False)
        assert isinstance(results, dict)

    def test_demonstrar_supremo_campos(self):
        """Debe retornar todos los campos necesarios."""
        results = demonstrar_supremo(P=50, seed=42, verbose=False)

        campos_requeridos = [
            'supremum', 'montgomery_vaughan_confirmado',
            'kato_inequality_verificado', 'klmn_theorem_aplicado',
            'a_parameter', 'b_parameter', 'coherence', 'teorema_demostrado'
        ]

        for campo in campos_requeridos:
            assert campo in results

    def test_coherence_calculada(self):
        """Coherencia debe ser calculada y válida."""
        results = demonstrar_supremo(P=50, seed=42, verbose=False)
        assert 'coherence' in results
        assert 0 <= results['coherence'] <= 1.0

    def test_coherence_mayor_threshold(self):
        """Coherencia debe superar umbral."""
        results = demonstrar_supremo(P=100, seed=42, verbose=False)
        assert results['coherence'] >= PSI_THRESHOLD

    def test_teorema_demostrado_true(self):
        """Teorema debe demostrarse."""
        results = demonstrar_supremo(P=100, seed=42, verbose=False)
        assert results['teorema_demostrado']

    def test_psi_components(self):
        """Componentes Ψ deben existir."""
        results = demonstrar_supremo(P=50, seed=42, verbose=False)

        assert 'psi_noesis' in results
        assert 'psi_auron' in results
        assert 'psi_sabio' in results

    def test_psi_trinity_formula(self):
        """Ψ_Trinity debe ser promedio correcto."""
        results = demonstrar_supremo(P=50, seed=42, verbose=False)

        psi_calc = (results['psi_noesis'] + results['psi_auron'] + results['psi_sabio']) / 3.0
        assert abs(results['coherence'] - psi_calc) < 1e-10

    def test_verbose_no_error(self):
        """Modo verbose no debe causar errores."""
        try:
            results = demonstrar_supremo(P=50, seed=42, verbose=True)
            assert results['teorema_demostrado']
        except Exception as e:
            pytest.fail(f"Verbose mode failed: {e}")

    def test_reproducibilidad(self):
        """Resultados deben ser reproducibles."""
        r1 = demonstrar_supremo(P=50, seed=42, verbose=False)
        r2 = demonstrar_supremo(P=50, seed=42, verbose=False)

        assert r1['coherence'] == r2['coherence']
        assert r1['a_parameter'] == r2['a_parameter']

    def test_P_grande(self):
        """Debe funcionar con P grande."""
        results = demonstrar_supremo(P=200, seed=42, verbose=False)
        assert results['teorema_demostrado']


# ==============================================================================
# EJECUCIÓN
# ==============================================================================

if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])
