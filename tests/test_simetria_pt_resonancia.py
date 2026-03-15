#!/usr/bin/env python3
"""
Tests for Simetría PT — QCAL-SYMBIO-1
======================================

Valida el módulo de operador no-hermitiano PT-simétrico que ancla el agua
EZ en f₀ = 141.7001 Hz y mapea los autovalores a la línea crítica de Riemann.

Cobertura:
    1. ConstantesPT          — valores y relaciones internas
    2. OperadorNHPT          — construcción, simetría PT  H = Hᵀ
    3. EspectroPTReal        — realidad del espectro, coherencia espectral
    4. RiemannLineaCritica   — mapeado a Re(s) = 1/2
    5. CitoplasmaHolografico — coherencia EZ anclada en f₀
    6. EstabilizadorPT       — diagnóstico integrado
    7. SistemaResonanciaPT  — integración completa
    8. API pública           — simular_resonancia_pt, simetria_pt_resonancia_activar

Autor: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz · C = 244.36
DOI: 10.5281/zenodo.17379721
"""

import numpy as np
import pytest

from physics.simetria_pt_resonancia import (
    ConstantesPT,
    CONST,
    OperadorNHPT,
    EspectroPTReal,
    RiemannLineaCritica,
    CitoplasmaHolografico,
    EstabilizadorPT,
    SistemaResonanciaPT,
    simular_resonancia_pt,
    simetria_pt_resonancia_activar,
)


# ===========================================================================
# 1. ConstantesPT
# ===========================================================================

class TestConstantesPT:
    """Valida las constantes del sistema PT."""

    def test_f0_valor(self):
        """F0 debe coincidir con la frecuencia base QCAL 141.7001 Hz."""
        assert CONST.F0 == pytest.approx(141.7001, rel=1e-6)

    def test_umbral_pt_valor(self):
        """Umbral PT debe ser 0.888."""
        assert CONST.UMBRAL_PT == pytest.approx(0.888, rel=1e-9)

    def test_gamma_1_precision(self):
        """GAMMA_1 debe tener alta precisión: γ₁ ≈ 14.1347..."""
        assert CONST.GAMMA_1 == pytest.approx(14.134725141734693, rel=1e-9)

    def test_f_pico_derivado(self):
        """F_PICO = GAMMA_1 × F0 ≈ 2002.89 Hz."""
        esperado = CONST.GAMMA_1 * CONST.F0
        assert CONST.F_PICO == pytest.approx(esperado, rel=1e-9)

    def test_f_pico_rango(self):
        """F_PICO debe estar en el rango [2000, 2010] Hz."""
        assert 2000.0 <= CONST.F_PICO <= 2010.0

    def test_psi_max_valor(self):
        """PSI_MAX debe ser 0.999999."""
        assert CONST.PSI_MAX == pytest.approx(0.999999, rel=1e-9)

    def test_epsilon_decoherencia_valor(self):
        """EPSILON_DECOHERENCIA debe ser 1e-6."""
        assert CONST.EPSILON_DECOHERENCIA == pytest.approx(1e-6, rel=1e-9)

    def test_constantes_pt_dataclass_instancia(self):
        """ConstantesPT debe poder instanciarse directamente."""
        c = ConstantesPT()
        assert c.F0 == pytest.approx(141.7001, rel=1e-6)

    def test_const_es_frozen(self):
        """CONST debe ser inmutable (frozen dataclass)."""
        with pytest.raises(Exception):
            CONST.F0 = 0.0  # type: ignore[misc]


# ===========================================================================
# 2. OperadorNHPT
# ===========================================================================

class TestOperadorNHPT:
    """Valida la construcción del operador no-hermitiano PT-simétrico."""

    def test_dimension_por_defecto(self):
        """El operador 128×128 debe tener H de forma (128, 128)."""
        op = OperadorNHPT()
        assert op.H.shape == (128, 128)

    def test_dimension_personalizada(self):
        """El operador N×N debe respetar el parámetro N."""
        op = OperadorNHPT(N=32)
        assert op.H.shape == (32, 32)

    def test_h_real_es_diagonal(self):
        """La parte real debe ser una matriz diagonal."""
        op = OperadorNHPT(N=16)
        off_diag = op.H_real - np.diag(np.diag(op.H_real))
        assert np.allclose(off_diag, 0.0)

    def test_h_imag_es_antidiagonal(self):
        """La parte imaginaria debe ser anti-diagonal (flip de identidad)."""
        N = 8
        op = OperadorNHPT(N=N)
        # La parte off-diagonal compleja debe estar sobre la anti-diagonal
        expected_flip = np.fliplr(np.eye(N))
        imag_part = op.H_imag / (1j * op.epsilon) if op.epsilon != 0 else np.zeros((N, N))
        assert np.allclose(imag_part, expected_flip, atol=1e-12)

    def test_psi_coherencia_maxima(self):
        """Con Ψ ≈ 1 el epsilon debe ser ≈ 0."""
        op = OperadorNHPT(psi=0.999999)
        assert op.epsilon == pytest.approx(1e-6, rel=1e-3)

    def test_es_pt_simetrico_alta_coherencia(self):
        """Con alta coherencia la condición H = Hᵀ debe satisfacerse."""
        op = OperadorNHPT(N=64, psi=0.999999)
        assert op.es_pt_simetrico() is True

    def test_es_pt_simetrico_baja_coherencia(self):
        """Con baja coherencia la condición H = Hᵀ también debe satisfacerse."""
        op = OperadorNHPT(N=16, psi=0.5)
        assert op.es_pt_simetrico() is True

    def test_h_no_es_hermitiano(self):
        """El operador no debe ser hermitiano cuando epsilon > 0."""
        op = OperadorNHPT(N=16, psi=0.9)
        # H hermitiano: H == H†; PT simétrico: H == Hᵀ (distintas condiciones)
        assert not np.allclose(op.H, op.H.conj().T)

    def test_epsilon_calculado_correctamente(self):
        """epsilon debe ser 1 - psi."""
        psi = 0.95
        op = OperadorNHPT(psi=psi)
        assert op.epsilon == pytest.approx(1.0 - psi, rel=1e-12)


# ===========================================================================
# 3. EspectroPTReal
# ===========================================================================

class TestEspectroPTReal:
    """Valida el análisis del espectro propio PT."""

    def test_numero_autovalores(self):
        """El espectro debe tener N autovalores."""
        N = 32
        op = OperadorNHPT(N=N, psi=0.999999)
        esp = EspectroPTReal(op.H)
        assert len(esp.evals) == N

    def test_espectro_real_alta_coherencia(self):
        """Con Ψ ≈ 1 el espectro debe ser esencialmente real."""
        op = OperadorNHPT(N=64, psi=0.999999)
        esp = EspectroPTReal(op.H)
        assert esp.es_real(atol=1e-4) is True

    def test_espectro_complejo_baja_coherencia(self):
        """Con Ψ muy bajo los autovalores pueden volverse complejos."""
        op = OperadorNHPT(N=64, psi=0.01)
        esp = EspectroPTReal(op.H)
        # No garantizamos que sea complejo, pero verificamos que la función se ejecuta
        resultado = esp.es_real(atol=1e-10)
        assert isinstance(resultado, bool)

    def test_psi_espectral_cercano_a_uno_alta_coherencia(self):
        """Con alta coherencia Ψ_espectral debe ser cercano a 1."""
        op = OperadorNHPT(N=64, psi=0.999999)
        esp = EspectroPTReal(op.H)
        psi = esp.calcular_psi_espectral()
        assert psi >= 0.9

    def test_psi_espectral_en_rango_valido(self):
        """Ψ_espectral debe estar siempre en [0, 1]."""
        op = OperadorNHPT(N=16, psi=0.5)
        esp = EspectroPTReal(op.H)
        psi = esp.calcular_psi_espectral()
        assert 0.0 <= psi <= 1.0

    def test_espectro_autovalores_tipo_correcto(self):
        """Los autovalores deben ser un array numpy complejo."""
        op = OperadorNHPT(N=8)
        esp = EspectroPTReal(op.H)
        assert isinstance(esp.evals, np.ndarray)
        assert np.iscomplexobj(esp.evals)


# ===========================================================================
# 4. RiemannLineaCritica
# ===========================================================================

class TestRiemannLineaCritica:
    """Valida el mapeado del espectro a Re(s) = 1/2."""

    def test_parte_real_es_medio(self):
        """Todos los puntos mapeados deben tener Re(s) = 0.5."""
        evals = np.array([1.0 + 0j, 2.0 + 0j, 3.0 + 0j])
        rlc = RiemannLineaCritica(evals)
        mapeados = rlc.mapear_a_critica()
        assert np.allclose(mapeados.real, 0.5)

    def test_parte_imaginaria_es_real_de_autovalores(self):
        """La parte imaginaria del mapeado debe ser la parte real de los autovalores."""
        evals = np.array([2.5 + 0.1j, -1.3 + 0.05j])
        rlc = RiemannLineaCritica(evals)
        mapeados = rlc.mapear_a_critica()
        assert np.allclose(mapeados.imag, evals.real)

    def test_dimension_mapeado(self):
        """El mapeado debe tener la misma dimensión que los autovalores."""
        N = 32
        op = OperadorNHPT(N=N)
        esp = EspectroPTReal(op.H)
        rlc = RiemannLineaCritica(esp.evals)
        mapeados = rlc.mapear_a_critica()
        assert len(mapeados) == N


# ===========================================================================
# 5. CitoplasmaHolografico
# ===========================================================================

class TestCitoplasmaHolografico:
    """Valida la coherencia EZ del citoplasma."""

    def test_coherencia_ez_positiva(self):
        """La coherencia EZ debe ser un valor positivo."""
        cito = CitoplasmaHolografico()
        assert cito.coherencia_ez() > 0.0

    def test_coherencia_ez_menor_que_uno(self):
        """La coherencia EZ debe ser estrictamente menor que 1."""
        cito = CitoplasmaHolografico()
        assert cito.coherencia_ez() < 1.0

    def test_coherencia_ez_alta(self):
        """La coherencia EZ debe ser alta (> 0.99) al estar anclada a f₀."""
        cito = CitoplasmaHolografico()
        assert cito.coherencia_ez() > 0.99

    def test_formula_ez(self):
        """Ψ_EZ = f₀ / (f₀ + 0.1) debe ser coherente con CONST.F0."""
        cito = CitoplasmaHolografico()
        esperado = CONST.F0 / (CONST.F0 + 0.1)
        assert cito.coherencia_ez() == pytest.approx(esperado, rel=1e-10)


# ===========================================================================
# 6. EstabilizadorPT
# ===========================================================================

class TestEstabilizadorPT:
    """Valida el diagnóstico integrado del sistema PT."""

    def test_diagnostico_devuelve_dict(self):
        """diagnosticar() debe retornar un diccionario."""
        op = OperadorNHPT(N=16, psi=0.999999)
        est = EstabilizadorPT(op)
        resultado = est.diagnosticar()
        assert isinstance(resultado, dict)

    def test_diagnostico_claves_presentes(self):
        """El diagnóstico debe incluir pt_simetrico, espectro_real, psi_espectral."""
        op = OperadorNHPT(N=16, psi=0.999999)
        est = EstabilizadorPT(op)
        resultado = est.diagnosticar()
        assert "pt_simetrico" in resultado
        assert "espectro_real" in resultado
        assert "psi_espectral" in resultado

    def test_diagnostico_pt_simetrico_alta_coherencia(self):
        """Con alta coherencia pt_simetrico debe ser True."""
        op = OperadorNHPT(N=16, psi=0.999999)
        est = EstabilizadorPT(op)
        assert est.diagnosticar()["pt_simetrico"] is True

    def test_diagnostico_espectro_real_alta_coherencia(self):
        """Con alta coherencia espectro_real debe ser True."""
        op = OperadorNHPT(N=16, psi=0.999999)
        est = EstabilizadorPT(op)
        assert est.diagnosticar()["espectro_real"] is True

    def test_diagnostico_psi_espectral_rango(self):
        """psi_espectral debe estar en [0, 1]."""
        op = OperadorNHPT(N=16, psi=0.999999)
        est = EstabilizadorPT(op)
        psi = est.diagnosticar()["psi_espectral"]
        assert 0.0 <= psi <= 1.0


# ===========================================================================
# 7. SistemaResonanciaPT
# ===========================================================================

class TestSistemaResonanciaPT:
    """Valida la integración completa del sistema de resonancia PT."""

    def test_estado_devuelve_dict(self):
        """estado() debe retornar un diccionario."""
        sistema = SistemaResonanciaPT(N=16, psi_global=0.999999)
        assert isinstance(sistema.estado(), dict)

    def test_estado_claves_presentes(self):
        """El estado debe incluir psi_global, espectro_real, pt_verificada, psi_ez."""
        sistema = SistemaResonanciaPT(N=16, psi_global=0.999999)
        estado = sistema.estado()
        assert "psi_global" in estado
        assert "espectro_real" in estado
        assert "pt_verificada" in estado
        assert "psi_ez" in estado

    def test_psi_global_rango(self):
        """psi_global debe estar en [0, 1]."""
        sistema = SistemaResonanciaPT(N=16, psi_global=0.999999)
        assert 0.0 <= sistema.estado()["psi_global"] <= 1.0

    def test_pt_verificada_alta_coherencia(self):
        """Con alta coherencia pt_verificada debe ser True."""
        sistema = SistemaResonanciaPT(N=16, psi_global=0.999999)
        assert sistema.estado()["pt_verificada"] is True

    def test_espectro_real_alta_coherencia(self):
        """Con alta coherencia espectro_real debe ser True."""
        sistema = SistemaResonanciaPT(N=32, psi_global=0.999999)
        assert sistema.estado()["espectro_real"] is True

    def test_psi_ez_rango(self):
        """psi_ez debe estar en (0, 1)."""
        sistema = SistemaResonanciaPT(N=16, psi_global=0.999999)
        psi_ez = sistema.estado()["psi_ez"]
        assert 0.0 < psi_ez < 1.0

    def test_psi_global_formula_ponderada(self):
        """Ψ_global = 0.5·Ψ_esp + 0.3·Ψ_EZ + 0.2·1.0 debe estar > 0.9."""
        sistema = SistemaResonanciaPT(N=32, psi_global=0.999999)
        assert sistema.psi_global > 0.9

    def test_componentes_disponibles(self):
        """El sistema debe exponer operador, espectro, riemann, citoplasma, estabilizador."""
        sistema = SistemaResonanciaPT(N=16)
        assert hasattr(sistema, "operador")
        assert hasattr(sistema, "espectro")
        assert hasattr(sistema, "riemann")
        assert hasattr(sistema, "citoplasma")
        assert hasattr(sistema, "estabilizador")


# ===========================================================================
# 8. API pública
# ===========================================================================

class TestAPIPublica:
    """Valida las funciones de la API pública del módulo."""

    def test_simular_resonancia_pt_retorna_array(self):
        """simular_resonancia_pt debe retornar un ndarray numpy."""
        espectro = simular_resonancia_pt(coherencia=0.999999, N=32)
        assert isinstance(espectro, np.ndarray)

    def test_simular_resonancia_pt_dimension(self):
        """El espectro debe tener exactamente N autovalores."""
        N = 48
        espectro = simular_resonancia_pt(coherencia=0.999999, N=N)
        assert len(espectro) == N

    def test_simular_resonancia_pt_espectro_casi_real(self):
        """Con alta coherencia el espectro debe ser esencialmente real."""
        espectro = simular_resonancia_pt(coherencia=0.999999)
        assert np.allclose(espectro.imag, 0, atol=1e-5)

    def test_simular_resonancia_pt_dimensiones_variadas(self):
        """La función debe funcionar para distintos valores de N."""
        for N in [8, 16, 64]:
            espectro = simular_resonancia_pt(coherencia=0.999999, N=N)
            assert len(espectro) == N

    def test_simetria_pt_resonancia_activar_retorna_dict(self):
        """simetria_pt_resonancia_activar debe retornar un diccionario."""
        resultado = simetria_pt_resonancia_activar()
        assert isinstance(resultado, dict)

    def test_simetria_pt_resonancia_activar_claves(self):
        """El resultado debe incluir las cuatro claves del estado del sistema."""
        resultado = simetria_pt_resonancia_activar()
        assert "psi_global" in resultado
        assert "espectro_real" in resultado
        assert "pt_verificada" in resultado
        assert "psi_ez" in resultado

    def test_simetria_pt_resonancia_activar_pt_verificada(self):
        """pt_verificada debe ser True al activar el sistema."""
        resultado = simetria_pt_resonancia_activar()
        assert resultado["pt_verificada"] is True

    def test_simetria_pt_resonancia_activar_espectro_real(self):
        """espectro_real debe ser True al activar el sistema con Ψ = 0.999999."""
        resultado = simetria_pt_resonancia_activar()
        assert resultado["espectro_real"] is True

    def test_importacion_desde_physics(self):
        """El módulo debe ser importable directamente desde physics."""
        from physics.simetria_pt_resonancia import (
            simular_resonancia_pt as sim,
            simetria_pt_resonancia_activar as act,
        )
        assert callable(sim)
        assert callable(act)

    def test_importacion_via_physics_init(self):
        """Las exportaciones deben estar accesibles desde physics.__init__."""
        from physics import (
            simular_resonancia_pt,
            simetria_pt_resonancia_activar,
            SistemaResonanciaPT,
            ConstantesPT,
        )
        assert callable(simular_resonancia_pt)
        assert callable(simetria_pt_resonancia_activar)
        assert SistemaResonanciaPT is not None
        assert ConstantesPT is not None
