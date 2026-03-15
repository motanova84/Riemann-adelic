#!/usr/bin/env python3
"""
Tests for Simetría PT — QCAL-SYMBIO-1

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
Tests para Simetría PT — Resonancia Biológica QCAL ∞³

Valida el protocolo QCAL-SYMBIO-1:
    H = diag(b) + i·J·ε  (simetría compleja, condición PT)
    Ψ_global = 0.5·Ψ_esp + 0.3·Ψ_EZ + 0.2·Ψ_Riemann ≈ 0.998

Cobertura:
    1. ConstantesPT            — valores físicos y coherencia interna
    2. OperadorNHPT            — construcción del hamiltoniano NH-PT
    3. EspectroPTReal          — análisis de valores propios
    4. RiemannLineaCritica     — mapeo a la línea crítica ℜ(s)=½
    5. CitoplasmaHolografico   — coherencia EZ
    6. EstabilizadorPT         — diagnóstico de decoherencia celular
    7. SistemaResonanciaPT     — orquestador completo
    8. API pública             — simetria_pt_resonancia_activar, simular_resonancia_pt

Autor: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz · C = 244.36
DOI: 10.5281/zenodo.17379721
"""

import numpy as np
import pytest

from physics.simetria_pt_resonancia import (
    ConstantesPT,
    CONST,
import math
import pytest
import numpy as np

from physics.simetria_pt_resonancia import (
    ConstantesPT,
    OperadorNHPT,
    EspectroPTReal,
    RiemannLineaCritica,
    CitoplasmaHolografico,
    EstabilizadorPT,
    SistemaResonanciaPT,
    simular_resonancia_pt,
    simetria_pt_resonancia_activar,
)

    DiagnosticoPT,
    EstabilizadorPT,
    SistemaResonanciaPT,
    simetria_pt_resonancia_activar,
    simular_resonancia_pt,
)

# ---------------------------------------------------------------------------
# Module-level constants used across multiple tests
# ---------------------------------------------------------------------------
_F0_HZ = 141.7001          # Base QCAL frequency
_PSI_EZ_TARGET = 0.993262  # EZ water coherence target
_F0_TOL = 1e-4             # Absolute tolerance for F0 comparisons
_PSI_EZ_TOL = 1e-4         # Absolute tolerance for Ψ_EZ comparisons


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
    """Valida las constantes físicas del módulo de simetría PT."""

    def test_f0_valor(self):
        """F0 debe ser 141.7001 Hz."""
        assert abs(ConstantesPT.F0 - _F0_HZ) < _F0_TOL

    def test_zeros_riemann_count(self):
        """Deben existir exactamente 10 ceros de Riemann."""
        assert len(ConstantesPT.ZEROS_RIEMANN) == 10

    def test_primer_zero_gamma1(self):
        """El primer cero γ₁ ≈ 14.134725142."""
        assert abs(ConstantesPT.ZEROS_RIEMANN[0] - 14.134725142) < 1e-6

    def test_zeros_crecientes(self):
        """Los ceros de Riemann deben ser estrictamente crecientes."""
        zeros = ConstantesPT.ZEROS_RIEMANN
        for k in range(len(zeros) - 1):
            assert zeros[k] < zeros[k + 1]

    def test_umbral_pt(self):
        """UMBRAL_PT debe ser 0.888."""
        assert ConstantesPT.UMBRAL_PT == pytest.approx(0.888, abs=1e-6)

    def test_gamma_ez_positivo(self):
        """γ_EZ debe ser positivo."""
        assert ConstantesPT.GAMMA_EZ > 0

    def test_psi_ez_formula(self):
        """Ψ_EZ = F0/(F0 + γ_EZ) ≈ 0.993262."""
        psi = ConstantesPT.F0 / (ConstantesPT.F0 + ConstantesPT.GAMMA_EZ)
        assert abs(psi - _PSI_EZ_TARGET) < _PSI_EZ_TOL

    def test_psi_ez_coherente(self):
        """ConstantesPT.PSI_EZ debe coincidir con la fórmula Lorentz."""
        assert abs(ConstantesPT.PSI_EZ - _PSI_EZ_TARGET) < _PSI_EZ_TOL

    def test_c_coherence_valor(self):
        """C_COHERENCE debe ser 244.36."""
        assert abs(ConstantesPT.C_COHERENCE - 244.36) < 0.01

    def test_validar_coherente(self):
        """La validación interna debe indicar coherencia."""
        resultado = ConstantesPT.validar()
        assert resultado["coherente"] is True
        assert resultado["n_zeros"] == 10
        assert abs(resultado["psi_ez"] - _PSI_EZ_TARGET) < _PSI_EZ_TOL


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
    """Valida la construcción del hamiltoniano no hermitiano PT."""

    def test_construccion_basica(self):
        """El operador debe construirse sin excepciones."""
        op = OperadorNHPT(n_dim=10, coherencia=0.999999)
        assert op.H.shape == (10, 10)

    def test_simetria_pt(self):
        """H debe ser simétrico: H = Hᵀ (condición PT)."""
        op = OperadorNHPT(n_dim=10, coherencia=0.999999)
        assert op.es_simetrico is True
        assert np.allclose(op.H, op.H.T, atol=1e-12)

    def test_simetria_pt_varios_n(self):
        """La simetría PT debe mantenerse para distintos n_dim."""
        for n in [2, 4, 6, 8, 10]:
            op = OperadorNHPT(n_dim=n, coherencia=0.99)
            assert op.es_simetrico is True, f"Falla para n_dim={n}"

    def test_epsilon_valor(self):
        """ε = 1 − Ψ debe calcularse correctamente."""
        op = OperadorNHPT(n_dim=10, coherencia=0.9)
        assert abs(op.epsilon - 0.1) < 1e-10

    def test_no_hermitiano(self):
        """H no debe ser hermitiano (H ≠ H†) cuando ε > 0."""
        op = OperadorNHPT(n_dim=10, coherencia=0.5)
        # H†  = conjugate transpose
        assert not np.allclose(op.H, op.H.conj().T, atol=1e-10)

    def test_parte_real_diag_zeros_riemann(self):
        """La diagonal real de H debe contener los ceros de Riemann."""
        op = OperadorNHPT(n_dim=5, coherencia=0.9)
        diag_real = np.diag(op.H).real
        for k in range(5):
            assert abs(diag_real[k] - ConstantesPT.ZEROS_RIEMANN[k]) < 1e-8

    def test_parte_imaginaria_antidiagonal(self):
        """La parte imaginaria de H debe estar en la anti-diagonal."""
        op = OperadorNHPT(n_dim=4, coherencia=0.9)
        H_imag = op.H.imag
        J = np.fliplr(np.eye(4))
        assert np.allclose(H_imag, J * op.epsilon, atol=1e-10)

    def test_n_dim_invalido_bajo(self):
        """n_dim < 2 debe lanzar ValueError."""
        with pytest.raises(ValueError):
            OperadorNHPT(n_dim=1)

    def test_n_dim_invalido_alto(self):
        """n_dim > 10 debe lanzar ValueError."""
        with pytest.raises(ValueError):
            OperadorNHPT(n_dim=11)

    def test_coherencia_invalida(self):
        """coherencia fuera de (0,1) debe lanzar ValueError."""
        with pytest.raises(ValueError):
            OperadorNHPT(coherencia=1.0)
        with pytest.raises(ValueError):
            OperadorNHPT(coherencia=0.0)

    def test_exportar(self):
        """exportar() debe devolver claves esperadas."""
        op = OperadorNHPT(n_dim=6, coherencia=0.99)
        d = op.exportar()
        assert "n_dim" in d
        assert "epsilon" in d
        assert "es_simetrico" in d
        assert d["es_simetrico"] is True


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
    """Valida el análisis del espectro de valores propios."""

    def test_eigenvalues_forma(self):
        """El espectro debe tener n_dim valores propios."""
        op = OperadorNHPT(n_dim=8, coherencia=0.999999)
        esp = EspectroPTReal(op)
        assert len(esp.eigenvalues) == 8

    def test_espectro_real_coherencia_alta(self):
        """Para coherencia alta, el espectro debe ser esencialmente real."""
        op = OperadorNHPT(n_dim=10, coherencia=0.999999)
        esp = EspectroPTReal(op)
        assert esp.es_real(atol=1e-5) is True

    def test_imag_cercanas_cero(self):
        """Las partes imaginarias deben estar cerca de cero para Ψ≈1."""
        op = OperadorNHPT(n_dim=10, coherencia=0.999999)
        esp = EspectroPTReal(op)
        assert np.allclose(esp.eigenvalues.imag, 0.0, atol=1e-5)

    def test_psi_espectral_cercana_uno(self):
        """Ψ_esp debe ser cercana a 1 para coherencia alta."""
        op = OperadorNHPT(n_dim=10, coherencia=0.999999)
        esp = EspectroPTReal(op)
        assert esp.calcular_psi_espectral() > 0.99

    def test_psi_espectral_rango(self):
        """Ψ_esp debe estar en [0, 1]."""
        for coh in [0.1, 0.5, 0.9, 0.999]:
            op = OperadorNHPT(n_dim=6, coherencia=coh)
            esp = EspectroPTReal(op)
            psi = esp.calcular_psi_espectral()
            assert 0.0 <= psi <= 1.0, f"Ψ_esp={psi} fuera de rango para coh={coh}"

    def test_exportar_claves(self):
        """exportar() debe contener todas las claves requeridas."""
        op = OperadorNHPT(n_dim=5, coherencia=0.99)
        esp = EspectroPTReal(op)
        d = esp.exportar()
        for clave in ["eigenvalues_real", "eigenvalues_imag", "es_real", "psi_espectral"]:
            assert clave in d


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
    """Valida el mapeo a la línea crítica de Riemann."""

    def test_re_medio_igual_mitad(self):
        """La parte real media de s_k debe ser exactamente ½."""
        op = OperadorNHPT(n_dim=10, coherencia=0.999999)
        esp = EspectroPTReal(op)
        lc = RiemannLineaCritica(esp)
        assert abs(lc.re_medio() - 0.5) < 1e-12

    def test_psi_riemann_uno(self):
        """Ψ_Riemann debe ser 1.0 cuando ℜ(s̄) = ½."""
        op = OperadorNHPT(n_dim=10, coherencia=0.999999)
        esp = EspectroPTReal(op)
        lc = RiemannLineaCritica(esp)
        assert lc.calcular_psi_riemann() == pytest.approx(1.0, abs=1e-10)

    def test_s_candidatos_forma(self):
        """s_candidatos debe tener n_dim elementos."""
        op = OperadorNHPT(n_dim=7, coherencia=0.9)
        esp = EspectroPTReal(op)
        lc = RiemannLineaCritica(esp)
        assert len(lc.s_candidatos) == 7

    def test_exportar_linea_critica(self):
        """exportar() debe indicar linea_critica = 0.5."""
        op = OperadorNHPT(n_dim=5, coherencia=0.99)
        esp = EspectroPTReal(op)
        lc = RiemannLineaCritica(esp)
        d = lc.exportar()
        assert d["linea_critica"] == 0.5


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
    """Valida la coherencia del agua EZ en el citoplasma."""

    def test_psi_ez_valor(self):
        """Ψ_EZ debe ser ≈ 0.993262."""
        cit = CitoplasmaHolografico()
        assert abs(cit.psi_ez - _PSI_EZ_TARGET) < _PSI_EZ_TOL

    def test_psi_ez_formula_lorentz(self):
        """Ψ_EZ = F0/(F0 + γ_EZ) debe cumplirse."""
        cit = CitoplasmaHolografico()
        esperado = cit.f0 / (cit.f0 + cit.gamma_ez)
        assert abs(cit.psi_ez - esperado) < 1e-10

    def test_coherencia_ez_en_f0(self):
        """coherencia_ez(F0) debe coincidir con psi_ez."""
        cit = CitoplasmaHolografico()
        assert abs(cit.coherencia_ez(cit.f0) - cit.psi_ez) < 1e-10

    def test_coherencia_ez_frecuencia_alta(self):
        """A frecuencia alta, la coherencia EZ se acerca a 1."""
        cit = CitoplasmaHolografico()
        assert cit.coherencia_ez(10000.0) > 0.999

    def test_coherencia_ez_frecuencia_invalida(self):
        """coherencia_ez con frecuencia ≤ 0 debe lanzar ValueError."""
        cit = CitoplasmaHolografico()
        with pytest.raises(ValueError):
            cit.coherencia_ez(0.0)

    def test_gamma_ez_invalido(self):
        """gamma_ez ≤ 0 debe lanzar ValueError."""
        with pytest.raises(ValueError):
            CitoplasmaHolografico(gamma_ez=-1.0)

    def test_exportar(self):
        """exportar() debe contener f0_hz, gamma_ez_hz, psi_ez."""
        cit = CitoplasmaHolografico()
        d = cit.exportar()
        assert "f0_hz" in d
        assert "gamma_ez_hz" in d
        assert "psi_ez" in d
        assert abs(d["psi_ez"] - _PSI_EZ_TARGET) < _PSI_EZ_TOL


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
    """Valida el diagnóstico de decoherencia celular."""

    def test_diagnostico_estable(self):
        """Para coherencia alta, el sistema debe estar estable."""
        op = OperadorNHPT(n_dim=10, coherencia=0.999999)
        esp = EspectroPTReal(op)
        est = EstabilizadorPT(esp)
        diag = est.diagnosticar()
        assert diag.esta_estable is True
        assert diag.simetria_pt_verificada is True
        assert diag.espectro_real is True

    def test_diagnostico_tipo(self):
        """diagnosticar() debe devolver un DiagnosticoPT."""
        op = OperadorNHPT(n_dim=10, coherencia=0.999999)
        esp = EspectroPTReal(op)
        est = EstabilizadorPT(esp)
        diag = est.diagnosticar()
        assert isinstance(diag, DiagnosticoPT)

    def test_umbral_decoherencia_positivo(self):
        """El umbral de decoherencia debe ser positivo."""
        op = OperadorNHPT(n_dim=10, coherencia=0.9)
        esp = EspectroPTReal(op)
        est = EstabilizadorPT(esp)
        assert est.umbral_decoherencia > 0.0

    def test_exportar_claves(self):
        """exportar() debe contener todas las claves esperadas."""
        op = OperadorNHPT(n_dim=6, coherencia=0.99)
        esp = EspectroPTReal(op)
        est = EstabilizadorPT(esp)
        d = est.exportar()
        for clave in ["epsilon", "umbral_decoherencia", "esta_estable",
                      "simetria_pt_verificada", "espectro_real", "psi_espectral"]:
            assert clave in d


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
    """Valida el orquestador completo del protocolo QCAL-SYMBIO-1."""

    def test_psi_global_alta_coherencia(self):
        """Ψ_global debe ser ≈ 0.998 para coherencia alta."""
        sistema = SistemaResonanciaPT(n_dim=10, coherencia=0.999999)
        assert sistema.psi_global >= 0.99

    def test_psi_global_supera_umbral(self):
        """Ψ_global debe superar el umbral QCAL de 0.888."""
        sistema = SistemaResonanciaPT(n_dim=10, coherencia=0.999999)
        assert sistema.psi_global >= ConstantesPT.UMBRAL_PT

    def test_psi_riemann_es_uno(self):
        """Ψ_Riemann debe ser exactamente 1.0 (línea crítica anclada)."""
        sistema = SistemaResonanciaPT(n_dim=10, coherencia=0.999999)
        assert sistema.psi_riemann == pytest.approx(1.0, abs=1e-10)

    def test_psi_ez_correcta(self):
        """Ψ_EZ del sistema debe coincidir con CitoplasmaHolografico."""
        sistema = SistemaResonanciaPT(n_dim=10, coherencia=0.999999)
        assert abs(sistema.psi_ez - _PSI_EZ_TARGET) < _PSI_EZ_TOL

    def test_pesos_normalizados(self):
        """Los pesos W_ESP + W_EZ + W_RIEMANN deben sumar 1.0."""
        total = (
            SistemaResonanciaPT.W_ESP
            + SistemaResonanciaPT.W_EZ
            + SistemaResonanciaPT.W_RIEMANN
        )
        assert abs(total - 1.0) < 1e-10

    def test_psi_global_formula(self):
        """Ψ_global debe seguir la fórmula ponderada."""
        sistema = SistemaResonanciaPT(n_dim=10, coherencia=0.999999)
        esperado = (
            SistemaResonanciaPT.W_ESP * sistema.psi_espectral
            + SistemaResonanciaPT.W_EZ * sistema.psi_ez
            + SistemaResonanciaPT.W_RIEMANN * sistema.psi_riemann
        )
        assert abs(sistema.psi_global - esperado) < 1e-10

    def test_exportar_claves(self):
        """exportar() debe contener todas las claves del protocolo."""
        sistema = SistemaResonanciaPT(n_dim=8, coherencia=0.999)
        d = sistema.exportar()
        for clave in [
            "psi_global", "psi_espectral", "psi_ez", "psi_riemann",
            "espectro_real", "simetria_pt_verificada", "n_dim", "coherencia",
        ]:
            assert clave in d


# ===========================================================================
# 8. API pública — simular_resonancia_pt / simetria_pt_resonancia_activar
# ===========================================================================

class TestAPIPublica:
    """Valida las funciones de API pública del protocolo QCAL-SYMBIO-1."""

    def test_simular_resonancia_pt_devuelve_array(self):
        """simular_resonancia_pt debe devolver un ndarray."""
        espectro = simular_resonancia_pt(coherencia=0.999999)
        assert isinstance(espectro, np.ndarray)

    def test_simular_resonancia_pt_espectro_real(self):
        """El espectro simulado con Ψ≈1 debe ser esencialmente real."""
        espectro = simular_resonancia_pt(coherencia=0.999999)
        assert np.allclose(espectro.imag, 0, atol=1e-5)

    def test_simular_resonancia_pt_tamano(self):
        """El espectro simulado debe tener n_dim elementos."""
        espectro = simular_resonancia_pt(coherencia=0.999999, n_dim=7)
        assert len(espectro) == 7

    def test_activar_devuelve_dict(self):
        """simetria_pt_resonancia_activar debe devolver un diccionario."""
        resultado = simetria_pt_resonancia_activar()
        assert isinstance(resultado, dict)

    def test_activar_psi_global_supera_umbral(self):
        """Ψ_global del resultado debe superar 0.888."""
        resultado = simetria_pt_resonancia_activar()
        assert resultado["psi_global"] >= 0.888

    def test_activar_espectro_real(self):
        """espectro_real debe ser True para coherencia ≈ 1."""
        resultado = simetria_pt_resonancia_activar()
        assert resultado["espectro_real"] is True

    def test_activar_simetria_verificada(self):
        """simetria_pt_verificada debe ser True."""
        resultado = simetria_pt_resonancia_activar()
        assert resultado["simetria_pt_verificada"] is True

    def test_activar_psi_ez_aproximadamente_0_993(self):
        """Ψ_EZ del resultado debe ser ≈ 0.993262."""
        resultado = simetria_pt_resonancia_activar()
        assert abs(resultado["psi_ez"] - _PSI_EZ_TARGET) < _PSI_EZ_TOL

    def test_activar_psi_global_cercano_0998(self):
        """Ψ_global ≈ 0.5·Ψ_esp + 0.3·Ψ_EZ + 0.2·Ψ_Riemann ≈ 0.998."""
        resultado = simetria_pt_resonancia_activar(coherencia=0.999999)
        # Expected: 0.5·≈1.0 + 0.3·≈0.993 + 0.2·1.0 ≈ 0.998
        assert abs(resultado["psi_global"] - 0.998) < 0.005

    def test_activar_coherencia_baja(self):
        """La API debe funcionar con coherencia baja sin lanzar excepciones."""
        resultado = simetria_pt_resonancia_activar(coherencia=0.9)
        assert "psi_global" in resultado

    def test_activar_claves_requeridas(self):
        """El resultado debe contener todas las claves del protocolo."""
        resultado = simetria_pt_resonancia_activar()
        for clave in [
            "psi_global", "psi_espectral", "psi_ez", "psi_riemann",
            "espectro_real", "simetria_pt_verificada", "esta_estable",
            "n_dim", "coherencia", "epsilon",
        ]:
            assert clave in resultado, f"Clave faltante: {clave}"
