#!/usr/bin/env python3
"""
Tests for KSS Holographic Fluid — Fluido Holográfico Perfecto
=============================================================

Valida el límite KSS (Kovtun-Son-Starinets) para el citoplasma celular:
    η/s ≥ ℏ/(4π k_B)

Cobertura:
    1. ConstantesKSSHolografico — valores físicos y coherencia interna
    2. ViscosidadMolecularRotor — cálculo de η via rotor molecular
    3. EntropiaDensidadUPE     — cálculo de s via emisión UPE
    4. FlujoHolograficoPerfecto — evaluación η/s vs límite KSS
    5. MicrotubuloCavidadKaluzaKlein — modos KK y capacidad de información
    6. ProtocoloValidacionKSS  — integración completa del protocolo

Autor: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz · C = 244.36
DOI: 10.5281/zenodo.17379721
"""

import math
import pytest
import numpy as np

from physics.kss_holographic_fluid import (
    ConstantesKSSHolografico,
    ViscosidadMolecularRotor,
    EntropiaDensidadUPE,
    ResultadoKSS,
    FlujoHolograficoPerfecto,
    ParametrosMicrotubulo,
    MicrotubuloCavidadKaluzaKlein,
    ResultadoProtocoloKSS,
    ProtocoloValidacionKSS,
)


# ===========================================================================
# 1. ConstantesKSSHolografico
# ===========================================================================

class TestConstantesKSSHolografico:
    """Valida las constantes físicas del límite KSS."""

    def test_hbar_valor(self):
        """ℏ debe ser la constante de Planck reducida estándar."""
        assert ConstantesKSSHolografico.HBAR == pytest.approx(1.0545718e-34, rel=1e-6)

    def test_k_b_valor(self):
        """k_B debe ser la constante de Boltzmann estándar."""
        assert abs(ConstantesKSSHolografico.K_B - 1.380649e-23) < 1e-29

    def test_kss_bound_formula(self):
        """KSS bound = ℏ/(4π k_B) debe coincidir con la fórmula."""
        kss_esperado = ConstantesKSSHolografico.HBAR / (
            4.0 * math.pi * ConstantesKSSHolografico.K_B
        )
        assert abs(ConstantesKSSHolografico.KSS_BOUND - kss_esperado) < 1e-18

    def test_kss_bound_orden_magnitud(self):
        """KSS bound debe estar en torno a 6.08 × 10⁻¹³ kg/K."""
        assert 6.0e-13 < ConstantesKSSHolografico.KSS_BOUND < 6.2e-13

    def test_f_pico_aproximadamente_2003_hz(self):
        """La frecuencia de pico UPE = γ₁ × f₀ debe ser ≈ 2003 Hz."""
        assert abs(ConstantesKSSHolografico.F_PICO - 2003.0) < 5.0

    def test_f_pico_derivacion(self):
        """f_pico = gamma_1 × f0."""
        esperado = ConstantesKSSHolografico.GAMMA_1 * ConstantesKSSHolografico.F0
        assert abs(ConstantesKSSHolografico.F_PICO - esperado) < 1e-6

    def test_psi_coherencia_maxima(self):
        """Ψ_coherencia_maxima debe ser 0.999999."""
        assert ConstantesKSSHolografico.PSI_COHERENCIA_MAXIMA == pytest.approx(0.999999)

    def test_reduccion_entropia_ez(self):
        """La reducción de entropía del agua EZ debe ser ≈ 49.66 %."""
        assert abs(ConstantesKSSHolografico.REDUCCION_ENTROPIA_EZ - 0.4966) < 1e-4

    def test_temperatura_fisiologica(self):
        """La temperatura fisiológica debe ser 310.15 K (37 °C)."""
        assert abs(ConstantesKSSHolografico.TEMPERATURA_FISIOLOGICA_K - 310.15) < 0.01

    def test_validar_coherente(self):
        """La validación interna debe indicar coherencia."""
        resultado = ConstantesKSSHolografico.validar()
        assert resultado["coherente"] is True
        assert resultado["kss_bound"] == pytest.approx(ConstantesKSSHolografico.KSS_BOUND)
        assert abs(resultado["delta_f_pico_2003"]) < 5.0


# ===========================================================================
# 2. ViscosidadMolecularRotor
# ===========================================================================

class TestViscosidadMolecularRotor:
    """Valida el estimador de viscosidad via rotor molecular."""

    def test_inicializacion_defaults(self):
        """Los parámetros por defecto deben ser los valores biofísicos estándar."""
        rotor = ViscosidadMolecularRotor()
        assert rotor.tau_0 == pytest.approx(0.4e-9)
        assert rotor.eta_0 == pytest.approx(6.92e-4)
        assert rotor.alpha == pytest.approx(0.6)

    def test_viscosidad_bruta_referencia(self):
        """Con tau_rot = tau_0 debe devolver eta_0."""
        rotor = ViscosidadMolecularRotor()
        eta = rotor.viscosidad_bruta(rotor.tau_0)
        assert eta == pytest.approx(rotor.eta_0, rel=1e-10)

    def test_viscosidad_bruta_escala(self):
        """La viscosidad crece con el tiempo de decaimiento."""
        rotor = ViscosidadMolecularRotor()
        eta1 = rotor.viscosidad_bruta(rotor.tau_0)
        eta2 = rotor.viscosidad_bruta(2.0 * rotor.tau_0)
        assert eta2 > eta1

    def test_viscosidad_ez_menor_que_bruta(self):
        """La viscosidad EZ debe ser menor que la bruta (reducción REDUCCION_ENTROPIA_EZ)."""
        rotor = ViscosidadMolecularRotor()
        tau = rotor.tau_0
        eta_bruta = rotor.viscosidad_bruta(tau)
        eta_ez = rotor.viscosidad_ez(tau)
        reduccion = ConstantesKSSHolografico.REDUCCION_ENTROPIA_EZ
        assert eta_ez < eta_bruta
        assert eta_ez == pytest.approx(eta_bruta * (1.0 - reduccion), rel=1e-10)

    def test_viscosidad_coherente_psi_0(self):
        """Con Ψ=0 la viscosidad coherente debe ser igual a la bruta."""
        rotor = ViscosidadMolecularRotor()
        tau = rotor.tau_0
        eta_bruta = rotor.viscosidad_bruta(tau)
        eta_coh = rotor.viscosidad_coherente(tau, psi=0.0)
        assert eta_coh == pytest.approx(eta_bruta, rel=1e-10)

    def test_viscosidad_coherente_decrece_con_psi(self):
        """La viscosidad coherente debe decrecer al aumentar Ψ."""
        rotor = ViscosidadMolecularRotor()
        tau = rotor.tau_0
        eta_low = rotor.viscosidad_coherente(tau, psi=0.5)
        eta_high = rotor.viscosidad_coherente(tau, psi=0.999)
        assert eta_high < eta_low

    def test_viscosidad_tau_invalido(self):
        """tau_rot ≤ 0 debe lanzar ValueError."""
        rotor = ViscosidadMolecularRotor()
        with pytest.raises(ValueError):
            rotor.viscosidad_bruta(0.0)
        with pytest.raises(ValueError):
            rotor.viscosidad_bruta(-1e-9)

    def test_viscosidad_psi_invalido(self):
        """Ψ fuera de [0,1] debe lanzar ValueError."""
        rotor = ViscosidadMolecularRotor()
        with pytest.raises(ValueError):
            rotor.viscosidad_coherente(rotor.tau_0, psi=-0.1)
        with pytest.raises(ValueError):
            rotor.viscosidad_coherente(rotor.tau_0, psi=1.1)

    def test_inicializacion_invalida(self):
        """Parámetros negativos en el constructor deben lanzar ValueError."""
        with pytest.raises(ValueError):
            ViscosidadMolecularRotor(tau_0=-1e-9)
        with pytest.raises(ValueError):
            ViscosidadMolecularRotor(eta_0=-1e-3)
        with pytest.raises(ValueError):
            ViscosidadMolecularRotor(alpha=-0.1)


# ===========================================================================
# 3. EntropiaDensidadUPE
# ===========================================================================

class TestEntropiaDensidadUPE:
    """Valida el estimador de densidad de entropía via UPE."""

    def test_inicializacion_defaults(self):
        """La frecuencia de pico por defecto debe ser γ₁ × f₀ ≈ 2003 Hz."""
        upe = EntropiaDensidadUPE()
        assert abs(upe.f_pico - ConstantesKSSHolografico.F_PICO) < 1e-6

    def test_omega_pico(self):
        """ω_pico = 2π × f_pico."""
        upe = EntropiaDensidadUPE()
        assert upe.omega_pico == pytest.approx(2.0 * math.pi * upe.f_pico, rel=1e-10)

    def test_densidad_entropia_escala_con_j_upe(self):
        """La densidad de entropía crece linealmente con J_UPE."""
        upe = EntropiaDensidadUPE()
        s1 = upe.densidad_entropia_bruta(1e12)
        s2 = upe.densidad_entropia_bruta(2e12)
        assert s2 == pytest.approx(2 * s1, rel=1e-10)

    def test_densidad_entropia_positiva(self):
        """La densidad de entropía debe ser positiva para J_UPE > 0."""
        upe = EntropiaDensidadUPE()
        s = upe.densidad_entropia_bruta(1e10)
        assert s > 0

    def test_densidad_entropia_coherente_decrece_con_psi(self):
        """La densidad de entropía efectiva decrece al aumentar Ψ."""
        upe = EntropiaDensidadUPE()
        s_low = upe.densidad_entropia_coherente(1e12, psi=0.5)
        s_high = upe.densidad_entropia_coherente(1e12, psi=0.999)
        assert s_high < s_low

    def test_densidad_entropia_psi_0(self):
        """Con Ψ=0 s_coherente debe coincidir con s_bruta."""
        upe = EntropiaDensidadUPE()
        j = 5e11
        s_bruta = upe.densidad_entropia_bruta(j)
        s_coh = upe.densidad_entropia_coherente(j, psi=0.0)
        assert s_coh == pytest.approx(s_bruta, rel=1e-10)

    def test_j_upe_invalido(self):
        """J_UPE negativo debe lanzar ValueError."""
        upe = EntropiaDensidadUPE()
        with pytest.raises(ValueError):
            upe.densidad_entropia_bruta(-1.0)

    def test_psi_invalido(self):
        """Ψ fuera de [0,1] debe lanzar ValueError."""
        upe = EntropiaDensidadUPE()
        with pytest.raises(ValueError):
            upe.densidad_entropia_coherente(1e12, psi=-0.1)
        with pytest.raises(ValueError):
            upe.densidad_entropia_coherente(1e12, psi=1.5)

    def test_frecuencia_personalizada(self):
        """Debe aceptar frecuencias personalizadas."""
        upe = EntropiaDensidadUPE(f_pico=2003.0)
        assert upe.f_pico == 2003.0


# ===========================================================================
# 4. FlujoHolograficoPerfecto
# ===========================================================================

class TestFlujoHolograficoPerfecto:
    """Valida la evaluación η/s vs límite KSS."""

    def test_cociente_exactamente_kss(self):
        """Con η/s = KSS_BOUND el cociente debe ser 1.0."""
        flujo = FlujoHolograficoPerfecto()
        kss = ConstantesKSSHolografico.KSS_BOUND
        resultado = flujo.calcular(kss, 1.0, psi=0.0)
        assert resultado.cociente_kss == pytest.approx(1.0, rel=1e-10)

    def test_fluido_holografico_con_psi_maximo(self):
        """Con η/s ≈ KSS y Ψ = 0.999999 debe ser holográfico."""
        flujo = FlujoHolograficoPerfecto()
        kss = ConstantesKSSHolografico.KSS_BOUND
        psi = ConstantesKSSHolografico.PSI_COHERENCIA_MAXIMA
        resultado = flujo.calcular(kss * 1.00005, 1.0, psi=psi)
        assert resultado.es_holografico is True

    def test_no_holografico_psi_bajo(self):
        """Con Ψ < 0.999999, incluso con η/s ≈ KSS no debe ser holográfico."""
        flujo = FlujoHolograficoPerfecto()
        kss = ConstantesKSSHolografico.KSS_BOUND
        resultado = flujo.calcular(kss * 1.00005, 1.0, psi=0.9)
        assert resultado.es_holografico is False

    def test_no_holografico_eta_muy_alto(self):
        """Con η/s >> KSS no debe ser holográfico."""
        flujo = FlujoHolograficoPerfecto()
        kss = ConstantesKSSHolografico.KSS_BOUND
        psi = ConstantesKSSHolografico.PSI_COHERENCIA_MAXIMA
        resultado = flujo.calcular(kss * 100.0, 1.0, psi=psi)
        assert resultado.es_holografico is False

    def test_violacion_kss_indica_problema(self):
        """Con η/s < KSS el cociente debe ser < 1."""
        flujo = FlujoHolograficoPerfecto()
        kss = ConstantesKSSHolografico.KSS_BOUND
        resultado = flujo.calcular(kss * 0.5, 1.0, psi=0.0)
        assert resultado.cociente_kss < 1.0

    def test_resultado_contiene_campos_correctos(self):
        """El resultado debe contener todos los campos esperados."""
        flujo = FlujoHolograficoPerfecto()
        kss = ConstantesKSSHolografico.KSS_BOUND
        resultado = flujo.calcular(kss, 1.0, psi=0.5)
        assert isinstance(resultado, ResultadoKSS)
        assert resultado.eta == pytest.approx(kss)
        assert resultado.s == pytest.approx(1.0)
        assert resultado.kss_bound == pytest.approx(kss)
        assert isinstance(resultado.mensaje, str)
        assert len(resultado.mensaje) > 0

    def test_calcular_invalidos(self):
        """Entradas inválidas deben lanzar ValueError."""
        flujo = FlujoHolograficoPerfecto()
        kss = ConstantesKSSHolografico.KSS_BOUND
        with pytest.raises(ValueError):
            flujo.calcular(0.0, 1.0)
        with pytest.raises(ValueError):
            flujo.calcular(kss, 0.0)
        with pytest.raises(ValueError):
            flujo.calcular(kss, 1.0, psi=1.5)

    def test_tolerancia_invalida(self):
        """Una tolerancia < 1 debe lanzar ValueError."""
        with pytest.raises(ValueError):
            FlujoHolograficoPerfecto(tolerancia_holografica=0.5)

    def test_calcular_desde_mediciones(self):
        """calcular_desde_mediciones debe producir un resultado válido."""
        flujo = FlujoHolograficoPerfecto()
        # Elegir tau_rot y j_upe que produzcan η/s ≈ KSS
        resultado = flujo.calcular_desde_mediciones(
            tau_rot=0.4e-9,
            j_upe=1e12,
            psi=0.5,
        )
        assert isinstance(resultado, ResultadoKSS)
        assert resultado.eta_sobre_s > 0


# ===========================================================================
# 5. MicrotubuloCavidadKaluzaKlein
# ===========================================================================

class TestMicrotubuloCavidadKaluzaKlein:
    """Valida el modelo de microtúbulo como cavidad Kaluza-Klein."""

    def test_parametros_defaults(self):
        """Los parámetros biofísicos por defecto deben ser correctos."""
        params = ParametrosMicrotubulo()
        assert params.diametro_externo_nm == pytest.approx(25.0)
        assert params.diametro_interno_nm == pytest.approx(15.0)
        assert params.longitud_dimer_nm == pytest.approx(8.0)
        assert params.n_protofilamentos == 13

    def test_radio_lumen_metros(self):
        """El radio del lumen debe ser 7.5 nm = 7.5e-9 m."""
        mt = MicrotubuloCavidadKaluzaKlein()
        assert abs(mt.radio_lumen_m - 7.5e-9) < 1e-15

    def test_frecuencias_kk_positivas(self):
        """Las frecuencias KK deben ser positivas."""
        mt = MicrotubuloCavidadKaluzaKlein()
        freqs = mt.frecuencias_kk(n_modos=5)
        assert len(freqs) == 5
        assert all(f > 0 for f in freqs)

    def test_frecuencias_kk_monotona(self):
        """Las frecuencias KK deben ser estrictamente crecientes."""
        mt = MicrotubuloCavidadKaluzaKlein()
        freqs = mt.frecuencias_kk(n_modos=5)
        for i in range(len(freqs) - 1):
            assert freqs[i + 1] > freqs[i]

    def test_frecuencias_kk_escalan_linealmente(self):
        """El modo n debe ser n veces el modo 1."""
        mt = MicrotubuloCavidadKaluzaKlein()
        freqs = mt.frecuencias_kk(n_modos=5)
        f1 = freqs[0]
        for n, f in enumerate(freqs, start=1):
            assert f == pytest.approx(n * f1, rel=1e-10)

    def test_frecuencias_qcal_kk(self):
        """Las frecuencias QCAL-KK deben ser γₙ × f₀."""
        mt = MicrotubuloCavidadKaluzaKlein()
        f0 = ConstantesKSSHolografico.F0
        freqs = mt.frecuencias_qcal_kk(n_modos=3)
        assert len(freqs) == 3
        for gamma, f in zip(mt.riemann_zeros[:3], freqs):
            assert f == pytest.approx(gamma * f0, rel=1e-10)

    def test_frecuencia_qcal_primera_aprox_2003(self):
        """La primera frecuencia QCAL-KK debe ser ≈ 2003 Hz."""
        mt = MicrotubuloCavidadKaluzaKlein()
        freqs = mt.frecuencias_qcal_kk(n_modos=1)
        assert abs(freqs[0] - 2003.0) < 5.0

    def test_capacidad_informacion_psi_cero(self):
        """Con Ψ=0, la capacidad debe ser cero."""
        mt = MicrotubuloCavidadKaluzaKlein()
        cap = mt.capacidad_informacion_kk(temperatura_k=310.15, psi=0.0)
        assert cap["capacidad_bits_s"] == pytest.approx(0.0, abs=1e-30)

    def test_capacidad_informacion_psi_max(self):
        """Con Ψ = PSI_COHERENCIA_MAXIMA, es_superfluid debe ser True."""
        mt = MicrotubuloCavidadKaluzaKlein()
        psi_max = ConstantesKSSHolografico.PSI_COHERENCIA_MAXIMA
        cap = mt.capacidad_informacion_kk(psi=psi_max)
        assert cap["es_superfluid"] is True

    def test_capacidad_informacion_psi_bajo(self):
        """Con Ψ < PSI_COHERENCIA_MAXIMA, es_superfluid debe ser False."""
        mt = MicrotubuloCavidadKaluzaKlein()
        cap = mt.capacidad_informacion_kk(psi=0.5)
        assert cap["es_superfluid"] is False

    def test_capacidad_invalida(self):
        """Temperatura o Ψ inválidos deben lanzar ValueError."""
        mt = MicrotubuloCavidadKaluzaKlein()
        with pytest.raises(ValueError):
            mt.capacidad_informacion_kk(temperatura_k=0.0)
        with pytest.raises(ValueError):
            mt.capacidad_informacion_kk(psi=1.5)


# ===========================================================================
# 6. ProtocoloValidacionKSS
# ===========================================================================

class TestProtocoloValidacionKSS:
    """Valida el protocolo completo de validación KSS."""

    def test_protocolo_devuelve_resultado(self):
        """El protocolo debe devolver una instancia de ResultadoProtocoloKSS."""
        protocolo = ProtocoloValidacionKSS()
        resultado = protocolo.validar(tau_rot=0.4e-9, j_upe=1e12, psi=0.5)
        assert isinstance(resultado, ResultadoProtocoloKSS)

    def test_protocolo_campos_correctos(self):
        """El resultado debe contener los campos esperados."""
        protocolo = ProtocoloValidacionKSS()
        resultado = protocolo.validar(tau_rot=0.4e-9, j_upe=1e12, psi=0.5)
        assert resultado.viscosidad_eta > 0
        assert resultado.entropia_s > 0
        assert isinstance(resultado.resultado_kss, ResultadoKSS)
        assert isinstance(resultado.capacidad_microtubulo, dict)
        assert resultado.frecuencia_pico_hz > 0

    def test_protocolo_psi_maximo_fluido_holografico(self):
        """Con los parámetros adecuados y Ψ=0.999999 debe detectar fluido holográfico."""
        # Necesitamos tau_rot y j_upe que produzcan eta/s ≈ KSS_BOUND.
        # Derivamos j_upe a partir de KSS_BOUND con tau_rot = tau_0:
        #   eta = eta_0 * (1 - psi * 0.4966)
        #   s = k_B * j_upe / (hbar * omega_pico) * (1 - psi * 0.4966)
        #   eta/s = eta_0 * hbar * omega_pico / (k_B * j_upe)  (los (1-...) se cancelan)
        # Despejando j_upe tal que eta/s = KSS_BOUND * 1.00002:
        kss = ConstantesKSSHolografico.KSS_BOUND
        hbar = ConstantesKSSHolografico.HBAR
        k_b = ConstantesKSSHolografico.K_B
        rotor = ViscosidadMolecularRotor()
        upe = EntropiaDensidadUPE()

        factor_target = 1.00002  # justo por encima de KSS pero dentro de tolerancia
        # eta/s = eta_0 * hbar * omega_pico / (k_B * j_upe) = kss * factor_target
        # → j_upe = eta_0 * hbar * omega_pico / (k_B * kss * factor_target)
        j_upe = (
            rotor.eta_0
            * hbar
            * upe.omega_pico
            / (k_b * kss * factor_target)
        )

        psi = ConstantesKSSHolografico.PSI_COHERENCIA_MAXIMA
        protocolo = ProtocoloValidacionKSS()
        resultado = protocolo.validar(tau_rot=rotor.tau_0, j_upe=j_upe, psi=psi)
        assert resultado.es_fluido_holografico is True

    def test_protocolo_psi_bajo_no_holografico(self):
        """Con Ψ < PSI_COHERENCIA_MAXIMA no debe ser fluido holográfico."""
        protocolo = ProtocoloValidacionKSS()
        resultado = protocolo.validar(tau_rot=0.4e-9, j_upe=1e12, psi=0.5)
        assert resultado.es_fluido_holografico is False

    def test_separacion_ordenes_es_finita(self):
        """La separación en órdenes de magnitud debe ser un float finito."""
        protocolo = ProtocoloValidacionKSS()
        resultado = protocolo.validar(tau_rot=0.4e-9, j_upe=1e12, psi=0.5)
        assert math.isfinite(resultado.separacion_ordenes_magnitud)

    def test_resumen_es_string(self):
        """El resumen generado debe ser un string no vacío."""
        protocolo = ProtocoloValidacionKSS()
        resultado = protocolo.validar(tau_rot=0.4e-9, j_upe=1e12, psi=0.5)
        resumen = protocolo.resumen(resultado)
        assert isinstance(resumen, str)
        assert len(resumen) > 0

    def test_resumen_contiene_kss(self):
        """El resumen debe mencionar el límite KSS."""
        protocolo = ProtocoloValidacionKSS()
        resultado = protocolo.validar(tau_rot=0.4e-9, j_upe=1e12, psi=0.5)
        resumen = protocolo.resumen(resultado)
        assert "KSS" in resumen

    def test_protocolo_frecuencia_pico_correcta(self):
        """La frecuencia de pico debe ser la de las constantes KSS."""
        protocolo = ProtocoloValidacionKSS()
        resultado = protocolo.validar(tau_rot=0.4e-9, j_upe=1e12, psi=0.5)
        assert resultado.frecuencia_pico_hz == pytest.approx(
            ConstantesKSSHolografico.F_PICO, rel=1e-6
        )


# ===========================================================================
# 7. Integración: physics.__init__ exporta el módulo
# ===========================================================================

class TestPhysicsModuleExports:
    """Verifica que physics.__init__ exporte correctamente las clases KSS."""

    def test_importacion_desde_physics(self):
        """Las clases KSS deben ser accesibles desde el módulo physics."""
        from physics import (
            ConstantesKSSHolografico,
            ViscosidadMolecularRotor,
            EntropiaDensidadUPE,
            FlujoHolograficoPerfecto,
            MicrotubuloCavidadKaluzaKlein,
            ProtocoloValidacionKSS,
        )
        assert ConstantesKSSHolografico is not None
        assert ViscosidadMolecularRotor is not None
        assert EntropiaDensidadUPE is not None
        assert FlujoHolograficoPerfecto is not None
        assert MicrotubuloCavidadKaluzaKlein is not None
        assert ProtocoloValidacionKSS is not None
