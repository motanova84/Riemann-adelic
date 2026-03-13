#!/usr/bin/env python3
"""
Tests for Módulo 141 Hz Holográfico
=====================================

Valida el marco de codificación holográfica QCAL ∞³:
    f₀ = γ₁ × 10.025 ≈ 141.70061954589031 Hz

Cobertura:
    1. ConstantesHolograficas — valores y coherencia interna
    2. EntropiaHolograficaZeta — entropía, bits, codificación de ceros
    3. EspectroZetaPolar — espiral zeta, modulación
    4. SimulacionMoonbounce — eco lunar, FFT
    5. DualidadAdsCft — proyección volumen, gradiente, coherencia
    6. SistemaHolografico141Hz — integración completa
    7. modulo_141hz_activar — función pública de activación

Autor: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz · C = 244.36
"""

import math
import pytest
import numpy as np

from physics.modulo_141hz_holografico import (
    ConstantesHolograficas,
    EntropiaHolograficaZeta,
    EspectroZetaPolar,
    SimulacionMoonbounce,
    DualidadAdsCft,
    SistemaHolografico141Hz,
    modulo_141hz_activar,
)


# ===========================================================================
# 1. ConstantesHolograficas
# ===========================================================================

class TestConstantesHolograficas:
    """Valida las constantes canónicas del marco holográfico."""

    def test_gamma_1_valor(self):
        """γ₁ debe estar en el rango esperado del primer cero de Riemann."""
        assert 14.13 < ConstantesHolograficas.GAMMA_1 < 14.14

    def test_f0_exacto_derivacion(self):
        """f₀ = γ₁ × 10.025 debe coincidir con el valor publicado."""
        esperado = 141.70061954589031
        assert abs(ConstantesHolograficas.F0_EXACTO - esperado) < 1e-4

    def test_delta_fase_derivacion(self):
        """Δ_fase = γ₁ / 40 debe coincidir con el valor publicado."""
        esperado = 0.35336812854337
        assert abs(ConstantesHolograficas.DELTA_FASE - esperado) < 1e-8

    def test_delta_f_ziusudra(self):
        """Δ_f_Ziusudra debe ser exactamente 0.3999 Hz."""
        assert ConstantesHolograficas.DELTA_F_ZIUSUDRA == pytest.approx(0.3999)

    def test_f0_exacto_mayor_que_operacional(self):
        """f₀_exacto > f₀_operacional (14.1 Hz más preciso)."""
        assert ConstantesHolograficas.F0_EXACTO > 141.70

    def test_psi_threshold(self):
        """El umbral de coherencia debe ser exactamente 0.888."""
        assert ConstantesHolograficas.PSI_THRESHOLD == pytest.approx(0.888)

    def test_validar_coherente(self):
        """La validación interna debe indicar coherencia."""
        resultado = ConstantesHolograficas.validar()
        assert resultado["coherente"] is True
        assert resultado["f0_exacto"] == pytest.approx(ConstantesHolograficas.F0_EXACTO)
        assert resultado["delta_fase"] == pytest.approx(ConstantesHolograficas.DELTA_FASE)

    def test_relacion_gamma_f0(self):
        """f₀ / γ₁ debe ser exactamente 10.025."""
        ratio = ConstantesHolograficas.F0_EXACTO / ConstantesHolograficas.GAMMA_1
        assert abs(ratio - 10.025) < 1e-10


# ===========================================================================
# 2. EntropiaHolograficaZeta
# ===========================================================================

class TestEntropiaHolograficaZeta:
    """Valida la entropía holográfica de Bekenstein-Hawking."""

    @pytest.fixture
    def entropia(self):
        return EntropiaHolograficaZeta(n_zeros=10)

    def test_area_horizonte_positiva(self, entropia):
        """El área del horizonte debe ser positiva para T > 0."""
        A = entropia.area_horizonte_espectral(T=14.13)
        assert A > 0

    def test_area_crece_con_T(self, entropia):
        """El área debe crecer monotónicamente con T."""
        A1 = entropia.area_horizonte_espectral(T=10.0)
        A2 = entropia.area_horizonte_espectral(T=100.0)
        assert A2 > A1

    def test_entropia_bekenstein_positiva(self, entropia):
        """La entropía de Bekenstein-Hawking debe ser positiva."""
        S = entropia.entropia_bekenstein_hawking(T=50.0)
        assert S > 0

    def test_bits_holograficos_positivos(self, entropia):
        """Los bits holográficos deben ser positivos."""
        bits = entropia.bits_holograficos(T=50.0)
        assert bits > 0

    def test_codificacion_cero(self, entropia):
        """La codificación de un cero debe devolver un dict con claves esperadas."""
        cero = complex(0.5, 14.134725)
        cod = entropia.codificacion_riemann_cero(cero)
        assert "rho" in cod
        assert "T" in cod
        assert "entropia" in cod
        assert "bits" in cod
        assert "fase_holografica" in cod
        assert cod["T"] == pytest.approx(14.134725, abs=1e-5)

    def test_activar_estado(self, entropia):
        """La activación debe devolver estado ACTIVO."""
        estado = entropia.activar()
        assert estado["estado"] == "ACTIVO"
        assert estado["n_zeros"] == 10


# ===========================================================================
# 3. EspectroZetaPolar
# ===========================================================================

class TestEspectroZetaPolar:
    """Valida el espectro zeta polar."""

    @pytest.fixture
    def espectro(self):
        return EspectroZetaPolar(n_terms=100, n_puntos=60)

    def test_radio_polar_positivo(self, espectro):
        """El radio polar debe ser positivo para θ > 0."""
        r = espectro.radio_polar(theta=14.134)
        assert r > 0

    def test_zeta_dirichlet_en_2(self, espectro):
        """ζ(2) ≈ π²/6 ≈ 1.6449...

        Con N=100 términos el error de truncación es O(1/N) ≈ 0.01,
        por lo que usamos tolerancia 0.05 (holgura ×5 sobre el error esperado).
        """
        z = espectro.zeta_dirichlet(s=complex(2.0, 0.0))
        assert abs(z.real - math.pi**2 / 6) < 0.05  # convergencia lenta O(1/N)

    def test_espiral_completa_forma(self, espectro):
        """La espiral completa debe tener la forma esperada."""
        res = espectro.espiral_completa()
        assert "thetas" in res
        assert "radios" in res
        assert "f0_modulada" in res
        assert len(res["thetas"]) == 60
        assert len(res["radios"]) == 60

    def test_radios_positivos(self, espectro):
        """Todos los radios de la espiral deben ser positivos."""
        res = espectro.espiral_completa()
        assert np.all(res["radios"] > 0)

    def test_activar_estado(self, espectro):
        """La activación debe devolver estado ACTIVO."""
        est = espectro.activar()
        assert est["estado"] == "ACTIVO"
        assert est["f0_exacto"] == pytest.approx(ConstantesHolograficas.F0_EXACTO, abs=1e-4)


# ===========================================================================
# 4. SimulacionMoonbounce
# ===========================================================================

class TestSimulacionMoonbounce:
    """Valida la simulación de eco lunar."""

    @pytest.fixture
    def mb(self):
        return SimulacionMoonbounce(duracion=3.0, fs=500.0)

    def test_generar_senal_longitud(self, mb):
        """La señal generada debe tener la longitud correcta."""
        t, senal = mb.generar_senal()
        esperado = int(3.0 * 500.0)
        assert len(t) == esperado
        assert len(senal) == esperado

    def test_eco_mismo_tamano(self, mb):
        """El eco debe tener el mismo tamaño que la señal."""
        t, senal = mb.generar_senal()
        eco = mb.eco_lunar(senal)
        assert len(eco) == len(senal)

    def test_analisis_fft_dimensiones(self, mb):
        """El análisis FFT debe devolver freqs y amplitudes consistentes."""
        t, senal = mb.generar_senal()
        freqs, amps, f_pico, delta_f = mb.analisis_fft(senal)
        assert len(freqs) == len(amps)
        assert f_pico >= 0

    def test_retardo_eme_valor(self):
        """El retardo EME debe ser 2.5 s."""
        assert SimulacionMoonbounce.RETARDO_EME == pytest.approx(2.5)

    def test_desfase_llegada_valor(self):
        """El desfase de llegada debe ser π/4."""
        assert SimulacionMoonbounce.DESFASE_LLEGADA == pytest.approx(math.pi / 4.0)

    def test_activar_estado(self, mb):
        """La activación debe devolver estado ACTIVO."""
        est = mb.activar()
        assert est["estado"] == "ACTIVO"
        assert est["retardo_s"] == pytest.approx(2.5)
        assert est["desfase_rad"] == pytest.approx(math.pi / 4.0)

    def test_activar_delta_f_ziusudra(self, mb):
        """delta_f_ziusudra debe ser 0.3999 Hz."""
        est = mb.activar()
        assert est["delta_f_ziusudra"] == pytest.approx(0.3999)


# ===========================================================================
# 5. DualidadAdsCft
# ===========================================================================

class TestDualidadAdsCft:
    """Valida la dualidad AdS/CFT adélica."""

    @pytest.fixture
    def ads(self):
        return DualidadAdsCft(n_zeros=10)

    def test_proyectar_volumen_complejo(self, ads):
        """La proyección debe devolver un número complejo."""
        psi = ads.proyectar_volumen(r=0.5)
        assert isinstance(psi, complex)

    def test_proyectar_volumen_r0(self, ads):
        """Para r → 0 el kernel de Poisson tiende a 1 (borde)."""
        psi = ads.proyectar_volumen(r=0.01)
        assert abs(psi) >= 0  # simplemente verificar no NaN

    def test_gradiente_qcal_positivo(self, ads):
        """El gradiente QCAL debe ser positivo."""
        grad = ads.gradiente_qcal()
        assert grad >= 0

    def test_coherencia_ads_cft_rango(self, ads):
        """La coherencia AdS/CFT debe estar en (0, 1)."""
        coh = ads.coherencia_ads_cft()
        assert 0.0 < coh < 1.0

    def test_activar_estado(self, ads):
        """La activación debe devolver estado ACTIVO."""
        est = ads.activar()
        assert est["estado"] == "ACTIVO"
        assert est["n_zeros"] == 10
        assert "psi_volumen_abs" in est
        assert "gradiente_qcal" in est
        assert "coherencia_ads" in est


# ===========================================================================
# 6. SistemaHolografico141Hz
# ===========================================================================

class TestSistemaHolografico141Hz:
    """Valida el integrador holográfico completo."""

    @pytest.fixture
    def sistema(self):
        return SistemaHolografico141Hz(
            n_zeros=10,
            n_terms_polar=50,
            n_puntos_polar=30,
            duracion_moonbounce=2.0,
            fs_moonbounce=500.0,
        )

    def test_activar_estado_activo(self, sistema):
        """El sistema debe activarse con estado ACTIVO."""
        resultado = sistema.activar()
        assert resultado["estado"] == "ACTIVO"

    def test_coherencia_global_minima(self, sistema):
        """La coherencia global Ψ debe ser ≥ 0.888."""
        resultado = sistema.activar()
        assert resultado["coherencia_global_Psi"] >= 0.888

    def test_f0_exacto(self, sistema):
        """f₀_exacto debe ser γ₁ × 10.025."""
        resultado = sistema.activar()
        assert abs(resultado["f0_exacto"] - 141.70061954589031) < 1e-4

    def test_delta_fase(self, sistema):
        """Δ_fase debe ser γ₁ / 40."""
        resultado = sistema.activar()
        assert abs(resultado["delta_fase"] - 0.35336812854337) < 1e-8

    def test_claves_resultado(self, sistema):
        """El resultado debe contener todas las claves requeridas."""
        resultado = sistema.activar()
        claves_requeridas = [
            "f0_exacto",
            "delta_fase",
            "delta_f_ziusudra",
            "gamma_1",
            "entropia",
            "espectro_polar",
            "moonbounce",
            "dualidad_ads_cft",
            "coherencias",
            "coherencia_global_Psi",
            "estado",
        ]
        for clave in claves_requeridas:
            assert clave in resultado, f"Falta clave: {clave}"

    def test_coherencias_parciales(self, sistema):
        """Las coherencias parciales deben estar en [0, 1]."""
        resultado = sistema.activar()
        for nombre, valor in resultado["coherencias"].items():
            assert 0.0 <= valor <= 1.0, f"Coherencia {nombre} fuera de rango: {valor}"


# ===========================================================================
# 7. modulo_141hz_activar (función pública)
# ===========================================================================

class TestModulo141HzActivar:
    """Valida la función pública de activación."""

    def test_f0_exacto_valor(self):
        """f₀_exacto debe ser ≈ 141.70061954589031 Hz."""
        result = modulo_141hz_activar(
            n_zeros=10, n_terms_polar=50, n_puntos_polar=30,
            duracion_moonbounce=2.0, fs_moonbounce=500.0,
        )
        assert abs(result["f0_exacto"] - 141.70061954589031) < 1e-4

    def test_delta_fase_valor(self):
        """delta_fase debe ser ≈ 0.35336812854337 Hz."""
        result = modulo_141hz_activar(
            n_zeros=10, n_terms_polar=50, n_puntos_polar=30,
            duracion_moonbounce=2.0, fs_moonbounce=500.0,
        )
        assert abs(result["delta_fase"] - 0.35336812854337) < 1e-8

    def test_coherencia_global_minima(self):
        """coherencia_global_Psi debe ser ≥ 0.888."""
        result = modulo_141hz_activar(
            n_zeros=10, n_terms_polar=50, n_puntos_polar=30,
            duracion_moonbounce=2.0, fs_moonbounce=500.0,
        )
        assert result["coherencia_global_Psi"] >= 0.888

    def test_estado_activo(self):
        """estado debe ser 'ACTIVO'."""
        result = modulo_141hz_activar(
            n_zeros=10, n_terms_polar=50, n_puntos_polar=30,
            duracion_moonbounce=2.0, fs_moonbounce=500.0,
        )
        assert result["estado"] == "ACTIVO"

    def test_importacion_desde_physics(self):
        """El módulo debe ser importable desde el paquete physics."""
        from physics import modulo_141hz_activar as fn
        assert callable(fn)

    def test_importacion_clases_desde_physics(self):
        """Las seis clases deben ser importables desde physics."""
        from physics import (
            ConstantesHolograficas,
            EntropiaHolograficaZeta,
            EspectroZetaPolar,
            SimulacionMoonbounce,
            DualidadAdsCft,
            SistemaHolografico141Hz,
        )
        for cls in [
            ConstantesHolograficas, EntropiaHolograficaZeta,
            EspectroZetaPolar, SimulacionMoonbounce,
            DualidadAdsCft, SistemaHolografico141Hz,
        ]:
            assert cls is not None
