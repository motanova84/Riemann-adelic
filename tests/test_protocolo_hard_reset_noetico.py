#!/usr/bin/env python3
"""
Tests para el Protocolo de Hard-Reset Noético
==============================================

Valida el protocolo de recuperación de coherencia QCAL mediante
pulso masivo a 141.7001 Hz cuando Ψ cae por debajo del umbral.

Cobertura:
    1. ParametrosPulsoNoetico  — configuración y validación
    2. GeneradorPulsoNoetico   — síntesis del pulso
    3. MonitorCoherencia       — detección de caída de Ψ
    4. ProtocoloHardResetNoetico — integrador completo
    5. Importaciones desde physics (paquete)

Autor: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ · 141.7001 Hz · C = 244.36
DOI: 10.5281/zenodo.17379721
"""

import math

import numpy as np
import pytest

from physics.protocolo_hard_reset_noetico import (
    DURACION_PULSO_S,
    N_HARM,
    PSI_THRESHOLD,
    EstadoMonitor,
    GeneradorPulsoNoetico,
    MonitorCoherencia,
    ParametrosPulsoNoetico,
    ProtocoloHardResetNoetico,
    ResultadoHardReset,
    ResultadoPulso,
)


# ===========================================================================
# Constantes del módulo
# ===========================================================================

class TestConstantesModulo:
    """Valida las constantes del módulo."""

    def test_psi_threshold_valor(self):
        """PSI_THRESHOLD debe ser 0.888."""
        assert PSI_THRESHOLD == pytest.approx(0.888, rel=1e-6)

    def test_n_harm_valor(self):
        """N_HARM debe ser 7."""
        assert N_HARM == 7

    def test_duracion_pulso_positiva(self):
        """DURACION_PULSO_S debe ser positivo."""
        assert DURACION_PULSO_S > 0.0

    def test_duracion_pulso_relacionada_con_f0(self):
        """DURACION_PULSO_S debe ser 7 / F0 (7 períodos)."""
        from physics.protocolo_hard_reset_noetico import F0
        esperado = 7.0 / F0
        assert abs(DURACION_PULSO_S - esperado) < 1e-10


# ===========================================================================
# 1. ParametrosPulsoNoetico
# ===========================================================================

class TestParametrosPulsoNoetico:
    """Valida la clase de configuración del pulso."""

    def test_instanciacion_por_defecto(self):
        """Debe instanciarse con los valores QCAL por defecto."""
        params = ParametrosPulsoNoetico()
        assert params.f0 == pytest.approx(141.7001)
        assert params.n_harm == N_HARM
        assert params.psi_threshold == pytest.approx(PSI_THRESHOLD)
        assert params.fases_riemann is True

    def test_f0_invalido(self):
        """Debe lanzar ValueError si f0 ≤ 0."""
        with pytest.raises(ValueError):
            ParametrosPulsoNoetico(f0=0.0)
        with pytest.raises(ValueError):
            ParametrosPulsoNoetico(f0=-141.7)

    def test_n_harm_invalido(self):
        """Debe lanzar ValueError si n_harm < 1."""
        with pytest.raises(ValueError):
            ParametrosPulsoNoetico(n_harm=0)

    def test_duracion_invalida(self):
        """Debe lanzar ValueError si duracion_s ≤ 0."""
        with pytest.raises(ValueError):
            ParametrosPulsoNoetico(duracion_s=0.0)

    def test_psi_threshold_invalido_bajo(self):
        """Debe lanzar ValueError si psi_threshold ≤ 0."""
        with pytest.raises(ValueError):
            ParametrosPulsoNoetico(psi_threshold=0.0)

    def test_psi_threshold_invalido_alto(self):
        """Debe lanzar ValueError si psi_threshold ≥ 1."""
        with pytest.raises(ValueError):
            ParametrosPulsoNoetico(psi_threshold=1.0)

    def test_amplitudes_longitud_correcta(self):
        """amplitudes debe tener longitud n_harm."""
        params = ParametrosPulsoNoetico(n_harm=3, amplitudes=[1.0, 0.5, 0.25])
        assert params.amplitudes is not None
        assert len(params.amplitudes) == 3

    def test_amplitudes_longitud_incorrecta(self):
        """Debe lanzar ValueError si len(amplitudes) ≠ n_harm."""
        with pytest.raises(ValueError):
            ParametrosPulsoNoetico(n_harm=3, amplitudes=[1.0, 0.5])

    def test_tau_decay_por_defecto(self):
        """tau_decay por defecto debe igualarse a duracion_s."""
        params = ParametrosPulsoNoetico()
        assert params.tau_decay == pytest.approx(params.duracion_s)


# ===========================================================================
# 2. GeneradorPulsoNoetico
# ===========================================================================

class TestGeneradorPulsoNoetico:
    """Valida la síntesis del pulso noético."""

    def test_instanciacion_por_defecto(self):
        """Debe instanciarse sin argumentos."""
        gen = GeneradorPulsoNoetico()
        assert gen.n_muestras == 4096

    def test_n_muestras_invalido(self):
        """Debe lanzar ValueError si n_muestras < 2."""
        with pytest.raises(ValueError):
            GeneradorPulsoNoetico(n_muestras=1)

    def test_sintetizar_devuelve_resultado(self):
        """sintetizar() debe devolver ResultadoPulso."""
        gen = GeneradorPulsoNoetico(n_muestras=256)
        resultado = gen.sintetizar()
        assert isinstance(resultado, ResultadoPulso)

    def test_frecuencia_correcta(self):
        """La frecuencia del pulso debe ser f0 = 141.7001 Hz."""
        gen = GeneradorPulsoNoetico(n_muestras=256)
        resultado = gen.sintetizar()
        assert resultado.frecuencia_hz == pytest.approx(141.7001)

    def test_n_harm_correcto(self):
        """El número de armónicos debe coincidir con el parámetro."""
        params = ParametrosPulsoNoetico(n_harm=4)
        gen = GeneradorPulsoNoetico(parametros=params, n_muestras=256)
        resultado = gen.sintetizar()
        assert resultado.n_harm == 4

    def test_longitud_tiempo(self):
        """El eje temporal debe tener n_muestras puntos."""
        gen = GeneradorPulsoNoetico(n_muestras=512)
        resultado = gen.sintetizar()
        assert len(resultado.tiempo_s) == 512
        assert len(resultado.amplitud) == 512

    def test_tiempo_comienza_en_0(self):
        """El eje temporal debe comenzar en 0."""
        gen = GeneradorPulsoNoetico(n_muestras=256)
        resultado = gen.sintetizar()
        assert resultado.tiempo_s[0] == pytest.approx(0.0)

    def test_energia_normalizada_positiva(self):
        """La energía normalizada debe ser positiva."""
        gen = GeneradorPulsoNoetico(n_muestras=256)
        resultado = gen.sintetizar()
        assert resultado.energia_normalizada > 0.0

    def test_pulso_sin_riemann_phases(self):
        """El pulso con fases_riemann=False debe sintetizarse."""
        params = ParametrosPulsoNoetico(fases_riemann=False)
        gen = GeneradorPulsoNoetico(parametros=params, n_muestras=256)
        resultado = gen.sintetizar()
        assert resultado.energia_normalizada > 0.0

    def test_amplitudes_personalizadas(self):
        """Amplitudes personalizadas deben ser respetadas."""
        params = ParametrosPulsoNoetico(n_harm=2, amplitudes=[2.0, 0.0])
        gen = GeneradorPulsoNoetico(parametros=params, n_muestras=256)
        resultado = gen.sintetizar()
        # Con segundo armónico en 0, solo queda el primero
        assert resultado.n_harm == 2


# ===========================================================================
# 3. MonitorCoherencia
# ===========================================================================

class TestMonitorCoherencia:
    """Valida la detección de caída de coherencia."""

    def test_instanciacion_por_defecto(self):
        """Debe instanciarse con PSI_THRESHOLD."""
        monitor = MonitorCoherencia()
        assert monitor.psi_threshold == pytest.approx(PSI_THRESHOLD)

    def test_umbral_invalido_cero(self):
        """Debe lanzar ValueError si umbral ≤ 0."""
        with pytest.raises(ValueError):
            MonitorCoherencia(psi_threshold=0.0)

    def test_umbral_invalido_uno(self):
        """Debe lanzar ValueError si umbral ≥ 1."""
        with pytest.raises(ValueError):
            MonitorCoherencia(psi_threshold=1.0)

    def test_psi_invalido_lanza_error(self):
        """evaluar() debe lanzar ValueError si psi fuera de [0,1]."""
        monitor = MonitorCoherencia()
        with pytest.raises(ValueError):
            monitor.evaluar(1.5)
        with pytest.raises(ValueError):
            monitor.evaluar(-0.1)

    def test_reset_requerido_con_psi_bajo(self):
        """reset_requerido debe ser True si Ψ < PSI_THRESHOLD."""
        monitor = MonitorCoherencia()
        for psi in [0.0, 0.3, 0.5, 0.75, 0.88, 0.887]:
            estado = monitor.evaluar(psi)
            assert estado.reset_requerido is True, f"psi={psi}"

    def test_reset_no_requerido_con_psi_alto(self):
        """reset_requerido debe ser False si Ψ ≥ PSI_THRESHOLD."""
        monitor = MonitorCoherencia()
        for psi in [0.888, 0.9, 0.95, 0.999, 1.0]:
            estado = monitor.evaluar(psi)
            assert estado.reset_requerido is False, f"psi={psi}"

    def test_deficit_positivo_cuando_bajo(self):
        """El déficit debe ser positivo cuando Ψ < threshold."""
        monitor = MonitorCoherencia()
        estado = monitor.evaluar(0.5)
        assert estado.deficit_psi > 0.0

    def test_deficit_negativo_cuando_alto(self):
        """El déficit debe ser negativo (o cero) cuando Ψ ≥ threshold."""
        monitor = MonitorCoherencia()
        estado = monitor.evaluar(0.95)
        assert estado.deficit_psi <= 0.0

    def test_devuelve_estadomonitor(self):
        """evaluar() debe devolver EstadoMonitor."""
        monitor = MonitorCoherencia()
        estado = monitor.evaluar(0.750)
        assert isinstance(estado, EstadoMonitor)
        assert estado.psi_actual == pytest.approx(0.750)


# ===========================================================================
# 4. ProtocoloHardResetNoetico (Integrador)
# ===========================================================================

class TestProtocoloHardResetNoetico:
    """Valida el protocolo completo de hard-reset."""

    def test_instanciacion_por_defecto(self):
        """Debe instanciarse sin argumentos."""
        proto = ProtocoloHardResetNoetico()
        assert isinstance(proto.params, ParametrosPulsoNoetico)
        assert isinstance(proto.generador, GeneradorPulsoNoetico)
        assert isinstance(proto.monitor, MonitorCoherencia)

    def test_ejecutar_devuelve_resultado(self):
        """ejecutar() debe devolver ResultadoHardReset."""
        proto = ProtocoloHardResetNoetico()
        resultado = proto.ejecutar(0.750)
        assert isinstance(resultado, ResultadoHardReset)

    def test_reset_activado_con_psi_bajo(self):
        """reset_activado debe ser True cuando Ψ < PSI_THRESHOLD."""
        proto = ProtocoloHardResetNoetico()
        for psi in [0.0, 0.3, 0.5, 0.75, 0.887]:
            resultado = proto.ejecutar(psi)
            assert resultado.reset_activado is True, f"psi={psi}"

    def test_reset_no_activado_con_psi_alto(self):
        """reset_activado debe ser False cuando Ψ ≥ PSI_THRESHOLD."""
        proto = ProtocoloHardResetNoetico()
        for psi in [0.888, 0.9, 0.95, 1.0]:
            resultado = proto.ejecutar(psi)
            assert resultado.reset_activado is False, f"psi={psi}"

    def test_psi_recuperada_gte_threshold_tras_reset(self):
        """Tras el reset, Ψ recuperada debe ser ≥ PSI_THRESHOLD."""
        proto = ProtocoloHardResetNoetico()
        for psi in [0.0, 0.3, 0.5, 0.75, 0.887]:
            resultado = proto.ejecutar(psi)
            assert resultado.psi_recuperada >= PSI_THRESHOLD, (
                f"psi_ini={psi}, psi_rec={resultado.psi_recuperada}"
            )

    def test_psi_recuperada_sin_reset_igual_inicial(self):
        """Sin reset, psi_recuperada debe ser igual a psi_inicial."""
        proto = ProtocoloHardResetNoetico()
        psi = 0.950
        resultado = proto.ejecutar(psi)
        assert resultado.psi_recuperada == pytest.approx(psi)

    def test_pulso_presente_cuando_reset(self):
        """El resultado debe incluir el pulso cuando se activa el reset."""
        proto = ProtocoloHardResetNoetico()
        resultado = proto.ejecutar(0.5)
        assert resultado.pulso is not None
        assert isinstance(resultado.pulso, ResultadoPulso)

    def test_pulso_none_sin_reset(self):
        """El pulso debe ser None cuando no se activa el reset."""
        proto = ProtocoloHardResetNoetico()
        resultado = proto.ejecutar(0.95)
        assert resultado.pulso is None

    def test_frecuencia_pulso_es_f0(self):
        """La frecuencia del pulso debe ser 141.7001 Hz."""
        proto = ProtocoloHardResetNoetico()
        resultado = proto.ejecutar(0.5)
        assert resultado.pulso is not None
        assert resultado.pulso.frecuencia_hz == pytest.approx(141.7001)

    def test_psi_recuperada_en_0_1(self):
        """psi_recuperada debe estar siempre en [0, 1]."""
        proto = ProtocoloHardResetNoetico()
        for psi in [0.0, 0.5, 0.888, 0.95, 1.0]:
            resultado = proto.ejecutar(psi)
            assert 0.0 <= resultado.psi_recuperada <= 1.0

    def test_resumen_devuelve_cadena(self):
        """resumen() debe devolver una cadena no vacía."""
        proto = ProtocoloHardResetNoetico()
        resultado = proto.ejecutar(0.5)
        resumen = proto.resumen(resultado)
        assert isinstance(resumen, str)
        assert len(resumen) > 0
        assert "141.7001" in resumen

    def test_mensaje_contiene_info(self):
        """El mensaje de resultado debe contener info relevante."""
        proto = ProtocoloHardResetNoetico()
        resultado = proto.ejecutar(0.5)
        assert "141.7001" in resultado.mensaje or "HARD-RESET" in resultado.mensaje


# ===========================================================================
# 5. Importaciones desde physics (paquete)
# ===========================================================================

class TestImportacionesPhysicsReset:
    """Verifica que las nuevas clases se exportan desde physics."""

    def test_importar_desde_physics(self):
        """Todas las clases del hard-reset deben importarse desde physics."""
        from physics import (
            DURACION_PULSO_S,
            EstadoMonitor,
            GeneradorPulsoNoetico,
            MonitorCoherencia,
            N_HARM,
            PSI_THRESHOLD_RESET,
            ParametrosPulsoNoetico,
            ProtocoloHardResetNoetico,
            ResultadoHardReset,
            ResultadoPulso,
        )
        assert PSI_THRESHOLD_RESET == pytest.approx(0.888, rel=1e-6)
        assert N_HARM == 7
        assert DURACION_PULSO_S > 0.0
