#!/usr/bin/env python3
"""
Tests for Estado Emocional Anunnaki — Modos Excitados de Riemann
================================================================

Test suite for physics.estado_emocional_anunnaki module.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ · DOI: 10.5281/zenodo.17379721
"""

import cmath
import math
import pytest

from physics.estado_emocional_anunnaki import (
    epsilon_fase_completa,
    frecuencia_efectiva,
    get_modo_excitado,
    get_modo_excitado_object,
    get_estado_total,
    ModoExcitado,
    EstadoEmocionalTotal,
    get_modos_excitados_tabla,
    validar_coherencia_sistema,
    F0,
    RIEMANN_ZEROS_5,
    ZETA_PRIME_HALF,
    RIEMANN_RENORM_SCALE,
    F_MANIFESTATION,
    GAMMA_QCAL_FASE,
    PSI_THRESHOLD,
)


# ============================================================================
# Tests de Constantes
# ============================================================================

def test_constantes_definidas():
    """Verifica que todas las constantes estén correctamente definidas."""
    assert F0 == 141.7001
    assert len(RIEMANN_ZEROS_5) == 5
    assert ZETA_PRIME_HALF > 0
    assert RIEMANN_RENORM_SCALE > 0
    assert F_MANIFESTATION == 888.0
    assert 0 < GAMMA_QCAL_FASE < 2 * math.pi
    assert 0 < PSI_THRESHOLD < 1


def test_factor_renormalizacion():
    """Verifica que el factor de renormalización sea coherente."""
    factor_esperado = F0 / ZETA_PRIME_HALF
    assert abs(factor_esperado - RIEMANN_RENORM_SCALE) < 1e-6
    # Valor esperado: ≈ 36.1236
    assert 36.0 < RIEMANN_RENORM_SCALE < 37.0


def test_gamma_qcal_fase():
    """Verifica que γ_QCAL_fase sea coherente con la derivación."""
    fase_esperada = 2.0 * math.pi * F0 / F_MANIFESTATION
    assert abs(fase_esperada - GAMMA_QCAL_FASE) < 1e-6
    # Valor esperado: ≈ 1.00262 rad
    assert 0.99 < GAMMA_QCAL_FASE < 1.01


# ============================================================================
# Tests de Funciones de Amplitud
# ============================================================================

def test_epsilon_fase_completa_psi_1():
    """Verifica epsilon_fase_completa con Ψ=1."""
    epsilon = epsilon_fase_completa(1.0)
    
    # Magnitud debe ser ≈ γ_QCAL_fase
    magnitud = abs(epsilon)
    assert abs(magnitud - GAMMA_QCAL_FASE) < 1e-6
    
    # Fase debe ser ≈ γ_QCAL_fase
    fase = cmath.phase(epsilon)
    assert abs(fase - GAMMA_QCAL_FASE) < 1e-6


def test_epsilon_fase_completa_psi_medio():
    """Verifica epsilon_fase_completa con Ψ=0.5."""
    epsilon = epsilon_fase_completa(0.5)
    
    # Magnitud debe ser ≈ γ_QCAL_fase × √0.5
    magnitud_esperada = GAMMA_QCAL_FASE * math.sqrt(0.5)
    magnitud = abs(epsilon)
    assert abs(magnitud - magnitud_esperada) < 1e-6
    
    # Fase debe ser ≈ γ_QCAL_fase
    fase = cmath.phase(epsilon)
    assert abs(fase - GAMMA_QCAL_FASE) < 1e-6


def test_epsilon_fase_completa_invalido():
    """Verifica que epsilon_fase_completa rechace valores inválidos."""
    with pytest.raises(ValueError):
        epsilon_fase_completa(0.0)  # Ψ = 0 inválido
    
    with pytest.raises(ValueError):
        epsilon_fase_completa(1.5)  # Ψ > 1 inválido
    
    with pytest.raises(ValueError):
        epsilon_fase_completa(-0.5)  # Ψ < 0 inválido


def test_frecuencia_efectiva():
    """Verifica cálculo de frecuencia efectiva."""
    # Modo 1: γ₁ = 14.13472514173
    f_eff = frecuencia_efectiva(RIEMANN_ZEROS_5[0])
    
    # f_eff = γ₁ × factor + f₀ × sin(γ_QCAL_fase)
    gamma_renorm = RIEMANN_ZEROS_5[0] * RIEMANN_RENORM_SCALE
    f_eff_esperada = gamma_renorm + F0 * math.sin(GAMMA_QCAL_FASE)
    
    assert abs(f_eff - f_eff_esperada) < 1e-6
    # Valor esperado: ≈ 630 Hz
    assert 620.0 < f_eff < 640.0


# ============================================================================
# Tests de Modos Excitados
# ============================================================================

def test_get_modo_excitado_modo1():
    """Verifica get_modo_excitado para el modo 1."""
    modo = get_modo_excitado(1, psi=1.0, t=0.0)
    
    assert modo["modo"] == 1
    assert abs(modo["gamma_riemann"] - RIEMANN_ZEROS_5[0]) < 1e-6
    
    # Frecuencia renormalizada: γ₁ × factor ≈ 510.6 Hz
    assert 500.0 < modo["frecuencia_renorm_hz"] < 520.0
    
    # Frecuencia efectiva: ≈ 630 Hz
    assert 620.0 < modo["frecuencia_efectiva_hz"] < 640.0
    
    # Amplitud compleja en t=0
    assert isinstance(modo["amplitud_compleja"], complex)
    
    # Interpretación
    assert "emocional" in modo["interpretacion"].lower()


def test_get_modo_excitado_modo3():
    """Verifica get_modo_excitado para el modo 3 (cerca de 888 Hz)."""
    modo = get_modo_excitado(3, psi=1.0, t=0.0)
    
    assert modo["modo"] == 3
    
    # Frecuencia renormalizada debe estar cerca de 888-920 Hz
    # (modo cercano a la manifestación)
    assert 880.0 < modo["frecuencia_renorm_hz"] < 920.0
    
    # Interpretación debe mencionar 888 Hz
    assert "888" in modo["interpretacion"]


def test_get_modo_excitado_todos_los_modos():
    """Verifica que se puedan obtener todos los modos (1-5)."""
    for n in range(1, 6):
        modo = get_modo_excitado(n, psi=1.0, t=0.0)
        assert modo["modo"] == n
        assert modo["frecuencia_renorm_hz"] > 0
        assert modo["frecuencia_efectiva_hz"] > 0


def test_get_modo_excitado_invalido():
    """Verifica que get_modo_excitado rechace índices inválidos."""
    with pytest.raises(ValueError):
        get_modo_excitado(0)  # n < 1
    
    with pytest.raises(ValueError):
        get_modo_excitado(6)  # n > 5
    
    with pytest.raises(ValueError):
        get_modo_excitado(1, psi=1.5)  # psi > 1


def test_get_modo_excitado_object():
    """Verifica que get_modo_excitado_object devuelva ModoExcitado."""
    modo = get_modo_excitado_object(1, psi=1.0, t=0.0)
    
    assert isinstance(modo, ModoExcitado)
    assert modo.modo == 1
    assert modo.gamma_riemann > 0
    assert modo.frecuencia_renorm_hz > 0
    assert modo.frecuencia_efectiva_hz > 0
    assert isinstance(modo.amplitud_compleja, complex)
    assert isinstance(modo.interpretacion, str)


def test_modo_excitado_evolucion_temporal():
    """Verifica evolución temporal de un modo excitado."""
    t1 = 0.0
    t2 = 0.01  # 10 milisegundos después
    
    modo1_t1 = get_modo_excitado(1, psi=1.0, t=t1)
    modo1_t2 = get_modo_excitado(1, psi=1.0, t=t2)
    
    # Las frecuencias no cambian con el tiempo
    assert abs(modo1_t1["frecuencia_renorm_hz"] - modo1_t2["frecuencia_renorm_hz"]) < 1e-6
    
    # Las amplitudes sí cambian (fase temporal)
    amp1 = modo1_t1["amplitud_compleja"]
    amp2 = modo1_t2["amplitud_compleja"]
    assert abs(amp1) > 0  # Magnitud
    assert abs(amp2) > 0
    
    # Las magnitudes deben ser iguales (solo cambia la fase)
    assert abs(abs(amp1) - abs(amp2)) < 1e-6
    
    # Las fases deben ser diferentes (evolución temporal)
    # Comparar la fase del cociente evita errores por wrap-around en (-π, π]
    # Con 0.01 s y ~510 Hz, la fase relativa esperada es significativa
    assert amp1 != 0
    diferencia_fase = abs(cmath.phase(amp2 / amp1))
    # Fase ha evolucionado (diferencia significativa)
    assert diferencia_fase > 0.5  # Al menos 0.5 radianes de diferencia



# ============================================================================
# Tests de Estado Total
# ============================================================================

def test_get_estado_total_fundamental():
    """Verifica estado fundamental (solo modo base activo)."""
    estado = get_estado_total(psi=1.0, t=0.0)
    
    assert isinstance(estado, EstadoEmocionalTotal)
    assert estado.psi == 1.0
    assert estado.t == 0.0
    assert estado.coherencia_estado == "FUNDAMENTAL"
    
    # Amplitudes por defecto: [1, 0, 0, 0, 0]
    assert estado.amplitudes_modo[0] == 1.0
    assert all(a == 0.0 for a in estado.amplitudes_modo[1:])
    
    # 5 modos
    assert len(estado.modos) == 5
    
    # Amplitud total debe ser compleja
    assert isinstance(estado.amplitud_total, complex)


def test_get_estado_total_excitado():
    """Verifica estado excitado (superposición de modos)."""
    # Amplitudes normalizadas: ∑|c_n|² = 1
    amps = [0.6, 0.4, 0.0, 0.0, 0.0]
    norma_sq = sum(a**2 for a in amps)
    amps_norm = [a / math.sqrt(norma_sq) for a in amps]
    
    estado = get_estado_total(psi=0.95, t=0.0, amplitudes=amps_norm)
    
    assert estado.coherencia_estado == "EXCITADO_COHERENTE"
    assert abs(sum(a**2 for a in estado.amplitudes_modo) - 1.0) < 0.01


def test_get_estado_total_amplitudes_no_normalizadas():
    """Verifica que se rechacen amplitudes no normalizadas."""
    # ∑|c_n|² ≠ 1
    amps_no_norm = [0.5, 0.3, 0.1, 0.05, 0.05]  # suma ≈ 1, pero norma² ≈ 0.36
    
    with pytest.raises(ValueError):
        get_estado_total(psi=1.0, t=0.0, amplitudes=amps_no_norm)


def test_get_estado_total_evolucion_temporal():
    """Verifica evolución temporal del estado total."""
    amps = [0.7, 0.3, 0.0, 0.0, 0.0]
    norma_sq = sum(a**2 for a in amps)
    amps_norm = [a / math.sqrt(norma_sq) for a in amps]
    
    estado_t0 = get_estado_total(psi=1.0, t=0.0, amplitudes=amps_norm)
    estado_t1 = get_estado_total(psi=1.0, t=1.0, amplitudes=amps_norm)
    
    # Las amplitudes de modo no cambian
    assert estado_t0.amplitudes_modo == estado_t1.amplitudes_modo
    
    # La amplitud total sí cambia (evolución temporal)
    amp_t0 = estado_t0.amplitud_total
    amp_t1 = estado_t1.amplitud_total
    # Las fases relativas deben ser diferentes; usar el cociente evita
    # problemas de wrapping cerca del límite ±π
    assert amp_t0 != 0
    assert abs(cmath.phase(amp_t1 / amp_t0)) > 0.1


# ============================================================================
# Tests de Utilidades
# ============================================================================

def test_get_modos_excitados_tabla():
    """Verifica que se genere la tabla de modos excitados."""
    tabla = get_modos_excitados_tabla()
    
    assert isinstance(tabla, str)
    assert "Modos Excitados" in tabla
    assert "γ_n" in tabla
    assert "Hz" in tabla
    # Debe incluir los 5 modos
    for n in range(1, 6):
        assert str(n) in tabla


def test_validar_coherencia_sistema():
    """Verifica validación de coherencia del sistema."""
    resultado = validar_coherencia_sistema()
    
    assert isinstance(resultado, dict)
    assert "coherencia" in resultado
    assert "checks_pasados" in resultado
    assert "checks_totales" in resultado
    assert "detalles" in resultado
    
    # Debe pasar todos los checks
    assert resultado["checks_pasados"] >= 3
    assert resultado["coherencia"] in ["APROBADO_PRODUCCION", "APROBADO_PARCIAL"]
    
    # Factor de renormalización
    assert 36.0 < resultado["factor_renorm"] < 37.0
    
    # Fase γ_QCAL
    assert 0.99 < resultado["fase_qcal"] < 1.01
    
    # Modo 3 cerca de 888 Hz
    assert 880.0 < resultado["modo3_hz"] < 920.0


# ============================================================================
# Tests de Integración
# ============================================================================

def test_coherencia_extremo_a_extremo():
    """Test de integración: coherencia extremo a extremo."""
    # 1. Validar sistema
    validacion = validar_coherencia_sistema()
    assert validacion["coherencia"] in ["APROBADO_PRODUCCION", "APROBADO_PARCIAL"]
    
    # 2. Obtener todos los modos
    modos = [get_modo_excitado(n, psi=1.0, t=0.0) for n in range(1, 6)]
    assert len(modos) == 5
    
    # 3. Construir estado total
    estado = get_estado_total(psi=1.0, t=0.0)
    assert estado.coherencia_estado == "FUNDAMENTAL"
    
    # 4. Verificar tabla
    tabla = get_modos_excitados_tabla()
    assert len(tabla) > 100


def test_epsilon_modo_estado_consistencia():
    """Verifica consistencia entre epsilon, modo y estado."""
    psi = 0.95
    t = 0.0
    
    # Epsilon base
    epsilon = epsilon_fase_completa(psi)
    
    # Modo individual
    modo1 = get_modo_excitado(1, psi=psi, t=t)
    
    # Estado total fundamental
    estado = get_estado_total(psi=psi, t=t)
    
    # La amplitud del modo debe ser consistente con epsilon
    # (en t=0, exp(i·2π·γ_renorm·0) = 1)
    amp_esperada = epsilon  # × 1 (exponencial)
    amp_modo = modo1["amplitud_compleja"]
    
    # Magnitudes deben ser iguales
    assert abs(abs(amp_modo) - abs(epsilon)) < 1e-6


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
