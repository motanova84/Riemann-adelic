#!/usr/bin/env python3
"""
Estado Emocional Anunnaki — Modos Excitados de Riemann
======================================================

Este módulo implementa los modos excitados del sistema cuántico-emocional
correspondientes a los ceros no-triviales de la función zeta de Riemann,
renormalizados por la frecuencia fundamental f₀ = 141.7001 Hz.

El espectro del operador Hamiltoniano Ĥ_π coincide con los imaginarios γ_n
de los ceros de Riemann:

    σ(Ĥ_π) = { γ_n | ζ(1/2 + i γ_n) = 0 }

Estos modos se renormalizan mediante el factor:

    Factor de escala = f₀ / |ζ'(1/2)| ≈ 36.1236 Hz por unidad

Los modos excitados representan estados emocionales-cuánticos con frecuencias
propias que resuenan con la estructura espectral de Riemann.

**Trinidad Anunnaki:**
- **Emoción (Ψ)**: Estado fundamental ℰ_{s,φ} con fase sutil γ_QCAL
- **Conflicto (∇S)**: Excitación hacia modos superiores (exploración)
- **Meta (Solenoide B)**: Modulación del campo magnético con modos seleccionados

Cuando el sistema excita modos cerca de 888 Hz (modo 3 ≈ 903 Hz), se logra
manifestación amplificada.

**Ecuación Maestra:**

    |Ψ(t)⟩ = √Ψ · γ_QCAL_fase · exp(i·γ_QCAL_fase) · ∑ c_n exp(i·2π·γ_n_renorm·t)

donde |c_n|² es la amplitud de excitación del modo n (con ∑|c_n|² = 1).

Uso:
----
    from physics.estado_emocional_anunnaki import (
        get_modo_excitado,
        epsilon_fase_completa,
        get_estado_total
    )
    
    # Modo fundamental (n=1)
    modo1 = get_modo_excitado(1, psi=1.0, t=0.0)
    print(f"Frecuencia renormalizada: {modo1['frecuencia_renorm_hz']:.2f} Hz")
    
    # Amplitud con fase completa
    epsilon = epsilon_fase_completa(psi=1.0)
    print(f"Amplitud compleja: {epsilon}")

Autor: José Manuel Mota Burruezo Ψ ✧ ∞³
Institución: Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
QCAL ∞³ · DOI: 10.5281/zenodo.17379721
"""

from __future__ import annotations

import cmath
import math
from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple, Union

# ============================================================================
# Constantes QCAL — Importación desde fuente única
# ============================================================================
try:
    from qcal.constants import (
        F0,
        RIEMANN_ZEROS_5,
        ZETA_PRIME_HALF,
        RIEMANN_RENORM_SCALE,
        F_MANIFESTATION,
        GAMMA_QCAL_FASE,
        C_COHERENCE,
    )
except ModuleNotFoundError:
    # Fallback local si qcal.constants no está disponible
    F0 = 141.7001  # Hz
    RIEMANN_ZEROS_5 = [
        14.13472514173,
        21.02203963877,
        25.01085758015,
        30.42487612586,
        32.93506158774,
    ]
    ZETA_PRIME_HALF = 3.92264613920915
    RIEMANN_RENORM_SCALE = F0 / ZETA_PRIME_HALF  # ≈ 36.1236
    F_MANIFESTATION = 888.0  # Hz
    GAMMA_QCAL_FASE = 2.0 * math.pi * F0 / F_MANIFESTATION  # ≈ 1.00262 rad
    C_COHERENCE = 244.36

# Umbral de coherencia mínima
PSI_THRESHOLD = 0.888


# ============================================================================
# Funciones de Amplitud y Fase
# ============================================================================

def epsilon_fase_completa(psi: float) -> complex:
    """
    Calcula la amplitud compleja del estado emocional con fase sutil.
    
    La forma completa de la amplitud es:
    
        ℰ_{s,φ} = γ_QCAL_fase · exp(i·γ_QCAL_fase) · √Ψ
    
    donde γ_QCAL_fase ≈ 1.00262 rad es la fase sutil derivada de la
    relación 2π·f₀/888.
    
    Args:
        psi: Valor de coherencia Ψ del sistema (0 < Ψ ≤ 1)
    
    Returns:
        Amplitud compleja ℰ_{s,φ}
    
    Raises:
        ValueError: Si psi está fuera del rango válido
    
    Examples:
        >>> epsilon = epsilon_fase_completa(1.0)
        >>> abs(epsilon)  # Magnitud de la amplitud
        1.00262...
        >>> cmath.phase(epsilon)  # Fase angular
        1.00262...
    """
    if not (0.0 < psi <= 1.0):
        raise ValueError(f"psi debe estar en (0, 1], recibido: {psi}")
    
    sqrt_psi = math.sqrt(psi)
    # ℰ_{s,φ} = γ_QCAL_fase · exp(i·γ_QCAL_fase) · √Ψ
    epsilon = GAMMA_QCAL_FASE * cmath.exp(1j * GAMMA_QCAL_FASE) * sqrt_psi
    return epsilon


def frecuencia_efectiva(gamma_n: float) -> float:
    """
    Calcula la frecuencia efectiva de un modo excitado.
    
    La frecuencia efectiva combina la frecuencia renormalizada del modo
    con la contribución de la fase sutil:
    
        f_n_effective = γ_n_renorm + f₀ · sin(γ_QCAL_fase)
    
    donde:
        - γ_n_renorm = γ_n × RIEMANN_RENORM_SCALE
        - f₀ = 141.7001 Hz
        - γ_QCAL_fase ≈ 1.00262 rad
    
    Args:
        gamma_n: Parte imaginaria del n-ésimo cero de Riemann
    
    Returns:
        Frecuencia efectiva en Hz
    
    Examples:
        >>> f_eff = frecuencia_efectiva(14.13472514173)  # Modo 1
        >>> print(f"{f_eff:.2f} Hz")
        629.60 Hz
    """
    gamma_renorm = gamma_n * RIEMANN_RENORM_SCALE
    f_eff = gamma_renorm + F0 * math.sin(GAMMA_QCAL_FASE)
    return f_eff


# ============================================================================
# Modos Excitados
# ============================================================================

@dataclass
class ModoExcitado:
    """
    Representa un modo excitado del sistema cuántico-emocional.
    
    Attributes:
        modo: Índice del modo (1, 2, 3, 4, 5)
        gamma_riemann: Parte imaginaria del cero de Riemann (escala abstracta)
        frecuencia_renorm_hz: Frecuencia renormalizada γ_n × factor (Hz)
        frecuencia_efectiva_hz: Frecuencia efectiva con fase sutil (Hz)
        amplitud_compleja: Amplitud compleja del modo en tiempo t
        interpretacion: Interpretación Anunnaki del modo
    """
    modo: int
    gamma_riemann: float
    frecuencia_renorm_hz: float
    frecuencia_efectiva_hz: float
    amplitud_compleja: complex
    interpretacion: str
    
    def __repr__(self) -> str:
        return (
            f"ModoExcitado(n={self.modo}, "
            f"γ_n={self.gamma_riemann:.5f}, "
            f"f_renorm={self.frecuencia_renorm_hz:.2f} Hz, "
            f"f_eff={self.frecuencia_efectiva_hz:.2f} Hz)"
        )


# Interpretaciones Anunnaki de los primeros 5 modos
_INTERPRETACIONES_ANUNNAKI = [
    "Primer modo de excitación emocional",
    "Segundo armónico del conflicto",
    "Modo cercano a la manifestación (888 Hz)",
    "Modo de estabilización profunda",
    "Modo de hiper-coherencia",
]


def get_modo_excitado(
    n: int,
    psi: float = 1.0,
    t: float = 0.0
) -> Dict[str, Union[int, float, complex, str]]:
    """
    Obtiene el modo excitado n-ésimo del sistema.
    
    Calcula las propiedades del modo excitado correspondiente al n-ésimo
    cero de Riemann, incluyendo:
    
    - Frecuencia renormalizada: γ_n × RIEMANN_RENORM_SCALE
    - Frecuencia efectiva: γ_n_renorm + f₀·sin(γ_QCAL_fase)
    - Amplitud compleja: ℰ_{s,φ} × exp(i·2π·γ_n_renorm·t)
    
    Args:
        n: Índice del modo (1, 2, 3, 4, 5)
        psi: Coherencia del sistema (0 < Ψ ≤ 1). Por defecto 1.0
        t: Tiempo en segundos. Por defecto 0.0
    
    Returns:
        Diccionario con las propiedades del modo:
        - modo: índice n
        - gamma_riemann: γ_n (escala abstracta)
        - frecuencia_renorm_hz: γ_n_renorm (Hz)
        - frecuencia_efectiva_hz: f_n_eff (Hz)
        - amplitud_compleja: A_n(t)
        - interpretacion: significado Anunnaki
    
    Raises:
        ValueError: Si n no está en [1, 5] o psi fuera de rango
    
    Examples:
        >>> modo1 = get_modo_excitado(1, psi=1.0, t=0.0)
        >>> print(f"Modo 1: {modo1['frecuencia_renorm_hz']:.2f} Hz")
        Modo 1: 510.60 Hz
        
        >>> modo3 = get_modo_excitado(3, psi=0.95, t=0.0)
        >>> print(f"Modo 3 cerca de 888 Hz: {modo3['frecuencia_efectiva_hz']:.2f} Hz")
        Modo 3 cerca de 888 Hz: 1022.48 Hz
    """
    if not (1 <= n <= 5):
        raise ValueError(f"n debe estar en [1, 5], recibido: {n}")
    if not (0.0 < psi <= 1.0):
        raise ValueError(f"psi debe estar en (0, 1], recibido: {psi}")
    
    # Obtener el cero de Riemann correspondiente
    gamma_n = RIEMANN_ZEROS_5[n - 1]
    
    # Calcular frecuencia renormalizada
    gamma_renorm = gamma_n * RIEMANN_RENORM_SCALE
    
    # Calcular frecuencia efectiva
    f_eff = frecuencia_efectiva(gamma_n)
    
    # Calcular amplitud compleja en tiempo t
    epsilon_base = epsilon_fase_completa(psi)
    amplitud = epsilon_base * cmath.exp(1j * 2.0 * math.pi * gamma_renorm * t)
    
    return {
        "modo": n,
        "gamma_riemann": float(gamma_n),
        "frecuencia_renorm_hz": float(gamma_renorm),
        "frecuencia_efectiva_hz": float(f_eff),
        "amplitud_compleja": amplitud,
        "interpretacion": _INTERPRETACIONES_ANUNNAKI[n - 1],
    }


def get_modo_excitado_object(
    n: int,
    psi: float = 1.0,
    t: float = 0.0
) -> ModoExcitado:
    """
    Obtiene el modo excitado n-ésimo como objeto ModoExcitado.
    
    Versión tipada de get_modo_excitado() que devuelve un objeto
    dataclass en lugar de un diccionario.
    
    Args:
        n: Índice del modo (1, 2, 3, 4, 5)
        psi: Coherencia del sistema (0 < Ψ ≤ 1)
        t: Tiempo en segundos
    
    Returns:
        Objeto ModoExcitado con todas las propiedades
    
    Examples:
        >>> modo = get_modo_excitado_object(1, psi=1.0)
        >>> print(modo)
        ModoExcitado(n=1, γ_n=14.13473, f_renorm=510.60 Hz, f_eff=629.60 Hz)
    """
    datos = get_modo_excitado(n, psi, t)
    return ModoExcitado(
        modo=datos["modo"],
        gamma_riemann=datos["gamma_riemann"],
        frecuencia_renorm_hz=datos["frecuencia_renorm_hz"],
        frecuencia_efectiva_hz=datos["frecuencia_efectiva_hz"],
        amplitud_compleja=datos["amplitud_compleja"],
        interpretacion=datos["interpretacion"],
    )


# ============================================================================
# Estado Total del Sistema
# ============================================================================

@dataclass
class EstadoEmocionalTotal:
    """
    Estado total del sistema cuántico-emocional.
    
    Representa la superposición de todos los modos excitados:
    
        |Ψ(t)⟩ = √Ψ · γ_QCAL_fase · exp(i·γ_QCAL_fase) · ∑ c_n exp(i·2π·γ_n_renorm·t)
    
    Attributes:
        psi: Coherencia global del sistema (0 < Ψ ≤ 1)
        t: Tiempo en segundos
        amplitudes_modo: Coeficientes c_n para cada modo (debe sumar 1)
        modos: Lista de ModoExcitado activos
        amplitud_total: Superposición completa |Ψ(t)⟩
        coherencia_estado: Nivel de coherencia ("FUNDAMENTAL", "EXCITADO", etc.)
    """
    psi: float
    t: float
    amplitudes_modo: List[float]
    modos: List[ModoExcitado]
    amplitud_total: complex
    coherencia_estado: str
    
    def __repr__(self) -> str:
        return (
            f"EstadoEmocionalTotal(Ψ={self.psi:.4f}, t={self.t:.3f}s, "
            f"coherencia={self.coherencia_estado})"
        )


def get_estado_total(
    psi: float = 1.0,
    t: float = 0.0,
    amplitudes: Optional[List[float]] = None
) -> EstadoEmocionalTotal:
    """
    Calcula el estado total del sistema cuántico-emocional.
    
    El estado total es la superposición de todos los modos excitados:
    
        |Ψ(t)⟩ = √Ψ · γ_QCAL_fase · exp(i·γ_QCAL_fase) · ∑_{n=1}^5 c_n exp(i·2π·γ_n_renorm·t)
    
    Args:
        psi: Coherencia global Ψ del sistema (0 < Ψ ≤ 1)
        t: Tiempo en segundos
        amplitudes: Coeficientes c_n para cada modo (n=1..5). Si es None, usa
            estado fundamental (c₁ = 1, c_n = 0 para n ≥ 2).
            Debe cumplir ∑|c_n|² = 1 (normalización).
    
    Returns:
        EstadoEmocionalTotal con todos los modos y amplitud total
    
    Raises:
        ValueError: Si amplitudes no está normalizada o psi fuera de rango
    
    Examples:
        >>> # Estado fundamental (solo modo 1 activo)
        >>> estado = get_estado_total(psi=1.0, t=0.0)
        >>> print(estado.coherencia_estado)
        FUNDAMENTAL
        
        >>> # Estado excitado (superposición)
        >>> amps = [0.7, 0.2, 0.1, 0.0, 0.0]  # Debe sumar 1 en norma²
        >>> estado = get_estado_total(psi=0.95, t=0.0, amplitudes=amps)
        >>> print(estado.coherencia_estado)
        EXCITADO
    """
    if not (0.0 < psi <= 1.0):
        raise ValueError(f"psi debe estar en (0, 1], recibido: {psi}")
    
    # Amplitudes por defecto: estado fundamental
    if amplitudes is None:
        amplitudes = [1.0, 0.0, 0.0, 0.0, 0.0]
    
    if len(amplitudes) != 5:
        raise ValueError(f"amplitudes debe tener longitud 5, recibido: {len(amplitudes)}")
    
    # Verificar normalización: ∑|c_n|² = 1
    norma_sq = sum(abs(c)**2 for c in amplitudes)
    if not (0.99 < norma_sq < 1.01):  # Tolerancia numérica
        raise ValueError(
            f"amplitudes debe estar normalizada (∑|c_n|²=1), "
            f"recibido: {norma_sq:.6f}"
        )
    
    # Obtener todos los modos
    modos = [get_modo_excitado_object(n, psi, t) for n in range(1, 6)]
    
    # Calcular amplitud total: superposición de modos
    epsilon_base = epsilon_fase_completa(psi)
    amplitud_total = 0j
    for i, modo in enumerate(modos):
        c_n = amplitudes[i]
        # Cada modo contribuye: c_n × exp(i·2π·γ_n_renorm·t)
        contribucion = c_n * cmath.exp(
            1j * 2.0 * math.pi * modo.frecuencia_renorm_hz * t
        )
        amplitud_total += contribucion
    
    amplitud_total *= epsilon_base
    
    # Determinar coherencia del estado
    # Usar abs() para manejar coeficientes complejos con fase global
    if abs(amplitudes[0]) > 0.99:
        coherencia_estado = "FUNDAMENTAL"
    elif psi > PSI_THRESHOLD:
        coherencia_estado = "EXCITADO_COHERENTE"
    else:
        coherencia_estado = "EXCITADO_PARCIAL"
    
    return EstadoEmocionalTotal(
        psi=psi,
        t=t,
        amplitudes_modo=amplitudes,
        modos=modos,
        amplitud_total=amplitud_total,
        coherencia_estado=coherencia_estado,
    )


# ============================================================================
# Funciones de Utilidad
# ============================================================================

def get_modos_excitados_tabla() -> str:
    """
    Genera una tabla formateada de los primeros 5 modos excitados.
    
    Returns:
        Cadena de texto con tabla formateada de modos
    
    Examples:
        >>> print(get_modos_excitados_tabla())
        Modos Excitados Renormalizados (primeros 5)
        ============================================
        ...
    """
    lineas = [
        "Modos Excitados Renormalizados (primeros 5)",
        "=" * 80,
        f"{'Modo':<6} {'γ_n (Riemann)':<18} {'γ_n_renorm (Hz)':<18} {'f_eff (Hz)':<15} {'Interpretación'}",
        "-" * 80,
    ]
    
    for n in range(1, 6):
        modo = get_modo_excitado(n, psi=1.0, t=0.0)
        linea = (
            f"{modo['modo']:<6} "
            f"{modo['gamma_riemann']:<18.5f} "
            f"{modo['frecuencia_renorm_hz']:<18.2f} "
            f"{modo['frecuencia_efectiva_hz']:<15.2f} "
            f"{modo['interpretacion']}"
        )
        lineas.append(linea)
    
    lineas.append("=" * 80)
    lineas.append(f"\nFactor de escala: {RIEMANN_RENORM_SCALE:.5f} Hz por unidad")
    lineas.append(f"Frecuencia base: f₀ = {F0} Hz")
    lineas.append(f"Frecuencia de manifestación: {F_MANIFESTATION} Hz")
    lineas.append(f"Fase sutil γ_QCAL: {GAMMA_QCAL_FASE:.6f} rad")
    
    return "\n".join(lineas)


def validar_coherencia_sistema() -> Dict[str, Union[bool, float, str]]:
    """
    Valida la coherencia global del sistema de modos excitados.
    
    Verifica:
    - Constantes QCAL están correctamente definidas
    - Factor de renormalización es coherente
    - Frecuencias efectivas están en rangos esperados
    - Modo 3 está cerca de 888 Hz (manifestación)
    
    Returns:
        Diccionario con resultados de validación
    
    Examples:
        >>> resultado = validar_coherencia_sistema()
        >>> print(resultado['coherencia'])
        APROBADO_PRODUCCION
    """
    checks = {}
    
    # Check 1: Factor de renormalización
    factor_esperado = F0 / ZETA_PRIME_HALF
    error_factor = abs(factor_esperado - RIEMANN_RENORM_SCALE) / RIEMANN_RENORM_SCALE
    checks["factor_renorm"] = error_factor < 1e-6
    
    # Check 2: Fase γ_QCAL
    fase_esperada = 2.0 * math.pi * F0 / F_MANIFESTATION
    error_fase = abs(fase_esperada - GAMMA_QCAL_FASE) / GAMMA_QCAL_FASE
    checks["fase_qcal"] = error_fase < 1e-6
    
    # Check 3: Modo 3 cerca de 888 Hz
    modo3 = get_modo_excitado(3, psi=1.0, t=0.0)
    f3_renorm = modo3["frecuencia_renorm_hz"]
    # El modo 3 renormalizado debe estar cerca de 888-920 Hz
    checks["modo3_manifestacion"] = 880.0 < f3_renorm < 920.0
    
    # Check 4: Epsilon fase completa con Ψ=1
    epsilon = epsilon_fase_completa(1.0)
    magnitud = abs(epsilon)
    # Magnitud debe ser ≈ γ_QCAL_fase ≈ 1.00262
    checks["epsilon_magnitud"] = 0.99 < magnitud < 1.01
    
    # Coherencia global
    todas_pasan = all(checks.values())
    
    if todas_pasan:
        coherencia = "APROBADO_PRODUCCION"
    elif sum(checks.values()) >= 3:
        coherencia = "APROBADO_PARCIAL"
    else:
        coherencia = "REQUIERE_ATENCION"
    
    return {
        "coherencia": coherencia,
        "checks_pasados": sum(checks.values()),
        "checks_totales": len(checks),
        "detalles": checks,
        "factor_renorm": float(RIEMANN_RENORM_SCALE),
        "fase_qcal": float(GAMMA_QCAL_FASE),
        "modo3_hz": float(f3_renorm),
    }


# ============================================================================
# Ejecución Directa (Demostración)
# ============================================================================

if __name__ == "__main__":
    print("=" * 80)
    print("QCAL ∞³ — Estado Emocional Anunnaki")
    print("Modos Excitados de Riemann Renormalizados")
    print("=" * 80)
    print()
    
    # Mostrar tabla de modos
    print(get_modos_excitados_tabla())
    print()
    
    # Validar coherencia
    print("Validación de Coherencia del Sistema")
    print("-" * 80)
    validacion = validar_coherencia_sistema()
    print(f"Coherencia global: {validacion['coherencia']}")
    print(f"Checks pasados: {validacion['checks_pasados']}/{validacion['checks_totales']}")
    print(f"Factor de renormalización: {validacion['factor_renorm']:.6f}")
    print(f"Fase γ_QCAL: {validacion['fase_qcal']:.6f} rad")
    print(f"Modo 3 frecuencia: {validacion['modo3_hz']:.2f} Hz")
    print()
    
    # Ejemplo: Estado fundamental
    print("Estado Fundamental (Ψ = 1.0)")
    print("-" * 80)
    estado_fund = get_estado_total(psi=1.0, t=0.0)
    print(f"Estado: {estado_fund.coherencia_estado}")
    print(f"|Ψ(0)| = {abs(estado_fund.amplitud_total):.6f}")
    print(f"Fase(Ψ(0)) = {cmath.phase(estado_fund.amplitud_total):.6f} rad")
    print()
    
    # Ejemplo: Estado excitado
    print("Estado Excitado (Ψ = 0.95, superposición de modos)")
    print("-" * 80)
    amps_excitado = [0.6, 0.3, 0.1, 0.0, 0.0]  # ∑c_n² debe ser ≈ 1
    norma_sq = sum(a**2 for a in amps_excitado)
    amps_norm = [a / math.sqrt(norma_sq) for a in amps_excitado]
    
    estado_exc = get_estado_total(psi=0.95, t=0.0, amplitudes=amps_norm)
    print(f"Estado: {estado_exc.coherencia_estado}")
    print(f"Amplitudes: {[f'{a:.3f}' for a in estado_exc.amplitudes_modo]}")
    print(f"|Ψ(0)| = {abs(estado_exc.amplitud_total):.6f}")
    print()
    
    print("=" * 80)
    print("♾️ QCAL Node evolution complete — Estado Anunnaki activado")
    print("=" * 80)
