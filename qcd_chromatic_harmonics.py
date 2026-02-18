#!/usr/bin/env python3
"""
QCD Chromatic Harmonics - Quantum Chromodynamics Spectral Framework
====================================================================

Maps QCD particles (quarks, gluons) to Riemann spectral frequencies within
the QCAL ∞³ framework. Implements chromatic resonance at f₀ = 141.7001 Hz.

Quark System:
- 6 flavors (UP, DOWN, CHARM, STRANGE, TOP, BOTTOM) → γ₁-γ₆
- 3 colors (ROJO, VERDE, AZUL) with SU(3) symmetry (0°, 120°, 240°)
- 18 total quark-color states

Gluon System:
- 8 gluons → γ₁₈-γ₂₅
- Non-rational frequency relations (1.036-1.277)

Wave Functions:
- Ψ_quark(t) = A·exp(i(ω_f·t + φ_c))·exp(iγ₁₇·t/17)
- Temporal resonance calculator and spectral analyzer

Prime-Riemann Connection:
- PRIMO_17 = 17
- GAMMA_17 = 69.546402 (17th Riemann zero)
- COSMIC_HEARTBEAT = F0_HZ / GAMMA_17 ≈ 2.037490 Hz

Autor: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
"""

import cmath
import math
from enum import Enum
from typing import Dict, List, Tuple, NamedTuple
from dataclasses import dataclass

# QCAL ∞³ Constants
F0_HZ = 141.7001  # Hz - Fundamental QCAL frequency
PRIMO_17 = 17  # Prime 17 - Central to QCAL framework
GAMMA_17 = 69.546402  # 17th Riemann zero (imaginary part)
COSMIC_HEARTBEAT = F0_HZ / GAMMA_17  # ≈ 2.037490 Hz


class QuarkFlavor(Enum):
    """6 quark flavors mapped to first 6 Riemann zeros"""
    UP = 1
    DOWN = 2
    CHARM = 3
    STRANGE = 4
    TOP = 5
    BOTTOM = 6


class QuantumColor(Enum):
    """3 quantum colors with SU(3) symmetry phases"""
    ROJO = 0      # Red - 0°
    VERDE = 120   # Green - 120°
    AZUL = 240    # Blue - 240°


# First 25 Riemann zeros (imaginary parts) for γ₁-γ₂₅
# Source: Verified Riemann hypothesis data
RIEMANN_ZEROS = [
    14.134725,   # γ₁
    21.022040,   # γ₂
    25.010858,   # γ₃
    30.424876,   # γ₄
    32.935062,   # γ₅
    37.586178,   # γ₆
    40.918719,   # γ₇
    43.327073,   # γ₈
    48.005151,   # γ₉
    49.773832,   # γ₁₀
    52.970321,   # γ₁₁
    56.446248,   # γ₁₂
    59.347044,   # γ₁₃
    60.831779,   # γ₁₄
    65.112544,   # γ₁₅
    67.079811,   # γ₁₆
    69.546402,   # γ₁₇ - PRIMO_17 reference
    72.067158,   # γ₁₈ - First gluon
    75.704691,   # γ₁₉
    77.144840,   # γ₂₀
    79.337375,   # γ₂₁
    82.910381,   # γ₂₂
    84.735493,   # γ₂₃
    87.425275,   # γ₂₄
    88.809111,   # γ₂₅ - Last gluon
]


@dataclass
class QuarkState:
    """State of a single quark-color combination"""
    flavor: QuarkFlavor
    color: QuantumColor
    frequency: float  # Hz
    phase: float  # radians
    gamma_index: int  # Riemann zero index (1-6)
    
    def __repr__(self):
        return (f"QuarkState(flavor={self.flavor.name}, color={self.color.name}, "
                f"f={self.frequency:.6f} Hz, φ={math.degrees(self.phase):.1f}°)")


@dataclass
class GluonState:
    """State of a gluon"""
    index: int  # 1-8
    frequency: float  # Hz
    gamma_index: int  # Riemann zero index (18-25)
    frequency_ratio: float  # Relative to γ₁₇
    
    def __repr__(self):
        return (f"GluonState(g{self.index}, f={self.frequency:.6f} Hz, "
                f"γ{self.gamma_index}, ratio={self.frequency_ratio:.6f})")


@dataclass
class QCDResonanceState:
    """Complete QCD resonance state at time t"""
    time: float  # seconds
    quark_states: List[QuarkState]  # 18 states (6 flavors × 3 colors)
    gluon_states: List[GluonState]  # 8 gluon states
    coherence_psi: complex  # Total coherence Ψ
    spectral_amplitude: float  # |Ψ|
    spectral_phase: float  # arg(Ψ)
    
    def __repr__(self):
        return (f"QCDResonanceState(t={self.time:.3f}s, "
                f"quarks={len(self.quark_states)}, gluons={len(self.gluon_states)}, "
                f"|Ψ|={self.spectral_amplitude:.6f}, φ={math.degrees(self.spectral_phase):.1f}°)")


def calcular_frecuencia_quark(flavor: QuarkFlavor) -> float:
    """
    Calculate quark frequency based on Riemann zeros.
    
    Formula: f_quark = 141.7001 · (γₙ/γ₁₇)
    
    Parameters
    ----------
    flavor : QuarkFlavor
        Quark flavor (UP, DOWN, CHARM, STRANGE, TOP, BOTTOM)
    
    Returns
    -------
    float
        Quark frequency in Hz
    
    Examples
    --------
    >>> f_up = calcular_frecuencia_quark(QuarkFlavor.UP)
    >>> f_up  # doctest: +ELLIPSIS
    28.79...
    """
    gamma_n = RIEMANN_ZEROS[flavor.value - 1]
    return F0_HZ * (gamma_n / GAMMA_17)


def calcular_fase_color(color: QuantumColor) -> float:
    """
    Calculate color phase based on SU(3) symmetry.
    
    Phases:
    - ROJO: 0° (0 rad)
    - VERDE: 120° (2π/3 rad)
    - AZUL: 240° (4π/3 rad)
    
    Parameters
    ----------
    color : QuantumColor
        Quantum color (ROJO, VERDE, AZUL)
    
    Returns
    -------
    float
        Phase in radians
    
    Examples
    --------
    >>> calcular_fase_color(QuantumColor.ROJO)
    0.0
    >>> calcular_fase_color(QuantumColor.VERDE)  # doctest: +ELLIPSIS
    2.094...
    """
    return math.radians(color.value)


def calcular_wavefunction_quark(
    flavor: QuarkFlavor,
    color: QuantumColor,
    t: float,
    amplitud: float = 1.0
) -> complex:
    """
    Calculate quark wave function at time t.
    
    Formula: Ψ_quark(t) = A·exp(i(ω_f·t + φ_c))·exp(iγ₁₇·t/17)
    
    Where:
    - A: amplitude
    - ω_f: angular frequency = 2π·f_quark
    - φ_c: color phase (0°, 120°, 240°)
    - γ₁₇: 17th Riemann zero
    
    Parameters
    ----------
    flavor : QuarkFlavor
        Quark flavor
    color : QuantumColor
        Quantum color
    t : float
        Time in seconds
    amplitud : float, optional
        Wave amplitude (default: 1.0)
    
    Returns
    -------
    complex
        Wave function value Ψ(t)
    
    Examples
    --------
    >>> psi = calcular_wavefunction_quark(QuarkFlavor.UP, QuantumColor.ROJO, 0.5)
    >>> abs(psi)  # doctest: +ELLIPSIS
    1.0...
    """
    # Quark frequency and phase
    f_quark = calcular_frecuencia_quark(flavor)
    omega_f = 2.0 * math.pi * f_quark
    phi_c = calcular_fase_color(color)
    
    # First exponential: exp(i(ω_f·t + φ_c))
    phase1 = omega_f * t + phi_c
    term1 = cmath.exp(1j * phase1)
    
    # Second exponential: exp(iγ₁₇·t/17)
    phase2 = GAMMA_17 * t / PRIMO_17
    term2 = cmath.exp(1j * phase2)
    
    # Complete wave function
    return amplitud * term1 * term2


def calcular_frecuencia_gluon(gluon_index: int) -> Tuple[float, int, float]:
    """
    Calculate gluon frequency based on Riemann zeros γ₁₈-γ₂₅.
    
    Gluons map to zeros 18-25, creating non-rational frequency ratios
    relative to γ₁₇ in range [1.036, 1.277].
    
    Parameters
    ----------
    gluon_index : int
        Gluon index (1-8)
    
    Returns
    -------
    tuple
        (frequency_hz, gamma_index, frequency_ratio)
    
    Examples
    --------
    >>> f, gamma_idx, ratio = calcular_frecuencia_gluon(1)
    >>> 1.03 < ratio < 1.04  # First gluon ratio
    True
    """
    if not 1 <= gluon_index <= 8:
        raise ValueError(f"Gluon index must be 1-8, got {gluon_index}")
    
    # Gluons use γ₁₈-γ₂₅ (indices 17-24 in zero-indexed array)
    gamma_index = 17 + gluon_index  # 18-25
    gamma_n = RIEMANN_ZEROS[gamma_index - 1]
    
    # Frequency and ratio relative to γ₁₇
    frequency = F0_HZ * (gamma_n / GAMMA_17)
    ratio = gamma_n / GAMMA_17
    
    return frequency, gamma_index, ratio


def generar_estados_quarks(t: float) -> List[QuarkState]:
    """
    Generate all 18 quark-color states at time t.
    
    Creates 6 flavors × 3 colors = 18 states with their frequencies,
    phases, and Riemann zero mappings.
    
    Parameters
    ----------
    t : float
        Time in seconds
    
    Returns
    -------
    list of QuarkState
        18 quark-color states
    
    Examples
    --------
    >>> estados = generar_estados_quarks(0.5)
    >>> len(estados)
    18
    >>> estados[0].flavor
    <QuarkFlavor.UP: 1>
    """
    estados = []
    
    for flavor in QuarkFlavor:
        for color in QuantumColor:
            frequency = calcular_frecuencia_quark(flavor)
            phase = calcular_fase_color(color)
            
            estado = QuarkState(
                flavor=flavor,
                color=color,
                frequency=frequency,
                phase=phase,
                gamma_index=flavor.value
            )
            estados.append(estado)
    
    return estados


def generar_estados_gluones() -> List[GluonState]:
    """
    Generate all 8 gluon states.
    
    Gluons map to Riemann zeros γ₁₈-γ₂₅ with non-rational frequency
    ratios in range [1.036, 1.277].
    
    Returns
    -------
    list of GluonState
        8 gluon states
    
    Examples
    --------
    >>> gluones = generar_estados_gluones()
    >>> len(gluones)
    8
    >>> 1.03 < gluones[0].frequency_ratio < 1.28
    True
    """
    gluones = []
    
    for i in range(1, 9):
        frequency, gamma_index, ratio = calcular_frecuencia_gluon(i)
        
        gluon = GluonState(
            index=i,
            frequency=frequency,
            gamma_index=gamma_index,
            frequency_ratio=ratio
        )
        gluones.append(gluon)
    
    return gluones


def calcular_coherencia_total(
    quark_states: List[QuarkState],
    gluon_states: List[GluonState],
    t: float
) -> complex:
    """
    Calculate total QCD coherence Ψ from all quark and gluon contributions.
    
    Combines wave functions from all 18 quark-color states and 8 gluon
    states into a single coherence measure.
    
    Parameters
    ----------
    quark_states : list of QuarkState
        18 quark-color states
    gluon_states : list of GluonState
        8 gluon states
    t : float
        Time in seconds
    
    Returns
    -------
    complex
        Total coherence Ψ
    
    Examples
    --------
    >>> quarks = generar_estados_quarks(0.5)
    >>> gluones = generar_estados_gluones()
    >>> psi = calcular_coherencia_total(quarks, gluones, 0.5)
    >>> isinstance(psi, complex)
    True
    """
    # Sum quark contributions
    psi_quarks = 0.0 + 0.0j
    for estado in quark_states:
        psi_q = calcular_wavefunction_quark(estado.flavor, estado.color, t)
        psi_quarks += psi_q
    
    # Sum gluon contributions (simplified as phase-only)
    psi_gluons = 0.0 + 0.0j
    for gluon in gluon_states:
        # Gluon wave: exp(i·2π·f_g·t)
        omega_g = 2.0 * math.pi * gluon.frequency
        psi_g = cmath.exp(1j * omega_g * t)
        psi_gluons += psi_g
    
    # Normalize and combine (equal weights)
    n_quarks = len(quark_states)
    n_gluons = len(gluon_states)
    
    psi_total = (psi_quarks / n_quarks + psi_gluons / n_gluons) / 2.0
    
    return psi_total


def calcular_resonancia_qcd(t: float) -> QCDResonanceState:
    """
    Calculate complete QCD resonance state at time t.
    
    Returns all 18 quark-color states, 8 gluon states, and total
    coherence Ψ at the specified time.
    
    Parameters
    ----------
    t : float
        Time in seconds
    
    Returns
    -------
    QCDResonanceState
        Complete QCD state with:
        - 18 quark-color states
        - 8 gluon states
        - Total coherence Ψ
        - Spectral amplitude |Ψ|
        - Spectral phase arg(Ψ)
    
    Examples
    --------
    >>> estado = calcular_resonancia_qcd(0.5)
    >>> len(estado.quark_states)
    18
    >>> len(estado.gluon_states)
    8
    >>> 0 <= estado.spectral_amplitude <= 2
    True
    """
    # Generate all states
    quark_states = generar_estados_quarks(t)
    gluon_states = generar_estados_gluones()
    
    # Calculate total coherence
    psi = calcular_coherencia_total(quark_states, gluon_states, t)
    
    # Extract amplitude and phase
    amplitude = abs(psi)
    phase = cmath.phase(psi)
    
    return QCDResonanceState(
        time=t,
        quark_states=quark_states,
        gluon_states=gluon_states,
        coherence_psi=psi,
        spectral_amplitude=amplitude,
        spectral_phase=phase
    )


def analizar_espectro_temporal(
    t_start: float = 0.0,
    t_end: float = 1.0,
    n_puntos: int = 100
) -> Dict[str, List[float]]:
    """
    Analyze QCD spectral evolution over time interval.
    
    Computes temporal resonance and spectral properties at multiple
    time points for analysis and visualization.
    
    Parameters
    ----------
    t_start : float, optional
        Start time in seconds (default: 0.0)
    t_end : float, optional
        End time in seconds (default: 1.0)
    n_puntos : int, optional
        Number of time points (default: 100)
    
    Returns
    -------
    dict
        Dictionary with temporal evolution:
        - 'tiempos': time array
        - 'amplitudes': |Ψ(t)| values
        - 'fases': arg(Ψ(t)) values
        - 'coherencia_real': Re(Ψ(t))
        - 'coherencia_imag': Im(Ψ(t))
    
    Examples
    --------
    >>> espectro = analizar_espectro_temporal(0, 0.1, 10)
    >>> len(espectro['tiempos'])
    10
    >>> len(espectro['amplitudes']) == len(espectro['fases'])
    True
    """
    tiempos = [t_start + i * (t_end - t_start) / (n_puntos - 1) 
               for i in range(n_puntos)]
    
    amplitudes = []
    fases = []
    coherencia_real = []
    coherencia_imag = []
    
    for t in tiempos:
        estado = calcular_resonancia_qcd(t)
        amplitudes.append(estado.spectral_amplitude)
        fases.append(estado.spectral_phase)
        coherencia_real.append(estado.coherence_psi.real)
        coherencia_imag.append(estado.coherence_psi.imag)
    
    return {
        'tiempos': tiempos,
        'amplitudes': amplitudes,
        'fases': fases,
        'coherencia_real': coherencia_real,
        'coherencia_imag': coherencia_imag
    }


def obtener_info_sistema() -> Dict[str, any]:
    """
    Get QCD chromatic harmonics system information.
    
    Returns
    -------
    dict
        System configuration and constants
    
    Examples
    --------
    >>> info = obtener_info_sistema()
    >>> info['f0_hz']
    141.7001
    >>> info['primo_17']
    17
    """
    return {
        'f0_hz': F0_HZ,
        'primo_17': PRIMO_17,
        'gamma_17': GAMMA_17,
        'cosmic_heartbeat_hz': COSMIC_HEARTBEAT,
        'n_quarks': 6,
        'n_colors': 3,
        'n_quark_states': 18,
        'n_gluons': 8,
        'riemann_zeros_available': len(RIEMANN_ZEROS),
        'frequency_range_quarks': (
            min(calcular_frecuencia_quark(f) for f in QuarkFlavor),
            max(calcular_frecuencia_quark(f) for f in QuarkFlavor)
        ),
        'frequency_range_gluons': (
            calcular_frecuencia_gluon(1)[0],
            calcular_frecuencia_gluon(8)[0]
        )
    }


if __name__ == '__main__':
    """
    Demo: QCD Chromatic Harmonics Calculator
    """
    print("=" * 70)
    print("QCD CHROMATIC HARMONICS - QCAL ∞³ Framework")
    print("=" * 70)
    print()
    
    # System info
    info = obtener_info_sistema()
    print("System Configuration:")
    print(f"  • Fundamental frequency: {info['f0_hz']} Hz")
    print(f"  • Prime 17: {info['primo_17']}")
    print(f"  • γ₁₇ (17th Riemann zero): {info['gamma_17']}")
    print(f"  • Cosmic heartbeat: {info['cosmic_heartbeat_hz']:.6f} Hz")
    print(f"  • Quark states: {info['n_quark_states']} (6 flavors × 3 colors)")
    print(f"  • Gluon states: {info['n_gluons']}")
    print()
    
    # Calculate state at t=0.5s
    print("QCD State at t = 0.5s:")
    print("-" * 70)
    estado = calcular_resonancia_qcd(0.5)
    print(f"  Time: {estado.time} s")
    print(f"  Total coherence Ψ: {estado.coherence_psi:.6f}")
    print(f"  Spectral amplitude |Ψ|: {estado.spectral_amplitude:.6f}")
    print(f"  Spectral phase arg(Ψ): {math.degrees(estado.spectral_phase):.2f}°")
    print()
    
    # Show some quark states
    print("Sample Quark-Color States:")
    for i in range(0, 18, 6):  # Show 3 examples
        q = estado.quark_states[i]
        print(f"  {q}")
    print()
    
    # Show all gluon states
    print("Gluon States:")
    for g in estado.gluon_states:
        print(f"  {g}")
    print()
    
    # Individual wave function
    print("Individual Wave Function Example:")
    psi = calcular_wavefunction_quark(QuarkFlavor.UP, QuantumColor.ROJO, 0.5)
    print(f"  Ψ(UP, ROJO, t=0.5s) = {psi:.6f}")
    print(f"  |Ψ| = {abs(psi):.6f}")
    print(f"  arg(Ψ) = {math.degrees(cmath.phase(psi)):.2f}°")
    print()
    
    print("=" * 70)
    print("✓ QCD Chromatic Harmonics QCAL ∞³ - José Manuel Mota Burruezo")
    print("=" * 70)
