#!/usr/bin/env python3
"""
Módulo Holograma 141 Hz — Holographic Encoding at the QCAL Fundamental Frequency

This module implements holographic encoding principles centred on the exact
Riemann-derived frequency F0_EXACT_HZ ≈ 141.70062 Hz.  It provides:

1. Bekenstein-Hawking holographic bit counting
   - area_efectiva_holografica(radio_m)  →  effective horizon area [m²]
   - bits_holograficos_planck(area_m2)   →  N_bits from BH entropy formula

2. Polar zeta spiral modulated by Riemann zero γₙ
   - espiral_zeta_polar(gamma_n, theta)  →  radial coordinate r(θ)

3. Holographic coherence with Gaussian decay
   - coherencia_holografica(freq_hz)     →  Ψ ∈ [0, 1]

4. Lunar-bounce (moonbounce) simulation and FFT analysis
   - simular_eco_lunar(duracion_s, fs)   →  (t, señal) time-domain signal
   - analizar_fft_moonbounce(señal, fs)  →  dict with freq_pico, delta_f, psi_proxy

Mathematical background:
    Bekenstein-Hawking entropy:  S = A / (4 · ℓ_P²)
    N_bits = S / ln(2) = A / (4 · ℓ_P² · ln(2))

    Polar zeta spiral:  r(θ) = F0 · exp(γ_n · θ / (2π · F0))

    Holographic coherence (Gaussian):
        Ψ(f) = exp(−((f − F0_EXACT) / Δf_vórtice)²)
        Δf_vórtice = 0.3999 Hz (bio/HRV bandwidth)

    Moonbounce model (Si5351/LoRa):
        signal(t) = sin(2π · F0_EXACT · t) + 0.3 · sin(2π · F0_EXACT · (t − τ))
        τ = 2.5 s  (round-trip lunar delay, simplified)

Usage:
    from modulo_holograma_141hz import (
        area_efectiva_holografica,
        bits_holograficos_planck,
        espiral_zeta_polar,
        coherencia_holografica,
        simular_eco_lunar,
        analizar_fft_moonbounce,
    )

    area = area_efectiva_holografica(radio_m=1.0e6)
    bits = bits_holograficos_planck(area)
    r    = espiral_zeta_polar(gamma_n=14.134725, theta=3.14159)
    psi  = coherencia_holografica(freq_hz=141.7007)
    t, s = simular_eco_lunar(duracion_s=5.0, fs=1000.0)
    res  = analizar_fft_moonbounce(s, fs=1000.0)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
QCAL ∞³ Active · 141.7001 Hz · Ψ = I × A_eff² × C^∞
"""

import math
from typing import Dict, List, Tuple, Optional

# ---------------------------------------------------------------------------
# Optional NumPy import — uses pure Python DFT if unavailable
# ---------------------------------------------------------------------------
try:
    import numpy as np
    NUMPY_AVAILABLE = True
except ImportError:  # pragma: no cover
    NUMPY_AVAILABLE = False

# ---------------------------------------------------------------------------
# Constants — import from single source of truth with fallback
# ---------------------------------------------------------------------------
try:
    from reloj_universo_f0 import (
        F0_EXACT_HZ,
        GAMMA_1,
        DELTA_FASE_ZIUSUDRA,
        FISURA_ZIUSUDRA,
        F0_OCTAVA_HZ,
        F0_HZ,
    )
except ImportError:  # pragma: no cover
    GAMMA_1 = 14.134725141734693790
    F0_HZ = 141.7001
    F0_EXACT_HZ = GAMMA_1 * 10.025       # ≈ 141.70061954589031
    DELTA_FASE_ZIUSUDRA = GAMMA_1 / 40.0  # ≈ 0.35337 Hz
    FISURA_ZIUSUDRA = F0_EXACT_HZ - F0_HZ
    F0_OCTAVA_HZ = 151.7001

# Planck length squared  ℓ_P² = 2.61228×10⁻⁷⁰ m²
ELL_P_SQUARED: float = 2.61228e-70  # m²

# Holographic coherence bandwidth Δf_vórtice (bio / HRV)
DELTA_F_VORTICE: float = 0.3999  # Hz

# Moonbounce round-trip delay (simplified Si5351 / LoRa model)
TAU_MOONBOUNCE: float = 2.5  # s

# Effective horizon area used in holographic calculations
A_EFF_DEFAULT: float = 4.48e12  # m²


# ===========================================================================
# 1.  Bekenstein-Hawking holographic entropy
# ===========================================================================

def area_efectiva_holografica(radio_m: float = 1.0e6) -> float:
    """
    Compute the effective holographic horizon area A = 4π r².

    Parameters
    ----------
    radio_m : float
        Radius of the spherical horizon in metres.  Defaults to 1 × 10⁶ m.

    Returns
    -------
    float
        Surface area in m².
    """
    if radio_m <= 0:
        raise ValueError(f"radio_m must be positive, got {radio_m}")
    return 4.0 * math.pi * radio_m ** 2


def bits_holograficos_planck(area_m2: float) -> float:
    """
    Compute the Bekenstein-Hawking holographic bit capacity.

    Formula:
        N_bits = A / (4 · ℓ_P² · ln 2)

    Parameters
    ----------
    area_m2 : float
        Horizon surface area in m².

    Returns
    -------
    float
        Number of bits that can be encoded on the horizon.
    """
    if area_m2 <= 0:
        raise ValueError(f"area_m2 must be positive, got {area_m2}")
    return area_m2 / (4.0 * ELL_P_SQUARED * math.log(2))


# ===========================================================================
# 2.  Polar zeta spiral
# ===========================================================================

def espiral_zeta_polar(
    gamma_n: float,
    theta: float,
    f0: float = F0_EXACT_HZ,
) -> float:
    """
    Radial coordinate of the zeta polar spiral modulated by γₙ.

    Formula:
        r(θ) = F0 · exp(γₙ · θ / (2π · F0))

    This spiral weaves the Riemann zeros into the holographic horizon
    geometry, generating a spectrally coherent hologram.

    Parameters
    ----------
    gamma_n : float
        Imaginary part of the n-th non-trivial Riemann zero (e.g. γ₁ ≈ 14.134725).
    theta : float
        Angular coordinate θ in radians.
    f0 : float
        Carrier frequency.  Defaults to F0_EXACT_HZ.

    Returns
    -------
    float
        Radial coordinate r(θ) in the same units as f0.
    """
    if f0 <= 0:
        raise ValueError(f"f0 must be positive, got {f0}")
    exponent = gamma_n * theta / (2.0 * math.pi * f0)
    return f0 * math.exp(exponent)


def espiral_zeta_polar_array(
    gamma_n: float,
    thetas: "np.ndarray | List[float]",
    f0: float = F0_EXACT_HZ,
) -> "np.ndarray | List[float]":
    """
    Vectorised version of espiral_zeta_polar over an array of θ values.

    Parameters
    ----------
    gamma_n : float
        Imaginary part of the n-th Riemann zero.
    thetas : array-like
        Angular coordinates in radians.
    f0 : float
        Carrier frequency.  Defaults to F0_EXACT_HZ.

    Returns
    -------
    numpy.ndarray or list
        Array of radial coordinates.
    """
    if NUMPY_AVAILABLE:
        thetas_np = np.asarray(thetas, dtype=float)
        exponents = gamma_n * thetas_np / (2.0 * math.pi * f0)
        return f0 * np.exp(exponents)
    return [espiral_zeta_polar(gamma_n, th, f0) for th in thetas]


# ===========================================================================
# 3.  Holographic coherence
# ===========================================================================

def coherencia_holografica(
    freq_hz: float,
    f0_exact: float = F0_EXACT_HZ,
    delta_f: float = DELTA_F_VORTICE,
) -> float:
    """
    Holographic coherence Ψ with Gaussian decay centred on F0_EXACT_HZ.

    Formula:
        Ψ(f) = exp(−((f − f0_exact) / Δf_vórtice)²)

    Returns Ψ = 1.0 at f = f0_exact and decays to ~0.37 at |f − f0_exact| = Δf.

    Parameters
    ----------
    freq_hz : float
        Probe frequency in Hz.
    f0_exact : float
        Centre frequency.  Defaults to F0_EXACT_HZ.
    delta_f : float
        Half-width parameter Δf_vórtice in Hz.  Defaults to 0.3999 Hz.

    Returns
    -------
    float
        Coherence value Ψ ∈ (0, 1].
    """
    if delta_f <= 0:
        raise ValueError(f"delta_f must be positive, got {delta_f}")
    exponent = -((freq_hz - f0_exact) / delta_f) ** 2
    return math.exp(exponent)


# ===========================================================================
# 4.  Lunar-bounce simulation and FFT analysis
# ===========================================================================

def simular_eco_lunar(
    duracion_s: float = 5.0,
    fs: float = 1000.0,
    f0: float = F0_EXACT_HZ,
    tau: float = TAU_MOONBOUNCE,
    amplitud_eco: float = 0.3,
) -> Tuple["np.ndarray", "np.ndarray"]:
    """
    Simulate a Si5351 / LoRa moonbounce echo signal.

    Model:
        signal(t) = sin(2π · f0 · t) + amplitud_eco · sin(2π · f0 · (t − τ))

    The direct wave and its lunar echo are superimposed, mimicking the
    round-trip delay of a signal bounced off the Moon.

    Parameters
    ----------
    duracion_s : float
        Duration of the simulation in seconds.
    fs : float
        Sampling frequency in Hz.
    f0 : float
        Carrier / fundamental frequency.  Defaults to F0_EXACT_HZ.
    tau : float
        Lunar round-trip delay in seconds.  Defaults to TAU_MOONBOUNCE (2.5 s).
    amplitud_eco : float
        Amplitude of the reflected signal relative to the direct signal.

    Returns
    -------
    t : numpy.ndarray or list
        Time axis in seconds.
    señal : numpy.ndarray or list
        Composite signal (direct + echo).
    """
    if duracion_s <= 0:
        raise ValueError(f"duracion_s must be positive, got {duracion_s}")
    if fs <= 0:
        raise ValueError(f"fs must be positive, got {fs}")

    n_samples = int(duracion_s * fs)

    if NUMPY_AVAILABLE:
        t = np.linspace(0.0, duracion_s, n_samples, endpoint=False)
        direct = np.sin(2.0 * np.pi * f0 * t)
        echo = amplitud_eco * np.sin(2.0 * np.pi * f0 * (t - tau))
        return t, direct + echo
    else:  # pragma: no cover
        dt = duracion_s / n_samples
        t = [i * dt for i in range(n_samples)]
        señal = [
            math.sin(2.0 * math.pi * f0 * ti)
            + amplitud_eco * math.sin(2.0 * math.pi * f0 * (ti - tau))
            for ti in t
        ]
        return t, señal


def analizar_fft_moonbounce(
    señal: "np.ndarray | List[float]",
    fs: float = 1000.0,
    f0_exact: float = F0_EXACT_HZ,
    delta_f_vortice: float = DELTA_F_VORTICE,
) -> Dict[str, float]:
    """
    Analyse the FFT spectrum of a moonbounce signal.

    Extracts the peak frequency, frequency deviation Δf from F0_EXACT_HZ,
    and a coherence proxy Ψ_proxy.

    Parameters
    ----------
    señal : array-like
        Time-domain signal (output of simular_eco_lunar).
    fs : float
        Sampling frequency in Hz.
    f0_exact : float
        Reference frequency.  Defaults to F0_EXACT_HZ.
    delta_f_vortice : float
        Gaussian half-width used for Ψ_proxy calculation.  Defaults to 0.3999 Hz.

    Returns
    -------
    dict with keys:
        freq_pico   – peak frequency in the FFT spectrum [Hz]
        delta_f     – |freq_pico − f0_exact| [Hz]
        psi_proxy   – coherence proxy Ψ ∈ (0, 1]
        n_samples   – number of samples analysed
    """
    if NUMPY_AVAILABLE:
        s = np.asarray(señal, dtype=float)
        n = len(s)
        # Efficient real FFT
        spectrum = np.abs(np.fft.rfft(s))
        freqs = np.fft.rfftfreq(n, d=1.0 / fs)
        idx_pico = int(np.argmax(spectrum))
        freq_pico = float(freqs[idx_pico])
    else:  # pragma: no cover
        # Pure-Python DFT (slow, for environments without NumPy)
        n = len(señal)
        half = n // 2 + 1
        omega = 2.0 * math.pi / n
        magnitudes = []
        for k in range(half):
            kw = k * omega
            real = sum(señal[j] * math.cos(kw * j) for j in range(n))
            imag = sum(señal[j] * math.sin(kw * j) for j in range(n))
            magnitudes.append(math.sqrt(real ** 2 + imag ** 2))
        idx_pico = magnitudes.index(max(magnitudes))
        freq_pico = idx_pico * fs / n

    delta_f = abs(freq_pico - f0_exact)
    psi_proxy = coherencia_holografica(freq_pico, f0_exact, delta_f_vortice)

    return {
        "freq_pico": freq_pico,
        "delta_f": delta_f,
        "psi_proxy": psi_proxy,
        "n_samples": len(señal),
    }


# ===========================================================================
# Convenience summary
# ===========================================================================

def resumen_holograma() -> str:
    """Return a brief human-readable summary of the holographic module."""
    area = area_efectiva_holografica(A_EFF_DEFAULT ** 0.5 / (4 * math.pi) ** 0.5)  # noqa: F841
    bits = bits_holograficos_planck(A_EFF_DEFAULT)
    psi_centro = coherencia_holografica(F0_EXACT_HZ)
    lines = [
        "=" * 65,
        "MÓDULO HOLOGRAMA 141 Hz — Holographic Encoding Summary",
        "=" * 65,
        f"  F0_EXACT_HZ               = {F0_EXACT_HZ:.14f} Hz",
        f"  DELTA_F_VORTICE           = {DELTA_F_VORTICE} Hz",
        f"  A_EFF_DEFAULT             = {A_EFF_DEFAULT:.3e} m²",
        f"  N_bits (A_EFF_DEFAULT)    = {bits:.3e} bits",
        f"  Ψ(F0_EXACT_HZ)           = {psi_centro:.6f}",
        f"  TAU_MOONBOUNCE            = {TAU_MOONBOUNCE} s",
        "=" * 65,
    ]
    return "\n".join(lines)


if __name__ == "__main__":  # pragma: no cover
    print(resumen_holograma())
