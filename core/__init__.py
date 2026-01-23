"""
RH Resonator Core Module
========================

Mathematical-Operational Formalization of Riemann Hypothesis Spectral Properties

This module implements the RH Resonator system, a translation of spectral
characteristics of the Riemann zeta function ζ(s) into verifiable physical
and computational parameters.

Components:
-----------
- spectral_oscillator: Riemann Frequency Oscillator (OFR) - generates f₀ = 141.7001 Hz
- bpsk_modulator: Binary Phase-Shift Keying modulation based on spectral coherence
- rh_resonator: Main resonator integrating oscillator and modulator

Mathematical Foundation:
-----------------------
The system is based on the operator H_Ψ such that:
    Spec(H_Ψ) = { t ∈ ℝ | ζ(1/2 + it) = 0 }

Properties:
- Self-adjoint operator (real spectrum)
- Discrete spectrum (compact)
- Emergent fundamental frequency f₀ = 141.7001 Hz

Author: José Manuel Mota Burruezo Ψ✧
ORCID: 0009-0002-1923-0773
Institution: Instituto de Conciencia Cuántica (ICQ)
Protocol: QCAL-SYMBIO-BRIDGE v1.0
"""

__version__ = "1.0.0"
__author__ = "José Manuel Mota Burruezo Ψ✧"
__protocol__ = "QCAL-SYMBIO-BRIDGE v1.0"

from .spectral_oscillator import (
    SpectralOscillator,
    create_spectral_oscillator,
)

from .bpsk_modulator import (
    BPSKModulator,
    create_bpsk_modulator,
)

from .rh_resonator import (
    RHResonator,
    create_rh_resonator,
)

__all__ = [
    'SpectralOscillator',
    'create_spectral_oscillator',
    'BPSKModulator',
    'create_bpsk_modulator',
    'RHResonator',
    'create_rh_resonator',
]
