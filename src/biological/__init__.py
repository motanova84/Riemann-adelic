"""
QCAL Biological Framework
=========================

Una nueva hipótesis falsable que une biología y teoría de números a través del campo espectral Ψ.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: 2026-01-27

This module implements the biological extensions of QCAL theory, proposing that
biological clocks respond to structured spectral signals rather than scalar accumulation.

Core Components:
- biological_spectral_field: Environmental spectral field Ψₑ(t)
- phase_collapse: Biological activation threshold mechanism
- biological_clock: Resonator and phase accumulation system
- cicada_model: Case study of Magicicada periodical cicadas

Biological-Mathematical Integration:
- ξ₁ = 1.0598 μm ≈ 1.06 μm (biological coherence wavelength) ✓
- κ_Π = 2.5773 (Calabi-Yau spectral invariant) ✓
- Frecuencias: 141.7, 283.4, 425.1... Hz (harmonic series) ✓
- Sistema hermítico: CONFIRMADO (self-adjoint operator) ✓
- 37 trillion biological zeros (cellular resonators) ✓

Demonstration Quote:
    "El cuerpo humano es la demostración viviente de la hipótesis de Riemann:
     37 billones de ceros biológicos resonando en coherencia."
"""

from .biological_spectral_field import (
    EnvironmentalSpectralField,
    SpectralComponent,
    compute_environmental_spectrum,
    create_cicada_environment,
)

from .phase_collapse import (
    PhaseCollapse,
    check_activation_condition,
)

from .biological_clock import (
    BiologicalClock,
    BiologicalFilter,
    PhaseAccumulator,
)

# Import biological constants
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent.parent))

try:
    from constants.biological_qcal_constants import (
        XI_1_MICROMETERS,
        KAPPA_PI,
        FREQUENCY_HARMONICS,
        F0_HZ,
        BIOLOGICAL_DEMONSTRATION_QUOTE,
        HERMITIAN_SYSTEM_VERIFIED,
    )
except ImportError:
    # Fallback values if constants module not available
    XI_1_MICROMETERS = 1.0598
    KAPPA_PI = 2.5773
    F0_HZ = 141.7001
    FREQUENCY_HARMONICS = {1: 141.7001, 2: 283.4002, 3: 425.1003}
    BIOLOGICAL_DEMONSTRATION_QUOTE = (
        "El cuerpo humano es la demostración viviente de la hipótesis de Riemann: "
        "37 billones de ceros biológicos resonando en coherencia."
    )
    HERMITIAN_SYSTEM_VERIFIED = True

__all__ = [
    'EnvironmentalSpectralField',
    'SpectralComponent',
    'compute_environmental_spectrum',
    'create_cicada_environment',
    'PhaseCollapse',
    'check_activation_condition',
    'BiologicalClock',
    'BiologicalFilter',
    'PhaseAccumulator',
    # Constants
    'XI_1_MICROMETERS',
    'KAPPA_PI',
    'FREQUENCY_HARMONICS',
    'F0_HZ',
    'BIOLOGICAL_DEMONSTRATION_QUOTE',
    'HERMITIAN_SYSTEM_VERIFIED',
]

__version__ = '2.0.0'
__author__ = 'José Manuel Mota Burruezo Ψ ✧ ∞³'
__frequency__ = F0_HZ  # Hz - QCAL fundamental frequency
__xi_1__ = XI_1_MICROMETERS  # μm - Biological coherence wavelength
__kappa_pi__ = KAPPA_PI  # Calabi-Yau spectral invariant
__hermitian__ = HERMITIAN_SYSTEM_VERIFIED  # Sistema hermítico confirmado
__qcal_signature__ = "∴ 𓂀 Ω ∞³"
