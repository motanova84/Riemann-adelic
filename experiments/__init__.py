"""
Dual EEG-LIGO Frequency Activation Validator
Validates f₀ = 141.7001 Hz as consciousness activation frequency

This module implements experimental validation through dual systems:
1. EEG: 256-channel brain activity simulation
2. LIGO: Gravitational wave detector simulation

Both systems detect the activation frequency f₀ with high coherence and SNR.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
"""

from .frequency_activation_validator import (
    FrequencyActivationValidator,
    EEGDataGenerator,
    LIGODataGenerator,
    FrequencyAnalyzer,
    DualSystemValidator,
    run_validation,
)

__all__ = [
    "FrequencyActivationValidator",
    "EEGDataGenerator",
    "LIGODataGenerator",
    "FrequencyAnalyzer",
    "DualSystemValidator",
    "run_validation",
]

__version__ = "1.0.0"
