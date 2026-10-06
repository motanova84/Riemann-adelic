"""Synthetic QCAL-EXP01 signal analysis, not a physics confirmation.

All statistical evidence is conditional on the declared measurement and noise
models. The DSP input is a real, Nyquist-valid intermediate-frequency signal,
not an 80 MHz carrier sampled at 1 MHz.
"""

from .dsp import (
    DSPConfig,
    DemodulatedBlock,
    FrequencyEstimate,
    PhaseConcentration,
    PhaseRegression,
    StreamingDemodulator,
    estimate_modulation_frequency,
    fit_phase_regression,
    phase_concentration,
)
from .statistics import gaussian_log_bayes_factor
from .monte_carlo import MonteCarloResult, simulate_power

__all__ = [
    "DSPConfig", "DemodulatedBlock", "FrequencyEstimate", "PhaseConcentration",
    "PhaseRegression", "StreamingDemodulator", "estimate_modulation_frequency",
    "fit_phase_regression", "phase_concentration", "gaussian_log_bayes_factor",
    "MonteCarloResult", "simulate_power",
]
