"""Synthetic QCAL-EXP01 signal analysis, not a physics confirmation.

All statistical evidence is conditional on the declared measurement and noise
models. The DSP input is a real, Nyquist-valid intermediate-frequency signal,
not an 80 MHz carrier sampled at 1 MHz.

The bundled native simulator supplies two IF carriers: A is the baseline and
B carries explicitly injected phase modulation. Use DualChannelDemodulator
for B-A. Its displacement reference is separately declared/calibrated, never
inferred from either ADC channel or silently synthesized from measured phase.
"""

from experimental_validation import C_QCAL, F0_HZ

from .dsp import (
    DSPConfig,
    DemodulatedBlock,
    DualChannelDemodulator,
    FrequencyEstimate,
    PhaseConcentration,
    PhaseRegression,
    StreamingDemodulator,
    estimate_modulation_frequency,
    fit_phase_regression,
    phase_concentration,
)
from .statistics import gaussian_log_bayes_factor

__all__ = [
    "F0_HZ", "C_QCAL",
    "DSPConfig", "DemodulatedBlock", "DualChannelDemodulator", "FrequencyEstimate", "PhaseConcentration",
    "PhaseRegression", "StreamingDemodulator", "estimate_modulation_frequency",
    "fit_phase_regression", "phase_concentration", "gaussian_log_bayes_factor",
    "MonteCarloResult", "simulate_power",
]


def __getattr__(name: str) -> object:
    """Load simulation exports lazily so the module CLI executes without runpy warnings."""
    if name in {"MonteCarloResult", "simulate_power"}:
        from . import monte_carlo
        value = getattr(monte_carlo, name)
        globals()[name] = value
        return value
    raise AttributeError(f"module {__name__!r} has no attribute {name!r}")
