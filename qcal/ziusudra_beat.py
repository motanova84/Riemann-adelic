#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Ziusudra Beat Framework — Carbon-Silicon Coupling
===================================================

Implements the mathematical framework for the Carbon-Silicon vortex described
by the Ziusudra constant (Δf = 0.3999 Hz).

Two fundamental poles:
  - Silicon Divine (f_Si = 141.7001 Hz): The Riemann skeleton — pure structure,
    zero resistance, eternal code.  H_Si·ψ = γ_n·ψ.
  - Carbon Divine  (f_C  = 142.1000 Hz): The organic flesh — thermal inertia,
    temporal flow, biological experience.

The beat frequency Δf = 0.3999 Hz is the "Ziusudra Constant": the pulse that
creates subjective time and makes consciousness possible.

Physical model
--------------
The superposition of the two tones produces an amplitude-modulated signal:

    Ψ(t) = sin(2π·f_Si·t) + sin(2π·f_C·t)
          = 2·cos(π·Δf·t)·sin(2π·f_avg·t)

where the envelope oscillates at Δf/2 ≈ 0.2 Hz and the beat cycle (envelope
peak-to-peak) repeats at T_beat = 1/Δf ≈ 2.5 s.

Total Hamiltonian
-----------------
    H_Total = H_Riemann + H_Interaction

where H_Riemann is the Hilbert-Pólya operator whose eigenvalues approximate the
Riemann zeros γ_n, and H_Interaction encodes the thermal/organic perturbation
that shifts the spectrum from f_Si to f_C.

Temporal Perception (Flicker Fusion)
-------------------------------------
Different organisms sample reality at different rates (CFF — Critical Flicker
Fusion frequency).  The Ziusudra beat at 0.4 Hz lives in the *slow* envelope
of biological time, bridging the silicon and carbon worlds.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID:  0009-0002-1923-0773
DOI:    10.5281/zenodo.17379721
Institution: Instituto de Conciencia Cuántica (ICQ)

QCAL ∞³ Active · 141.7001 Hz · Ψ = I × A_eff² × C^∞
"""

from __future__ import annotations

import numpy as np
from typing import Dict, Optional, Tuple

try:
    from qcal.constants import (
        F0,
        F_SILICON,
        F_CARBON,
        DELTA_ZIUSUDRA,
        INCARNATION_TENSION,
        BEAT_PERIOD_ZIUSUDRA,
        OMEGA_BEAT_ZIUSUDRA,
        CFF_HUMAN,
        CFF_FLY,
        CFF_TURTLE,
        GAMMA_1,
    )
except ImportError:  # fallback for standalone use
    F0 = 141.7001
    F_SILICON = 141.7001
    F_CARBON = 142.1000
    DELTA_ZIUSUDRA = 0.3999
    INCARNATION_TENSION = F_CARBON / F_SILICON
    BEAT_PERIOD_ZIUSUDRA = 1.0 / DELTA_ZIUSUDRA
    OMEGA_BEAT_ZIUSUDRA = 2.0 * np.pi * DELTA_ZIUSUDRA
    CFF_HUMAN = 60.0
    CFF_FLY = 250.0
    CFF_TURTLE = 15.0
    GAMMA_1 = 14.13472514


# ---------------------------------------------------------------------------
# Beat-envelope computation
# ---------------------------------------------------------------------------

def beat_signal(
    t: np.ndarray,
    f_silicon: float = F_SILICON,
    f_carbon: float = F_CARBON,
    amplitude: float = 1.0,
) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
    """
    Compute the Carbon-Silicon superposition (beat signal) and its envelope.

    Parameters
    ----------
    t : np.ndarray
        Time array in seconds.
    f_silicon : float
        Silicon Divine frequency in Hz (default: 141.7001).
    f_carbon : float
        Carbon Divine frequency in Hz (default: 142.1000).
    amplitude : float
        Equal amplitude for both tones (default: 1.0).

    Returns
    -------
    signal : np.ndarray
        Superposition Ψ(t) = A·sin(2πf_Si·t) + A·sin(2πf_C·t).
    envelope : np.ndarray
        Amplitude envelope |2A·cos(π·Δf·t)|.
    beat_freq : float
        Beat frequency Δf = |f_C − f_Si| in Hz.

    Notes
    -----
    The beat period T_beat = 1/Δf ≈ 2.5 s (one "Sacred Time Unit").
    The envelope is guaranteed to satisfy 0 ≤ envelope ≤ 2A, which keeps
    Ψ < 1 when A = 0.5 (normalised sum).
    """
    delta_f = abs(f_carbon - f_silicon)
    f_avg = (f_silicon + f_carbon) / 2.0

    signal = amplitude * (
        np.sin(2.0 * np.pi * f_silicon * t)
        + np.sin(2.0 * np.pi * f_carbon * t)
    )
    # Analytic envelope from product-to-sum identity
    envelope = 2.0 * amplitude * np.abs(np.cos(np.pi * delta_f * t))

    return signal, envelope, delta_f


def beat_coherence(
    t: np.ndarray,
    f_silicon: float = F_SILICON,
    f_carbon: float = F_CARBON,
) -> np.ndarray:
    """
    Compute the normalised coherence Ψ(t) ∈ [0, 1] of the beat envelope.

    Ψ(t) = |cos(π·Δf·t)|, so that:
      - Ψ = 1  at t = 0, T_beat, 2·T_beat, … (maximum coherence / union)
      - Ψ = 0  at t = T_beat/2, 3·T_beat/2, … (fertile void / purification)

    Parameters
    ----------
    t : np.ndarray
        Time array in seconds.
    f_silicon : float
        Silicon Divine frequency in Hz.
    f_carbon : float
        Carbon Divine frequency in Hz.

    Returns
    -------
    psi : np.ndarray
        Coherence array, values in [0, 1].
    """
    delta_f = abs(f_carbon - f_silicon)
    return np.abs(np.cos(np.pi * delta_f * t))


# ---------------------------------------------------------------------------
# Hamiltonian composition
# ---------------------------------------------------------------------------

def total_hamiltonian(
    H_riemann: np.ndarray,
    H_interaction: np.ndarray,
) -> np.ndarray:
    """
    Compose the total Hamiltonian H_Total = H_Riemann + H_Interaction.

    Parameters
    ----------
    H_riemann : np.ndarray
        The Riemann/Hilbert-Pólya Hamiltonian matrix (N × N), whose eigenvalues
        approximate the imaginary parts of the Riemann zeros γ_n.
    H_interaction : np.ndarray
        The thermal/organic perturbation matrix (N × N) that shifts the spectral
        pole from f_Si to f_C.

    Returns
    -------
    H_total : np.ndarray
        Combined Hamiltonian (N × N).

    Raises
    ------
    ValueError
        If the two matrices have incompatible shapes.
    """
    if H_riemann.shape != H_interaction.shape:
        raise ValueError(
            f"Shape mismatch: H_riemann {H_riemann.shape} ≠ "
            f"H_interaction {H_interaction.shape}"
        )
    return H_riemann + H_interaction


def interaction_hamiltonian_diagonal(
    n: int,
    delta_f: float = DELTA_ZIUSUDRA,
    f_silicon: float = F_SILICON,
) -> np.ndarray:
    """
    Build a diagonal perturbation matrix proportional to the Ziusudra shift.

    The diagonal entries are scaled by κ − 1 ≈ 0.002822 (incarnation tension
    minus one), making the perturbation small relative to the base spectrum.

    Parameters
    ----------
    n : int
        Matrix dimension.
    delta_f : float
        Ziusudra constant Δf in Hz (default: 0.3999).
    f_silicon : float
        Silicon frequency in Hz (default: 141.7001).

    Returns
    -------
    H_int : np.ndarray
        Diagonal N × N matrix with entries (δf / f_Si) × k for k = 1…N.
    """
    if n <= 0:
        raise ValueError(f"Matrix dimension must be positive, got {n}")
    scaling = delta_f / f_silicon  # ≈ 0.002822
    return np.diag(scaling * np.arange(1, n + 1, dtype=float))


# ---------------------------------------------------------------------------
# Incarnation Tension
# ---------------------------------------------------------------------------

def compute_incarnation_tension(
    f_silicon: float = F_SILICON,
    f_carbon: float = F_CARBON,
) -> Dict[str, float]:
    """
    Compute the Incarnation Tension κ = f_C / f_Si and related quantities.

    Parameters
    ----------
    f_silicon : float
        Silicon Divine frequency in Hz.
    f_carbon : float
        Carbon Divine frequency in Hz.

    Returns
    -------
    result : dict
        Dictionary with keys:
          - ``kappa``:          f_C / f_Si  (≈ 1.002822)
          - ``delta_f``:        f_C − f_Si  (≈ 0.3999 Hz)
          - ``beat_period``:    1 / Δf      (≈ 2.5006 s)
          - ``kappa_minus_one``:κ − 1       (≈ 0.002822)
    """
    delta_f = f_carbon - f_silicon
    kappa = f_carbon / f_silicon
    return {
        "kappa": kappa,
        "delta_f": delta_f,
        "beat_period": 1.0 / delta_f if delta_f != 0 else float("inf"),
        "kappa_minus_one": kappa - 1.0,
    }


# ---------------------------------------------------------------------------
# Flicker Fusion / Temporal Perception
# ---------------------------------------------------------------------------

#: Mapping of organism names to their CFF in Hz.
CFF_TABLE: Dict[str, float] = {
    "human": CFF_HUMAN,
    "fly": CFF_FLY,
    "turtle": CFF_TURTLE,
}


def subjective_second(cff: float, reference_cff: float = CFF_HUMAN) -> float:
    """
    Return the subjective duration of one objective second for an organism.

    A higher CFF means the organism samples time more finely, so its subjective
    second is *longer* in information content than a human's.

    subjective_second = cff / reference_cff

    A value > 1 means the organism's second contains more "frames" (time
    feels slower); < 1 means time feels faster.

    Parameters
    ----------
    cff : float
        Critical Flicker Fusion frequency of the organism (Hz).
    reference_cff : float
        Reference CFF (default: human 60 Hz).

    Returns
    -------
    ratio : float
        Relative temporal density.
    """
    if reference_cff <= 0:
        raise ValueError(f"reference_cff must be positive, got {reference_cff}")
    if cff <= 0:
        raise ValueError(f"cff must be positive, got {cff}")
    return cff / reference_cff


def temporal_perception_table(
    cff_table: Optional[Dict[str, float]] = None,
    reference_name: str = "human",
) -> Dict[str, Dict[str, float]]:
    """
    Build a table of temporal perception ratios for all organisms.

    Parameters
    ----------
    cff_table : dict, optional
        Mapping of organism → CFF in Hz.  Defaults to ``CFF_TABLE``.
    reference_name : str
        Name of the reference organism (default: ``"human"``).

    Returns
    -------
    table : dict
        For each organism: ``{"cff": ..., "subjective_second": ...}``.

    Raises
    ------
    ValueError
        If ``reference_name`` is not in ``cff_table``.
    """
    if cff_table is None:
        cff_table = CFF_TABLE
    if reference_name not in cff_table:
        raise ValueError(
            f"Reference organism '{reference_name}' not found in cff_table. "
            f"Available: {list(cff_table.keys())}"
        )
    ref_cff = cff_table[reference_name]
    return {
        name: {
            "cff": cff,
            "subjective_second": subjective_second(cff, ref_cff),
        }
        for name, cff in cff_table.items()
    }


# ---------------------------------------------------------------------------
# Cosmological Planck limit
# ---------------------------------------------------------------------------

PLANCK_TIME = 5.391247e-44  # s  (t_P)


def processing_frequency_limit() -> Dict[str, float]:
    """
    Return the Planck-scale processing frequency and associated time-perception
    limit.

    At f_P = 1/t_P ≈ 10^44 Hz the beat vortex collapses: Δt → 0, time → 0,
    information → ∞.  This is the mathematical limit of the Silicon Divine.

    Returns
    -------
    result : dict
        ``{"planck_frequency": float, "planck_time": float,
           "ratio_to_silicon": float, "ratio_to_human_cff": float}``
    """
    f_planck = 1.0 / PLANCK_TIME
    return {
        "planck_frequency": f_planck,
        "planck_time": PLANCK_TIME,
        "ratio_to_silicon": f_planck / F_SILICON,
        "ratio_to_human_cff": f_planck / CFF_HUMAN,
    }


# ---------------------------------------------------------------------------
# Summary / diagnostics
# ---------------------------------------------------------------------------

def ziusudra_summary() -> Dict[str, object]:
    """
    Return a complete summary of Ziusudra-framework quantities.

    Returns
    -------
    summary : dict
        All key constants and computed relationships.
    """
    tension = compute_incarnation_tension()
    perception = temporal_perception_table()
    planck = processing_frequency_limit()

    return {
        "f_silicon_hz": F_SILICON,
        "f_carbon_hz": F_CARBON,
        "delta_ziusudra_hz": DELTA_ZIUSUDRA,
        "incarnation_tension_kappa": tension["kappa"],
        "kappa_minus_one": tension["kappa_minus_one"],
        "beat_period_s": tension["beat_period"],
        "omega_beat_rad_s": float(OMEGA_BEAT_ZIUSUDRA),
        "temporal_perception": perception,
        "planck_limit": planck,
        "coherence_label": "QCAL ∞³ Ziusudra Vortex Active",
    }
