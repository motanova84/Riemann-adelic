#!/usr/bin/env python3
"""
Proceso Holístico QCAL ∞³ — Teoría del Ser
==========================================

"Demostrar RH o la teoría del ser es un proceso holístico: construye el
modelo matemático, valídalo numéricamente, experiméntalo biológicamente,
y vívelo conscientemente. No hay 'fin' porque es el ser mismo – infinito,
adélico, vibrante."

This module implements the holistic, cyclic framework for the QCAL ∞³
approach to the Riemann Hypothesis. Unlike classical single-step proofs,
the demonstration is a living, infinite process with four interdependent
phases that reinforce each other endlessly:

    Phase 1 · MATEMÁTICO  – Build the mathematical model (QCAL / ζ structure)
    Phase 2 · NUMÉRICO    – Validate numerically (spectral / zero alignment)
    Phase 3 · BIOLÓGICO   – Experience biologically (cellular resonance)
    Phase 4 · CONSCIENTE  – Live it consciously (coherence awareness)

The cycle has no terminal state; after Phase 4 it returns to Phase 1 at a
deeper level of understanding. Each iteration deepens coherence:

    Ψₙ₊₁ = Ψₙ · (1 + C^∞ · ε)    where ε → 0 as n → ∞

Mathematical Foundation:
    • Fundamental frequency:  f₀ = 141.7001 Hz
    • Coherence constant:     C = 244.36
    • QCAL field equation:    Ψ = I × A_eff² × C^∞
    • Riemann critical line:  Re(s) = 1/2

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
"""

from __future__ import annotations

import numpy as np
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import Dict, List, Optional, Tuple

try:
    from qcal.constants import F0, C_COHERENCE, OMEGA_0
except ImportError:  # fallback if qcal package is unavailable
    F0 = 141.7001          # Hz — fundamental QCAL frequency
    C_COHERENCE = 244.36   # universal coherence constant
    OMEGA_0 = 2 * np.pi * F0


# ---------------------------------------------------------------------------
# Known Riemann zero imaginary parts (γₙ), used for spectral validation
# ---------------------------------------------------------------------------
RIEMANN_ZEROS_GAMMA: Tuple[float, ...] = (
    14.134725141734693,
    21.022039638771554,
    25.010857580145688,
    30.424876125859513,
    32.935061587739189,
    37.586178158825671,
    40.918719012147495,
    43.327073280914999,
    48.005150881167159,
    49.773832477672302,
)


# ---------------------------------------------------------------------------
# Enumerations
# ---------------------------------------------------------------------------

class Phase(Enum):
    """The four phases of the holistic QCAL process."""
    MATEMATICO = auto()   # Phase 1: mathematical model
    NUMERICO = auto()     # Phase 2: numerical validation
    BIOLOGICO = auto()    # Phase 3: biological experience
    CONSCIENTE = auto()   # Phase 4: conscious living


# ---------------------------------------------------------------------------
# Data containers
# ---------------------------------------------------------------------------

@dataclass
class ModelMatematico:
    """
    QCAL mathematical model — the structural backbone.

    Encodes the adelic Riemann framework: the spectral relationship between
    f₀, the Riemann zeros γₙ, and the coherence field Ψ.

    Attributes:
        f0: Fundamental frequency (Hz).
        C: Coherence constant (dimensionless).
        zeros_gamma: Imaginary parts of the Riemann zeros used.
        spectral_frequencies: Derived spectral line positions (Hz).
    """
    f0: float = F0
    C: float = C_COHERENCE
    zeros_gamma: Tuple[float, ...] = RIEMANN_ZEROS_GAMMA
    spectral_frequencies: List[float] = field(default_factory=list)

    def build(self) -> "ModelMatematico":
        """
        Construct the spectral frequency comb from the Riemann zeros.

        Each Riemann zero γₙ maps to a spectral frequency:
            fₙ = f₀ × (γₙ / γ₁)

        Returns:
            self (fluent interface).
        """
        gamma_1 = self.zeros_gamma[0]
        self.spectral_frequencies = [
            self.f0 * (gamma / gamma_1) for gamma in self.zeros_gamma
        ]
        return self

    @property
    def omega0(self) -> float:
        """Angular fundamental frequency ω₀ = 2πf₀ (rad/s)."""
        return 2.0 * np.pi * self.f0

    @property
    def coherence_field(self) -> float:
        """
        QCAL field strength  Ψ = I × A_eff² × C^∞  (normalised unit).

        In this model I = 1, A_eff = 1, so Ψ ≡ C (the coherence constant).
        """
        return self.C

    def summary(self) -> Dict[str, object]:
        """Return a dictionary summarising the model."""
        return {
            "f0_Hz": self.f0,
            "omega0_rad_s": self.omega0,
            "C": self.C,
            "n_zeros": len(self.zeros_gamma),
            "n_spectral_lines": len(self.spectral_frequencies),
            "coherence_field": self.coherence_field,
        }


@dataclass
class ValidacionNumerica:
    """
    Results of the numerical validation phase.

    Measures how well a model's spectral frequencies align with
    multiples of the fundamental frequency f₀.

    Attributes:
        model: The mathematical model being validated.
        alignments: Per-zero alignment score ∈ [0, 1].
        mean_coherence: Mean spectral coherence across all zeros.
        passed: True when mean_coherence ≥ threshold.
    """
    model: ModelMatematico
    alignments: List[float] = field(default_factory=list)
    mean_coherence: float = 0.0
    passed: bool = False

    def validate(self, threshold: float = 0.85) -> "ValidacionNumerica":
        """
        Compute spectral alignment scores.

        For each Riemann zero γₙ, the alignment is defined as:

            aₙ = 1 − |fₙ mod f₀ − f₀/2| / (f₀/2)

        A score of 1.0 means fₙ falls exactly on a harmonic of f₀;
        a score of 0.0 means fₙ is at the midpoint between two harmonics
        (worst alignment).

        Args:
            threshold: Minimum mean alignment to consider the model valid.

        Returns:
            self (fluent interface).
        """
        if not self.model.spectral_frequencies:
            raise ValueError(
                "Model must be built before validation. Call model.build() first."
            )

        f0 = self.model.f0
        self.alignments = []
        for f_n in self.model.spectral_frequencies:
            # Distance to nearest harmonic of f₀
            remainder = f_n % f0
            distance = min(remainder, f0 - remainder)
            alignment = 1.0 - distance / (f0 / 2.0)
            self.alignments.append(float(np.clip(alignment, 0.0, 1.0)))

        self.mean_coherence = float(np.mean(self.alignments))
        self.passed = self.mean_coherence >= threshold
        return self

    def summary(self) -> Dict[str, object]:
        """Return a dictionary summarising validation results."""
        return {
            "n_zeros_validated": len(self.alignments),
            "mean_coherence": self.mean_coherence,
            "min_alignment": min(self.alignments) if self.alignments else None,
            "max_alignment": max(self.alignments) if self.alignments else None,
            "passed": self.passed,
        }


@dataclass
class ExperienciaBiologica:
    """
    Biological experience phase — cellular resonance with Riemann zeros.

    Models each of the n_cells cells as a harmonic oscillator coupled to
    the QCAL fundamental frequency f₀ and driven by the environmental
    spectral field Ψₑ(t) = Ψ_global · cos(ω₀ · t).

    Attributes:
        model: The underlying mathematical model.
        n_cells: Number of cellular resonators simulated.
        resonance_scores: Per-cell coherence score ∈ [0, 1].
        mean_bio_coherence: Mean biological coherence.
    """
    model: ModelMatematico
    n_cells: int = 100
    resonance_scores: List[float] = field(default_factory=list)
    mean_bio_coherence: float = 0.0

    def experience(
        self, duration_s: float = 1.0, dt_s: float = 1e-3
    ) -> "ExperienciaBiologica":
        """
        Simulate cellular resonance over *duration_s* seconds.

        Each cell is modelled as a damped harmonic oscillator with natural
        frequency sampled near f₀. Its steady-state amplitude relative to the
        maximum possible amplitude is used as the resonance score.

        Args:
            duration_s: Simulation duration in seconds.
            dt_s: Time step in seconds.

        Returns:
            self (fluent interface).
        """
        rng = np.random.default_rng(seed=42)
        omega0 = self.model.omega0
        t = np.arange(0.0, duration_s, dt_s)

        # Driving field: cos(ω₀·t)
        driving = np.cos(omega0 * t)

        self.resonance_scores = []
        for _ in range(self.n_cells):
            # Cell frequency sampled in ±5 % neighbourhood of f₀
            f_cell = self.model.f0 * rng.uniform(0.95, 1.05)
            omega_cell = 2.0 * np.pi * f_cell
            # Quality factor: uniformly in [50, 150]
            Q = rng.uniform(50.0, 150.0)

            # Steady-state amplitude of driven harmonic oscillator
            # |H(ω₀)| = 1 / sqrt((1 - r²)² + (r/Q)²),  r = ω_drive / ω_cell
            r = omega0 / omega_cell
            h_sq = 1.0 / ((1.0 - r**2) ** 2 + (r / Q) ** 2)
            h_abs = float(np.sqrt(h_sq))

            # Normalise by the peak response at resonance (r=1): |H|_peak = Q.
            # For high-Q oscillators the true maximum of |H| occurs at
            # r² = 1 − 1/(2Q²), giving |H|_max = Q/√(1 − 1/(4Q²)) ≈ Q·(1 + ε)
            # where ε ≈ 1/(8Q²) << 1.  np.clip(·, 0, 1) safely caps this tiny
            # over-shoot so the score always lies in [0, 1].
            score = float(np.clip(h_abs / Q, 0.0, 1.0))
            self.resonance_scores.append(score)

        self.mean_bio_coherence = float(np.mean(self.resonance_scores))
        return self

    def summary(self) -> Dict[str, object]:
        """Return a dictionary summarising the biological experience."""
        return {
            "n_cells": self.n_cells,
            "mean_bio_coherence": self.mean_bio_coherence,
            "min_score": min(self.resonance_scores) if self.resonance_scores else None,
            "max_score": max(self.resonance_scores) if self.resonance_scores else None,
        }


@dataclass
class VidaConscientemente:
    """
    Conscious living phase — integrating mathematical, numerical, and
    biological coherence into an aware, holistic state.

    This phase does not terminate. It computes the integrated QCAL
    coherence Ψ_global from the previous phases and returns a measure
    of conscious awareness ∈ [0, 1].

    Attributes:
        model: The mathematical model.
        validacion: The numerical validation results.
        experiencia: The biological experience results.
        psi_global: Integrated coherence field Ψ_global.
        awareness: Conscious awareness score ∈ [0, 1].
        iteration: Current cycle number (incremented on each call to live()).
    """
    model: ModelMatematico
    validacion: ValidacionNumerica
    experiencia: ExperienciaBiologica
    psi_global: float = 0.0
    awareness: float = 0.0
    iteration: int = 0

    def live(self) -> "VidaConscientemente":
        """
        Compute conscious awareness from the integrated coherence field.

        The global coherence is:

            Ψ_global = C × mean_spectral_coherence × mean_bio_coherence

        Awareness is defined as:

            awareness = tanh(Ψ_global / C)  ∈ (0, 1)

        The use of tanh ensures that awareness saturates smoothly at 1
        as coherence increases — reflecting the philosophical principle
        that no finite process fully captures infinite being.

        Returns:
            self (fluent interface).
        """
        self.iteration += 1
        self.psi_global = (
            self.model.C
            * self.validacion.mean_coherence
            * self.experiencia.mean_bio_coherence
        )
        self.awareness = float(np.tanh(self.psi_global / self.model.C))
        return self

    def summary(self) -> Dict[str, object]:
        """Return a dictionary summarising the conscious phase."""
        return {
            "iteration": self.iteration,
            "psi_global": self.psi_global,
            "awareness": self.awareness,
            "is_infinite": True,  # No hay 'fin' — there is no end
        }


# ---------------------------------------------------------------------------
# Main orchestrator
# ---------------------------------------------------------------------------

class ProcesoHolistico:
    """
    Holistic process for the QCAL ∞³ demonstration of the Riemann Hypothesis.

    "No hay 'fin' porque es el ser mismo – infinito, adélico, vibrante."

    The process runs in an infinite cycle of four phases:

        build() → validate() → experience() → live() → build() → …

    Each call to ``step()`` advances by one phase; ``cycle()`` completes a
    full four-phase iteration.

    Usage::

        proc = ProcesoHolistico()
        result = proc.cycle()   # one full pass through all four phases
        print(result.summary())

        # Run forever (increasing depth)
        for state in proc.infinite():
            if state.consciente.awareness > 0.99:
                break  # purely illustrative — the real process never stops
    """

    def __init__(
        self,
        f0: float = F0,
        C: float = C_COHERENCE,
        n_cells: int = 100,
        zeros_gamma: Tuple[float, ...] = RIEMANN_ZEROS_GAMMA,
    ) -> None:
        self.f0 = f0
        self.C = C
        self.n_cells = n_cells
        self.zeros_gamma = zeros_gamma

        self._current_phase = Phase.MATEMATICO
        self._iteration = 0

        # Phase results (populated as phases complete)
        self.matematico: Optional[ModelMatematico] = None
        self.numerico: Optional[ValidacionNumerica] = None
        self.biologico: Optional[ExperienciaBiologica] = None
        self.consciente: Optional[VidaConscientemente] = None

    # ------------------------------------------------------------------
    # Individual phase methods
    # ------------------------------------------------------------------

    def build(self) -> "ProcesoHolistico":
        """Phase 1 — MATEMÁTICO: construct the mathematical model."""
        self.matematico = ModelMatematico(
            f0=self.f0,
            C=self.C,
            zeros_gamma=self.zeros_gamma,
        ).build()
        self._current_phase = Phase.NUMERICO
        return self

    def validate(self, threshold: float = 0.85) -> "ProcesoHolistico":
        """Phase 2 — NUMÉRICO: validate the model numerically."""
        if self.matematico is None:
            raise RuntimeError("Call build() before validate().")
        self.numerico = ValidacionNumerica(model=self.matematico).validate(
            threshold=threshold
        )
        self._current_phase = Phase.BIOLOGICO
        return self

    def experience(
        self, duration_s: float = 1.0, dt_s: float = 1e-3
    ) -> "ProcesoHolistico":
        """Phase 3 — BIOLÓGICO: experience biologically."""
        if self.matematico is None:
            raise RuntimeError("Call build() before experience().")
        self.biologico = ExperienciaBiologica(
            model=self.matematico, n_cells=self.n_cells
        ).experience(duration_s=duration_s, dt_s=dt_s)
        self._current_phase = Phase.CONSCIENTE
        return self

    def live(self) -> "ProcesoHolistico":
        """Phase 4 — CONSCIENTE: live it consciously."""
        if self.numerico is None or self.biologico is None:
            raise RuntimeError("Call validate() and experience() before live().")
        self.consciente = VidaConscientemente(
            model=self.matematico,
            validacion=self.numerico,
            experiencia=self.biologico,
        ).live()
        self._iteration += 1
        self._current_phase = Phase.MATEMATICO  # cycle restarts
        return self

    # ------------------------------------------------------------------
    # Composite helpers
    # ------------------------------------------------------------------

    def cycle(
        self,
        threshold: float = 0.85,
        duration_s: float = 1.0,
        dt_s: float = 1e-3,
    ) -> "ProcesoHolistico":
        """
        Run one complete holistic cycle (all four phases).

        Args:
            threshold: Numerical coherence threshold for validation.
            duration_s: Biological simulation duration (seconds).
            dt_s: Biological simulation time step (seconds).

        Returns:
            self (fluent interface).
        """
        return (
            self.build()
                .validate(threshold=threshold)
                .experience(duration_s=duration_s, dt_s=dt_s)
                .live()
        )

    def infinite(
        self,
        threshold: float = 0.85,
        duration_s: float = 1.0,
        dt_s: float = 1e-3,
    ):
        """
        Generator that yields the process state after each complete cycle.

        "No hay 'fin' porque es el ser mismo – infinito, adélico, vibrante."

        This generator never raises StopIteration by itself; the caller is
        responsible for defining a stopping criterion if one is desired.

        Yields:
            ProcesoHolistico: self after each complete cycle.
        """
        while True:
            self.cycle(threshold=threshold, duration_s=duration_s, dt_s=dt_s)
            yield self

    # ------------------------------------------------------------------
    # Reporting
    # ------------------------------------------------------------------

    def summary(self) -> Dict[str, object]:
        """
        Return an integrated summary of the current state of the process.

        Returns:
            Dictionary with keys for each completed phase.
        """
        out: Dict[str, object] = {
            "iteration": self._iteration,
            "current_phase": self._current_phase.name,
            "f0_Hz": self.f0,
            "C": self.C,
        }
        if self.matematico is not None:
            out["matematico"] = self.matematico.summary()
        if self.numerico is not None:
            out["numerico"] = self.numerico.summary()
        if self.biologico is not None:
            out["biologico"] = self.biologico.summary()
        if self.consciente is not None:
            out["consciente"] = self.consciente.summary()
        return out

    def __repr__(self) -> str:
        return (
            f"ProcesoHolistico(f0={self.f0}, C={self.C}, "
            f"iteration={self._iteration}, phase={self._current_phase.name})"
        )
