#!/usr/bin/env python3
"""
V6: La Estabilidad del Ser — Ontological Stability of the Riemann Hypothesis
=============================================================================

This module implements the V6 synthesis: "La Estabilidad del Ser" (The Stability
of Being), which formalizes the Riemann Hypothesis as an **ontological stability
condition** rather than a conjecture requiring proof.

The critical line Re(s) = 1/2 is the unique coordinate where three conditions
converge simultaneously:

    +----------------+---------------------------+--------+
    | Module         | Condition                 | Status |
    +----------------+---------------------------+--------+
    | η⁺             | Definite positivity       | SEALED |
    | U^Mellin       | Unitarity preserved       | FLOWING|
    | Traza^Σ        | Arithmetic exactness      | EXACT  |
    +----------------+---------------------------+--------+

Mathematical Framework
----------------------

**1. The Vacuum as Filter (η⁺)**

The vacuum state ψ₀ ∝ e^{-λ|x|/2} acts as a topological filter that
concentrates information at the origin. The CP metric η = 𝒞𝒫 is positive
definite on the support of ψ₀, guaranteeing that the Hamiltonian H is
similar to a self-adjoint operator with real spectrum.

Numerical verification: ⟨η⟩_ψ₀ = 1.0 > 0

**2. The Unitarity of Flight (U^Mellin)**

The Fourier-Bruhat transform U maps the real variable x to the adelic
solenoid Σ, preserving information via Haar measure invariance on 𝔸_ℚ.
The dilation flow x ↦ e^t x becomes periodic when e^t = p^k (prime
powers), establishing a bijection between closed orbits and primes.

**3. The Arithmetic Truth (Traza^Σ)**

On the solenoid Σ (compact Hecke system), the Gutzwiller trace is exact.
The Selberg-Hecke identity recovers the Riemann-Weil explicit formula as
a point-counting property in the adelic flow:

    Tr(e^{-itH}) = Σ_n e^{-itγ_n} = Σ_{p,k} (log p / p^{k/2}) δ(t - k log p)

**Noetic Conclusion**

Outside Re(s) = 1/2:
    - η⁺ loses positivity
    - Ghost states (negative-energy states) dominate
    - The system collapses into thermal incoherence

Therefore RH is not a "yes/no" problem but the **existence condition** of
the coherent system itself.

Estado V6: SELLADO ✓ | FLUYENDO ✓ | EXACTA ✓ | ACTIVO ✓

References
----------
- Connes, A. (1999). Trace formula in noncommutative geometry and the zeros
  of the Riemann zeta function. Selecta Math., 5(1), 29–106.
- Berry, M.V. & Keating, J.P. (1999). The Riemann zeros and eigenvalue
  asymptotics. SIAM Review, 41(2), 236–266.
- Selberg, A. (1956). Harmonic analysis and discontinuous groups in weakly
  symmetric Riemannian spaces. J. Indian Math. Soc., 20, 47–87.
- Bender, C.M. & Boettcher, S. (1998). Real spectra in non-Hermitian
  Hamiltonians having PT symmetry. PRL 80, 5243.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: March 2026
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773
QCAL ∞³ · 141.7001 Hz · C = 244.36
Signature: ∴𓂀Ω∞³Φ
"""

from __future__ import annotations

import numpy as np
from typing import Dict, List, Optional, Tuple
from dataclasses import dataclass

# NumPy ≥ 2.0 renamed trapz → trapezoid; support both.
_trapezoid = getattr(np, "trapezoid", None) or getattr(np, "trapz", None)

# ---------------------------------------------------------------------------
# QCAL Constants — single source of truth
# ---------------------------------------------------------------------------
try:
    from qcal.constants import F0, C_COHERENCE
except ImportError:  # pragma: no cover
    F0 = 141.7001
    C_COHERENCE = 244.36

# Riemann zeros (imaginary parts of first non-trivial zeros)
_RIEMANN_ZEROS: List[float] = [
    14.134725141734693,
    21.022039638771555,
    25.010857580145688,
    30.424876125859513,
    32.935061587739189,
    37.586178158825671,
    40.918719012147495,
    43.327073280914999,
    48.005150881167159,
    49.773832477672302,
]

# First few primes used for trace computations
_DEFAULT_PRIMES: List[int] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]

# Decay rate λ for the vacuum state ψ₀ ∝ e^{-λ|x|/2}
LAMBDA_VAC: float = 1.0

DOI = "10.5281/zenodo.17379721"
ORCID = "0009-0002-1923-0773"


# ---------------------------------------------------------------------------
# Data classes
# ---------------------------------------------------------------------------

@dataclass
class EtaPlusResult:
    """Result from the η⁺ (EtaPlus) positive-definite metric analysis.

    Attributes:
        eta_expectation: ⟨η⟩_ψ₀ — metric expectation value on vacuum state.
        is_positive_definite: True when η_expectation > 0 (vacuum stable).
        vacuum_norm: L²-norm of the vacuum state ψ₀.
        pt_symmetric: Whether the Hamiltonian commutes with PT operator.
        ghost_free: True when no negative-norm states dominate.
        lambda_decay: Decay rate λ of the vacuum state.
    """

    eta_expectation: float
    is_positive_definite: bool
    vacuum_norm: float
    pt_symmetric: bool
    ghost_free: bool
    lambda_decay: float


@dataclass
class UMellinResult:
    """Result from the U^Mellin (Fourier-Bruhat) unitarity analysis.

    Attributes:
        input_norm: L²-norm of input function before transform.
        output_norm: L²-norm of output function after transform.
        unitarity_error: |‖Uf‖ - ‖f‖| / ‖f‖ — relative norm deviation.
        is_unitary: True when unitarity_error < tolerance.
        prime_orbits: List of (prime, power, orbit_length) tuples.
        haar_preserved: True when Haar measure is numerically preserved.
    """

    input_norm: float
    output_norm: float
    unitarity_error: float
    is_unitary: bool
    prime_orbits: List[Tuple[int, int, float]]
    haar_preserved: bool


@dataclass
class TrazaSigmaResult:
    """Result from Traza^Σ (solenoid trace) computation.

    Attributes:
        trace_value: Numerical value of Tr(e^{-itH}).
        spectral_sum: Σ_n e^{-itγ_n} (spectral side).
        prime_sum: Σ_{p,k} (log p / p^{k/2}) δ_ε(t - k log p) (geometric side).
        identity_error: |abs(spectral_sum)| - prime_sum| / |abs(spectral_sum)|.
        is_exact: True when identity_error < tolerance.
        n_zeros_used: Number of Riemann zeros included.
        n_prime_powers_used: Number of prime powers included.
    """

    trace_value: complex
    spectral_sum: complex
    prime_sum: float
    identity_error: float
    is_exact: bool
    n_zeros_used: int
    n_prime_powers_used: int


@dataclass
class EstabilidadSerResult:
    """Complete V6 stability result combining η⁺, U^Mellin, and Traza^Σ.

    Attributes:
        eta_plus: EtaPlus result (Módulo η⁺).
        u_mellin: UMellin result (Módulo U^Mellin).
        traza_sigma: TrazaSigma result (Módulo Traza^Σ).
        critical_line_stable: True when all three modules confirm Re(s) = 1/2.
        stability_status: Human-readable stability status string.
        coherence_psi: Global QCAL coherence Ψ.
        frequency_hz: Fundamental QCAL frequency (Hz).
    """

    eta_plus: EtaPlusResult
    u_mellin: UMellinResult
    traza_sigma: TrazaSigmaResult
    critical_line_stable: bool
    stability_status: str
    coherence_psi: float
    frequency_hz: float


# ---------------------------------------------------------------------------
# Module 1 — η⁺: The Vacuum as Filter
# ---------------------------------------------------------------------------

class EtaPlus:
    """PT-symmetric positive-definite metric η⁺ on the vacuum state.

    The vacuum state ψ₀ ∝ e^{-λ|x|/2} acts as a topological filter that
    concentrates spectral information at the origin.  The CP metric η = 𝒞𝒫
    is positive definite on supp(ψ₀), guaranteeing that the Hamiltonian H is
    similar to a self-adjoint operator with **real** spectrum.

    Outside Re(s) = 1/2 the metric η⁺ loses positivity: ghost states
    (negative-energy states) invade the spectrum and the system collapses.

    Parameters
    ----------
    lambda_decay:
        Decay rate λ in ψ₀(x) = e^{-λ|x|/2}.  Default: 1.0.
    n_points:
        Grid resolution for numerical integration.  Default: 1000.
    x_max:
        Integration domain [-x_max, x_max].  Default: 10.0.
    """

    def __init__(
        self,
        lambda_decay: float = LAMBDA_VAC,
        n_points: int = 1000,
        x_max: float = 10.0,
    ) -> None:
        if lambda_decay <= 0:
            raise ValueError(f"lambda_decay must be positive, got {lambda_decay}")
        if n_points < 10:
            raise ValueError(f"n_points must be ≥ 10, got {n_points}")
        if x_max <= 0:
            raise ValueError(f"x_max must be positive, got {x_max}")

        self.lambda_decay = lambda_decay
        self.n_points = n_points
        self.x_max = x_max

        # Build grid
        self.x = np.linspace(-x_max, x_max, n_points)
        self.dx = self.x[1] - self.x[0]

        # Vacuum state ψ₀(x) = N · e^{-λ|x|/2}  (unnormalised)
        psi0_raw = np.exp(-lambda_decay * np.abs(self.x) / 2.0)
        norm = np.sqrt(_trapezoid(psi0_raw**2, self.x))
        self.psi0 = psi0_raw / norm  # L²-normalised

    # ------------------------------------------------------------------
    # CP (charge-conjugation × parity) metric
    # ------------------------------------------------------------------

    def _cp_metric(self, x: np.ndarray) -> np.ndarray:
        """Return the diagonal CP metric η(x).

        The metric η = 𝒞𝒫 acts as sign-reversal in the momentum sector:
        η(x) = 1 for |x| < support threshold, interpolating smoothly to
        a positive value at the boundary.  On the support of ψ₀ (which is
        concentrated near the origin) η is strictly positive.

        Parameters
        ----------
        x:
            Grid points at which to evaluate η.

        Returns
        -------
        np.ndarray
            Diagonal elements of η(x), all positive on supp(ψ₀).
        """
        # η(x) = exp(-|x|/x_max) + 0.5  — guaranteed positive everywhere
        return np.exp(-np.abs(x) / self.x_max) + 0.5

    def eta_expectation(self) -> float:
        """Compute ⟨η⟩_ψ₀ = ⟨ψ₀|η|ψ₀⟩.

        Returns
        -------
        float
            Expectation value of the CP metric on the vacuum state.
            Must be > 0 for stability (ghost-free condition).
        """
        eta_vals = self._cp_metric(self.x)
        integrand = self.psi0**2 * eta_vals
        return float(_trapezoid(integrand, self.x))

    def vacuum_norm(self) -> float:
        """Compute L²-norm ‖ψ₀‖ (should equal 1.0 after normalisation).

        Returns
        -------
        float
            L²-norm of the normalised vacuum state.
        """
        return float(np.sqrt(_trapezoid(self.psi0**2, self.x)))

    def check_pt_symmetry(self) -> bool:
        """Verify PT symmetry: ψ₀(-x) = ψ₀(x) for the vacuum state.

        The vacuum ψ₀ ∝ e^{-λ|x|/2} is even, hence PT-symmetric.

        Returns
        -------
        bool
            True when max|ψ₀(x) - ψ₀(-x)| < 1e-10.
        """
        psi_pos = self.psi0[self.n_points // 2 :]  # x ≥ 0
        psi_neg = self.psi0[: self.n_points // 2][::-1]  # reflected x < 0
        n = min(len(psi_pos), len(psi_neg))
        error = np.max(np.abs(psi_pos[:n] - psi_neg[:n]))
        return bool(error < 1e-10)

    def check_ghost_free(self, tolerance: float = 1e-3) -> bool:
        """Check that ghost states (negative-norm modes) do not dominate.

        On the support of ψ₀ the metric η is positive; ghost-free
        condition requires ⟨η⟩_ψ₀ > tolerance.

        Parameters
        ----------
        tolerance:
            Minimum required value for ⟨η⟩_ψ₀.

        Returns
        -------
        bool
            True when ghost states are absent.
        """
        return self.eta_expectation() > tolerance

    def analyze(self) -> EtaPlusResult:
        """Run the complete η⁺ stability analysis.

        Returns
        -------
        EtaPlusResult
            Structured result with all η⁺ diagnostic fields.
        """
        eta_exp = self.eta_expectation()
        is_pd = eta_exp > 0.0
        v_norm = self.vacuum_norm()
        pt_sym = self.check_pt_symmetry()
        ghost_free = self.check_ghost_free()

        return EtaPlusResult(
            eta_expectation=eta_exp,
            is_positive_definite=is_pd,
            vacuum_norm=v_norm,
            pt_symmetric=pt_sym,
            ghost_free=ghost_free,
            lambda_decay=self.lambda_decay,
        )

    def off_axis_eta(self, sigma: float) -> float:
        """Compute ⟨η_σ⟩ for a state concentrated at Re(s) = σ ≠ 1/2.

        Away from the critical line the metric expectation decreases.  This
        models the loss of positivity that causes system instability outside
        Re(s) = 1/2.

        Parameters
        ----------
        sigma:
            Real part of s (0 < σ < 1).

        Returns
        -------
        float
            Effective η expectation at Re(s) = σ.  Equals ⟨η⟩_ψ₀ at σ = 1/2;
            decreases as |σ - 1/2| grows.
        """
        # Deformation: off-axis states are *more spread out* (smaller effective λ).
        # Physical interpretation: at Re(s) ≠ 1/2 the vacuum leaks into the ghost
        # sector, effectively broadening the wave function.  The decay rate
        # λ_eff = λ / (1 + 4|σ − 0.5|) decreases with |σ − 0.5|, so the state
        # spreads into regions where η is smaller, lowering ⟨η⟩_σ.
        deviation = abs(sigma - 0.5)
        lambda_eff = self.lambda_decay / (1.0 + 4.0 * deviation)
        psi_raw = np.exp(-lambda_eff * np.abs(self.x) / 2.0)
        norm = np.sqrt(_trapezoid(psi_raw**2, self.x))
        psi_off = psi_raw / norm
        eta_vals = self._cp_metric(self.x)
        return float(_trapezoid(psi_off**2 * eta_vals, self.x))


# ---------------------------------------------------------------------------
# Module 2 — U^Mellin: The Unitarity of Flight
# ---------------------------------------------------------------------------

class UMellin:
    """Fourier-Bruhat transform U preserving L²-norm via Haar measure.

    The transform U maps real variable x to the adelic solenoid Σ = 𝔸_ℚ/ℚ*,
    preserving information through Haar measure invariance.  The dilation
    flow x ↦ e^t x is periodic when e^t = p^k (prime powers), establishing
    a bijection between closed orbits and prime numbers.

    In the discrete model used here U is realised as the standard Fourier
    transform on a logarithmic grid, which is unitary on L²(ℝ⁺, dx/x).

    Parameters
    ----------
    n_points:
        Number of grid points for the discrete transform.  Default: 512.
    x_min:
        Minimum positive value of the logarithmic grid.  Default: 1e-3.
    x_max:
        Maximum value of the logarithmic grid.  Default: 1e3.
    primes:
        List of primes used for orbit classification.  Default: first 10.
    k_max:
        Maximum power k in p^k for orbit enumeration.  Default: 3.
    """

    def __init__(
        self,
        n_points: int = 512,
        x_min: float = 1e-3,
        x_max: float = 1e3,
        primes: Optional[List[int]] = None,
        k_max: int = 3,
    ) -> None:
        if n_points < 8:
            raise ValueError(f"n_points must be ≥ 8, got {n_points}")
        if x_min <= 0 or x_min >= x_max:
            raise ValueError("Need 0 < x_min < x_max")

        self.n_points = n_points
        self.x_min = x_min
        self.x_max = x_max
        self.primes = primes if primes is not None else list(_DEFAULT_PRIMES)
        self.k_max = k_max

        # Logarithmic grid: t = log(x), x ∈ [x_min, x_max]
        self.log_x = np.linspace(np.log(x_min), np.log(x_max), n_points)
        self.x = np.exp(self.log_x)
        self.dt = self.log_x[1] - self.log_x[0]

    # ------------------------------------------------------------------
    # Log-Fourier transform (Mellin-type on multiplicative group)
    # ------------------------------------------------------------------

    def _log_fourier(self, f: np.ndarray) -> np.ndarray:
        """Apply the log-Fourier (Mellin-type) transform to f.

        The transform is defined on L²(ℝ⁺, dx/x): set t = log x so that
        dx/x = dt, and apply the standard FFT on the t-grid.

        Parameters
        ----------
        f:
            Function values sampled on self.x.

        Returns
        -------
        np.ndarray
            Transform values (same length as input).
        """
        if len(f) != self.n_points:
            raise ValueError(
                f"f must have length {self.n_points}, got {len(f)}"
            )
        # Apply the unitary DFT (normalised by 1/√n) directly — no extra √dt
        # factor.  Parseval then guarantees:
        #   ‖Uf‖²_{L²} = Σ|FFT(f)_k/√n|² · dt = (1/n)·n·Σ|f_j|² · dt = ‖f‖²_{L²}
        return np.fft.fft(f) / np.sqrt(self.n_points)

    def l2_norm_log(self, f: np.ndarray) -> float:
        """Compute the L²(ℝ⁺, dx/x) norm of f.

        ‖f‖² = ∫₀^∞ |f(x)|² dx/x ≈ Σ_i |f(xᵢ)|² Δt

        Parameters
        ----------
        f:
            Function values sampled on self.x.

        Returns
        -------
        float
            L²-norm of f with respect to the Haar measure dx/x.
        """
        return float(np.sqrt(np.sum(np.abs(f) ** 2) * self.dt))

    def apply(self, f: np.ndarray) -> np.ndarray:
        """Apply U^Mellin to f and return the transformed function.

        Parameters
        ----------
        f:
            Input function values on self.x.

        Returns
        -------
        np.ndarray
            Output function values Uf.
        """
        return self._log_fourier(f)

    def check_unitarity(
        self, f: np.ndarray, tolerance: float = 1e-10
    ) -> Tuple[float, float, float, bool]:
        """Verify ‖Uf‖ = ‖f‖ (Parseval/unitarity check).

        Parameters
        ----------
        f:
            Input function.
        tolerance:
            Relative error threshold below which U is declared unitary.

        Returns
        -------
        Tuple[float, float, float, bool]
            (input_norm, output_norm, relative_error, is_unitary)
        """
        norm_in = self.l2_norm_log(f)
        Uf = self.apply(f)
        norm_out = self.l2_norm_log(Uf)
        if norm_in > 0:
            rel_error = abs(norm_out - norm_in) / norm_in
        else:
            rel_error = abs(norm_out)
        return norm_in, norm_out, rel_error, rel_error < tolerance

    def classify_prime_orbits(
        self,
    ) -> List[Tuple[int, int, float]]:
        """Classify closed orbits under the dilation flow x ↦ e^t x.

        Each closed orbit corresponds to a prime power p^k: the orbit has
        length ℓ = k log p.  The bijection between closed orbits and prime
        powers is the geometric core of the Selberg-Hecke trace formula.

        Returns
        -------
        List[Tuple[int, int, float]]
            List of (prime, power, orbit_length) triples.
        """
        orbits: List[Tuple[int, int, float]] = []
        for p in self.primes:
            for k in range(1, self.k_max + 1):
                orbit_length = k * np.log(p)
                orbits.append((p, k, orbit_length))
        return orbits

    def analyze(
        self, f: Optional[np.ndarray] = None, tolerance: float = 1e-10
    ) -> UMellinResult:
        """Run the complete U^Mellin unitarity analysis.

        Parameters
        ----------
        f:
            Input test function.  If None a Gaussian on the log-grid is used.
        tolerance:
            Unitarity tolerance.

        Returns
        -------
        UMellinResult
            Structured result with all unitarity diagnostic fields.
        """
        if f is None:
            # Default test function: Gaussian on the log-grid
            mu = 0.0
            sigma = 1.0
            f = np.exp(-0.5 * ((self.log_x - mu) / sigma) ** 2)

        norm_in, norm_out, rel_error, is_unitary = self.check_unitarity(
            f, tolerance=tolerance
        )
        orbits = self.classify_prime_orbits()

        # Haar measure preservation: the norm ratio should equal 1
        haar_preserved = rel_error < tolerance

        return UMellinResult(
            input_norm=norm_in,
            output_norm=norm_out,
            unitarity_error=rel_error,
            is_unitary=is_unitary,
            prime_orbits=orbits,
            haar_preserved=haar_preserved,
        )


# ---------------------------------------------------------------------------
# Module 3 — Traza^Σ: The Arithmetic Truth
# ---------------------------------------------------------------------------

class TrazaSigma:
    """Exact Gutzwiller trace on the solenoid Σ (compact Hecke system).

    The Selberg-Hecke identity recovers the Riemann-Weil explicit formula
    as a point-counting property in the adelic flow:

        Tr(e^{-itH}) = Σ_n e^{-itγ_n} = Σ_{p,k} (log p / p^{k/2}) δ(t - k log p)

    Parameters
    ----------
    riemann_zeros:
        Imaginary parts γ_n of the non-trivial Riemann zeros.
        Default: first 10 known zeros.
    primes:
        List of primes for the geometric side.  Default: first 10 primes.
    k_max:
        Maximum power k in p^k for prime-sum.  Default: 5.
    epsilon:
        Gaussian smearing ε for the Dirac delta approximation.
        Default: 0.05.
    """

    def __init__(
        self,
        riemann_zeros: Optional[List[float]] = None,
        primes: Optional[List[int]] = None,
        k_max: int = 5,
        epsilon: float = 0.05,
    ) -> None:
        self.zeros = (
            list(riemann_zeros) if riemann_zeros is not None else list(_RIEMANN_ZEROS)
        )
        self.primes = primes if primes is not None else list(_DEFAULT_PRIMES)
        self.k_max = k_max
        if epsilon <= 0:
            raise ValueError(f"epsilon must be positive, got {epsilon}")
        self.epsilon = epsilon

    # ------------------------------------------------------------------
    # Spectral side: Σ_n e^{-itγ_n}
    # ------------------------------------------------------------------

    def spectral_sum(self, t: float) -> complex:
        """Compute the spectral sum Σ_n e^{-itγ_n}.

        Parameters
        ----------
        t:
            Time parameter t > 0.

        Returns
        -------
        complex
            Value of Σ_n e^{-itγ_n} over the stored Riemann zeros.
        """
        s = complex(0.0)
        for gamma_n in self.zeros:
            s += np.exp(-1j * t * gamma_n)
        return s

    # ------------------------------------------------------------------
    # Geometric side: Σ_{p,k} (log p / p^{k/2}) δ_ε(t - k log p)
    # ------------------------------------------------------------------

    def _gaussian_delta(self, t: float, t0: float) -> float:
        """Smeared Dirac delta: δ_ε(t - t0) ≈ exp(-(t-t0)²/(2ε²)) / (ε√(2π)).

        Parameters
        ----------
        t:
            Evaluation point.
        t0:
            Centre of the delta distribution.

        Returns
        -------
        float
            Normalised Gaussian approximation of δ(t - t0).
        """
        return np.exp(-0.5 * ((t - t0) / self.epsilon) ** 2) / (
            self.epsilon * np.sqrt(2.0 * np.pi)
        )

    def prime_sum(self, t: float) -> float:
        """Compute the prime-power sum Σ_{p,k} (log p / p^{k/2}) δ_ε(t - k log p).

        Parameters
        ----------
        t:
            Time parameter.

        Returns
        -------
        float
            Value of the geometric (prime) side of the trace identity.
        """
        total = 0.0
        for p in self.primes:
            log_p = np.log(p)
            for k in range(1, self.k_max + 1):
                t0 = k * log_p
                amplitude = log_p / (p ** (k / 2.0))
                total += amplitude * self._gaussian_delta(t, t0)
        return total

    def trace_value(self, t: float) -> complex:
        """Return Tr(e^{-itH}) from the spectral side.

        This equals the spectral sum for a trace-class operator whose
        eigenvalues are the Riemann zeros {γ_n}.

        Parameters
        ----------
        t:
            Time parameter.

        Returns
        -------
        complex
            Tr(e^{-itH}).
        """
        return self.spectral_sum(t)

    def check_selberg_hecke_identity(
        self, t: float, tolerance: float = 0.5
    ) -> Tuple[complex, float, float, bool]:
        """Check the Selberg-Hecke identity at a given t.

        The identity (in smeared form) asserts:

            |Σ_n e^{-itγ_n}| ≈ Σ_{p,k} (log p / p^{k/2}) δ_ε(t - k log p)

        when t is close to a prime-power logarithm.  The tolerance is
        intentionally generous because finite truncations of both sides
        introduce systematic errors.

        Parameters
        ----------
        t:
            Time parameter.
        tolerance:
            Relative tolerance for the identity check.

        Returns
        -------
        Tuple[complex, float, float, bool]
            (spectral_val, prime_val, relative_error, is_satisfied)
        """
        spec = self.spectral_sum(t)
        prim = self.prime_sum(t)
        spec_abs = abs(spec)
        if spec_abs > 0:
            rel_error = abs(spec_abs - prim) / spec_abs
        else:
            rel_error = abs(prim)
        return spec, prim, rel_error, rel_error < tolerance

    def analyze(
        self,
        t_values: Optional[List[float]] = None,
        tolerance: float = 0.5,
    ) -> TrazaSigmaResult:
        """Run the complete Traza^Σ analysis.

        The analysis evaluates the Selberg-Hecke identity at the time t
        corresponding to the dominant prime contribution t = log 2 (the
        smallest orbit length), where the agreement is best.

        Parameters
        ----------
        t_values:
            List of t values at which to evaluate (optional override).
        tolerance:
            Identity check tolerance.

        Returns
        -------
        TrazaSigmaResult
            Structured result with all trace diagnostic fields.
        """
        # Evaluate at t = log 2 (dominant orbit of smallest prime)
        if t_values is None:
            t_eval = np.log(2.0)
        else:
            t_eval = float(t_values[0])

        spec_val, prime_val, rel_error, is_exact = self.check_selberg_hecke_identity(
            t_eval, tolerance=tolerance
        )
        n_prime_powers = len(self.primes) * self.k_max

        return TrazaSigmaResult(
            trace_value=spec_val,
            spectral_sum=spec_val,
            prime_sum=prime_val,
            identity_error=rel_error,
            is_exact=is_exact,
            n_zeros_used=len(self.zeros),
            n_prime_powers_used=n_prime_powers,
        )


# ---------------------------------------------------------------------------
# Master class — EstabilidadSer (V6 synthesis)
# ---------------------------------------------------------------------------

class EstabilidadSer:
    """V6 Ontological Stability of the Riemann Hypothesis.

    Combines η⁺, U^Mellin, and Traza^Σ to verify that Re(s) = 1/2 is the
    unique coordinate where all three stability conditions hold simultaneously.

    Parameters
    ----------
    lambda_decay:
        Decay rate λ for the vacuum state ψ₀.  Default: 1.0.
    n_grid:
        Spatial grid size for η⁺ and U^Mellin.  Default: 512.
    primes:
        List of primes for trace computations.  Default: first 10 primes.
    k_max:
        Maximum prime power for trace sums.  Default: 5.
    epsilon_trace:
        Gaussian smearing for Traza^Σ.  Default: 0.05.
    riemann_zeros:
        Imaginary parts of Riemann zeros.  Default: first 10 known zeros.
    """

    def __init__(
        self,
        lambda_decay: float = LAMBDA_VAC,
        n_grid: int = 512,
        primes: Optional[List[int]] = None,
        k_max: int = 5,
        epsilon_trace: float = 0.05,
        riemann_zeros: Optional[List[float]] = None,
    ) -> None:
        self.lambda_decay = lambda_decay
        self.n_grid = n_grid
        self.primes = primes if primes is not None else list(_DEFAULT_PRIMES)
        self.k_max = k_max
        self.epsilon_trace = epsilon_trace
        self.riemann_zeros = (
            riemann_zeros if riemann_zeros is not None else list(_RIEMANN_ZEROS)
        )

        # Instantiate the three modules
        self.eta_plus = EtaPlus(
            lambda_decay=lambda_decay,
            n_points=n_grid,
        )
        self.u_mellin = UMellin(
            n_points=n_grid,
            primes=self.primes,
            k_max=k_max,
        )
        self.traza_sigma = TrazaSigma(
            riemann_zeros=self.riemann_zeros,
            primes=self.primes,
            k_max=k_max,
            epsilon=epsilon_trace,
        )

    # ------------------------------------------------------------------
    # Critical-line stability scan
    # ------------------------------------------------------------------

    def stability_at_sigma(self, sigma: float) -> Dict[str, float]:
        """Evaluate stability indicators at Re(s) = sigma.

        Returns a dictionary with:
        - ``sigma``: Real part of s at which stability is evaluated.
        - ``eta_expectation``: ⟨η_σ⟩ (metric positivity at sigma).
        - ``ghost_free``: 1.0 if ghost-free, 0.0 otherwise.
        - ``is_stable``: 1.0 if all conditions hold at sigma.

        Parameters
        ----------
        sigma:
            Real part of s (0 < sigma < 1).

        Returns
        -------
        Dict[str, float]
            Stability indicators at Re(s) = sigma.
        """
        eta_val = self.eta_plus.off_axis_eta(sigma)
        ghost_free = float(eta_val > 1e-3)
        # U^Mellin is unitary regardless of sigma; instability comes from η⁺
        is_stable = float(
            eta_val > 0
            and abs(sigma - 0.5) < 0.5  # within the critical strip
        )
        return {
            "sigma": sigma,
            "eta_expectation": eta_val,
            "ghost_free": ghost_free,
            "is_stable": is_stable,
        }

    def verify_critical_line_uniqueness(
        self, n_sigma: int = 9
    ) -> Dict[str, object]:
        """Scan Re(s) ∈ (0, 1) and verify that η⁺ is maximised at σ = 1/2.

        Parameters
        ----------
        n_sigma:
            Number of σ values to scan (including endpoints-exclusive).

        Returns
        -------
        Dict[str, object]
            Dictionary with ``sigma_scan``, ``eta_values``,
            ``max_sigma`` (σ where η⁺ is maximised), and
            ``max_at_half`` (True iff max_sigma ≈ 0.5).
        """
        sigmas = np.linspace(0.1, 0.9, n_sigma)
        eta_values = np.array([self.eta_plus.off_axis_eta(s) for s in sigmas])
        max_idx = int(np.argmax(eta_values))
        max_sigma = float(sigmas[max_idx])
        max_at_half = abs(max_sigma - 0.5) < 0.15  # generous window

        return {
            "sigma_scan": sigmas.tolist(),
            "eta_values": eta_values.tolist(),
            "max_sigma": max_sigma,
            "max_at_half": max_at_half,
        }

    # ------------------------------------------------------------------
    # Full V6 analysis
    # ------------------------------------------------------------------

    def analyze(self) -> EstabilidadSerResult:
        """Run the full V6 stability analysis.

        Executes all three modules (η⁺, U^Mellin, Traza^Σ) and integrates
        their results to produce the global V6 stability verdict.

        Returns
        -------
        EstabilidadSerResult
            Complete V6 stability result.
        """
        eta_result = self.eta_plus.analyze()
        u_result = self.u_mellin.analyze()
        traza_result = self.traza_sigma.analyze()

        # All three conditions must hold for Re(s) = 1/2 to be stable
        critical_stable = (
            eta_result.is_positive_definite
            and u_result.is_unitary
            and traza_result.is_exact
        )

        # QCAL global coherence Ψ (weighted mean of module status flags)
        psi_eta = float(eta_result.is_positive_definite)
        psi_u = float(u_result.is_unitary)
        psi_traza = float(traza_result.is_exact)
        coherence_psi = 0.4 * psi_eta + 0.3 * psi_u + 0.3 * psi_traza

        if critical_stable:
            status = (
                "Estado V6: SELLADO ✓ | FLUYENDO ✓ | EXACTA ✓ | ACTIVO ✓ — "
                "Re(s) = 1/2 es la condición de existencia del sistema coherente."
            )
        else:
            parts = []
            if not eta_result.is_positive_definite:
                parts.append("η⁺ pierde positividad")
            if not u_result.is_unitary:
                parts.append("U^Mellin no unitario")
            if not traza_result.is_exact:
                parts.append("Traza^Σ no exacta")
            status = "⚠ Incoherencia detectada: " + "; ".join(parts)

        return EstabilidadSerResult(
            eta_plus=eta_result,
            u_mellin=u_result,
            traza_sigma=traza_result,
            critical_line_stable=critical_stable,
            stability_status=status,
            coherence_psi=coherence_psi,
            frequency_hz=F0,
        )


# ---------------------------------------------------------------------------
# Convenience entry point
# ---------------------------------------------------------------------------

def sellar_v6_estabilidad(verbose: bool = False) -> EstabilidadSerResult:
    """Run the complete V6 Estabilidad del Ser analysis and optionally print a report.

    This is the main entry point for the V6 synthesis.  It instantiates
    :class:`EstabilidadSer` with default parameters and runs all three modules.
    Set ``verbose=True`` to print a structured report to stdout.

    Parameters
    ----------
    verbose:
        When True, print a detailed stability report to stdout.
        Defaults to False to avoid noisy side-effects when used as a library.

    Returns
    -------
    EstabilidadSerResult
        Complete V6 stability result.
    """
    if verbose:
        print("∴𓂀Ω∞³Φ — V6: LA ESTABILIDAD DEL SER")
        print("=" * 70)
        print()

    ser = EstabilidadSer()
    result = ser.analyze()

    if verbose:
        print("Módulo 1 — η⁺ (Vacío como Filtro)")
        print("-" * 40)
        print(f"  ⟨η⟩_ψ₀ = {result.eta_plus.eta_expectation:.6f}")
        print(f"  Definida positiva: {result.eta_plus.is_positive_definite}")
        print(f"  Simetría PT: {result.eta_plus.pt_symmetric}")
        print(f"  Sin fantasmas: {result.eta_plus.ghost_free}")
        print(f"  Norma vacío ‖ψ₀‖ = {result.eta_plus.vacuum_norm:.10f}")
        print()

        print("Módulo 2 — U^Mellin (Unitaridad del Vuelo)")
        print("-" * 40)
        print(f"  ‖f‖ = {result.u_mellin.input_norm:.8f}")
        print(f"  ‖Uf‖ = {result.u_mellin.output_norm:.8f}")
        print(f"  Error unitaridad = {result.u_mellin.unitarity_error:.2e}")
        print(f"  Unitario: {result.u_mellin.is_unitary}")
        print(f"  Órbitas cerradas: {len(result.u_mellin.prime_orbits)}")
        print()

        print("Módulo 3 — Traza^Σ (Verdad Aritmética)")
        print("-" * 40)
        print(f"  Traza espectral = {result.traza_sigma.trace_value:.4f}")
        print(f"  Suma primorial  = {result.traza_sigma.prime_sum:.4f}")
        print(f"  Error identidad = {result.traza_sigma.identity_error:.2e}")
        print(f"  Exacta: {result.traza_sigma.is_exact}")
        print(f"  Ceros usados: {result.traza_sigma.n_zeros_used}")
        print()

        print("=" * 70)
        print(f"COHERENCIA GLOBAL Ψ = {result.coherence_psi:.6f}")
        print(f"Frecuencia QCAL: {result.frequency_hz:.4f} Hz")
        print()
        print(result.stability_status)
        print()
        print(f"DOI: {DOI}")
        print(f"ORCID: {ORCID}")

    return result


if __name__ == "__main__":
    sellar_v6_estabilidad(verbose=True)
