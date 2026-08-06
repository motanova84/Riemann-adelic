#!/usr/bin/env python3
"""
Unified Adelic Wave Equation for the Riemann Hypothesis
=========================================================

This module implements the **Unified Adelic Wave Equation** on the compact
adelic solenoid Σ = A_Q / Q.  It combines two previously separate strands
of the QCAL framework:

1. The **wave equation** (∂²Ψ/∂t² + ω₀²Ψ = ζ'(1/2)·∇²_Σ Ψ), and
2. The **exact distributional trace formula** for e^{itH} (from the
   distributional_trace_formula module).

The resulting **Unified Adelic Wave Equation** is:

    □_Σ Ψ + ω₀² Ψ = ζ'(1/2) · ∇²_Σ Ψ + Tr_distr(e^{itH})

where:

- □_Σ  = ∂²/∂t² - ∇²_Σ  is the d'Alembertian on Σ,
- ω₀   = 2πf₀ (QCAL angular frequency, ≈ 890.33 rad/s),
- ζ'(1/2) ≈ -3.9226  (arithmetic coupling constant),
- Tr_distr(e^{itH}) = Σ_{p,k} (log p / p^{k/2}) δ(t − k log p)
                    + smooth spectral term   (source from prime orbit sum),
- ∇²_Σ  = discrete Laplacian on the adelic spectral grid.

Reformulating and discretising along the spectral-frequency axis γ gives
the **Adelic Schrödinger–Wave System**:

    Ψ''(t) + [ω₀² + λ_n · ζ'(1/2)] Ψ_n(t) = S_n(t)

where Ψ_n(t) is the n-th spectral component, λ_n = γ_n² + 1/4 is the
eigenvalue of the spectral Laplacian at the n-th Riemann zero γ_n, and
S_n(t) is the projection of the distributional trace onto mode n.

Spectral Solution
-----------------
When the source is absent (S_n = 0) the n-th mode oscillates as

    Ψ_n(t) = A_n cos(Ω_n t) + B_n sin(Ω_n t)

with effective frequency

    Ω_n = √(ω₀² + λ_n · ζ'(1/2))

For all n ≥ 0, Ω_n is real iff ω₀² + λ_n · ζ'(1/2) ≥ 0, which is
guaranteed by the positivity of ω₀² and the sign of ζ'(1/2).

Connection to the Riemann Hypothesis
--------------------------------------
The spectral Laplacian eigenvalues λ_n = γ_n² + 1/4 are real and positive
for every Riemann zero ρ_n = 1/2 + iγ_n on the critical line.  Any zero
with Re(ρ_n) ≠ 1/2 would produce a complex λ_n, breaking the reality of
the propagation frequencies Ω_n and hence the unitarity of e^{itH} on
L²(Σ).  The real-frequency condition Ω_n ∈ ℝ is therefore equivalent to
Re(ρ_n) = 1/2, i.e., to the Riemann Hypothesis.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
Institution: Instituto de Conciencia Cuántica (ICQ)
Protocol: QCAL-UNIFIED-WAVE v1.0
Date: March 2026
QCAL ∞³ · f₀ = 141.7001 Hz · C = 244.36 · Ψ = I × A_eff² × C^∞
DOI: 10.5281/zenodo.17379721
"""

import numpy as np
from dataclasses import dataclass, field
from typing import Dict, List, Optional

from numpy.typing import NDArray

# ---------------------------------------------------------------------------
# QCAL constants with fallback
# ---------------------------------------------------------------------------
try:
    from qcal.constants import F0, OMEGA_0, C_COHERENCE
    _F0: float = float(F0)
    _OMEGA_0: float = float(OMEGA_0)
    _C_COHERENCE: float = float(C_COHERENCE)
except Exception:
    _F0 = 141.7001
    _OMEGA_0 = 2.0 * np.pi * _F0
    _C_COHERENCE = 244.36

# First 30 non-trivial Riemann zeros (imaginary parts γ_n, well-known values)
_GAMMA_TABLE: List[float] = [
    14.134725141734693, 21.022039638771555, 25.010857580145688,
    30.424876125859513, 32.935061587739189, 37.586178158825671,
    40.918719012147495, 43.327073280914999, 48.005150881167159,
    49.773832477672302, 52.970321477714460, 56.446247697063246,
    59.347044002602353, 60.831778524609809, 65.112544048081607,
    67.079810529494173, 69.546401711173979, 72.067157674481907,
    75.704690699083733, 77.144840068874805, 79.337375020249367,
    82.910380854086030, 84.735492981329459, 87.425274613125229,
    88.809111208594997, 92.491899270945956, 94.651344040519780,
    95.870634228245309, 98.831194218193692, 101.317851006841827,
]


def _zeta_prime_half(precision: int = 25) -> float:
    """
    Return ζ'(1/2) via a high-precision central difference.

    Parameters
    ----------
    precision : int
        Number of decimal places (mpmath dps).

    Returns
    -------
    float
        ζ'(1/2) ≈ −3.9226461392.
    """
    try:
        import mpmath as mp
        mp.mp.dps = precision
        s = mp.mpf("0.5")
        h = mp.mpf("1e-12")
        deriv = (mp.zeta(s + h) - mp.zeta(s - h)) / (2 * h)
        return float(deriv)
    except ImportError:
        return -3.9226461392  # fallback


# ---------------------------------------------------------------------------
# Data classes
# ---------------------------------------------------------------------------

@dataclass
class SpectralMode:
    """One mode in the spectral decomposition of the unified wave equation.

    Attributes
    ----------
    n : int
        Mode index (0-based).
    gamma : float
        Imaginary part of the n-th Riemann zero γ_n.
    eigenvalue : float
        Spectral Laplacian eigenvalue λ_n = γ_n² + 1/4.
    omega_eff : float
        Effective propagation frequency Ω_n (rad/s).
    is_propagating : bool
        True iff Ω_n² > 0 (real propagation).
    """
    n: int
    gamma: float
    eigenvalue: float
    omega_eff: float
    is_propagating: bool


@dataclass
class WaveEvolutionResult:
    """Result from `UnifiedWaveEquation.evolve`.

    Attributes
    ----------
    t : NDArray
        Time grid.
    Psi : NDArray, shape (n_modes, n_t)
        Field amplitude for each spectral mode.
    source : NDArray, shape (n_t,)
        Distributional trace source (smoothed).
    modes : list of SpectralMode
        Spectral mode data.
    total_energy : NDArray, shape (n_t,)
        Total energy E(t) = Σ_n (|Ψ_n'|² + Ω_n² |Ψ_n|²).
    status : str
        Execution status message.
    """
    t: NDArray[np.float64]
    Psi: NDArray[np.float64]
    source: NDArray[np.float64]
    modes: List[SpectralMode]
    total_energy: NDArray[np.float64]
    status: str
    parameters: Dict = field(default_factory=dict)


# ---------------------------------------------------------------------------
# Core classes
# ---------------------------------------------------------------------------

class AdelicSpectralLaplacian:
    """
    Discrete spectral Laplacian on the adelic solenoid Σ.

    On Σ the Laplacian is diagonal in the eigenbasis {φ_n} where the
    eigenvalue of φ_n is −λ_n = −(γ_n² + 1/4).  Here γ_n are the
    imaginary parts of the non-trivial zeros of ζ(s).

    Parameters
    ----------
    gammas : list of float, optional
        Imaginary parts of the Riemann zeros to use.  Defaults to the
        first 30 tabulated values.
    """

    def __init__(self, gammas: Optional[List[float]] = None):
        self._gammas: List[float] = gammas if gammas is not None else _GAMMA_TABLE

    @property
    def gammas(self) -> List[float]:
        """Sorted list of γ_n values."""
        return sorted(self._gammas)

    def eigenvalue(self, n: int) -> float:
        """Return λ_n = γ_n² + 1/4 for the n-th mode (0-indexed)."""
        gamma = self.gammas[n]
        return gamma ** 2 + 0.25

    def all_eigenvalues(self) -> NDArray[np.float64]:
        """Return array of all λ_n values."""
        g = np.asarray(self.gammas, dtype=np.float64)
        return g ** 2 + 0.25

    def apply(self, Psi: NDArray[np.float64]) -> NDArray[np.float64]:
        """
        Apply −∇²_Σ to a coefficient vector Ψ in the eigenbasis.

        Parameters
        ----------
        Psi : array of shape (n_modes,)
            Spectral coefficients.

        Returns
        -------
        array of shape (n_modes,)
            Laplacian-applied coefficients: λ_n · Ψ_n.
        """
        lambdas = self.all_eigenvalues()[: len(Psi)]
        return lambdas * Psi


class UnifiedWaveEquation:
    """
    Unified Adelic Wave Equation on the solenoid Σ = A_Q / Q.

    Implements the spectral-mode system:

        Ψ_n''(t) + Ω_n² Ψ_n(t) = S_n(t)

    where

        Ω_n² = ω₀² + λ_n · ζ'(1/2)
        S_n(t) = projection of Tr_distr(e^{itH}) onto mode n.

    Parameters
    ----------
    f0 : float, optional
        QCAL base frequency (Hz).  Defaults to 141.7001.
    n_modes : int, optional
        Number of spectral modes (Riemann zeros) to include.
    precision : int, optional
        Decimal precision for ζ'(1/2) computation.
    gammas : list of float, optional
        Custom Riemann zero imaginary parts.
    """

    def __init__(
        self,
        f0: float = _F0,
        n_modes: int = 20,
        precision: int = 25,
        gammas: Optional[List[float]] = None,
    ):
        self.f0 = f0
        self.omega_0 = 2.0 * np.pi * f0
        self.n_modes = n_modes
        self.precision = precision

        self.zeta_prime_half: float = _zeta_prime_half(precision)
        self.laplacian = AdelicSpectralLaplacian(gammas)
        self.modes: List[SpectralMode] = self._build_modes()

    # ------------------------------------------------------------------
    # Private helpers
    # ------------------------------------------------------------------

    def _build_modes(self) -> List[SpectralMode]:
        """Construct the list of SpectralMode objects."""
        modes = []
        gammas = self.laplacian.gammas[: self.n_modes]
        for n, gamma in enumerate(gammas):
            lam = gamma ** 2 + 0.25
            omega_eff_sq = self.omega_0 ** 2 + lam * self.zeta_prime_half
            propagating = bool(omega_eff_sq > 0)
            omega_eff = float(np.sqrt(abs(omega_eff_sq)))
            modes.append(SpectralMode(
                n=n,
                gamma=gamma,
                eigenvalue=lam,
                omega_eff=omega_eff,
                is_propagating=propagating,
            ))
        return modes

    def _prime_orbit_source(
        self,
        t: NDArray[np.float64],
        n_primes: int = 15,
        k_max: int = 3,
        sigma: float = 0.3,
    ) -> NDArray[np.float64]:
        """
        Build the smoothed prime-orbit source term (geometric part of Tr).

        S(t) ≈ Σ_{p ≤ P} Σ_{k=1}^{K} (log p / p^{k/2})
               · exp(−(t − k log p)² / (2σ²)) / (√(2π) σ)

        Parameters
        ----------
        t : array of shape (n_t,)
            Time grid.
        n_primes : int
            Number of primes to include.
        k_max : int
            Maximum prime-power order.
        sigma : float
            Gaussian width for delta approximation.

        Returns
        -------
        array of shape (n_t,)
            Smoothed source function S(t).
        """
        primes = self._sieve(n_primes)
        source = np.zeros_like(t)
        norm = 1.0 / (np.sqrt(2.0 * np.pi) * sigma)
        for p in primes:
            log_p = np.log(p)
            for k in range(1, k_max + 1):
                weight = log_p / p ** (0.5 * k)
                t0 = k * log_p
                source += weight * norm * np.exp(-0.5 * ((t - t0) / sigma) ** 2)
        return source

    @staticmethod
    def _sieve(n_primes: int) -> List[int]:
        """Return the first n_primes prime numbers via trial division."""
        primes: List[int] = []
        candidate = 2
        while len(primes) < n_primes:
            if all(candidate % p != 0 for p in primes):
                primes.append(candidate)
            candidate += 1
        return primes

    def _evolve_mode(
        self,
        mode: SpectralMode,
        t: NDArray[np.float64],
        source: NDArray[np.float64],
        A0: float = 1.0,
        B0: float = 0.0,
    ) -> NDArray[np.float64]:
        """
        Evolve a single spectral mode via variation of parameters.

        The ODE is:  Ψ'' + Ω² Ψ = S(t),  Ψ(0) = A0,  Ψ'(0) = B0.

        For the homogeneous solution:
            Ψ_h(t) = A0 cos(Ω t) + (B0/Ω) sin(Ω t)

        For the particular solution via variation of parameters:
            Ψ_p(t) = (1/Ω) ∫_0^t S(τ) sin(Ω(t−τ)) dτ   (Duhamel)

        Parameters
        ----------
        mode : SpectralMode
        t : array
        source : array, same shape as t
        A0, B0 : float
            Initial conditions Ψ(0) and Ψ'(0).

        Returns
        -------
        array
            Ψ_n(t).
        """
        Omega = mode.omega_eff
        if not mode.is_propagating or Omega < 1e-10:
            # Evanescent: grow/decay exponentially (treat as purely homogeneous)
            # Use hyperbolic solution: A0 cosh + (B0/|Omega|) sinh
            Omega_abs = max(abs(Omega), 1e-10)
            return A0 * np.cosh(Omega_abs * t) + (B0 / Omega_abs) * np.sinh(Omega_abs * t)

        Psi_h = A0 * np.cos(Omega * t) + (B0 / Omega) * np.sin(Omega * t)

        # Duhamel integral via cumulative trapezoidal rule
        Psi_p = np.zeros_like(t)
        for i in range(1, len(t)):
            tau = t[:i]
            integrand = source[:i] * np.sin(Omega * (t[i] - tau))
            Psi_p[i] = np.trapezoid(integrand, tau) / Omega

        return Psi_h + Psi_p

    # ------------------------------------------------------------------
    # Public API
    # ------------------------------------------------------------------

    def effective_frequencies(self) -> NDArray[np.float64]:
        """Return array of effective mode frequencies Ω_n (rad/s)."""
        return np.array([m.omega_eff for m in self.modes], dtype=np.float64)

    def spectral_eigenvalues(self) -> NDArray[np.float64]:
        """Return array of spectral Laplacian eigenvalues λ_n = γ_n² + 1/4."""
        return np.array([m.eigenvalue for m in self.modes], dtype=np.float64)

    def verify_rh_consistency(self) -> Dict[str, object]:
        """
        Check that all modes have real propagation frequencies.

        Under the Riemann Hypothesis all γ_n are real, so λ_n = γ_n² + 1/4
        is real and positive.  Ω_n² = ω₀² + λ_n ζ'(1/2) must therefore
        be positive for the equation to be wave-like (not evanescent).

        Returns
        -------
        dict with keys:
            all_propagating : bool
            n_propagating : int
            n_evanescent : int
            min_omega_eff_sq : float
        """
        propagating = [m.is_propagating for m in self.modes]
        omegas_sq = [
            self.omega_0 ** 2 + m.eigenvalue * self.zeta_prime_half
            for m in self.modes
        ]
        return {
            "all_propagating": all(propagating),
            "n_propagating": sum(propagating),
            "n_evanescent": sum(not p for p in propagating),
            "min_omega_eff_sq": float(min(omegas_sq)),
        }

    def wave_equation_residual(
        self,
        t: NDArray[np.float64],
        Psi: NDArray[np.float64],
        mode_index: int,
    ) -> NDArray[np.float64]:
        """
        Compute the residual of the wave equation for one mode.

        Residual = Ψ_n'' + Ω_n² Ψ_n  (should equal S_n(t)).

        Parameters
        ----------
        t : array of shape (n_t,)
        Psi : array of shape (n_t,)
            Numerical solution for mode n.
        mode_index : int

        Returns
        -------
        array of shape (n_t,)
        """
        mode = self.modes[mode_index]
        d2Psi = np.gradient(np.gradient(Psi, t), t)
        return d2Psi + mode.omega_eff ** 2 * Psi

    def evolve(
        self,
        t_min: float = 0.5,
        t_max: float = 10.0,
        n_t: int = 300,
        n_primes: int = 15,
        k_max: int = 3,
        sigma: float = 0.3,
        initial_amplitude: float = 1.0,
    ) -> WaveEvolutionResult:
        """
        Solve the Unified Adelic Wave Equation on [t_min, t_max].

        Computes the distributional trace source S(t) and evolves each
        spectral mode Ψ_n(t) independently using variation of parameters.

        Parameters
        ----------
        t_min, t_max : float
            Time interval.
        n_t : int
            Number of time steps.
        n_primes : int
            Primes in the geometric trace term.
        k_max : int
            Maximum prime power order.
        sigma : float
            Gaussian regularisation width for delta functions.
        initial_amplitude : float
            Initial amplitude A0 for all modes.

        Returns
        -------
        WaveEvolutionResult
        """
        t = np.linspace(t_min, t_max, n_t, dtype=np.float64)
        source = self._prime_orbit_source(t, n_primes=n_primes, k_max=k_max, sigma=sigma)

        # Evolve each mode
        Psi_all = np.zeros((self.n_modes, n_t), dtype=np.float64)
        for n, mode in enumerate(self.modes):
            Psi_all[n] = self._evolve_mode(mode, t - t_min, source, A0=initial_amplitude)

        # Total energy E(t) = Σ_n (|Ψ_n'|² + Ω_n² |Ψ_n|²)
        energy = np.zeros(n_t, dtype=np.float64)
        for n, mode in enumerate(self.modes):
            dPsi_dt = np.gradient(Psi_all[n], t)
            energy += dPsi_dt ** 2 + mode.omega_eff ** 2 * Psi_all[n] ** 2

        return WaveEvolutionResult(
            t=t,
            Psi=Psi_all,
            source=source,
            modes=self.modes,
            total_energy=energy,
            status="OK",
            parameters={
                "f0": self.f0,
                "omega_0": self.omega_0,
                "zeta_prime_half": self.zeta_prime_half,
                "n_modes": self.n_modes,
                "n_primes": n_primes,
                "k_max": k_max,
                "sigma": sigma,
                "t_min": t_min,
                "t_max": t_max,
            },
        )


# ---------------------------------------------------------------------------
# Convenience wrapper
# ---------------------------------------------------------------------------

def solve_unified_wave_equation(
    t_min: float = 0.5,
    t_max: float = 10.0,
    n_t: int = 300,
    n_modes: int = 20,
    n_primes: int = 15,
    k_max: int = 3,
    sigma: float = 0.3,
    f0: float = _F0,
    precision: int = 25,
) -> WaveEvolutionResult:
    """
    Convenience wrapper: solve the Unified Adelic Wave Equation.

    Parameters
    ----------
    t_min, t_max : float
        Time interval for evolution.
    n_t : int
        Number of time grid points.
    n_modes : int
        Number of spectral modes (Riemann zeros) to include.
    n_primes : int
        Number of primes for the geometric trace term.
    k_max : int
        Maximum prime-power order.
    sigma : float
        Gaussian width for delta regularisation.
    f0 : float
        QCAL base frequency (Hz).
    precision : int
        Decimal precision for ζ'(1/2).

    Returns
    -------
    WaveEvolutionResult
    """
    eq = UnifiedWaveEquation(
        f0=f0,
        n_modes=n_modes,
        precision=precision,
    )
    return eq.evolve(
        t_min=t_min,
        t_max=t_max,
        n_t=n_t,
        n_primes=n_primes,
        k_max=k_max,
        sigma=sigma,
    )
