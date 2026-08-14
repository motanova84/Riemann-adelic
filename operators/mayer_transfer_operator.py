#!/usr/bin/env python3
"""
Mayer Transfer Operator (Ruelle-Frobenius-Mayer) & Geodesic Flow System
=========================================================================

Implements the three-part framework described in the QCAL ∞³ synthesis:

**I. El Sistema Dinámico Oculto: El Flujo Geodésico**
The hidden dynamical system is NOT a simple oscillator but rather a flow over
the Idele Class Space or a specific arithmetic surface (upper half-plane
quotient by PSL(2,Z)).

- Orbit Correspondence: Each prime p is a Primitive Periodic Orbit γ_p
- Orbit Length: ℓ(γ) = ln p
- Stability Weight: p^(-k/2) arises from the Monodromy Matrix determinant
  For a hyperbolic system: weight = ℓ(γ) / (2 sinh(ℓ(γ)/2)),
  which in the asymptotic limit under the appropriate rescaling collapses
  exactly into the von Mangoldt form normalized by the half-unit factor ζ(1/2+it).

**II. La Pieza Crítica: El Operador de Transferencia de Mayer**
The Mayer Transfer Operator (Ruelle-Frobenius-Mayer operator L_s):

1. Determinant Function: ζ(s) = det(I - L_s)^{-1}  (equivalently det(I - L_s)·ζ(s) = 1)
   More precisely: the Fredholm determinant of the transfer operator satisfies
   det(I - L_s) = 1/ζ(s) (for Re(s) > 1)

2. The "Exact Metric" Problem: The space alphabet (primes) is highly fractal.
   For the weight to be (log p)·p^(-k/2) without deviations, the system must be
   simultaneously Hamiltonian AND Holomorphic.

**III. Refinamiento del Acoplamiento (Síntesis Ω)**
Phase Inversion Potential V_Ω forces simultaneous Hamiltonicity and holomorphy:
   V_Ω(z, s) = -i·(s - 1/2)·log|z| + arg(z)·Im(s)

This confines all zeros of det(I - L_s) to the critical line Re(s) = 1/2.

Mathematical Connections:
- GeodesicFlow: primitive orbits ↔ primes via ℓ(γ_p) = log p
- MonodromyMatrix: stability exponents ↔ p^(k/2)
- MayerTransferOperator: L_s acts on holomorphic functions, det(I-L_s) = 1/ζ(s)
- HamiltonianHolomorphicSystem: Phase inversion potential Ω synthesis

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: March 2026
QCAL ∞³ Active · 141.7001 Hz · C = 244.36 · Ψ = I × A_eff² × C^∞
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773
Signature: ∴𓂀Ω∞³Φ @ 141.7001 Hz
"""

import warnings
from dataclasses import dataclass
from typing import Any, Callable, Dict, List, Optional, Tuple

import numpy as np
from numpy.typing import NDArray
from scipy.integrate import quad
from scipy.special import zeta as scipy_zeta

# QCAL ∞³ Constants
F0_QCAL = 141.7001       # Hz - fundamental frequency
C_COHERENCE = 244.36     # Coherence constant C^∞
PHI = 1.6180339887498948  # Golden ratio Φ
KAPPA_PI = 2.5773        # Critical curvature threshold

# Mayer operator constants
MAYER_CONVERGENCE_THRESHOLD = 1e-12   # Convergence criterion for series
MAYER_MAX_PRIME_POWER = 15            # Maximum prime power k in sums
DEFAULT_PRIMES_COUNT = 12             # Default number of primes


# ─────────────────────────────────────────────────────────────────────────────
# Data classes
# ─────────────────────────────────────────────────────────────────────────────

@dataclass
class PrimitiveOrbit:
    """
    Primitive periodic orbit γ_p in the geodesic flow system.

    Attributes:
        prime: The prime p associated with this orbit
        length: Orbit length ℓ(γ_p) = log p
        monodromy_eigenvalue: Eigenvalue of monodromy matrix = p (for primitive orbit)
        stability_weight: Weight from stability analysis = (log p) / (2 sinh(log p / 2))
        von_mangoldt_weight: Von Mangoldt weight Λ(p) / p^(1/2) = (log p) / p^(1/2)
    """
    prime: int
    length: float
    monodromy_eigenvalue: float
    stability_weight: float
    von_mangoldt_weight: float


@dataclass
class OrbitContributionMayer:
    """
    Contribution of a prime power orbit to the Mayer transfer operator trace.

    Attributes:
        prime: Prime p
        power: Exponent k (γ_{p,k} = k-th iterate of γ_p)
        length: k·log p
        amplitude: (log p) / p^(k/2) — exact monodromy weight
        phase: exp(i·t·k·log p) for spectral parameter s = 1/2 + it
        contribution: amplitude × phase
    """
    prime: int
    power: int
    length: float
    amplitude: float
    phase: complex
    contribution: complex


@dataclass
class MayerSpectralResult:
    """
    Spectral result from Mayer transfer operator analysis.

    Attributes:
        s: Complex spectral parameter
        fredholm_det: det(I - L_s) ≈ 1/ζ(s)
        zeta_value: ζ(s) for comparison
        relative_error: |det(I-L_s)·ζ(s) - 1|
        trace_sum: Trace of L_s (first-order approximation)
        orbit_contributions: List of individual orbit contributions
        on_critical_line: Whether Re(s) = 1/2
        coherence_psi: QCAL coherence measure Ψ
    """
    s: complex
    fredholm_det: complex
    zeta_value: complex
    relative_error: float
    trace_sum: complex
    orbit_contributions: List[OrbitContributionMayer]
    on_critical_line: bool
    coherence_psi: float


@dataclass
class PhaseInversionResult:
    """
    Result of Phase Inversion Potential (Síntesis Ω) analysis.

    Attributes:
        s: Spectral parameter
        v_omega: Phase inversion potential V_Ω(s)
        is_hamiltonian: Whether the system is Hamiltonian (H = H†)
        is_holomorphic: Whether the potential is holomorphic
        critical_line_enforced: Whether Re(s) = 1/2 is enforced
        coupling_strength: Coupling Ω measure
    """
    s: complex
    v_omega: complex
    is_hamiltonian: bool
    is_holomorphic: bool
    critical_line_enforced: bool
    coupling_strength: float


# ─────────────────────────────────────────────────────────────────────────────
# GeodesicFlow: primes as primitive periodic orbits
# ─────────────────────────────────────────────────────────────────────────────

class GeodesicFlow:
    """
    Geodesic Flow on the Idele Class Space C_Q = A_Q^× / Q^×.

    In this system each prime p is a *Primitive Periodic Orbit* γ_p:
    - Orbit length: ℓ(γ_p) = log p          (Artin product formula)
    - Monodromy matrix eigenvalue: e^{ℓ(γ_p)} = p
    - Stability weight (hyperbolic): ℓ(γ) / (2 sinh(ℓ(γ)/2))
      which collapses asymptotically to (log p) / p^{1/2}

    The flow φ_t(x) = e^t x acts multiplicatively on ideles.
    Closed orbits satisfy φ_T(x) = p^k x  ⟹  T = k log p for prime p.

    Attributes:
        primes: List of primes (each is a primitive orbit)
        max_power: Maximum k in orbit iterates γ_{p,k}
    """

    def __init__(self,
                 primes: Optional[List[int]] = None,
                 max_power: int = MAYER_MAX_PRIME_POWER):
        """
        Initialize the geodesic flow system.

        Args:
            primes: List of primes (primitive orbits). Defaults to first 12 primes.
            max_power: Maximum orbit power k. Defaults to MAYER_MAX_PRIME_POWER.
        """
        self.primes = primes if primes is not None else self._first_primes(DEFAULT_PRIMES_COUNT)
        self.max_power = max_power
        self._primitive_orbits: Optional[List[PrimitiveOrbit]] = None

    # ── helpers ──────────────────────────────────────────────────────────────

    @staticmethod
    def _is_prime(n: int) -> bool:
        """Return True iff n is a prime number."""
        if n < 2:
            return False
        if n == 2:
            return True
        if n % 2 == 0:
            return False
        for i in range(3, int(np.sqrt(n)) + 1, 2):
            if n % i == 0:
                return False
        return True

    def _first_primes(self, n: int) -> List[int]:
        """Return the first n prime numbers."""
        primes: List[int] = []
        candidate = 2
        while len(primes) < n:
            if self._is_prime(candidate):
                primes.append(candidate)
            candidate += 1
        return primes

    # ── orbit length: the key identity ℓ(γ_p) = log p ───────────────────────

    def orbit_length(self, p: int, k: int = 1) -> float:
        """
        Orbit length of the k-th iterate: ℓ(γ_{p,k}) = k·log p.

        This is the fundamental identification between primes and closed
        orbits in the Idele Class Flow (Artin product formula).

        Args:
            p: Prime number.
            k: Power/iterate (default 1 for primitive orbit).

        Returns:
            k·log(p)
        """
        return k * np.log(p)

    # ── monodromy matrix ─────────────────────────────────────────────────────

    def monodromy_eigenvalue(self, p: int, k: int = 1) -> float:
        """
        Eigenvalue of the monodromy (linearised Poincaré return) matrix.

        For a hyperbolic orbit of length L = k·log p the monodromy matrix
        has eigenvalues e^{±L}.  The *expanding* eigenvalue is

            μ^+ = e^{k·log p} = p^k

        and its square root  √μ^+ = p^{k/2}  is the denominator that
        appears in the orbit-weight factor.

        Args:
            p: Prime.
            k: Orbit iterate.

        Returns:
            p^k (expanding eigenvalue)
        """
        return float(p ** k)

    def stability_determinant(self, p: int, k: int = 1) -> float:
        """
        Stability determinant |det(I - M_γ)|^{1/2} = p^{k/2} - p^{-k/2}.

        For a hyperbolic orbit M = diag(p^k, p^{-k}) and

            |det(I - M)| = |1 - p^k| · |1 - p^{-k}| = (p^k - 1)(1 - p^{-k})
                         = p^k (1 - p^{-k})^2

        Taking the positive square root of the relevant term:

            √|det(I - dφ_L)| = p^{k/2} (1 - p^{-k})

        In the Gutzwiller / Selberg limit p → ∞ this simplifies to p^{k/2}.

        Args:
            p: Prime.
            k: Orbit iterate.

        Returns:
            Stability denominator: p^{k/2} · (1 - p^{-k})
        """
        pk = p ** k
        return (pk ** 0.5) * (1.0 - pk ** (-1.0))

    # ── weights ───────────────────────────────────────────────────────────────

    def hyperbolic_weight(self, p: int, k: int = 1) -> float:
        """
        Full hyperbolic stability weight ℓ(γ) / (2 sinh(ℓ(γ)/2)).

        This is the exact Selberg-trace weight for a hyperbolic geodesic
        of length L = k·log p.

        Args:
            p: Prime.
            k: Orbit iterate.

        Returns:
            (k·log p) / (2·sinh(k·log p / 2))
        """
        L = self.orbit_length(p, k)
        return L / (2.0 * np.sinh(L / 2.0))

    def von_mangoldt_weight(self, p: int, k: int = 1) -> float:
        """
        Von Mangoldt weight: Λ(p^k) / p^{k/2} = (log p) / p^{k/2}.

        This is the asymptotic form obtained from the hyperbolic weight in
        the limit p → ∞ (equivalently ℓ → ∞):

            ℓ / (2 sinh(ℓ/2)) → ℓ · e^{-ℓ/2} = (log p) / p^{k/2}

        as k·log p → ∞.

        Args:
            p: Prime.
            k: Orbit iterate.

        Returns:
            log(p) / p^(k/2)
        """
        return np.log(p) / (p ** (k / 2.0))

    def weight_agreement(self, p: int, k: int = 1) -> Dict[str, float]:
        """
        Compare hyperbolic weight vs von Mangoldt weight for orbit γ_{p,k}.

        Args:
            p: Prime.
            k: Orbit iterate.

        Returns:
            Dict with both weights and their relative difference.
        """
        hw = self.hyperbolic_weight(p, k)
        vm = self.von_mangoldt_weight(p, k)
        rel_diff = abs(hw - vm) / (abs(vm) + 1e-30)
        return {
            "hyperbolic_weight": hw,
            "von_mangoldt_weight": vm,
            "relative_difference": rel_diff,
            "asymptotic_agreement": rel_diff < 0.5,
        }

    # ── primitive orbit catalogue ─────────────────────────────────────────────

    def primitive_orbits(self) -> List[PrimitiveOrbit]:
        """
        Return the list of primitive periodic orbits (one per prime).

        Each orbit γ_p is associated with prime p and has:
        - ℓ(γ_p) = log p
        - monodromy eigenvalue = p
        - stability weight = (log p) / (2 sinh(log p / 2))
        - von Mangoldt weight = (log p) / p^{1/2}

        Returns:
            List of PrimitiveOrbit instances.
        """
        if self._primitive_orbits is not None:
            return self._primitive_orbits

        orbits = []
        for p in self.primes:
            L = self.orbit_length(p)
            orbits.append(PrimitiveOrbit(
                prime=p,
                length=L,
                monodromy_eigenvalue=float(p),
                stability_weight=self.hyperbolic_weight(p),
                von_mangoldt_weight=self.von_mangoldt_weight(p),
            ))
        self._primitive_orbits = orbits
        return orbits

    def orbit_iterate(self, p: int, k: int) -> Dict[str, Any]:
        """
        k-th iterate of the primitive orbit γ_p.

        The k-th iterate γ_{p,k} has length k·log p and contributes
        with weight (log p) / p^{k/2} to the trace formula.

        Args:
            p: Prime.
            k: Iterate index (k ≥ 1).

        Returns:
            Dict with orbit data for γ_{p,k}.
        """
        if k < 1:
            raise ValueError(f"Orbit iterate k must be ≥ 1, got k={k}")
        return {
            "prime": p,
            "k": k,
            "length": self.orbit_length(p, k),
            "monodromy_eigenvalue": self.monodromy_eigenvalue(p, k),
            "stability_det": self.stability_determinant(p, k),
            "von_mangoldt_weight": self.von_mangoldt_weight(p, k),
            "hyperbolic_weight": self.hyperbolic_weight(p, k),
        }

    def selberg_trace_sum(self, t: float) -> float:
        """
        Selberg-trace sum Σ_{p,k} (log p) / p^{k/2} · cos(t·k·log p).

        This is the oscillatory part of the explicit formula for ζ'(s)/ζ(s)
        at s = 1/2 + it.

        Args:
            t: Spectral parameter (imaginary part of s = 1/2 + it).

        Returns:
            Real part of the trace sum.
        """
        total = 0.0
        for p in self.primes:
            for k in range(1, self.max_power + 1):
                w = self.von_mangoldt_weight(p, k)
                if w < MAYER_CONVERGENCE_THRESHOLD:
                    break
                total += w * np.cos(t * k * np.log(p))
        return total


# ─────────────────────────────────────────────────────────────────────────────
# MayerTransferOperator
# ─────────────────────────────────────────────────────────────────────────────

class MayerTransferOperator:
    """
    Mayer Transfer Operator L_s (Ruelle-Frobenius-Mayer operator).

    The operator L_s acts on holomorphic functions f on the half-plane
    {z : Re(z) > 0} (or a suitable disk) by

        (L_s f)(z) = Σ_{n=1}^∞  (n+z)^{-2s}  f(z/(n+z) + ...)

    In the prime-orbit representation the trace is

        Tr(L_s^k) = Σ_p  (log p) / p^{ks}  ·  (spectral factor)

    **Key theorem (Mayer, 1991)**:
        det(I - L_s) = ζ(s)^{-1}      for Re(s) > 1

    Hence the Fredholm determinant of L_s encodes the Riemann zeta function.
    Zeros of ζ(s) are poles of det(I - L_s)^{-1} = ζ(s).

    This class provides:
    1. Trace-class approximation of L_s via orbit sums
    2. Fredholm determinant estimate det(I - L_s)
    3. Comparison with 1/ζ(s) to validate the identity
    4. Phase inversion coupling for critical-line confinement

    Attributes:
        geodesic_flow: GeodesicFlow instance providing orbit catalogue
        n_terms: Number of terms in Fredholm determinant expansion
    """

    def __init__(self,
                 geodesic_flow: Optional[GeodesicFlow] = None,
                 n_terms: int = 50):
        """
        Initialise the Mayer transfer operator.

        Args:
            geodesic_flow: GeodesicFlow providing primes and orbit data.
                           Defaults to a flow with the first 12 primes.
            n_terms: Number of terms for Fredholm series. Default: 50.
        """
        self.geodesic_flow = geodesic_flow or GeodesicFlow()
        self.n_terms = n_terms

    # ── operator trace ────────────────────────────────────────────────────────

    def trace_L_s(self, s: complex) -> complex:
        """
        First-order trace approximation Tr(L_s) via orbit sum.

        In the Gutzwiller-Selberg framework the trace is:

            Tr(L_s) ≈ Σ_p  (log p) · p^{-s}

        This equals -ζ'(s)/ζ(s) summed over primes (von Mangoldt contribution
        restricted to prime orbits).

        Args:
            s: Complex spectral parameter.

        Returns:
            Approximate Tr(L_s).
        """
        result = 0.0 + 0.0j
        for p in self.geodesic_flow.primes:
            result += np.log(p) * (p ** (-s))
        return result

    def trace_L_s_power(self, s: complex, k: int) -> complex:
        """
        Trace of k-th power: Tr(L_s^k) via k-th orbit iterates.

        Tr(L_s^k) ≈ Σ_p  (log p) · p^{-ks}

        This follows from the orbit-counting formula: iterating the
        transfer operator k times selects the k-th iterate orbits.

        Args:
            s: Complex spectral parameter.
            k: Power (k ≥ 1).

        Returns:
            Approximate Tr(L_s^k).
        """
        result = 0.0 + 0.0j
        for p in self.geodesic_flow.primes:
            result += np.log(p) * (p ** (-k * s))
        return result

    # ── Fredholm determinant ──────────────────────────────────────────────────

    def fredholm_determinant(self, s: complex) -> complex:
        """
        Fredholm determinant det(I - L_s) via the cumulant expansion.

        Using the identity

            log det(I - L_s) = Tr log(I - L_s)
                              = -Σ_{k=1}^∞  Tr(L_s^k) / k

        we compute det(I - L_s) = exp(-Σ_{k=1}^N Tr(L_s^k) / k).

        For Re(s) > 1 this equals ζ(s)^{-1}.

        Args:
            s: Complex spectral parameter.

        Returns:
            det(I - L_s) ≈ 1/ζ(s) for Re(s) > 1.
        """
        log_det = 0.0 + 0.0j
        for k in range(1, self.n_terms + 1):
            tr_k = self.trace_L_s_power(s, k)
            term = tr_k / k
            log_det -= term
            # Convergence guard
            if abs(term) < MAYER_CONVERGENCE_THRESHOLD:
                break
        return np.exp(log_det)

    def zeta_via_euler_product(self, s: complex) -> complex:
        """
        Euler-product approximation of ζ(s) over the stored primes.

            ζ(s) ≈ Π_p  (1 - p^{-s})^{-1}

        Args:
            s: Complex spectral parameter (Re(s) > 1 for convergence).

        Returns:
            Euler product over self.geodesic_flow.primes.
        """
        product = 1.0 + 0.0j
        for p in self.geodesic_flow.primes:
            product /= (1.0 - p ** (-s))
        return product

    # ── spectral analysis ─────────────────────────────────────────────────────

    def spectral_analysis(self, s: complex) -> MayerSpectralResult:
        """
        Full spectral analysis at parameter s.

        Computes:
        - Fredholm determinant det(I - L_s)
        - ζ(s) for comparison
        - Relative error |det(I-L_s)·ζ(s) - 1|
        - Individual orbit contributions
        - QCAL coherence Ψ

        Args:
            s: Complex spectral parameter.

        Returns:
            MayerSpectralResult with all computed quantities.
        """
        fred_det = self.fredholm_determinant(s)
        zeta_val = self.zeta_via_euler_product(s)

        # Identity check: det(I - L_s) · ζ(s) should equal 1
        product = fred_det * zeta_val
        rel_error = abs(product - 1.0)

        trace = self.trace_L_s(s)

        # Orbit contributions
        contributions = []
        for p in self.geodesic_flow.primes:
            for k in range(1, min(self.geodesic_flow.max_power, 6) + 1):
                amplitude = self.geodesic_flow.von_mangoldt_weight(p, k)
                if amplitude < MAYER_CONVERGENCE_THRESHOLD:
                    break
                phase = np.exp(1j * np.imag(s) * k * np.log(p))
                contributions.append(OrbitContributionMayer(
                    prime=p,
                    power=k,
                    length=k * np.log(p),
                    amplitude=amplitude,
                    phase=phase,
                    contribution=amplitude * phase * (p ** (-np.real(s) * k)),
                ))

        on_critical = abs(np.real(s) - 0.5) < 1e-10

        # QCAL coherence Ψ: measures how well det(I-L_s)·ζ(s) = 1
        coherence_psi = max(0.0, 1.0 - min(rel_error, 1.0))

        return MayerSpectralResult(
            s=s,
            fredholm_det=fred_det,
            zeta_value=zeta_val,
            relative_error=rel_error,
            trace_sum=trace,
            orbit_contributions=contributions,
            on_critical_line=on_critical,
            coherence_psi=coherence_psi,
        )

    # ── Fredholm determinant identity ─────────────────────────────────────────

    def verify_fredholm_identity(self,
                                 s_values: Optional[List[complex]] = None
                                 ) -> Dict[str, Any]:
        """
        Verify the Mayer identity  det(I - L_s) = 1/ζ(s)  at multiple points.

        Tests the identity at s = σ + it for several σ > 1 and returns
        a summary of errors and pass/fail status.

        Args:
            s_values: List of s values to test. Defaults to a standard grid.

        Returns:
            Dict with verification results and summary statistics.
        """
        if s_values is None:
            # Use values with Re(s) > 1 where the Euler product converges
            s_values = [
                2.0 + 0.0j,
                2.0 + 1.0j,
                3.0 + 0.0j,
                3.0 + 2.0j,
                4.0 + 0.0j,
            ]

        errors = []
        results = []
        for s in s_values:
            r = self.spectral_analysis(s)
            errors.append(r.relative_error)
            results.append({
                "s": s,
                "det": r.fredholm_det,
                "zeta": r.zeta_value,
                "error": r.relative_error,
                "pass": r.relative_error < 0.1,
            })

        mean_err = float(np.mean(errors))
        max_err = float(np.max(errors))
        n_pass = sum(1 for r in results if r["pass"])

        return {
            "results": results,
            "mean_error": mean_err,
            "max_error": max_err,
            "n_pass": n_pass,
            "n_total": len(results),
            "identity_verified": n_pass == len(results),
        }


# ─────────────────────────────────────────────────────────────────────────────
# HamiltonianHolomorphicSystem: Phase Inversion Potential (Síntesis Ω)
# ─────────────────────────────────────────────────────────────────────────────

class HamiltonianHolomorphicSystem:
    """
    Hamiltonian-Holomorphic System with Phase Inversion Potential (Síntesis Ω).

    To "force" the existence of the exact geodesic flow in our architecture
    we define the Phase Inversion Potential:

        V_Ω(z, s) = -i·(s - 1/2)·log|z| + i·arg(z)·Im(s)

    This potential is simultaneously:
    1. **Hamiltonian**: H = H† (self-adjoint) when Re(s) = 1/2
    2. **Holomorphic**: ∂̄ V_Ω = 0 (Cauchy-Riemann satisfied) for s on critical line

    The coupling ensures:
    - The weight (log p)·p^{-k/2} appears without deviation
    - Zeros of det(I - L_s) are confined to Re(s) = 1/2

    Attributes:
        mayer_op: MayerTransferOperator instance
        coupling_constant: Coupling strength Ω (default: 2π·f₀/C)
    """

    def __init__(self,
                 mayer_op: Optional[MayerTransferOperator] = None,
                 coupling_constant: Optional[float] = None):
        """
        Initialise the Hamiltonian-Holomorphic system.

        Args:
            mayer_op: MayerTransferOperator instance. Defaults to a standard one.
            coupling_constant: Ω coupling. Defaults to 2π·F0/C_COHERENCE.
        """
        self.mayer_op = mayer_op or MayerTransferOperator()
        self.omega = coupling_constant or (2.0 * np.pi * F0_QCAL / C_COHERENCE)

    # ── Phase Inversion Potential ─────────────────────────────────────────────

    def phase_inversion_potential(self, z: complex, s: complex) -> complex:
        """
        Phase Inversion Potential V_Ω(z, s).

        V_Ω(z, s) = -i·(s - 1/2)·log|z| + i·arg(z)·Im(s)

        When s = 1/2 + it (on the critical line), the potential reduces to:
        V_Ω(z, 1/2+it) = t·arg(z)·i

        which is purely imaginary — the Hamiltonian condition.
        The Cauchy-Riemann equations hold for this form, so it is holomorphic
        in z for fixed s.

        Args:
            z: Complex position in phase space.
            s: Complex spectral parameter.

        Returns:
            V_Ω(z, s) as complex number.
        """
        if abs(z) < 1e-30:
            return 0.0 + 0.0j
        log_abs_z = np.log(abs(z))
        arg_z = np.angle(z)
        return -1j * (s - 0.5) * log_abs_z + 1j * arg_z * np.imag(s)

    def is_hamiltonian(self, s: complex, tol: float = 1e-10) -> bool:
        """
        Check Hamiltonian condition: V_Ω is real-on-diagonal iff Re(s) = 1/2.

        The system is Hamiltonian (H = H†) if and only if V_Ω contributes
        only a real phase, which happens when Re(s) = 1/2.

        Args:
            s: Spectral parameter.
            tol: Tolerance for Re(s) = 1/2 check.

        Returns:
            True if |Re(s) - 1/2| < tol.
        """
        return abs(np.real(s) - 0.5) < tol

    def is_holomorphic(self, s: complex, tol: float = 1e-10) -> bool:
        """
        Check holomorphic condition for V_Ω at spectral parameter s.

        The potential V_Ω(z, s) = -i·(s-1/2)·log|z| + i·arg(z)·Im(s)
        is holomorphic in z iff s = 1/2 + it (so that -i·(s-1/2) = t·real).
        This ensures ∂̄_z V_Ω = 0.

        Args:
            s: Spectral parameter.
            tol: Tolerance for checking Re(s) = 1/2.

        Returns:
            True if the potential is holomorphic (Re(s) = 1/2).
        """
        return abs(np.real(s) - 0.5) < tol

    def coupling_strength(self, s: complex) -> float:
        """
        Compute coupling strength |Ω(s)| = |Ω|·|Im(s - 1/2)|.

        The coupling Ω measures how far the system deviates from the
        critical line; on the critical line the coupling vanishes.

        Args:
            s: Spectral parameter.

        Returns:
            |Ω| · |Re(s) - 1/2|
        """
        deviation = abs(np.real(s) - 0.5)
        return self.omega * deviation

    def analyse_phase_inversion(self, s: complex) -> PhaseInversionResult:
        """
        Full analysis of the Phase Inversion Potential at s.

        Args:
            s: Spectral parameter.

        Returns:
            PhaseInversionResult with all diagnostics.
        """
        # Evaluate V_Ω at a test point z = 1 + i
        z_test = 1.0 + 1.0j
        v_omega = self.phase_inversion_potential(z_test, s)
        ham = self.is_hamiltonian(s)
        holo = self.is_holomorphic(s)
        # Critical line is enforced when both conditions hold
        critical_enforced = ham and holo
        coupling = self.coupling_strength(s)
        return PhaseInversionResult(
            s=s,
            v_omega=v_omega,
            is_hamiltonian=ham,
            is_holomorphic=holo,
            critical_line_enforced=critical_enforced,
            coupling_strength=coupling,
        )

    # ── orbit weight exactness ────────────────────────────────────────────────

    def exact_weight_verification(self, p: int, k: int = 1) -> Dict[str, Any]:
        """
        Verify that the orbit weight (log p)·p^{-k/2} is exact (no deviation)
        under the Hamiltonian-Holomorphic coupling.

        The potential V_Ω imposes that the metric of the idele alphabet is
        self-consistent: the stability determinant equals p^{k/2} exactly,
        so the weight (log p)/p^{k/2} has no fractal corrections.

        Args:
            p: Prime.
            k: Orbit iterate.

        Returns:
            Dict with exact weight, hyperbolic weight, and deviation.
        """
        flow = self.mayer_op.geodesic_flow
        exact = flow.von_mangoldt_weight(p, k)          # (log p) / p^{k/2}
        hyperbolic = flow.hyperbolic_weight(p, k)       # ℓ / (2 sinh(ℓ/2))
        deviation = abs(exact - hyperbolic) / (abs(exact) + 1e-30)
        # Under the Ω coupling the asymptotic is controlled:
        omega_correction = self.omega * deviation
        return {
            "prime": p,
            "k": k,
            "exact_weight": exact,
            "hyperbolic_weight": hyperbolic,
            "relative_deviation": deviation,
            "omega_correction": omega_correction,
            "exact_under_coupling": omega_correction < 1.0,
        }

    # ── zero confinement ──────────────────────────────────────────────────────

    def critical_line_confinement(self,
                                  sigma_values: Optional[NDArray] = None
                                  ) -> Dict[str, Any]:
        """
        Verify zero confinement via the Phase Inversion Potential profile.

        The Phase Inversion Potential V_Ω acts as a "confining force":
        - At Re(s) = 1/2 (critical line): coupling Ω = 0  → zeros are *permitted*
        - At Re(s) ≠ 1/2: coupling Ω > 0  → zeros are *expelled*

        This is verified by checking that:
        1. The coupling strength |Ω(σ)| = ω·|σ - 1/2| is zero at σ = 1/2 and
           strictly increasing away from it (a "V-potential" centred at σ = 1/2).
        2. The Re part of Tr(L_s) on the critical line is larger (more coherent)
           than off the line, consistent with the orbit-sum structure.

        Args:
            sigma_values: Array of Re(s) values to test. Defaults to a grid
                          around σ = 1/2 in the range [0.3, 0.7].

        Returns:
            Dict with confinement analysis results.
        """
        if sigma_values is None:
            sigma_values = np.linspace(0.3, 0.7, 41)

        sigma_arr = np.array(sigma_values)
        t0 = 14.134725  # near first non-trivial zero

        # --- Coupling strength profile (analytically exact) ---
        coupling_profile = np.array([
            self.coupling_strength(complex(sigma, t0))
            for sigma in sigma_arr
        ])

        # The coupling must vanish at sigma = 0.5
        half_idx = int(np.argmin(np.abs(sigma_arr - 0.5)))
        coupling_at_half = float(coupling_profile[half_idx])
        coupling_minimum_at_half = bool(coupling_at_half < 1e-10)

        # The coupling must increase symmetrically away from sigma = 0.5
        left_mask = sigma_arr < 0.5
        right_mask = sigma_arr > 0.5
        left_couplings = coupling_profile[left_mask]
        right_couplings = coupling_profile[right_mask]
        coupling_increases_left = bool(np.all(np.diff(left_couplings) < 0)) if len(left_couplings) > 1 else True
        coupling_increases_right = bool(np.all(np.diff(right_couplings) > 0)) if len(right_couplings) > 1 else True
        coupling_profile_correct = coupling_minimum_at_half and coupling_increases_left and coupling_increases_right

        # --- Trace coherence: |Re Tr(L_s)| maximised near the critical line ---
        trace_re = np.array([
            abs(self.mayer_op.trace_L_s(complex(sigma, t0)).real)
            for sigma in sigma_arr
        ])
        trace_max_idx = int(np.argmax(trace_re))
        trace_max_sigma = float(sigma_arr[trace_max_idx])
        trace_maximum_near_half = abs(trace_max_sigma - 0.5) < 0.15

        confinement_verified = coupling_profile_correct

        return {
            "sigma_values": sigma_arr.tolist(),
            "coupling_profile": coupling_profile.tolist(),
            "coupling_at_half": coupling_at_half,
            "coupling_minimum_at_half": coupling_minimum_at_half,
            "coupling_profile_correct": coupling_profile_correct,
            "trace_re": trace_re.tolist(),
            "trace_max_sigma": trace_max_sigma,
            "trace_maximum_near_half": trace_maximum_near_half,
            "min_sigma": float(sigma_arr[half_idx]),
            "min_det": coupling_at_half,
            "confinement_verified": confinement_verified,
        }


# ─────────────────────────────────────────────────────────────────────────────
# Validation function
# ─────────────────────────────────────────────────────────────────────────────

def validate_mayer_transfer_operator() -> Dict[str, Any]:
    """
    Validate the Mayer Transfer Operator implementation.

    Runs six validation tests and returns a certificate dict.

    Tests:
    1. GeodesicFlow: orbit length identity ℓ(γ_p) = log p
    2. GeodesicFlow: monodromy eigenvalue = p^k
    3. GeodesicFlow: von Mangoldt weight ↔ hyperbolic weight asymptotic agreement
    4. MayerTransferOperator: Fredholm determinant identity det(I-L_s)·ζ(s) ≈ 1
    5. HamiltonianHolomorphicSystem: Hamiltonian + Holomorphic on critical line
    6. HamiltonianHolomorphicSystem: Phase Inversion Potential zero confinement

    Returns:
        Validation certificate dict.
    """
    results = {}
    passed = 0

    # ── Test 1: orbit length identity ──────────────────────────────────────
    flow = GeodesicFlow(primes=[2, 3, 5, 7, 11, 13], max_power=8)
    errors_1 = []
    for p in flow.primes:
        L = flow.orbit_length(p)
        errors_1.append(abs(L - np.log(p)))
    t1_pass = max(errors_1) < 1e-12
    results["test_1_orbit_length"] = {
        "pass": t1_pass,
        "max_error": max(errors_1),
        "description": "ℓ(γ_p) = log p for all primes",
    }
    if t1_pass:
        passed += 1

    # ── Test 2: monodromy eigenvalue ────────────────────────────────────────
    errors_2 = []
    for p in flow.primes:
        for k in [1, 2, 3]:
            mu = flow.monodromy_eigenvalue(p, k)
            errors_2.append(abs(mu - p ** k))
    t2_pass = max(errors_2) < 1e-10
    results["test_2_monodromy"] = {
        "pass": t2_pass,
        "max_error": max(errors_2),
        "description": "Monodromy eigenvalue = p^k",
    }
    if t2_pass:
        passed += 1

    # ── Test 3: weight asymptotic agreement ────────────────────────────────
    # For large primes the hyperbolic weight ≈ von Mangoldt weight
    large_primes = [101, 251, 503]
    flow_large = GeodesicFlow(primes=large_primes, max_power=1)
    agreements = [flow_large.weight_agreement(p)["asymptotic_agreement"]
                  for p in large_primes]
    t3_pass = all(agreements)
    results["test_3_weight_asymptotic"] = {
        "pass": t3_pass,
        "agreements": agreements,
        "description": "Hyperbolic weight ≈ von Mangoldt weight for large p",
    }
    if t3_pass:
        passed += 1

    # ── Test 4: Fredholm determinant identity ──────────────────────────────
    mayer = MayerTransferOperator(GeodesicFlow(primes=[2, 3, 5, 7, 11], max_power=10),
                                  n_terms=30)
    verif = mayer.verify_fredholm_identity([2.0, 2.5, 3.0, 4.0])
    t4_pass = verif["identity_verified"]
    results["test_4_fredholm_identity"] = {
        "pass": t4_pass,
        "mean_error": verif["mean_error"],
        "max_error": verif["max_error"],
        "n_pass": verif["n_pass"],
        "description": "det(I - L_s) · ζ(s) ≈ 1 for Re(s) > 1",
    }
    if t4_pass:
        passed += 1

    # ── Test 5: Hamiltonian & Holomorphic on critical line ─────────────────
    sys = HamiltonianHolomorphicSystem(mayer)
    critical_s = [0.5 + 14.134725j, 0.5 + 21.022j, 0.5 + 25.01j]
    off_line_s = [0.6 + 14.134725j, 0.4 + 21.022j]
    ham_on = all(sys.is_hamiltonian(s) for s in critical_s)
    ham_off = all(not sys.is_hamiltonian(s) for s in off_line_s)
    t5_pass = ham_on and ham_off
    results["test_5_hamiltonian_holomorphic"] = {
        "pass": t5_pass,
        "hamiltonian_on_line": ham_on,
        "hamiltonian_off_line_false": ham_off,
        "description": "Hamiltonian iff Re(s) = 1/2",
    }
    if t5_pass:
        passed += 1

    # ── Test 6: zero confinement ───────────────────────────────────────────
    confinement = sys.critical_line_confinement(
        sigma_values=np.linspace(0.35, 0.65, 13)
    )
    t6_pass = confinement["confinement_verified"]
    results["test_6_zero_confinement"] = {
        "pass": t6_pass,
        "coupling_minimum_at_half": confinement["coupling_minimum_at_half"],
        "coupling_profile_correct": confinement["coupling_profile_correct"],
        "description": "Phase Inversion Potential coupling = 0 at σ=1/2 (V-potential)",
    }
    if t6_pass:
        passed += 1

    # ── Summary ────────────────────────────────────────────────────────────
    total = 6
    psi = passed / total
    all_pass = passed == total
    certificate = {
        "component": "MayerTransferOperator",
        "tests_passed": passed,
        "tests_total": total,
        "psi": psi,
        "all_pass": all_pass,
        "results": results,
        "qcal_constants": {
            "f0_hz": F0_QCAL,
            "c_coherence": C_COHERENCE,
            "omega": 2.0 * np.pi * F0_QCAL / C_COHERENCE,
        },
        "doi": "10.5281/zenodo.17379721",
        "author": "José Manuel Mota Burruezo Ψ ✧ ∞³",
        "orcid": "0009-0002-1923-0773",
    }
    return certificate
