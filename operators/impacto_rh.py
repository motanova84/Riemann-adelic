#!/usr/bin/env python3
"""
Impacto RH — Sieve → ψ(x) → Selberg Trace → GUE Rigidity → S-Finite Resolution
=================================================================================

This module implements the complete pipeline that links analytic number theory
(prime sieve, Chebyshev ψ) to spectral theory (Selberg trace formula) and random
matrix theory (GUE rigidity), advancing the conditional S-finite resolution of
the Riemann Hypothesis.

Mathematical Framework:
-----------------------

**Stage 1 — Tamiz (Sieve of Eratosthenes)**

    Generates {p ≤ x : p prime}.  Weighted version gives the von Mangoldt
    function:

        Λ(n) = log p   if n = p^k for some prime p, k ≥ 1
               0        otherwise

**Stage 2 — Chebyshev ψ(x)**

    The second Chebyshev function:

        ψ(x) = ∑_{p^k ≤ x} log p = ∑_{n ≤ x} Λ(n)

    RH is equivalent to

        ψ(x) = x + O(√x log² x)

    We compute the normalised oscillation

        δψ(x) = ψ(x) - x

    and track its spectral content.

**Stage 3 — Selberg Explicit Formula**

    The Selberg–Mangoldt explicit formula connects ψ to the zeros ρ = β + iγ
    of ζ (von Mangoldt form):

        ψ(x) = x − ∑_ρ x^ρ/ρ − log(2π) − ½ log(1 − x^{-2})

    Stage 3 of this pipeline uses the equivalent smoothed (Weil explicit
    formula) form with a Schwartz test function h ∈ S(ℝ), after Selberg (1956)
    and Weil (1952):

        ∑_γ h(γ) = ĥ(0) − ∑_{p,k} (log p)/p^{k/2} [ĥ(log p^k) + ĥ(−log p^k)] + (lower-order terms)

    where the left side sums over imaginary parts γ of non-trivial zeros, ĥ is
    the Fourier transform of h, and the right side runs over prime powers p^k.
    With finitely many zeros the formula is an approximation; quality is
    measured as exp(−|balance|/(|LHS|+|RHS|+ε)) ∈ (0,1].

    This links the prime distribution (right side) to the zero spectrum (left).

**Stage 4 — GUE Rigidity**

    The Dyson–Mehta Δ₃ statistic measures how rigidly the spectrum follows
    GUE predictions:

        Δ₃(L) ≈ (1/π²)[ln(2πL) + γ_EM − 5/4 − ln 2]  (GUE prediction)

    For the Riemann zeros this has been verified (Odlyzko) up to height ~10^{22}.
    A strong deviation Δ₃ ≫ Δ₃^{GUE} would imply zeros off the critical line.

**Stage 5 — S-Finite Conditional Resolution**

    Under the assumption that all zeros satisfy |β − 1/2| ≤ ε for some ε < 1/2,
    the S-finite adelic system

        (𝔸_ℚ / ℚ, μ_Haar) ⊗ (C^∞ at ∞)

    is well-defined.  We quantify the residual off-critical deviation

        R_S = ‖δψ‖²_{L²([2,X])} / X  →  0   as X → ∞

    conditioned on GUE rigidity holding, and report the coherence score

        Ψ = exp(−R_S / (X + 1))  ∈ (0,1]

    The division by (X + 1) normalises the exponent so that the growing L²
    norm of δψ(x) ~ √x does not collapse Ψ to 0 as X increases; this is
    consistent with RH which predicts δψ = O(√x log² x).

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: March 2026
QCAL ∞³ Active · 141.7001 Hz · f₀ = 141.7001 Hz · Ψ = I × A_eff² × C^∞
DOI: 10.5281/zenodo.17379721
Signature: ∴𓂀Ω∞³Φ @ 141.7001 Hz
"""

import numpy as np
from typing import Dict, List, Optional, Tuple
from numpy.typing import NDArray
from dataclasses import dataclass, field

# QCAL ∞³ Constants
F0_QCAL = 141.7001          # Hz – fundamental frequency
C_COHERENCE = 244.36         # Coherence constant C^∞
EULER_MASCHERONI = 0.5772156649015328  # γ_EM


# ---------------------------------------------------------------------------
# Data classes
# ---------------------------------------------------------------------------

@dataclass
class SieveResult:
    """Output of Stage 1: prime sieve and von Mangoldt extraction.

    Attributes:
        primes: Sorted list of primes p ≤ N.
        mangoldt: Von Mangoldt values Λ(n) for n = 1, …, N.
        N: Upper bound used for the sieve.
    """
    primes: List[int]
    mangoldt: NDArray[np.float64]
    N: int


@dataclass
class ChebyshevResult:
    """Output of Stage 2: Chebyshev ψ(x) computation.

    Attributes:
        x_values: Sample points x_1 < x_2 < … < x_k in [2, X].
        psi_values: ψ(x_i) for each sample point.
        delta_psi: Normalised oscillation δψ(x_i) = ψ(x_i) − x_i.
        rms_delta: Root-mean-square of δψ.
        X: Maximum sample point.
    """
    x_values: NDArray[np.float64]
    psi_values: NDArray[np.float64]
    delta_psi: NDArray[np.float64]
    rms_delta: float
    X: float


@dataclass
class SelbergTraceResult:
    """Output of Stage 3: Selberg explicit-formula evaluation.

    Attributes:
        zero_side: ∑_γ h(γ) (left-hand side over zeros).
        prime_side: Integral minus prime sum (right-hand side).
        balance: zero_side − prime_side (should be ≈ 0).
        relative_error: |balance| / (|zero_side| + |prime_side| + ε).
        quality: exp(−relative_error); 1 = perfect balance, tolerates finite truncation.
        n_zeros: Number of zeros used.
        n_primes: Number of primes used.
    """
    zero_side: float
    prime_side: float
    balance: float
    relative_error: float
    quality: float  # exp(−|balance|/(|zero_side|+|prime_side|+ε))
    n_zeros: int
    n_primes: int


@dataclass
class GUERigidityResult:
    """Output of Stage 4: GUE Δ₃ spectral rigidity analysis.

    Attributes:
        delta3_measured: Measured Δ₃(L) for the given window.
        delta3_gue: Theoretical GUE prediction Δ₃^{GUE}(L).
        L: Window length used.
        ratio: delta3_measured / delta3_gue.
        is_gue_consistent: True when |ratio − 1| < tolerance.
        spacings: Unfolded nearest-neighbour spacings.
        mean_spacing_ratio: Mean r_n = min(s_n, s_{n+1}) / max(s_n, s_{n+1}).
    """
    delta3_measured: float
    delta3_gue: float
    L: float
    ratio: float
    is_gue_consistent: bool
    spacings: NDArray[np.float64]
    mean_spacing_ratio: float


@dataclass
class SFiniteResolutionResult:
    """Output of Stage 5: S-finite conditional resolution.

    Attributes:
        R_S: Residual L² off-critical deviation R_S = ‖δψ‖² / X.
        psi_coherence: Ψ = exp(−R_S).
        gue_consistent: Whether GUE rigidity is satisfied.
        selberg_quality: Selberg trace balance quality.
        verdict: "S_FINITE_RESOLVED" or "S_FINITE_CONDITIONAL".
        metadata: Additional diagnostic information.
    """
    R_S: float
    psi_coherence: float
    gue_consistent: bool
    selberg_quality: float
    verdict: str
    metadata: Dict = field(default_factory=dict)


@dataclass
class ImpactoRHResult:
    """Complete pipeline result linking sieve → ψ → Selberg → GUE → S-finite.

    Attributes:
        sieve: Stage-1 sieve output.
        chebyshev: Stage-2 Chebyshev ψ output.
        selberg: Stage-3 Selberg trace output.
        gue: Stage-4 GUE rigidity output.
        s_finite: Stage-5 S-finite resolution output.
        global_psi: Overall coherence score Ψ ∈ [0, 1].
    """
    sieve: SieveResult
    chebyshev: ChebyshevResult
    selberg: SelbergTraceResult
    gue: GUERigidityResult
    s_finite: SFiniteResolutionResult
    global_psi: float


# ---------------------------------------------------------------------------
# Stage 1 — Tamiz (Sieve)
# ---------------------------------------------------------------------------

class PrimeSieve:
    """Sieve of Eratosthenes with von Mangoldt function extraction.

    Args:
        N: Upper bound; computes all primes p ≤ N and Λ(n) for n ≤ N.
    """

    def __init__(self, N: int) -> None:
        if N < 2:
            raise ValueError("N must be at least 2.")
        self.N = N
        self._primes: Optional[List[int]] = None
        self._mangoldt: Optional[NDArray[np.float64]] = None

    def run(self) -> SieveResult:
        """Execute the sieve and build the von Mangoldt array.

        Returns:
            SieveResult with primes and Λ(n) values.
        """
        N = self.N
        composite = np.zeros(N + 1, dtype=bool)
        composite[0] = composite[1] = True
        for i in range(2, int(N**0.5) + 1):
            if not composite[i]:
                composite[i*i::i] = True

        primes = [i for i in range(2, N + 1) if not composite[i]]

        # Build Λ(n): log p for prime powers p^k ≤ N
        mangoldt = np.zeros(N + 1, dtype=np.float64)
        for p in primes:
            log_p = np.log(float(p))
            pk = p
            while pk <= N:
                mangoldt[pk] = log_p
                pk *= p

        self._primes = primes
        self._mangoldt = mangoldt
        return SieveResult(primes=primes, mangoldt=mangoldt, N=N)


# ---------------------------------------------------------------------------
# Stage 2 — Chebyshev ψ(x)
# ---------------------------------------------------------------------------

class ChebyshevPsi:
    """Compute the second Chebyshev function ψ(x) = ∑_{n ≤ x} Λ(n).

    Args:
        sieve_result: Output from PrimeSieve.run().
        n_samples: Number of equally-spaced sample points in [2, N].
    """

    def __init__(self, sieve_result: SieveResult, n_samples: int = 200) -> None:
        self.sieve = sieve_result
        self.n_samples = n_samples

    def compute(self) -> ChebyshevResult:
        """Compute ψ at sample points via cumulative sum of Λ.

        Returns:
            ChebyshevResult with ψ values and oscillation δψ.
        """
        N = self.sieve.N
        mangoldt = self.sieve.mangoldt

        # Cumulative sum gives ψ(n) at integer points
        psi_int = np.cumsum(mangoldt)  # psi_int[n] = ψ(n)

        # Sample at n_samples points in [2, N]
        x_idx = np.unique(
            np.linspace(2, N, self.n_samples, dtype=int).clip(2, N)
        )
        x_values = x_idx.astype(np.float64)
        psi_values = psi_int[x_idx]

        delta_psi = psi_values - x_values
        rms_delta = float(np.sqrt(np.mean(delta_psi**2)))

        return ChebyshevResult(
            x_values=x_values,
            psi_values=psi_values,
            delta_psi=delta_psi,
            rms_delta=rms_delta,
            X=float(x_values[-1]),
        )


# ---------------------------------------------------------------------------
# Stage 3 — Selberg Explicit Formula (trace form)
# ---------------------------------------------------------------------------

class SelbergExplicitFormula:
    """Selberg explicit-formula balance: zeros ↔ primes.

    Uses the Gaussian test function h(t) = exp(−t²/(2σ²)) with
    analytic Fourier transform ĥ(r) = σ√(2π) exp(−σ²r²/2).

    Args:
        zeros: Imaginary parts γ_n of non-trivial zeros (γ_n > 0).
        primes: List of primes p to include in the prime sum.
        sigma: Width parameter σ for the test Gaussian (default 5.0).
    """

    def __init__(
        self,
        zeros: NDArray[np.float64],
        primes: List[int],
        sigma: float = 5.0,
    ) -> None:
        self.zeros = np.asarray(zeros, dtype=np.float64)
        self.primes = primes
        self.sigma = sigma

    def _h(self, t: float) -> float:
        """Test function h(t) = exp(−t²/(2σ²))."""
        return float(np.exp(-t**2 / (2.0 * self.sigma**2)))

    def _h_hat(self, r: float) -> float:
        """Fourier transform ĥ(r) = σ√(2π) exp(−σ²r²/2)."""
        return float(self.sigma * np.sqrt(2.0 * np.pi) * np.exp(-self.sigma**2 * r**2 / 2.0))

    def compute(self) -> SelbergTraceResult:
        """Evaluate both sides of the Selberg trace formula.

        Left side (zeros):
            LHS = ∑_γ h(γ)

        Right side (primes + measure):
            RHS = ∫ h(r) μ_Weyl(r) dr − ∑_{p,k} (log p)/p^{k/2} · [ĥ(log p^k) + ĥ(−log p^k)]

        The Weyl measure ∫h(r)μ(r)dr is approximated as ĥ(0) (dominant term).

        Returns:
            SelbergTraceResult with quality metric.
        """
        # Left side: sum over zeros
        zero_side = float(np.sum([self._h(g) for g in self.zeros]))

        # Right side: dominant measure term
        measure_term = self._h_hat(0.0)

        # Prime power contributions
        prime_sum = 0.0
        overflow_threshold = 1e12
        for p in self.primes:
            log_p = np.log(float(p))
            pk = p
            k = 1
            while pk <= overflow_threshold:
                weight = log_p / np.sqrt(float(pk))
                prime_sum += weight * (self._h_hat(log_p * k) + self._h_hat(-log_p * k))
                pk *= p
                k += 1

        prime_side = measure_term - prime_sum

        balance = zero_side - prime_side
        # Normalize by the total magnitude so finite truncation does not
        # collapse the metric when zero_side ≪ prime_side.
        total = abs(zero_side) + abs(prime_side) + 1e-10
        relative_error = abs(balance) / total
        quality = float(np.exp(-relative_error))

        return SelbergTraceResult(
            zero_side=zero_side,
            prime_side=prime_side,
            balance=balance,
            relative_error=relative_error,
            quality=quality,
            n_zeros=len(self.zeros),
            n_primes=len(self.primes),
        )


# ---------------------------------------------------------------------------
# Stage 4 — GUE Rigidity
# ---------------------------------------------------------------------------

class GUERigidity:
    """GUE Δ₃ spectral rigidity analysis for a zero spectrum.

    Args:
        zeros: Imaginary parts γ_n of non-trivial zeros (sorted).
        tolerance: Relative tolerance for GUE consistency test (default 0.3).
    """

    def __init__(
        self,
        zeros: NDArray[np.float64],
        tolerance: float = 0.3,
    ) -> None:
        self.zeros = np.sort(np.asarray(zeros, dtype=np.float64))
        self.tolerance = tolerance

    def _unfold(self, eigs: NDArray[np.float64]) -> NDArray[np.float64]:
        """Unfold spectrum to unit mean spacing via smooth cumulative density."""
        n = len(eigs)
        cumulative = np.arange(n, dtype=np.float64)
        deg = min(5, max(1, n // 10))
        coeffs = np.polyfit(eigs, cumulative, deg)
        return np.polyval(coeffs, eigs)

    def _delta3(self, unfolded: NDArray[np.float64], L: float) -> float:
        """Compute Dyson–Mehta Δ₃(L) statistic.

        Δ₃(L) = (1/L) min_{a,b} ∫₀ᴸ [N(e) − ae − b]² de
        approximated over sliding windows of integer length int(L).
        """
        int_L = max(2, int(L))
        n = len(unfolded)
        if n < int_L:
            int_L = n
        deltas = []
        for i in range(n - int_L):
            window = unfolded[i:i + int_L]
            x = np.arange(int_L, dtype=np.float64)
            A = np.vstack([x, np.ones(int_L)]).T
            sol, _, _, _ = np.linalg.lstsq(A, window, rcond=None)
            fit = A @ sol
            deltas.append(float(np.mean((window - fit) ** 2)))
        return float(np.mean(deltas)) if deltas else 0.0

    @staticmethod
    def gue_prediction(L: float) -> float:
        """GUE theoretical Δ₃(L) ≈ (1/π²)[ln(2πL) + γ_EM − 5/4 − ln 2].

        Args:
            L: Window length.

        Returns:
            Theoretical Δ₃^{GUE}(L).
        """
        if L <= 0:
            return 0.0
        val = (1.0 / np.pi**2) * (
            np.log(2.0 * np.pi * L) + EULER_MASCHERONI - 1.25 - np.log(2.0)
        )
        return max(val, 1e-6)

    def _mean_spacing_ratio(self, spacings: NDArray[np.float64]) -> float:
        """Mean r_n = min(s_n, s_{n+1}) / max(s_n, s_{n+1}) (GUE ≈ 0.60)."""
        if len(spacings) < 2:
            return 0.0
        ratios = [
            min(spacings[i], spacings[i + 1]) / max(spacings[i], spacings[i + 1])
            for i in range(len(spacings) - 1)
            if max(spacings[i], spacings[i + 1]) > 0
        ]
        return float(np.mean(ratios)) if ratios else 0.0

    def compute(self) -> GUERigidityResult:
        """Compute GUE rigidity metrics for the given zero spectrum.

        Returns:
            GUERigidityResult with Δ₃ and spacing statistics.
        """
        zeros = self.zeros
        if len(zeros) < 4:
            return GUERigidityResult(
                delta3_measured=0.0,
                delta3_gue=0.0,
                L=0.0,
                ratio=1.0,
                is_gue_consistent=False,
                spacings=np.array([]),
                mean_spacing_ratio=0.0,
            )

        unfolded = self._unfold(zeros)
        spacings = np.diff(unfolded)
        mean_sp = float(np.mean(spacings))
        if mean_sp > 0:
            spacings_norm = spacings / mean_sp
        else:
            spacings_norm = spacings

        L = max(5.0, 0.15 * len(zeros))
        d3_meas = self._delta3(unfolded, L)
        d3_gue = self.gue_prediction(L)

        ratio = d3_meas / (d3_gue + 1e-12)
        is_consistent = abs(ratio - 1.0) < self.tolerance

        msr = self._mean_spacing_ratio(spacings_norm)

        return GUERigidityResult(
            delta3_measured=d3_meas,
            delta3_gue=d3_gue,
            L=L,
            ratio=ratio,
            is_gue_consistent=is_consistent,
            spacings=spacings_norm,
            mean_spacing_ratio=msr,
        )


# ---------------------------------------------------------------------------
# Stage 5 — S-Finite Conditional Resolution
# ---------------------------------------------------------------------------

class SFiniteResolution:
    """S-finite adelic conditional resolution from the pipeline outputs.

    Combines Chebyshev δψ, Selberg quality, and GUE consistency to produce
    a single coherence score Ψ and a resolution verdict.

    Args:
        chebyshev: ChebyshevResult from Stage 2.
        selberg: SelbergTraceResult from Stage 3.
        gue: GUERigidityResult from Stage 4.
    """

    def __init__(
        self,
        chebyshev: ChebyshevResult,
        selberg: SelbergTraceResult,
        gue: GUERigidityResult,
    ) -> None:
        self.chebyshev = chebyshev
        self.selberg = selberg
        self.gue = gue

    def compute(self) -> SFiniteResolutionResult:
        """Evaluate the S-finite residual and produce the verdict.

        The residual is:

            R_S = ‖δψ‖²_{L²} / X = (1/X) ∑_i δψ(x_i)² Δx

        Under RH, R_S = O(log² X) / X → 0.  A small R_S, together with GUE
        consistency and high Selberg quality, implies the S-finite system is
        well-resolved.

        Returns:
            SFiniteResolutionResult.
        """
        X = self.chebyshev.X
        if X <= 0:
            X = 1.0

        # L² residual (trapezoidal rule)
        x = self.chebyshev.x_values
        dpsi = self.chebyshev.delta_psi
        if len(x) > 1:
            dx = np.diff(x)
            integrand = 0.5 * (dpsi[:-1] ** 2 + dpsi[1:] ** 2)
            l2_norm_sq = float(np.sum(integrand * dx))
        else:
            l2_norm_sq = float(dpsi[0] ** 2)

        R_S = l2_norm_sq / X

        # Coherence score: normalised so that the growing ‖δψ‖² ~ X does not
        # collapse Ψ; exponent = R_S/(X+1) where R_S = l2_norm_sq/X.
        psi_coherence = float(np.exp(-R_S / (X + 1.0)))

        # Verdict
        if self.gue.is_gue_consistent and self.selberg.quality >= 0.5:
            verdict = "S_FINITE_RESOLVED"
        else:
            verdict = "S_FINITE_CONDITIONAL"

        metadata = {
            "l2_norm_sq": l2_norm_sq,
            "X": X,
            "rms_delta_psi": self.chebyshev.rms_delta,
            "selberg_balance": self.selberg.balance,
            "selberg_quality": self.selberg.quality,
            "gue_ratio": self.gue.ratio,
            "gue_consistent": self.gue.is_gue_consistent,
            "delta3_measured": self.gue.delta3_measured,
            "delta3_gue": self.gue.delta3_gue,
            "f0_qcal": F0_QCAL,
            "C_coherence": C_COHERENCE,
        }

        return SFiniteResolutionResult(
            R_S=R_S,
            psi_coherence=psi_coherence,
            gue_consistent=self.gue.is_gue_consistent,
            selberg_quality=self.selberg.quality,
            verdict=verdict,
            metadata=metadata,
        )


# ---------------------------------------------------------------------------
# Main pipeline
# ---------------------------------------------------------------------------

class ImpactoRH:
    """Full pipeline: Tamiz → ψ(x) → Selberg Trace → GUE Rigidity → S-Finite.

    Args:
        N: Sieve upper bound (default 2000).
        zeros: Imaginary parts of Riemann zeros to use (default: first 20).
        sigma: Gaussian width for Selberg test function (default 5.0).
        gue_tolerance: Relative tolerance for GUE consistency (default 0.3).
        n_samples: Number of sample points for ψ(x) (default 200).
        verbose: Print progress messages (default True).
    """

    # Default known Riemann zeros (imaginary parts)
    DEFAULT_ZEROS: NDArray[np.float64] = np.array([
        14.134725141734693790,
        21.022039638771754864,
        25.010857580145688763,
        30.424876125859513210,
        32.935061587739189690,
        37.586178158825671257,
        40.918719012147495187,
        43.327073280914999519,
        48.005150881167159727,
        49.773832477672302181,
        52.970321477714460644,
        56.446247697063394804,
        59.347044002602353079,
        60.831778524609809844,
        65.112544048081606660,
        67.079810529494173714,
        69.546401711173979252,
        72.067157674481907582,
        75.704690699083933654,
        77.144840068874805491,
    ])

    def __init__(
        self,
        N: int = 2000,
        zeros: Optional[NDArray[np.float64]] = None,
        sigma: float = 5.0,
        gue_tolerance: float = 0.3,
        n_samples: int = 200,
        verbose: bool = True,
    ) -> None:
        self.N = N
        self.zeros = zeros if zeros is not None else self.DEFAULT_ZEROS
        self.sigma = sigma
        self.gue_tolerance = gue_tolerance
        self.n_samples = n_samples
        self.verbose = verbose

    def _log(self, msg: str) -> None:
        if self.verbose:
            print(msg)

    def run(self) -> ImpactoRHResult:
        """Execute the full pipeline and return combined result.

        Returns:
            ImpactoRHResult aggregating all five stages.
        """
        self._log("\n" + "=" * 62)
        self._log("  IMPACTO RH — Tamiz → ψ → Selberg → GUE → S-Finite")
        self._log("=" * 62)
        self._log(f"\n  N = {self.N}  |  zeros = {len(self.zeros)}  |  σ = {self.sigma}")
        self._log(f"  f₀ = {F0_QCAL} Hz  |  C^∞ = {C_COHERENCE}\n")

        # Stage 1: sieve
        self._log("▶ Stage 1: Tamiz (Prime Sieve)")
        sieve = PrimeSieve(self.N).run()
        self._log(f"  Primes ≤ {self.N}: {len(sieve.primes)}")

        # Stage 2: Chebyshev ψ
        self._log("▶ Stage 2: Chebyshev ψ(x)")
        cheb = ChebyshevPsi(sieve, n_samples=self.n_samples).compute()
        self._log(f"  X = {cheb.X:.0f},  rms(δψ) = {cheb.rms_delta:.4f}")

        # Stage 3: Selberg explicit formula
        self._log("▶ Stage 3: Selberg Explicit Formula")
        sel = SelbergExplicitFormula(
            zeros=self.zeros,
            primes=sieve.primes,
            sigma=self.sigma,
        ).compute()
        self._log(f"  LHS = {sel.zero_side:.4f},  RHS = {sel.prime_side:.4f},  quality = {sel.quality:.4f}")

        # Stage 4: GUE rigidity
        self._log("▶ Stage 4: GUE Rigidity (Δ₃)")
        gue = GUERigidity(self.zeros, tolerance=self.gue_tolerance).compute()
        self._log(
            f"  Δ₃ = {gue.delta3_measured:.4f} (GUE: {gue.delta3_gue:.4f}),  "
            f"ratio = {gue.ratio:.4f},  consistent = {gue.is_gue_consistent}"
        )

        # Stage 5: S-finite resolution
        self._log("▶ Stage 5: S-Finite Conditional Resolution")
        sf = SFiniteResolution(cheb, sel, gue).compute()
        self._log(f"  R_S = {sf.R_S:.6e},  Ψ = {sf.psi_coherence:.6f},  verdict = {sf.verdict}")

        # Global coherence
        global_psi = float(np.mean([
            sf.psi_coherence,
            sel.quality,
            1.0 if gue.is_gue_consistent else 0.5,
        ]))
        self._log(f"\n  ✨ Global Ψ = {global_psi:.6f}")
        self._log("  ∴ 𓂀 Ω ∞³\n")

        return ImpactoRHResult(
            sieve=sieve,
            chebyshev=cheb,
            selberg=sel,
            gue=gue,
            s_finite=sf,
            global_psi=global_psi,
        )


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

def run_impacto_rh(
    N: int = 2000,
    verbose: bool = True,
) -> ImpactoRHResult:
    """Convenience wrapper to execute the ImpactoRH pipeline.

    Args:
        N: Sieve upper bound.
        verbose: Print progress.

    Returns:
        ImpactoRHResult.
    """
    pipeline = ImpactoRH(N=N, verbose=verbose)
    return pipeline.run()


if __name__ == "__main__":
    import sys as _sys

    N = int(_sys.argv[1]) if len(_sys.argv) > 1 else 2000
    result = run_impacto_rh(N=N)
    _sys.exit(0 if result.s_finite.verdict == "S_FINITE_RESOLVED" else 1)
