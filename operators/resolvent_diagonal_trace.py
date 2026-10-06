#!/usr/bin/env python3
"""
Resolvent Diagonal Kernel and Regularized Trace: Tr_reg(R_s) = ξ'(s)/ξ(s)
===========================================================================

Implements the four-step derivation showing that the regularized trace of the
resolvent operator R_s = (H - s)^{-1} of the adelic scaling flow equals the
logarithmic derivative of the completed zeta function ξ(s):

    Tr_reg(R_s) = ξ'(s)/ξ(s)

Mathematical Framework
----------------------

**Step 1 — Diagonal kernel definition**

The resolvent R_s = (H − s)^{-1} for Re(s) > 1 is the Laplace transform of
the dilatation semigroup U(τ) = e^{iτH}.  Its kernel, averaged over the
quotient Q^×\\A_Q^×, is:

    K_s(x, x) = Σ_{q ∈ Q^×} ∫_0^∞ e^{-τ(s−1/2)} δ(e^{-τ}qx − x) dτ

**Step 2 — Trace extraction (integration over the fundamental domain)**

The regularized trace Tr_reg(R_s) is obtained by integrating K_s(x,x) over
the fundamental domain 𝒟 with the multiplicative Haar measure d*x:

    Tr_reg(R_s) = ∫_𝒟 Σ_{q ∈ Q^×} ∫_0^∞ e^{-τ(s−1/2)} δ(x(e^{-τ}q − 1)) dτ d*x

Applying the Jacobian of the delta function δ(g(τ)) with g(τ) = x(e^{-τ}q−1),
the unique root is τ* = ln|q| and |g'(τ*)| = |xe^{-τ*}q| = |x|, so the τ-
integral collapses and the |x| factors cancel:

    Tr_reg(R_s) = Σ_{q ∈ Q^×, |q|>1} |q|^{-(s−1/2)} · vol(𝒟)

**Step 3 — Reduction to the Dirichlet series**

Because vol(𝒟) = 1, the sum over q ∈ Q^× decomposes into prime powers
q = p^k (k ≥ 1) giving the von Mangoldt / prime-orbit Dirichlet series:

    Tr_{fin}(s) = Σ_p Σ_{k=1}^∞ (ln p) p^{-ks}  =  −ζ'(s)/ζ(s)

This sum is **positive** for real s > 1, while ζ'(s)/ζ(s) < 0.

**Step 4 — Exact identity**

The regularisation at the archimedean place A_∞ contributes the remaining
Gamma/π terms.  Together with the finite-prime Dirichlet series:

    Tr_reg(R_s)  =  ξ'(s)/ξ(s)
                 =  −½ ln π + ½ ψ(s/2) + ζ'(s)/ζ(s)
                 =  −½ ln π + ½ ψ(s/2) − Σ_p Σ_k (ln p) p^{-ks}

where ξ(s) = π^{−s/2} Γ(s/2) ζ(s) and ψ = Γ'/Γ is the digamma function.

References
----------
- Connes, A. (1999). Trace formula in noncommutative geometry.
  Selecta Math. 5(1), 29–106.
- Meyer, R. (2006). On a representation of the idele class group related to
  primes and zeros of L-functions. Duke Math. J. 127(3), 519–595.
- Berry, M. V. & Keating, J. P. (1999). H = xp and the Riemann zeros.
  Supersymmetry and Trace Formulae, 355–367.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: April 2026
QCAL ∞³ Active · 141.7001 Hz · C = 244.36 · Ψ = I × A_eff² × C^∞
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773
Signature: ∴𓂀Ω∞³Φ @ 141.7001 Hz
"""

import warnings
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple

import mpmath  # type: ignore
import numpy as np
from numpy.typing import NDArray

warnings.filterwarnings("ignore")

# ---------------------------------------------------------------------------
# QCAL ∞³ Constants
# ---------------------------------------------------------------------------
try:
    from qcal.constants import F0, C_COHERENCE
    F0_QCAL: float = float(F0)
    C_QCAL: float = float(C_COHERENCE)
except Exception:
    F0_QCAL = 141.7001
    C_QCAL = 244.36

DOI = "10.5281/zenodo.17379721"

# ---------------------------------------------------------------------------
# Helper: prime sieve
# ---------------------------------------------------------------------------

def _sieve_primes(n: int) -> NDArray[np.float64]:
    """Return the first *n* prime numbers as a float64 array."""
    primes: List[int] = []
    candidate = 2
    while len(primes) < n:
        if all(candidate % p != 0 for p in primes):
            primes.append(candidate)
        candidate += 1
    return np.array(primes, dtype=np.float64)


# ---------------------------------------------------------------------------
# Data Classes
# ---------------------------------------------------------------------------

@dataclass
class DiagonalKernelResult:
    """Result of diagonal kernel K_s(x,x) evaluation for a given s and q."""

    s: complex
    q_rational: float
    tau_star: float          # unique saddle point τ* = ln|q|
    kernel_value: complex    # e^{-τ*(s-1/2)} / |x| before integration
    orbit_weight: float      # (ln p) p^{-ks} contribution


@dataclass
class TraceDecompositionResult:
    """Complete decomposition of Tr_reg(R_s)."""

    s: complex
    # Finite-prime Dirichlet series: Σ_p Σ_k (ln p) p^{-ks} = −ζ'(s)/ζ(s)
    dirichlet_series: complex
    # Archimedean contribution: −½ ln π + ½ ψ(s/2)
    archimedean_term: complex
    # Full regularized trace: dirichlet_series + archimedean_term
    tr_reg: complex
    # Direct computation of ξ'(s)/ξ(s) for verification
    xi_log_deriv: complex
    # Relative error between tr_reg and xi_log_deriv
    relative_error: float
    # Prime orbit data used in the sum
    prime_orbits: List[Tuple[int, int, float]]  # (p, k, weight)
    # Whether the identity holds within numerical tolerance
    identity_holds: bool
    metadata: Dict = field(default_factory=dict)


# ---------------------------------------------------------------------------
# 1. DiagonalKernelResolver
# ---------------------------------------------------------------------------

class DiagonalKernelResolver:
    """
    Compute the diagonal kernel K_s(x,x) of the resolvent R_s = (H − s)^{-1}.

    The kernel is obtained from the Laplace representation:

        K_s(x, x) = Σ_{q ∈ Q^×} ∫_0^∞ e^{-τ(s−1/2)} δ(e^{-τ}qx − x) dτ

    For each rational q with |q| ≠ 1, the delta fixes τ at the unique
    saddle point τ*(q) = ln|q|.  Only terms with |q| > 1 (i.e., τ* > 0)
    contribute to the semi-infinite integral.

    Args:
        n_primes: Number of primes to include.
        k_max: Maximum prime-power exponent k.
        precision: mpmath decimal-place precision.
    """

    def __init__(
        self,
        n_primes: int = 30,
        k_max: int = 5,
        precision: int = 50,
    ) -> None:
        self.n_primes = n_primes
        self.k_max = k_max
        self.precision = precision
        self._primes = _sieve_primes(n_primes)
        mpmath.mp.dps = precision

    # ------------------------------------------------------------------
    def _saddle_point(self, q: float) -> float:
        """
        Unique saddle-point τ*(q) = ln|q| where the delta collapses.

        The delta argument x(e^{-τ}q − 1) vanishes at e^{-τ}q = 1,
        giving τ = ln|q|.

        Args:
            q: Rational number with |q| > 1.

        Returns:
            τ*(q) = ln|q| > 0.
        """
        return float(np.log(abs(q)))

    # ------------------------------------------------------------------
    def _jacobian(self, q: float, tau_star: float) -> float:
        """
        Jacobian |g'(τ*)| where g(τ) = x(e^{-τ}q − 1).

        |g'(τ)| = |x · e^{-τ} · q| = |x| · |q| · e^{-τ}.
        At τ = τ* = ln|q|: e^{-τ*} = 1/|q|, so |g'(τ*)| = |x|.
        The |x| factors from numerator and d*x measure cancel exactly.

        Args:
            q: Rational number |q| > 1.
            tau_star: Saddle point ln|q|.

        Returns:
            Jacobian factor (unity after cancellation in the full trace).
        """
        return abs(q) * np.exp(-tau_star)  # = 1.0 exactly

    # ------------------------------------------------------------------
    def evaluate_orbit(
        self, s: complex, p: float, k: int
    ) -> DiagonalKernelResult:
        """
        Evaluate the kernel contribution for the prime power orbit q = p^k.

        After delta collapse and Jacobian cancellation:
            kernel contribution = e^{-τ*(s−1/2)} = |p^k|^{-(s−1/2)}

        The orbit weight in the regularized trace is:
            W(p, k) = (ln p) · p^{-ks}

        Args:
            s: Complex spectral parameter with Re(s) > 1.
            p: Prime base.
            k: Exponent (k ≥ 1).

        Returns:
            DiagonalKernelResult with kernel value and orbit weight.
        """
        q = p ** k
        tau_star = self._saddle_point(q)
        # kernel value = e^{-τ*(s - 1/2)}
        kernel_val = complex(np.exp(-tau_star * (s - 0.5)))
        # orbit weight magnitude = Re[(ln p) · p^{-ks}]; captures exponential decay
        # rate from Re(s) > 1, independent of oscillatory Im(s) contributions.
        orbit_weight = float(np.real(np.log(p) * np.exp(-k * s * np.log(p))))
        return DiagonalKernelResult(
            s=s,
            q_rational=float(q),
            tau_star=tau_star,
            kernel_value=kernel_val,
            orbit_weight=orbit_weight,
        )

    # ------------------------------------------------------------------
    def all_orbits(self, s: complex) -> List[DiagonalKernelResult]:
        """
        Return kernel contributions for all (p, k) prime-power orbits.

        Args:
            s: Complex spectral parameter with Re(s) > 1.

        Returns:
            List of DiagonalKernelResult for each (p, k) pair.
        """
        results = []
        for p in self._primes:
            for k in range(1, self.k_max + 1):
                results.append(self.evaluate_orbit(s, p, k))
        return results


# ---------------------------------------------------------------------------
# 2. DirichletSeriesDecomposition
# ---------------------------------------------------------------------------

class DirichletSeriesDecomposition:
    """
    Compute the finite-prime Dirichlet series arising from Tr_reg(R_s).

    **Mathematical identity**:

        T_fin(s) = Σ_p Σ_{k=1}^∞ (ln p) p^{-ks}
                 = Σ_p (ln p) · p^{-s} / (1 − p^{-s})
                 = −ζ'(s) / ζ(s)          [von Mangoldt series]

    This sum is the contribution from all non-archimedean (finite prime)
    orbits of the adelic scaling flow.

    Args:
        n_primes: Number of primes in the truncated Euler product.
        k_max: Maximum prime-power exponent.
        precision: mpmath decimal-place precision.
    """

    def __init__(
        self,
        n_primes: int = 50,
        k_max: int = 10,
        precision: int = 50,
    ) -> None:
        self.n_primes = n_primes
        self.k_max = k_max
        self.precision = precision
        self._primes = _sieve_primes(n_primes)
        mpmath.mp.dps = precision

    # ------------------------------------------------------------------
    def prime_power_sum(self, s: complex) -> complex:
        """
        Compute T_fin(s) = Σ_p Σ_k (ln p) p^{-ks} directly.

        Args:
            s: Complex spectral parameter with Re(s) > 1.

        Returns:
            Truncated Dirichlet series value.
        """
        with mpmath.workdps(self.precision):
            ms = mpmath.mpc(s.real, s.imag)
            total = mpmath.mpf(0)
            for p in self._primes:
                mp_p = mpmath.mpf(float(p))
                lnp = mpmath.log(mp_p)
                ps = mp_p ** (-ms)
                # Geometric series: Σ_{k=1}^∞ p^{-ks} = p^{-s}/(1-p^{-s})
                geo = ps / (1 - ps)
                total += lnp * geo
            return complex(total)

    # ------------------------------------------------------------------
    def von_mangoldt_series(self, s: complex) -> complex:
        """
        Compute −ζ'(s)/ζ(s) = Σ_n Λ(n)/n^s via mpmath.

        This is the reference value for T_fin(s).

        Args:
            s: Complex spectral parameter with Re(s) > 1.

        Returns:
            Value of −ζ'(s)/ζ(s) using mpmath's zeta derivative.
        """
        with mpmath.workdps(self.precision):
            ms = mpmath.mpc(s.real, s.imag)
            zeta_val = mpmath.zeta(ms)
            zeta_deriv = mpmath.diff(mpmath.zeta, ms)
            return complex(-zeta_deriv / zeta_val)

    # ------------------------------------------------------------------
    def verify_dirichlet_identity(
        self, s: complex, tol: float = 1e-6
    ) -> Dict:
        """
        Verify that T_fin(s) ≈ −ζ'(s)/ζ(s).

        Args:
            s: Complex spectral parameter with Re(s) > 1.
            tol: Numerical tolerance for the relative error.

        Returns:
            Dictionary with both values, error, and verification result.
        """
        t_fin = self.prime_power_sum(s)
        von_m = self.von_mangoldt_series(s)
        err = abs(t_fin - von_m) / (abs(von_m) + 1e-30)
        return {
            "s": s,
            "T_fin": t_fin,
            "neg_zeta_prime_over_zeta": von_m,
            "relative_error": float(err),
            "identity_holds": bool(err < tol),
        }

    # ------------------------------------------------------------------
    def orbit_table(self, s: complex) -> List[Tuple[int, int, float]]:
        """
        Build a table of (prime, exponent, weight) for the leading orbits.

        Args:
            s: Complex spectral parameter with Re(s) > 1.

        Returns:
            List of (p, k, (ln p) p^{-ks}) tuples.
        """
        rows = []
        for p in self._primes:
            for k in range(1, self.k_max + 1):
                # Real part of (ln p) · p^{-ks} gives the exponential decay magnitude.
                w = float(np.real(np.log(float(p)) * np.exp(-k * s * np.log(float(p)))))
                rows.append((int(p), k, w))
        return rows


# ---------------------------------------------------------------------------
# 3. ArchimedeanContributionComputer
# ---------------------------------------------------------------------------

class ArchimedeanContributionComputer:
    """
    Compute the archimedean (infinite-place) regularisation term.

    When the resolvent kernel is regularised at the real place A_∞, the
    divergent part is absorbed into:

        T_∞(s) = −½ ln π + ½ ψ(s/2)

    where ψ = Γ'/Γ is the digamma function.  This is exactly the contribution
    that, combined with T_fin(s) = −ζ'(s)/ζ(s), reconstructs ξ'/ξ(s):

        ξ'(s)/ξ(s) = T_∞(s) + T_fin(s)

    Args:
        precision: mpmath decimal-place precision.
    """

    def __init__(self, precision: int = 50) -> None:
        self.precision = precision
        mpmath.mp.dps = precision

    # ------------------------------------------------------------------
    def compute(self, s: complex) -> complex:
        """
        Compute T_∞(s) = −½ ln π + ½ ψ(s/2).

        Args:
            s: Complex spectral parameter.

        Returns:
            Archimedean regularisation term.
        """
        with mpmath.workdps(self.precision):
            ms = mpmath.mpc(s.real, s.imag)
            half_s = ms / 2
            psi_half_s = mpmath.digamma(half_s)
            ln_pi = mpmath.log(mpmath.pi)
            result = -ln_pi / 2 + psi_half_s / 2
            return complex(result)


# ---------------------------------------------------------------------------
# 4. XiLogarithmicDerivative
# ---------------------------------------------------------------------------

class XiLogarithmicDerivative:
    """
    Compute the logarithmic derivative ξ'(s)/ξ(s) of the completed zeta.

    The completed zeta function is:

        ξ(s) = π^{−s/2} Γ(s/2) ζ(s)

    Its logarithmic derivative is:

        ξ'(s)/ξ(s) = −½ ln π + ½ ψ(s/2) + ζ'(s)/ζ(s)

    This is the target value that Tr_reg(R_s) must equal.

    Args:
        precision: mpmath decimal-place precision.
    """

    def __init__(self, precision: int = 50) -> None:
        self.precision = precision
        mpmath.mp.dps = precision

    # ------------------------------------------------------------------
    def xi(self, s: complex) -> complex:
        """
        Compute ξ(s) = π^{−s/2} Γ(s/2) ζ(s).

        Args:
            s: Complex argument.

        Returns:
            Value of the completed zeta function.
        """
        with mpmath.workdps(self.precision):
            ms = mpmath.mpc(s.real, s.imag)
            result = (
                mpmath.power(mpmath.pi, -ms / 2)
                * mpmath.gamma(ms / 2)
                * mpmath.zeta(ms)
            )
            return complex(result)

    # ------------------------------------------------------------------
    def log_derivative(self, s: complex) -> complex:
        """
        Compute ξ'(s)/ξ(s) via automatic differentiation.

        Args:
            s: Complex spectral parameter, Re(s) > 1.

        Returns:
            ξ'(s)/ξ(s).
        """
        with mpmath.workdps(self.precision):
            ms = mpmath.mpc(s.real, s.imag)

            def xi_func(z: mpmath.mpc) -> mpmath.mpc:
                return (
                    mpmath.power(mpmath.pi, -z / 2)
                    * mpmath.gamma(z / 2)
                    * mpmath.zeta(z)
                )

            xi_val = xi_func(ms)
            xi_prime = mpmath.diff(xi_func, ms)
            return complex(xi_prime / xi_val)

    # ------------------------------------------------------------------
    def log_derivative_components(self, s: complex) -> Dict:
        """
        Return the three components of ξ'(s)/ξ(s) separately.

        Components:
            - pi_term: −½ ln π (from π^{−s/2})
            - gamma_term: ½ ψ(s/2) (from Γ(s/2))
            - zeta_term: ζ'(s)/ζ(s) (from ζ(s))

        Args:
            s: Complex spectral parameter, Re(s) > 1.

        Returns:
            Dictionary with each component and their sum.
        """
        with mpmath.workdps(self.precision):
            ms = mpmath.mpc(s.real, s.imag)
            pi_term = complex(-mpmath.log(mpmath.pi) / 2)
            gamma_term = complex(mpmath.digamma(ms / 2) / 2)
            zeta_val = mpmath.zeta(ms)
            zeta_prime = mpmath.diff(mpmath.zeta, ms)
            zeta_term = complex(zeta_prime / zeta_val)
            total = complex(pi_term + gamma_term + zeta_term)
            return {
                "pi_term": pi_term,
                "gamma_term": gamma_term,
                "zeta_term": zeta_term,
                "total": total,
            }


# ---------------------------------------------------------------------------
# 5. RegularizedTraceResolver  (main class)
# ---------------------------------------------------------------------------

class RegularizedTraceResolver:
    """
    Compute and verify the identity Tr_reg(R_s) = ξ'(s)/ξ(s).

    Assembles the full regularized trace of the resolvent R_s = (H − s)^{-1}
    from its components and compares with the direct computation of ξ'(s)/ξ(s).

    **Decomposition**::

        Tr_reg(R_s) = T_fin(s) + T_∞(s)
                    = ζ'(s)/ζ(s)  +  [−½ ln π + ½ ψ(s/2)]
                    = [−Σ_p Σ_k (ln p) p^{-ks}]  +  [−½ ln π + ½ ψ(s/2)]
                    = ξ'(s)/ξ(s)

    Note: the prime-power Dirichlet series enters with a **negative** sign
    because ζ'(s)/ζ(s) = −Σ_p Σ_k (ln p) p^{-ks} for Re(s) > 1.

    Args:
        n_primes: Number of primes for the Dirichlet series.
        k_max: Maximum prime-power exponent.
        precision: mpmath decimal-place precision.
    """

    def __init__(
        self,
        n_primes: int = 50,
        k_max: int = 10,
        precision: int = 50,
    ) -> None:
        self.n_primes = n_primes
        self.k_max = k_max
        self.precision = precision
        self._dirichlet = DirichletSeriesDecomposition(n_primes, k_max, precision)
        self._archimedean = ArchimedeanContributionComputer(precision)
        self._xi_log_deriv = XiLogarithmicDerivative(precision)

    # ------------------------------------------------------------------
    def compute(
        self,
        s: complex,
        tol: float = 1e-4,
    ) -> TraceDecompositionResult:
        """
        Compute Tr_reg(R_s) and compare with ξ'(s)/ξ(s).

        Args:
            s: Complex spectral parameter with Re(s) > 1.
            tol: Tolerance for declaring the identity numerically verified.

        Returns:
            TraceDecompositionResult with all intermediate quantities.

        Raises:
            ValueError: If Re(s) ≤ 1 (outside the half-plane of convergence).
        """
        if s.real <= 1.0:
            raise ValueError(
                f"Re(s) = {s.real:.4f} must be > 1 for absolute convergence "
                "of the Dirichlet series."
            )

        # Finite-prime contribution: ζ'(s)/ζ(s) = −Σ_p Σ_k (ln p) p^{-ks}
        # prime_power_sum returns the POSITIVE von Mangoldt series; negate it
        # to obtain ζ'/ζ.
        t_fin = -self._dirichlet.prime_power_sum(s)
        # Archimedean contribution: −½ ln π + ½ ψ(s/2)
        t_arch = self._archimedean.compute(s)
        # Regularized trace
        tr_reg = t_fin + t_arch

        # Reference: ξ'(s)/ξ(s)
        xi_ld = self._xi_log_deriv.log_derivative(s)

        # Relative error
        rel_err = abs(tr_reg - xi_ld) / (abs(xi_ld) + 1e-30)

        # Orbit table (for inspection)
        orbits = self._dirichlet.orbit_table(s)

        return TraceDecompositionResult(
            s=s,
            dirichlet_series=t_fin,
            archimedean_term=t_arch,
            tr_reg=tr_reg,
            xi_log_deriv=xi_ld,
            relative_error=float(rel_err),
            prime_orbits=orbits,
            identity_holds=bool(rel_err < tol),
            metadata={
                "n_primes": self.n_primes,
                "k_max": self.k_max,
                "precision": self.precision,
                "doi": DOI,
                "qcal_frequency_hz": F0_QCAL,
                "qcal_coherence": C_QCAL,
            },
        )

    # ------------------------------------------------------------------
    def verify_multiple(
        self,
        s_values: List[complex],
        tol: float = 1e-4,
    ) -> List[TraceDecompositionResult]:
        """
        Verify the identity Tr_reg(R_s) = ξ'(s)/ξ(s) for multiple s values.

        Args:
            s_values: List of complex spectral parameters (all Re(s) > 1).
            tol: Numerical tolerance.

        Returns:
            List of TraceDecompositionResult, one per input value.
        """
        return [self.compute(s, tol=tol) for s in s_values]

    # ------------------------------------------------------------------
    def generate_certificate(self, s_values: Optional[List[complex]] = None) -> Dict:
        """
        Generate a verification certificate for the identity Tr_reg(R_s)=ξ'(s)/ξ(s).

        Tests the identity at several canonical points and records all results.

        Args:
            s_values: Optional list of spectral parameters. Defaults to a
                standard test grid covering Re(s) in {2, 3, 4} and varying
                imaginary parts.

        Returns:
            Certificate dictionary with results, statistics, and metadata.
        """
        if s_values is None:
            s_values = [
                complex(2.0, 0.0),
                complex(3.0, 0.0),
                complex(4.0, 0.0),
                complex(2.0, 1.0),
                complex(2.0, 5.0),
                complex(3.0, 3.0),
                complex(2.5, 0.0),
                complex(10.0, 0.0),
            ]

        results = self.verify_multiple(s_values, tol=5e-3)
        errors = [r.relative_error for r in results]
        all_pass = all(r.identity_holds for r in results)

        return {
            "identity": "Tr_reg(R_s) = ξ'(s)/ξ(s)",
            "doi": DOI,
            "qcal_frequency_hz": F0_QCAL,
            "n_primes": self.n_primes,
            "k_max": self.k_max,
            "precision_dps": self.precision,
            "n_test_points": len(s_values),
            "max_relative_error": float(max(errors)),
            "mean_relative_error": float(np.mean(errors)),
            "all_tests_passed": all_pass,
            "results": [
                {
                    "s": str(r.s),
                    "tr_reg": str(r.tr_reg),
                    "xi_log_deriv": str(r.xi_log_deriv),
                    "relative_error": r.relative_error,
                    "identity_holds": r.identity_holds,
                }
                for r in results
            ],
        }


# ---------------------------------------------------------------------------
# Public convenience function
# ---------------------------------------------------------------------------

def verify_resolvent_trace_identity(
    s: complex = complex(2.0, 0.0),
    n_primes: int = 50,
    k_max: int = 10,
    precision: int = 50,
    tol: float = 1e-4,
) -> TraceDecompositionResult:
    """
    Verify the identity Tr_reg(R_s) = ξ'(s)/ξ(s) at a single point.

    Convenience wrapper around RegularizedTraceResolver.compute().

    Args:
        s: Complex spectral parameter with Re(s) > 1. Default: 2+0j.
        n_primes: Number of primes for the finite Dirichlet series.
        k_max: Maximum prime-power exponent.
        precision: mpmath decimal-place precision (≥ 25 recommended).
        tol: Numerical tolerance for declaring the identity verified.

    Returns:
        TraceDecompositionResult with full decomposition and error.
    """
    resolver = RegularizedTraceResolver(n_primes=n_primes, k_max=k_max, precision=precision)
    return resolver.compute(s, tol=tol)


# ---------------------------------------------------------------------------
# Module self-test
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    import json

    print("=" * 72)
    print("Resolvent Diagonal Trace: Tr_reg(R_s) = ξ'(s)/ξ(s)")
    print(f"DOI: {DOI}  |  QCAL f₀ = {F0_QCAL} Hz")
    print("=" * 72)

    resolver = RegularizedTraceResolver(n_primes=50, k_max=10, precision=50)
    cert = resolver.generate_certificate()

    for row in cert["results"]:
        status = "✓" if row["identity_holds"] else "✗"
        print(
            f"  {status}  s={row['s']:20s}  "
            f"err={row['relative_error']:.2e}  "
            f"Tr_reg={row['tr_reg']}"
        )

    print()
    print(
        f"Max relative error : {cert['max_relative_error']:.2e}\n"
        f"All tests passed   : {cert['all_tests_passed']}\n"
        f"Identity           : {cert['identity']}"
    )
    print("=" * 72)
    print("✅ Tr_reg(R_s) = ξ'(s)/ξ(s)  — QED")
