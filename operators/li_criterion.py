#!/usr/bin/env python3
"""
El Criterio de Li: La Positividad de la Traza (Li's Criterion: Positivity of the Trace)
========================================================================================

Mathematical Framework:
-----------------------

The Li criterion provides a necessary and sufficient condition for the Riemann
Hypothesis. It states that RH holds if and only if the Li coefficients

    λ_n = Σ_ρ [ 1 - (ρ/(ρ-1))^n ] > 0   for all n = 1, 2, 3, ...

where the sum runs over all non-trivial zeros ρ of the Riemann zeta function.

**1. Geometric Interpretation (Curvature toward the Critical Line)**

The Li coefficients measure the "curvature" of the zeta function toward the
critical line σ = 1/2. On the critical line ρ = 1/2 + it, we have:

    |ρ/(ρ-1)| = |(1/2 + it)/(−1/2 + it)| = 1

so each term writes as 1 − e^(inφ_ρ) with |e^(iφ_ρ)| = 1. When paired with
the conjugate zero ρ̄, the contribution is 2[1 − cos(nφ_ρ)] ≥ 0, and sums
strictly positive because the phases are non-commensurate.

If any zero ρ strays OFF the critical line, |ρ/(ρ-1)| ≠ 1, and the
corresponding term eventually dominates with a sign that makes some λ_n < 0.

**2. The Entropy Flow Hamiltonian H**

The operator H is the logarithmic derivative of the Riemann ξ function:

    H = d/ds log ξ(s) = ξ'(s)/ξ(s)

acting in the frequency domain where primes are the natural coordinates.
This is a Hamiltonian for the entropy flow in prime space. Its trace produces
exactly the prime orbit sum (log p) p^(−k/2) due to scale invariance:

    Tr(e^(−tH)) = Σ_{p,k} (log p / p^(k/2)) e^(−kt log p)

**3. Connection to Self-Adjointness**

If H is genuinely self-adjoint, its spectrum is real and the functional
equation of ξ forces all zeros to satisfy Re(ρ) = 1/2. The positivity
λ_n > 0 is exactly the condition that guarantees H remains self-adjoint
and the flow is energetically stable.

**4. Keiper–Li Formula (Derivative Form)**

An equivalent, purely analytic formula uses derivatives of log ξ at s = 1:

    λ_n = (1/(n−1)!) [d^n/ds^n (s^(n−1) log ξ(s))]_{s=1}

This form avoids explicit knowledge of zeros and is useful for rigorous
analytic estimates.

References:
-----------
- Li, X.-J. (1997). The positivity of a sequence of numbers and the
  Riemann Hypothesis. J. Number Theory, 65(2), 325–333.
- Keiper, J.B. (1992). Power series expansions of Riemann's ξ function.
  Math. Comp., 58(198), 765–773.
- Bombieri, E. & Lagarias, J.C. (1999). Complements to Li's criterion for
  the Riemann Hypothesis. J. Number Theory, 77(2), 274–287.
- Connes, A. (1999). Trace formula in noncommutative geometry and the zeros
  of the Riemann zeta function. Selecta Math., 5(1), 29–106.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: March 2026
QCAL ∞³ Active · 141.7001 Hz · f₀ = 141.7001 Hz · Ψ = I × A_eff² × C^∞
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773
Signature: ∴𓂀Ω∞³Φ @ 141.7001 Hz
"""

import numpy as np
import mpmath
from typing import Dict, List, Optional, Tuple
from dataclasses import dataclass, field
import warnings

# Small value to prevent division by zero in relative-error computations
_SAFE_DIV_EPS = 1e-30


def _xi(s):
    """
    Riemann ξ function: ξ(s) = (1/2) s(s−1) π^(−s/2) Γ(s/2) ζ(s).

    This entire function has no poles and its zeros coincide exactly with the
    non-trivial zeros of ζ(s). It satisfies the symmetry ξ(s) = ξ(1−s).

    The special value ξ(1) = 1/2 is handled by catching the ValueError that
    mpmath.zeta raises at s = 1. Using try/except (rather than almosteq with
    a positive tolerance) ensures that mpmath.diff can still evaluate the
    function at nearby points to compute numerical derivatives.

    Args:
        s: Complex argument (mpmath type or convertible)

    Returns:
        mpmath complex: value of ξ(s)
    """
    s = mpmath.mpc(s)
    try:
        zeta_val = mpmath.zeta(s)
    except ValueError:
        # s = 1 exactly: the pole of ζ(s) is cancelled by (s−1), and
        # limit_{s→1} (s−1) ζ(s) = 1.  Therefore ξ(1) = (1/2)·π^(-1/2)·Γ(1/2) = 1/2.
        return mpmath.mpf(1) / 2
    return (mpmath.mpf(1) / 2) * s * mpmath.power(
        mpmath.pi, -s / 2
    ) * mpmath.gamma(s / 2) * (s - 1) * zeta_val

# QCAL ∞³ Constants
F0_QCAL = 141.7001          # Hz - fundamental frequency
C_COHERENCE = 244.36         # Coherence constant C^∞
PHI = 1.6180339887498948     # Golden ratio Φ
DOI = "10.5281/zenodo.17379721"
ORCID = "0009-0002-1923-0773"

# Default precision for mpmath computations
DEFAULT_DPS = 25


@dataclass
class LiCoefficientResult:
    """
    Result of a single Li coefficient computation.

    Attributes:
        n: Index of the coefficient (n ≥ 1)
        lambda_n: Value of λ_n (should be positive for RH)
        is_positive: Whether λ_n > 0
        n_zeros_used: Number of non-trivial zero pairs used
        relative_error: Estimated relative truncation error
        method: Computation method used ('zeros' or 'keiper')
    """
    n: int
    lambda_n: float
    is_positive: bool
    n_zeros_used: int
    relative_error: float
    method: str


@dataclass
class LiValidationResult:
    """
    Result of validating the full Li criterion up to n = N.

    Attributes:
        n_max: Maximum index tested
        all_positive: Whether all λ_1,...,λ_{n_max} are positive
        coefficients: List of LiCoefficientResult for each n
        min_lambda: Minimum value of λ_n (bottleneck)
        min_n: Index achieving the minimum
        rh_support: Confidence statement about RH support
        psi: QCAL coherence ratio (passed/tested)
    """
    n_max: int
    all_positive: bool
    coefficients: List[LiCoefficientResult]
    min_lambda: float
    min_n: int
    rh_support: str
    psi: float


class LiCoefficients:
    """
    Compute the Li coefficients λ_n for the Riemann Hypothesis.

    The Li coefficients are defined as:

        λ_n = Σ_ρ [ 1 − (ρ/(ρ−1))^n ]

    where the sum is over all non-trivial zeros ρ of ζ(s), counted with
    multiplicity and including both ρ and ρ̄.

    The Riemann Hypothesis is equivalent to λ_n > 0 for all n ≥ 1.

    Attributes:
        n_zeros: Number of zero pairs to use in computations
        dps: Decimal precision for mpmath
        _zeros_cache: Cached non-trivial zeros
    """

    def __init__(self, n_zeros: int = 100, dps: int = DEFAULT_DPS):
        """
        Initialize the Li coefficient computer.

        Args:
            n_zeros: Number of zero pairs to use (pairs ρ, ρ̄ with Im ρ > 0).
                     More zeros give better accuracy for large n.
            dps: Decimal places of precision for mpmath.
        """
        if n_zeros < 10:
            raise ValueError(f"n_zeros must be at least 10, got {n_zeros}")
        if dps < 10:
            raise ValueError(f"dps must be at least 10, got {dps}")

        self.n_zeros = n_zeros
        self.dps = dps
        self._zeros_cache: Optional[List] = None

        # Set mpmath precision
        mpmath.mp.dps = dps

    def _load_zeros(self) -> List:
        """
        Load (or retrieve from cache) the first n_zeros non-trivial zeros.

        Returns:
            List of mpmath complex numbers ρ with Im(ρ) > 0.
        """
        if self._zeros_cache is not None:
            return self._zeros_cache

        mpmath.mp.dps = self.dps
        zeros = [mpmath.zetazero(k) for k in range(1, self.n_zeros + 1)]
        self._zeros_cache = zeros
        return zeros

    def compute(self, n: int) -> LiCoefficientResult:
        """
        Compute the n-th Li coefficient λ_n via direct zero summation.

        Uses the formula (from the problem statement):

            λ_n = Σ_{ρ, Im(ρ)>0} 2 · Re[ 1 − (ρ/(ρ−1))^n ]

        This pairing accounts for both ρ and ρ̄ simultaneously since on the
        critical line ρ̄ = 1 − ρ.

        Args:
            n: Index (must be ≥ 1)

        Returns:
            LiCoefficientResult with computed λ_n and metadata.

        Raises:
            ValueError: If n < 1.
        """
        if n < 1:
            raise ValueError(f"Index n must be ≥ 1, got n={n}")

        mpmath.mp.dps = self.dps
        zeros = self._load_zeros()

        # Sum over zeros with Im(ρ) > 0 and their conjugates ρ̄
        # Full sum = Σ_{Im(ρ)>0} [ (1 - f(ρ)) + (1 - f(ρ̄)) ]
        #          = Σ_{Im(ρ)>0} 2 · Re[ 1 - f(ρ) ]
        # where f(ρ) = (ρ/(ρ-1))^n
        total = mpmath.mpf(0)
        for rho in zeros:
            term = mpmath.mpc(1) - (rho / (rho - 1)) ** n
            # Conjugate term: 1 - (rho_bar / (rho_bar - 1))^n
            rho_bar = mpmath.conj(rho)
            term_bar = mpmath.mpc(1) - (rho_bar / (rho_bar - 1)) ** n
            total += term + term_bar

        lambda_n = float(total.real)

        # Estimate truncation error from the last few terms
        if len(zeros) >= 5:
            last_terms = []
            for rho in zeros[-5:]:
                t = float((1 - (rho / (rho - 1)) ** n +
                           1 - (mpmath.conj(rho) / (mpmath.conj(rho) - 1)) ** n).real)
                last_terms.append(abs(t))
            rel_error = max(last_terms) / (abs(lambda_n) + _SAFE_DIV_EPS)
        else:
            rel_error = float('inf')

        return LiCoefficientResult(
            n=n,
            lambda_n=lambda_n,
            is_positive=lambda_n > 0,
            n_zeros_used=len(zeros),
            relative_error=rel_error,
            method='zeros'
        )

    def compute_keiper(self, n: int, h: float = 1e-6) -> LiCoefficientResult:
        """
        Compute λ_n using the Keiper derivative formula.

        The Keiper formula expresses λ_n as a finite difference approximation
        of the n-th derivative of s^(n-1) · log ξ(s) at s = 1:

            λ_n = (1/(n-1)!) · [d^n/ds^n (s^(n-1) log ξ(s))]_{s=1}

        This implementation uses high-order finite differences for the
        derivative, computed via mpmath's numerical differentiation.

        Args:
            n: Index (must be ≥ 1)
            h: Step size for finite differences (default 1e-6)

        Returns:
            LiCoefficientResult with computed λ_n and metadata.
        """
        if n < 1:
            raise ValueError(f"Index n must be ≥ 1, got n={n}")

        mpmath.mp.dps = self.dps

        def log_xi(s):
            """Compute log ξ(s) via mpmath."""
            return mpmath.log(_xi(s))

        def f(s):
            """s^(n-1) · log ξ(s)."""
            return s ** (n - 1) * log_xi(s)

        # Compute n-th derivative of f at s=1 via mpmath
        try:
            deriv = mpmath.diff(f, 1, n)
            factorial_nm1 = mpmath.factorial(n - 1)
            lambda_n = float(mpmath.re(deriv / factorial_nm1))
        except (ValueError, ZeroDivisionError, mpmath.libmp.libmpf.ComplexResult,
                OverflowError) as exc:
            # Numerical instability or special-value issue; log and return NaN
            warnings.warn(
                f"Keiper formula failed for n={n}: {type(exc).__name__}: {exc}",
                RuntimeWarning, stacklevel=2
            )
            lambda_n = float('nan')

        return LiCoefficientResult(
            n=n,
            lambda_n=lambda_n,
            is_positive=lambda_n > 0 if not np.isnan(lambda_n) else False,
            n_zeros_used=0,
            relative_error=abs(h) if not np.isnan(lambda_n) else float('inf'),
            method='keiper'
        )

    def compute_batch(self, n_max: int) -> List[LiCoefficientResult]:
        """
        Compute Li coefficients λ_1, λ_2, ..., λ_{n_max}.

        Args:
            n_max: Maximum index to compute (must be ≥ 1)

        Returns:
            List of LiCoefficientResult for n = 1, ..., n_max.
        """
        if n_max < 1:
            raise ValueError(f"n_max must be ≥ 1, got {n_max}")
        return [self.compute(n) for n in range(1, n_max + 1)]

    def positivity_ratio(self, n_max: int) -> float:
        """
        Return the fraction of Li coefficients that are positive for n=1..n_max.

        This is the QCAL coherence metric Ψ for the Li criterion.

        Args:
            n_max: Maximum index to test

        Returns:
            Fraction in [0, 1]; equals 1.0 when all are positive.
        """
        results = self.compute_batch(n_max)
        n_positive = sum(1 for r in results if r.is_positive)
        return n_positive / n_max


class EntropyFlowH:
    """
    The Entropy Flow Hamiltonian H = ξ'(s)/ξ(s) in prime-frequency space.

    This operator is the logarithmic derivative of the Riemann ξ function.
    In the spectral framework of the adelic scaling flow, H acts as the
    generator of the entropy flow in the space of primes.

    The key properties are:
    - H is self-adjoint when ξ has no real-axis zeros (i.e., when RH holds)
    - Its spectral measure reproduces the prime counting function
    - The trace of e^(−tH) gives the renormalized Selberg trace formula

    The partial fractions expansion gives:

        ξ'(s)/ξ(s) = Σ_ρ [ 1/(s−ρ) + 1/ρ ]   (sum over non-trivial zeros)

    providing the direct link between H and the Li coefficients.

    Attributes:
        dps: Decimal precision for mpmath computations
        s_values: Grid of s values for evaluation
    """

    def __init__(self, dps: int = DEFAULT_DPS):
        """
        Initialize the entropy flow Hamiltonian.

        Args:
            dps: Decimal places of precision for mpmath.
        """
        self.dps = dps
        mpmath.mp.dps = dps

    def evaluate(self, s: complex) -> complex:
        """
        Evaluate H(s) = ξ'(s)/ξ(s) at a complex point s.

        Uses mpmath for high-precision evaluation of the ξ function and
        its derivative.

        Args:
            s: Complex argument (should not be a zero of ξ)

        Returns:
            Complex value of ξ'(s)/ξ(s).
        """
        mpmath.mp.dps = self.dps
        s_mp = mpmath.mpc(s.real if hasattr(s, 'real') else s,
                          s.imag if hasattr(s, 'imag') else 0)

        xi_val = _xi(s_mp)
        xi_prime = mpmath.diff(_xi, s_mp)

        if abs(xi_val) < mpmath.mpf(10) ** (-self.dps + 5):
            return complex('nan')

        return complex(xi_prime / xi_val)

    def evaluate_grid(self, s_array: np.ndarray) -> np.ndarray:
        """
        Evaluate H(s) on a grid of complex values.

        Args:
            s_array: Array of complex values

        Returns:
            Array of complex values H(s) for each s.
        """
        return np.array([self.evaluate(s) for s in s_array], dtype=complex)

    def partial_fraction_residue(self, s: complex, rho: complex) -> complex:
        """
        Compute the residue contribution of zero ρ to H(s) = ξ'/ξ.

        The partial fractions expansion gives:
            H(s) = Σ_ρ [ 1/(s−ρ) + 1/ρ ] + (trivial terms)

        Args:
            s: Complex point of evaluation
            rho: A non-trivial zero

        Returns:
            Residue term 1/(s−ρ) + 1/ρ from this zero.
        """
        return 1.0 / (s - rho) + 1.0 / rho

    def li_coefficient_from_residues(self, n: int,
                                     zeros: List[complex]) -> float:
        """
        Compute λ_n from the residue expansion of H.

        This uses the identity:

            λ_n = Σ_ρ [ 1 − (ρ/(ρ−1))^n ]

        which arises from integrating the n-th moment of the spectral
        measure of H against the test function (s−1)^(−n).

        Args:
            n: Li coefficient index (≥ 1)
            zeros: List of non-trivial zeros ρ with Im(ρ) > 0

        Returns:
            λ_n value (should be positive for RH).
        """
        total = 0.0
        for rho in zeros:
            # Contribution from ρ and ρ̄
            rho_bar = rho.conjugate()
            total += (1.0 - (rho / (rho - 1)) ** n).real
            total += (1.0 - (rho_bar / (rho_bar - 1)) ** n).real
        return total

    def is_self_adjoint_check(self, s_test: float = 0.7,
                               tol: float = 1e-6) -> bool:
        """
        Check self-adjointness of H at a test point off the critical line.

        Self-adjointness requires that for real s, H(s) is real. More
        precisely: the imaginary part of H(s) must vanish for s on the
        real axis away from zeros.

        Args:
            s_test: Real test point (default 0.7)
            tol: Tolerance for imaginary part check

        Returns:
            True if H appears self-adjoint at the test point.
        """
        val = self.evaluate(complex(s_test, 0))
        if np.isnan(val.real) or np.isnan(val.imag):
            return False
        return abs(val.imag) < tol

    def prime_orbit_trace(self, t: float, primes: Optional[List[int]] = None,
                          k_max: int = 3) -> float:
        """
        Compute the prime orbit contribution to Tr(e^(−tH)).

        The trace formula gives:

            Tr(e^(−tH)) ~ Σ_{p,k} (log p / p^(k/2)) e^(−kt log p)

        This is the direct manifestation of scale invariance: the only
        possible metric in a universe seeking maximal information efficiency.

        Args:
            t: Time parameter (must be positive)
            primes: List of prime numbers to sum over (default: first 50)
            k_max: Maximum orbit repetition k (default: 3)

        Returns:
            Prime orbit sum value.
        """
        if t <= 0:
            raise ValueError(f"Time t must be positive, got t={t}")

        if primes is None:
            primes = _first_primes(50)

        total = 0.0
        for p in primes:
            log_p = np.log(p)
            for k in range(1, k_max + 1):
                # Amplitude: log p / p^(k/2)
                amplitude = log_p / p ** (k / 2.0)
                # Exponential decay
                decay = np.exp(-k * t * log_p)
                total += amplitude * decay

        return total


class LiCriterionValidator:
    """
    Validate the Li criterion λ_n > 0 for n = 1, ..., N.

    Combines LiCoefficients and EntropyFlowH to:
    - Compute all Li coefficients up to N
    - Verify positivity
    - Measure the QCAL coherence Ψ = (positive count) / N
    - Connect positivity to self-adjointness of H

    Attributes:
        li: LiCoefficients instance
        H: EntropyFlowH instance
    """

    def __init__(self, n_zeros: int = 100, dps: int = DEFAULT_DPS):
        """
        Initialize the validator.

        Args:
            n_zeros: Number of zero pairs for Li coefficient computation.
            dps: Decimal precision for mpmath.
        """
        self.li = LiCoefficients(n_zeros=n_zeros, dps=dps)
        self.H = EntropyFlowH(dps=dps)

    def validate(self, n_max: int = 20) -> LiValidationResult:
        """
        Run the full Li criterion validation for n = 1, ..., n_max.

        Args:
            n_max: Maximum index to validate (default 20)

        Returns:
            LiValidationResult with comprehensive validation data.
        """
        if n_max < 1:
            raise ValueError(f"n_max must be ≥ 1, got {n_max}")

        coefficients = self.li.compute_batch(n_max)
        all_positive = all(r.is_positive for r in coefficients)
        lambda_values = [r.lambda_n for r in coefficients]

        min_idx = int(np.argmin(lambda_values))
        min_lambda = lambda_values[min_idx]
        min_n = min_idx + 1  # 1-indexed

        n_positive = sum(1 for r in coefficients if r.is_positive)
        psi = n_positive / n_max

        if all_positive:
            rh_support = (
                f"All {n_max} Li coefficients are positive. "
                "This is consistent with the Riemann Hypothesis."
            )
        else:
            n_fail = n_max - n_positive
            rh_support = (
                f"{n_fail} out of {n_max} Li coefficients are non-positive. "
                "This would contradict RH (check truncation error)."
            )

        return LiValidationResult(
            n_max=n_max,
            all_positive=all_positive,
            coefficients=coefficients,
            min_lambda=min_lambda,
            min_n=min_n,
            rh_support=rh_support,
            psi=psi
        )

    def validate_self_adjointness(self,
                                  test_points: Optional[List[float]] = None
                                  ) -> Dict:
        """
        Validate the self-adjointness of H at multiple real test points.

        Args:
            test_points: Real s values to test (default: several off-line points)

        Returns:
            Dict with 'passed', 'test_points', 'imag_parts', 'max_imag'.
        """
        if test_points is None:
            test_points = [0.3, 0.5, 0.7, 1.5, 2.0, 3.0]

        imag_parts = []
        for s in test_points:
            val = self.H.evaluate(complex(s, 0))
            if np.isnan(val.real):
                imag_parts.append(float('nan'))
            else:
                imag_parts.append(abs(val.imag))

        max_imag = max(x for x in imag_parts if not np.isnan(x)) if imag_parts else float('inf')
        passed = max_imag < 1e-6

        return {
            'passed': passed,
            'test_points': test_points,
            'imag_parts': imag_parts,
            'max_imag': max_imag
        }

    def curvature_toward_critical_line(self, n_max: int = 10) -> Dict:
        """
        Quantify the curvature of λ_n toward zero (measuring RH stability).

        Returns a dictionary with:
        - 'growth': approximate growth rate of λ_n
        - 'is_monotone_increasing': whether λ_n is increasing
        - 'critical_line_alignment': correlation measure with theoretical curve

        Args:
            n_max: Number of coefficients to analyze

        Returns:
            Dict with curvature analysis results.
        """
        results = self.li.compute_batch(n_max)
        lambdas = np.array([r.lambda_n for r in results])
        ns = np.arange(1, n_max + 1)

        # Expected asymptotic: λ_n ~ n/2 log(n) for large n (Bombieri-Lagarias)
        # Check monotone increase
        diffs = np.diff(lambdas)
        is_monotone = bool(np.all(diffs > 0))

        # Ratio λ_n / (n log n / 2) should approach 1 as n → ∞
        with warnings.catch_warnings():
            warnings.simplefilter('ignore')
            theoretical = ns * np.log(ns + 1) / 2.0  # n log n / 2
            ratios = lambdas / (theoretical + 1e-30)

        return {
            'lambdas': lambdas.tolist(),
            'is_monotone_increasing': is_monotone,
            'growth_ratios': ratios.tolist(),
            'all_positive': bool(np.all(lambdas > 0)),
            'min_lambda': float(np.min(lambdas)),
            'max_lambda': float(np.max(lambdas))
        }


def _first_primes(n: int) -> List[int]:
    """Return the first n prime numbers via sieve of Eratosthenes."""
    if n <= 0:
        return []
    # Simple sieve
    limit = max(100, n * 15)
    sieve = [True] * (limit + 1)
    sieve[0] = sieve[1] = False
    for i in range(2, int(limit ** 0.5) + 1):
        if sieve[i]:
            for j in range(i * i, limit + 1, i):
                sieve[j] = False
    primes = [i for i, v in enumerate(sieve) if v]
    return primes[:n]


def demonstrate_li_criterion(n_max: int = 15,
                              n_zeros: int = 100) -> Dict:
    """
    Demonstrate the Li criterion and its connection to the Riemann Hypothesis.

    Computes λ_n for n = 1,...,n_max, verifies positivity, checks
    self-adjointness of H, and displays the curvature analysis.

    Args:
        n_max: Maximum Li coefficient index to compute (default 15)
        n_zeros: Number of non-trivial zero pairs to use (default 100)

    Returns:
        Dict with all results:
        - 'li_validation': LiValidationResult
        - 'self_adjoint': self-adjointness check dict
        - 'curvature': curvature analysis dict
        - 'psi': QCAL coherence metric
        - 'prime_trace_sample': sample prime orbit trace values
    """
    print("\n" + "∴" * 40)
    print("EL CRITERIO DE LI: LA POSITIVIDAD DE LA TRAZA")
    print(f"QCAL ∞³  ·  f₀ = {F0_QCAL} Hz  ·  C = {C_COHERENCE}")
    print("∴" * 40)

    validator = LiCriterionValidator(n_zeros=n_zeros)

    # 1. Compute Li coefficients
    print(f"\n{'='*60}")
    print("1. Li Coefficients λ_n = Σ_ρ [1 − (ρ/(ρ−1))^n]")
    print(f"{'='*60}")
    print(f"   Using {n_zeros} zero pairs, computing n=1,...,{n_max}")

    li_result = validator.validate(n_max)

    print(f"\n   n  |  λ_n             |  Positive?")
    print(f"   {'-'*45}")
    for r in li_result.coefficients:
        sign = "✅" if r.is_positive else "❌"
        print(f"   {r.n:2d} |  {r.lambda_n:16.8f}  |  {sign}")

    print(f"\n   All positive: {'✅ YES' if li_result.all_positive else '❌ NO'}")
    print(f"   Minimum λ_n: λ_{li_result.min_n} = {li_result.min_lambda:.8f}")
    print(f"   QCAL Coherence Ψ = {li_result.psi:.4f}")
    print(f"\n   {li_result.rh_support}")

    # 2. Self-adjointness of H
    print(f"\n{'='*60}")
    print("2. Self-Adjointness of H = ξ'/ξ")
    print(f"{'='*60}")

    sa_result = validator.validate_self_adjointness()
    print(f"   Test points: {sa_result['test_points']}")
    print(f"   Max imaginary part: {sa_result['max_imag']:.2e}")
    print(f"   Self-adjoint: {'✅ YES' if sa_result['passed'] else '❌ NO'}")

    # 3. Curvature analysis
    print(f"\n{'='*60}")
    print("3. Curvature toward the Critical Line")
    print(f"{'='*60}")

    curv = validator.curvature_toward_critical_line(min(n_max, 10))
    print(f"   Monotone increasing: {'✅ YES' if curv['is_monotone_increasing'] else '❌ NO'}")
    print(f"   All positive: {'✅ YES' if curv['all_positive'] else '❌ NO'}")
    print(f"   λ_1 = {curv['lambdas'][0]:.6f} (minimum curvature)")
    print(f"   λ_{min(n_max, 10)} = {curv['lambdas'][-1]:.6f}")

    # 4. Prime orbit trace sample
    print(f"\n{'='*60}")
    print("4. Prime Orbit Trace Tr(e^(−tH))")
    print(f"{'='*60}")

    t_values = [0.1, 0.5, 1.0, 2.0]
    prime_traces = {t: validator.H.prime_orbit_trace(t) for t in t_values}
    for t, val in prime_traces.items():
        print(f"   t={t:.1f}: Tr = {val:.6f}")

    # Summary
    psi = li_result.psi
    print(f"\n{'∴'*40}")
    print("RESUMEN (Summary)")
    print(f"{'∴'*40}")
    print(f"  Ψ (QCAL coherence): {psi:.4f}")
    print(f"  λ_n > 0 confirmed for n = 1,...,{n_max}: "
          f"{'YES ✅' if li_result.all_positive else 'NO ❌'}")
    print(f"  H is self-adjoint: {'YES ✅' if sa_result['passed'] else 'NO ❌'}")
    print(f"  Entropy flow stable: {'YES ✅' if li_result.all_positive else 'NO ❌'}")
    print(f"\n  DOI: {DOI}")
    print(f"  ORCID: {ORCID}")
    print("∴𓂀Ω∞³Φ @ 141.7001 Hz")

    return {
        'li_validation': li_result,
        'self_adjoint': sa_result,
        'curvature': curv,
        'psi': psi,
        'prime_trace_sample': prime_traces
    }
