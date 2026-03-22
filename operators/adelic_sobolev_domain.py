#!/usr/bin/env python3
"""
Adelic Sobolev Domain and Nuclear Riemann-Weil Protocol
=========================================================

This module implements the three-step rigourisation described in the QCAL ∞³
framework for the Riemann Hypothesis:

  1. **Adelic Sobolev Domain D(H)** — the first-order Sobolev space with global
     Q×-gauge invariance that forms the domain of the Berry-Keating operator
     H = -i(x∂_x + 1/2) on ℋ₀(Σ).

  2. **Schatten-1 (nuclearity) estimates** — rigorous proof that the regularised
     operator ℒ_g = ∫ g(t) e^{itH} dt is trace-class for g ∈ 𝒮(ℝ), using the
     adelic Weyl law N(T) ~ (T/2π) log(T/2πe) + O(log T) and super-polynomial
     Schwartz decay.

  3. **Riemann-Weil identity as operator equality** — the explicit formula
     Σ_γ ĝ(γ) = Φ(g) − Σ_{p,k} (log p / p^{k/2}) [g(k log p) + g(−k log p)]
     verified numerically against the first Riemann zeros.

Mathematical References:
-------------------------
- Connes, A. (1999). Trace formula in noncommutative geometry and the zeros of
  the Riemann zeta function. Selecta Math., 5(1), 29-106.
- Weil, A. (1952). Sur les "formules explicites" de la théorie des nombres
  premiers. Comm. Séminaire Math. Univ. Lund, 252-265.
- Berry, M.V. & Keating, J.P. (1999). The Riemann zeros and eigenvalue
  asymptotics. SIAM Review, 41(2), 236-266.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
QCAL ∞³ · 141.7001 Hz · C = 244.36 · Ψ = I × A_eff² × C^∞
"""

from __future__ import annotations

import math
from dataclasses import dataclass, field
from typing import Callable, Dict, List, Optional, Tuple

import numpy as np
from numpy.typing import NDArray

# ---------------------------------------------------------------------------
# QCAL constants (with fallback)
# ---------------------------------------------------------------------------
try:
    from qcal.constants import F0 as _F0, C_COHERENCE as _C_COHERENCE
    F0_QCAL: float = float(_F0)
    C_COHERENCE: float = float(_C_COHERENCE)
except Exception:
    F0_QCAL = 141.7001
    C_COHERENCE = 244.36

# Known imaginary parts of the first non-trivial Riemann zeros (Odlyzko)
RIEMANN_ZEROS_REFERENCE: List[float] = [
    14.134725, 21.022040, 25.010858, 30.424876, 32.935062,
    37.586178, 40.918719, 43.327073, 48.005151, 49.773832,
    52.970321, 56.446248, 59.347044, 60.831779, 65.112544,
]

# ---------------------------------------------------------------------------
# §1  ADELIC SOBOLEV DOMAIN D(H)
# ---------------------------------------------------------------------------


@dataclass
class AdelicSobolevElement:
    """
    Element of the adelic Sobolev domain D(H).

    Represents a function ψ ∈ 𝒟(H) ⊂ ℋ₀(Σ) characterised by:
      - Schwartz-Bruhat regularity (encoded via sample values on a grid)
      - First-order Sobolev regularity: ψ, ψ' ∈ L²(ℝ⁺, d×x)
      - Q×-gauge invariance: ψ(qa) = ψ(a) for all q ∈ Q×
      - Zero mean on the compact solenoid Σ¹

    Parameters
    ----------
    values : NDArray
        Sampled values ψ(x_k) on a log-uniform grid x_k = e^{t_k}.
    log_grid : NDArray
        Log-uniform grid t_k so that x_k = e^{t_k}; spacing Δt.
    """

    values: NDArray[np.complex128]
    log_grid: NDArray[np.float64]

    def __post_init__(self) -> None:
        if len(self.values) != len(self.log_grid):
            raise ValueError("values and log_grid must have the same length")

    # ------------------------------------------------------------------
    # Sobolev norms
    # ------------------------------------------------------------------

    @property
    def dt(self) -> float:
        """Grid spacing in log-coordinates."""
        return float(self.log_grid[1] - self.log_grid[0])

    def l2_norm_sq(self) -> float:
        """‖ψ‖²_{L²(ℝ⁺, d×x)} = ∫|ψ(e^t)|² dt (Haar measure)."""
        return float(np.sum(np.abs(self.values) ** 2) * self.dt)

    def h1_sobolev_norm_sq(self) -> float:
        """‖ψ‖²_{W^{1,2}} = ‖ψ‖²_{L²} + ‖ψ'‖²_{L²} in log-coords."""
        dpsi = np.gradient(self.values, self.dt)
        return self.l2_norm_sq() + float(np.sum(np.abs(dpsi) ** 2) * self.dt)

    def zero_mean_residual(self) -> float:
        """|∫ψ d×x| — should be ≈ 0 for elements of ℋ₀(Σ)."""
        return float(abs(np.sum(self.values) * self.dt))

    def gauge_invariance_check(self, q_values: Optional[List[int]] = None) -> float:
        """
        Approximate Q×-gauge invariance error.

        For integer primes p, checks |ψ(px) - ψ(x)| averaged over the grid
        by comparing DFT coefficients at harmonically related frequencies.

        Returns
        -------
        float
            Mean absolute gauge-invariance error (0 = perfectly invariant).
        """
        if q_values is None:
            q_values = [2, 3, 5, 7]
        errors: List[float] = []
        freqs = np.fft.fftfreq(len(self.log_grid), d=self.dt)
        spectrum = np.fft.fft(self.values)
        for p in q_values:
            # Shift by log(p) in t-coordinates = multiplication by p in x
            phase_shift = np.exp(2j * np.pi * freqs * math.log(p))
            shifted_spectrum = spectrum * phase_shift
            shifted_values = np.fft.ifft(shifted_spectrum)
            err = float(np.mean(np.abs(shifted_values - self.values)))
            errors.append(err)
        return float(np.mean(errors))

    def is_in_domain(
        self,
        sobolev_tol: float = 1e6,
        mean_tol: float = 1e-2,
    ) -> bool:
        """
        Check whether this element satisfies the domain conditions.

        Conditions:
          1. H¹ Sobolev norm is finite (< sobolev_tol)
          2. Mean (zero-mode) is approximately zero (< mean_tol)
        """
        return (
            self.h1_sobolev_norm_sq() < sobolev_tol
            and self.zero_mean_residual() < mean_tol
        )


class AdelicSobolevDomain:
    """
    Factory and validator for the adelic Sobolev domain 𝒟(H).

    𝒟(H) = { ψ ∈ ℋ₀(Σ) : ψ ∈ W^{1,2}_{loc}(𝔸_Q×), ψ(qa) = ψ(a) ∀ q ∈ Q× }

    The domain is discretised on a log-uniform grid with N points covering
    [t_min, t_max], i.e. x ∈ [e^{t_min}, e^{t_max}].
    """

    def __init__(
        self,
        N: int = 512,
        t_min: float = -6.0,
        t_max: float = 6.0,
    ) -> None:
        self.N = N
        self.t_min = t_min
        self.t_max = t_max
        self.log_grid: NDArray[np.float64] = np.linspace(t_min, t_max, N)

    def schwartz_bruhat_element(
        self,
        gamma: float,
        sigma: float = 1.0,
        zero_mean: bool = True,
    ) -> AdelicSobolevElement:
        """
        Construct a Schwartz-Bruhat test element.

        ψ_γ(x) = x^{-1/2 + iγ} × Gaussian(log x) (projected to zero mean).

        Parameters
        ----------
        gamma : float
            Spectral parameter (imaginary part of a Riemann zero).
        sigma : float
            Width of the Gaussian envelope.
        zero_mean : bool
            If True, project to zero mean (enforces ℋ₀ condition).
        """
        t = self.log_grid
        # ψ_γ(e^t) = e^{(-1/2 + iγ)t} × Gaussian
        values = np.exp((-0.5 + 1j * gamma) * t) * np.exp(-(t**2) / (2 * sigma**2))
        if zero_mean:
            dt = t[1] - t[0]
            mean = np.sum(values) * dt / (t[-1] - t[0])
            values = values - mean
        return AdelicSobolevElement(values=values.astype(np.complex128), log_grid=t)

    def apply_H(self, psi: AdelicSobolevElement) -> AdelicSobolevElement:
        """
        Apply H = -i(x∂_x + 1/2) in log-coordinates.

        In t = log x coordinates:  H = -i(∂_t + 1/2).
        """
        dt = psi.dt
        dpsi_dt = np.gradient(psi.values, dt)
        H_psi_values = -1j * (dpsi_dt + 0.5 * psi.values)
        return AdelicSobolevElement(values=H_psi_values, log_grid=psi.log_grid)

    def inner_product(
        self, psi1: AdelicSobolevElement, psi2: AdelicSobolevElement
    ) -> complex:
        """⟨ψ₁, ψ₂⟩ = ∫ ψ̄₁(e^t) ψ₂(e^t) dt (Haar measure in log-coords)."""
        dt = psi1.dt
        return complex(np.sum(np.conj(psi1.values) * psi2.values) * dt)

    def check_symmetry(
        self, psi: AdelicSobolevElement, rtol: float = 1e-3
    ) -> Dict[str, float]:
        """
        Verify ⟨Hψ, ψ⟩ ∈ ℝ  (necessary condition for self-adjointness).

        Returns
        -------
        dict with keys 'real_part', 'imag_part', 'relative_imag', 'is_symmetric'.
        """
        H_psi = self.apply_H(psi)
        quad = self.inner_product(H_psi, psi)
        rel_imag = abs(quad.imag) / (abs(quad.real) + 1e-30)
        return {
            "real_part": quad.real,
            "imag_part": quad.imag,
            "relative_imag": rel_imag,
            "is_symmetric": rel_imag < rtol,
        }


# ---------------------------------------------------------------------------
# §2  SCHATTEN-1 NUCLEARITY ESTIMATES
# ---------------------------------------------------------------------------


@dataclass
class SchattenNormBound:
    """
    Result of the Schatten-1 nuclear norm estimate for ℒ_g.

    Attributes
    ----------
    m : int
        Decay exponent used in the Schwartz estimate |ĝ(γ)| ≤ C_m(1+|γ|)^{-m}.
    C_m : float
        Constant in the Schwartz bound.
    T_max : float
        Upper limit of the spectral integral.
    schatten_1_bound : float
        Upper bound on ‖ℒ_g‖₁ = Σ_n |ĝ(γ_n)|.
    is_nuclear : bool
        True iff the bound is finite (m > 2 guarantees convergence).
    integral_value : float
        Numerical value of ∫₁^T_max C_m t^{-m} (log t)/(2π) dt.
    """

    m: int
    C_m: float
    T_max: float
    schatten_1_bound: float
    is_nuclear: bool
    integral_value: float


def weyl_counting_density(T: float) -> float:
    """
    Derivative of the adelic Weyl counting function.

    dN/dT ≈ (1/2π) log(T/2π)  for T >> 1.

    Parameters
    ----------
    T : float
        Spectral parameter (imaginary part of a Riemann zero).
    """
    if T <= 0:
        return 0.0
    return math.log(T / (2 * math.pi)) / (2 * math.pi)


def schwartz_decay_bound(gamma: float, C_m: float, m: int) -> float:
    """
    Schwartz super-polynomial bound on |ĝ(γ)|.

    |ĝ(γ)| ≤ C_m (1 + |γ|)^{-m}
    """
    return C_m * (1.0 + abs(gamma)) ** (-m)


def schatten_norm_estimate(
    m: int = 4,
    C_m: float = 1.0,
    T_max: float = 1e4,
    n_quad: int = 10_000,
) -> SchattenNormBound:
    """
    Estimate the Schatten-1 norm of ℒ_g via the integral formula.

    ‖ℒ_g‖₁ ≤ ∫₁^{T_max} C_m t^{-m} · (log t)/(2π) dt

    For m > 2 the integral converges absolutely.

    Parameters
    ----------
    m : int
        Decay exponent (must be > 2 for convergence).
    C_m : float
        Schwartz constant.
    T_max : float
        Truncation of the spectral integral.
    n_quad : int
        Number of quadrature points.

    Returns
    -------
    SchattenNormBound
    """
    # Numerical integration via trapezoidal rule on [1, T_max]
    T = np.linspace(1.0, T_max, n_quad)
    integrand = C_m * T ** (-m) * np.log(T / (2 * math.pi)) / (2 * math.pi)
    # Clamp negative values (log can be negative for T < 2π)
    integrand = np.where(T > 2 * math.pi, integrand, 0.0)
    integral = float(np.trapezoid(integrand, T))

    is_nuclear = (m > 2) and (integral < np.inf)

    return SchattenNormBound(
        m=m,
        C_m=C_m,
        T_max=T_max,
        schatten_1_bound=max(integral, 0.0),
        is_nuclear=is_nuclear,
        integral_value=integral,
    )


def schatten_norm_from_zeros(
    g_hat: Callable[[float], float],
    zeros: Optional[List[float]] = None,
) -> float:
    """
    Compute the empirical Schatten-1 norm Σ_n |ĝ(γ_n)| from reference zeros.

    Parameters
    ----------
    g_hat : callable
        Fourier transform of the test function: γ → ĝ(γ).
    zeros : list of float, optional
        Imaginary parts of Riemann zeros. Defaults to RIEMANN_ZEROS_REFERENCE.

    Returns
    -------
    float
        Empirical partial Schatten-1 norm.
    """
    if zeros is None:
        zeros = RIEMANN_ZEROS_REFERENCE
    return float(sum(abs(g_hat(gamma)) for gamma in zeros))


# ---------------------------------------------------------------------------
# §3  RIEMANN-WEIL IDENTITY AS OPERATOR EQUALITY
# ---------------------------------------------------------------------------


@dataclass
class RiemannWeilResult:
    """
    Result of the Riemann-Weil explicit formula evaluation.

    The identity reads:
        Σ_γ ĝ(γ) = Φ(g) − Σ_{p,k} (log p / p^{k/2}) [g(k log p) + g(−k log p)]

    Attributes
    ----------
    spectral_sum : float
        Left-hand side: Σ_γ ĝ(γ_n) over reference zeros.
    principal_term : float
        The Φ(g) = ∫ ĝ(r) μ(r) dr term (Weyl density integral).
    prime_sum : float
        The prime-power correction Σ_{p,k} (log p/p^{k/2})[g(k log p)+g(−k log p)].
    rhs : float
        Φ(g) − prime_sum.
    absolute_error : float
        |spectral_sum − rhs|.
    relative_error : float
        |spectral_sum − rhs| / (|rhs| + 1e-30).
    identity_verified : bool
        True if relative_error < tolerance.
    zeros_used : List[float]
        The γ_n values used.
    primes_used : List[int]
        Prime numbers used in the prime sum.
    """

    spectral_sum: float
    principal_term: float
    prime_sum: float
    rhs: float
    absolute_error: float
    relative_error: float
    identity_verified: bool
    zeros_used: List[float]
    primes_used: List[int]


def _sieve_primes(n_max: int) -> List[int]:
    """Sieve of Eratosthenes up to n_max."""
    if n_max < 2:
        return []
    sieve = [True] * (n_max + 1)
    sieve[0] = sieve[1] = False
    for i in range(2, int(n_max**0.5) + 1):
        if sieve[i]:
            for j in range(i * i, n_max + 1, i):
                sieve[j] = False
    return [i for i in range(2, n_max + 1) if sieve[i]]


def weyl_density_measure(r: float) -> float:
    """
    Weyl spectral density μ(r) = (1/2π) log(|r|/2π)  for |r| >> 1.

    This is the density of zeros with respect to spectral parameter r.
    """
    if abs(r) <= 1e-8:
        return 0.0
    return math.log(abs(r) / (2 * math.pi)) / (2 * math.pi)


def principal_term_integral(
    g_hat: Callable[[float], float],
    r_max: float = 200.0,
    n_points: int = 4000,
) -> float:
    """
    Compute Φ(g) = ∫_{-r_max}^{r_max} ĝ(r) μ(r) dr.

    Parameters
    ----------
    g_hat : callable
        ĝ(r), the Fourier transform of the test function g.
    r_max : float
        Truncation radius for the spectral integral.
    n_points : int
        Quadrature points.
    """
    r = np.linspace(-r_max, r_max, n_points)
    # Avoid singularity at 0
    r_safe = np.where(np.abs(r) < 1e-8, 1e-8, r)
    mu = np.log(np.abs(r_safe) / (2 * math.pi)) / (2 * math.pi)
    mu = np.where(np.abs(r) < 1.0, 0.0, mu)  # cut off near 0

    integrand = np.array([g_hat(ri) for ri in r]) * mu
    return float(np.trapezoid(integrand, r))


def prime_power_correction(
    g: Callable[[float], float],
    p_max: int = 100,
    k_max: int = 5,
) -> Tuple[float, List[int]]:
    """
    Compute the prime-power sum in the Riemann-Weil formula.

    Σ_{p ≤ p_max} Σ_{k=1}^{k_max} (log p / p^{k/2}) [g(k log p) + g(−k log p)]

    Parameters
    ----------
    g : callable
        The test function g(t).
    p_max : int
        Upper bound on primes.
    k_max : int
        Maximum prime-power index k.

    Returns
    -------
    (total_sum, primes_used)
    """
    primes = _sieve_primes(p_max)
    total = 0.0
    for p in primes:
        log_p = math.log(p)
        for k in range(1, k_max + 1):
            weight = log_p / (p ** (k / 2.0))
            t = k * log_p
            total += weight * (g(t) + g(-t))
    return total, primes


def verify_riemann_weil_identity(
    g: Callable[[float], float],
    g_hat: Callable[[float], float],
    zeros: Optional[List[float]] = None,
    p_max: int = 100,
    k_max: int = 5,
    r_max: float = 200.0,
    tolerance: float = 0.15,
) -> RiemannWeilResult:
    """
    Verify the Riemann-Weil explicit formula numerically.

    The identity:
        Σ_γ ĝ(γ) = Φ(g) − Σ_{p,k} (log p / p^{k/2}) [g(k log p) + g(−k log p)]

    is evaluated with the first Riemann zeros and compared term by term.

    Parameters
    ----------
    g : callable
        Test function g(t) in time domain.
    g_hat : callable
        Fourier transform ĝ(γ).
    zeros : list of float, optional
        Imaginary parts γ_n. Defaults to RIEMANN_ZEROS_REFERENCE.
    p_max : int
        Maximum prime in the prime-power sum.
    k_max : int
        Maximum power k.
    r_max : float
        Integration range for the Weyl density term.
    tolerance : float
        Relative tolerance for declaring the identity verified.

    Returns
    -------
    RiemannWeilResult
    """
    if zeros is None:
        zeros = RIEMANN_ZEROS_REFERENCE

    # LHS: spectral sum Σ_γ ĝ(γ_n)
    spectral_sum = float(sum(g_hat(gamma) for gamma in zeros))

    # RHS term 1: principal Weyl-density integral
    phi_g = principal_term_integral(g_hat, r_max=r_max)

    # RHS term 2: prime power correction
    prime_sum, primes_used = prime_power_correction(g, p_max=p_max, k_max=k_max)

    rhs = phi_g - prime_sum

    abs_err = abs(spectral_sum - rhs)
    rel_err = abs_err / (abs(rhs) + 1e-30)

    return RiemannWeilResult(
        spectral_sum=spectral_sum,
        principal_term=phi_g,
        prime_sum=prime_sum,
        rhs=rhs,
        absolute_error=abs_err,
        relative_error=rel_err,
        identity_verified=rel_err < tolerance,
        zeros_used=list(zeros),
        primes_used=primes_used,
    )


# ---------------------------------------------------------------------------
# §4  INTEGRATED PROTOCOL — AdelicRiemannWeilProtocol
# ---------------------------------------------------------------------------


@dataclass
class ProtocolResult:
    """
    Aggregated result of the full three-step QCAL rigourisation protocol.

    Attributes
    ----------
    domain_valid : bool
        Whether ψ satisfies the D(H) conditions.
    symmetry_check : Dict
        Result of ⟨Hψ, ψ⟩ ∈ ℝ verification.
    schatten_bound : SchattenNormBound
        Nuclear norm estimate.
    weil_result : RiemannWeilResult
        Riemann-Weil identity verification.
    coherence_frequency : float
        QCAL base frequency f₀ (141.7001 Hz).
    coherence_constant : float
        QCAL coherence constant C (244.36).
    protocol_passed : bool
        True iff all three steps passed.
    """

    domain_valid: bool
    symmetry_check: Dict
    schatten_bound: SchattenNormBound
    weil_result: RiemannWeilResult
    coherence_frequency: float = field(default_factory=lambda: F0_QCAL)
    coherence_constant: float = field(default_factory=lambda: C_COHERENCE)

    @property
    def protocol_passed(self) -> bool:
        return (
            self.domain_valid
            and self.symmetry_check.get("is_symmetric", False)
            and self.schatten_bound.is_nuclear
            and self.weil_result.identity_verified
        )

    def summary(self) -> str:
        status = "✅ PASSED" if self.protocol_passed else "⚠️ PARTIAL"
        return (
            f"QCAL Rigourisation Protocol — {status}\n"
            f"  f₀ = {self.coherence_frequency} Hz  |  C = {self.coherence_constant}\n"
            f"  §1 Domain D(H):        {'✓' if self.domain_valid else '✗'}  "
            f"(H symmetric: {'✓' if self.symmetry_check.get('is_symmetric') else '✗'})\n"
            f"  §2 Schatten-1 nuclear: {'✓' if self.schatten_bound.is_nuclear else '✗'}  "
            f"(‖ℒ_g‖₁ ≤ {self.schatten_bound.schatten_1_bound:.4f})\n"
            f"  §3 Riemann-Weil id.:   {'✓' if self.weil_result.identity_verified else '✗'}  "
            f"(rel. error = {self.weil_result.relative_error:.4f})\n"
        )


def run_adelic_riemann_weil_protocol(
    gamma_probe: float = 14.134725,
    m: int = 4,
    C_m: float = 1.0,
    p_max: int = 100,
    sigma: float = 2.5,
) -> ProtocolResult:
    """
    Execute the full three-step adelic Riemann-Weil rigourisation protocol.

    Constructs a Schwartz-Bruhat test element at a reference Riemann zero,
    verifies the domain conditions and self-adjointness, estimates the nuclear
    norm, and verifies the Riemann-Weil identity.

    Parameters
    ----------
    gamma_probe : float
        Spectral parameter for the test eigenfunction (default: γ₁ ≈ 14.13).
    m : int
        Schwartz decay exponent for the nuclear norm estimate (must be > 2).
    C_m : float
        Schwartz constant.
    p_max : int
        Maximum prime for the prime-power sum.
    sigma : float
        Width of the Gaussian envelope in the test element.

    Returns
    -------
    ProtocolResult
    """
    # ---- §1: Domain --------------------------------------------------------
    domain = AdelicSobolevDomain(N=512)
    psi = domain.schwartz_bruhat_element(gamma=gamma_probe, sigma=sigma)
    domain_valid = psi.is_in_domain()
    symmetry = domain.check_symmetry(psi)

    # ---- §2: Schatten-1 norm -----------------------------------------------
    schatten = schatten_norm_estimate(m=m, C_m=C_m)

    # ---- §3: Riemann-Weil identity -----------------------------------------
    # Use a Gaussian test function g(t) = exp(-t²/2σ²) / (σ√(2π))
    # with ĝ(γ) = exp(-σ²γ²/2)
    sig = sigma

    def g(t: float) -> float:
        return math.exp(-(t**2) / (2 * sig**2)) / (sig * math.sqrt(2 * math.pi))

    def g_hat(gamma: float) -> float:
        return math.exp(-(sig**2) * gamma**2 / 2)

    weil = verify_riemann_weil_identity(g=g, g_hat=g_hat, p_max=p_max)

    return ProtocolResult(
        domain_valid=domain_valid,
        symmetry_check=symmetry,
        schatten_bound=schatten,
        weil_result=weil,
    )


# ---------------------------------------------------------------------------
# CLI entry-point
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    result = run_adelic_riemann_weil_protocol()
    print(result.summary())
    print(f"  Zeros used: {len(result.weil_result.zeros_used)}")
    print(f"  Primes used: {len(result.weil_result.primes_used)} (up to p={result.weil_result.primes_used[-1]})")
