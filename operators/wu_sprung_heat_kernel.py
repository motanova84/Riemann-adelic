#!/usr/bin/env python3
"""
Wu-Sprung Heat Kernel Expansion Coefficients
============================================

Implements the heat kernel trace expansion for the Wu-Sprung Hamiltonian H
whose spectral counting function N(E) mimics the smooth part of Riemann zeros.

Mathematical Framework:
-----------------------

**Smooth counting function (Weyl-type):**

    N_smooth(E) = (E/2π) ln(E/2π) - (E/2π) + 7/8 + 1/(48π·E) + ...

**Heat kernel trace (via Laplace–Stieltjes transform):**

    Tr(e^{-tH}) = ∫₀^∞ e^{-tE} dN(E)
               = t · ∫₀^∞ e^{-tE} N(E) dE   (integration by parts)

**Asymptotic expansion for t → 0⁺:**

    Tr(e^{-tH}) ~ A₀·ln(1/t)/t + A₁/t + A₂ + A₃·t·ln(1/t) + A₄·t + O(t²)

**Analytically derived coefficients:**

    A₀ = 1/(2π)                            [≈ 0.15915]
    A₁ = -(γ + ln(2π)) / (2π)             [≈ -0.38437]
    A₂ = 7/8                               [= 0.875]
    A₃ = 1/(48π)                           [≈ 0.00663]
    A₄ = -γ/(48π)                          [≈ -0.00383]

where γ = Euler–Mascheroni constant ≈ 0.57722.

Derivation sketch
-----------------
Using the Mellin–Barnes identity for L[E^s] = Γ(s+1)/t^{s+1}:

    L[E·ln E]    = (1 - γ - ln t) / t²
    L[E]         = 1 / t²
    L[1]         = 1 / t
    L[1/E]  ~  (-ln t - γ)  for t → 0⁺  (exponential integral E₁)

Applying t·L[·] to N_smooth:

    t · L[N_smooth_extended]
      = (1 - γ - ln t)/(2πt)           [from (E/2π)·ln E]
      - ln(2π)/(2πt)                   [from -(E/2π)·ln(2π)]
      - 1/(2πt)                        [from -E/(2π)]
      + 7/8                            [from 7/8]
      + t·(-ln t - γ)/(48π)           [from 1/(48πE)]

Collecting by power/log:

    A₀ = 1/(2π)
    A₁ = (1 - γ - ln(2π) - 1)/(2π) = -(γ + ln(2π))/(2π)
    A₂ = 7/8
    A₃ = 1/(48π)
    A₄ = -γ/(48π)

References:
-----------
- Berry, M.V. & Keating, J.P. (1999). The Riemann zeros and eigenvalue asymptotics.
- Wu, H. & Sprung, D.W.L. (1993). Riemann zeros and a fractal potential.
- Connes, A. (1999). Trace formula in noncommutative geometry and the zeros of
  the Riemann zeta function.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
Institution: Instituto de Conciencia Cuántica (ICQ)
Protocol: QCAL-WU-SPRUNG-HEAT-KERNEL v1.0
DOI: 10.5281/zenodo.17379721
QCAL ∞³ · f₀ = 141.7001 Hz · C = 244.36 · Ψ = I × A_eff² × C^∞
"""

import math
from dataclasses import dataclass
from typing import Dict, Any

import numpy as np
from scipy.special import exp1  # E₁(t) = ∫_t^∞ e^{-u}/u du

# QCAL constants
F0_QCAL = 141.7001       # Hz – fundamental resonance frequency
C_COHERENCE = 244.36     # Coherence constant

# Mathematical constants
EULER_GAMMA = 0.5772156649015328606  # Euler–Mascheroni constant γ


@dataclass
class HeatKernelCoefficients:
    """
    Heat kernel expansion coefficients for the Wu-Sprung operator.

    The asymptotic expansion of Tr(e^{-tH}) as t → 0⁺ is:

        Tr(e^{-tH}) ~ A0·ln(1/t)/t + A1/t + A2 + A3·t·ln(1/t) + A4·t + …

    Attributes:
        A0: Coefficient of ln(1/t)/t.  Equals 1/(2π).
        A1: Coefficient of 1/t.  Equals -(γ + ln(2π))/(2π).
        A2: Constant term.  Equals 7/8.
        A3: Coefficient of t·ln(1/t).  Equals 1/(48π).
        A4: Coefficient of t.  Equals -γ/(48π).
        euler_gamma: Euler–Mascheroni constant used in derivation.
    """

    A0: float
    A1: float
    A2: float
    A3: float
    A4: float
    euler_gamma: float


class WuSprungHeatKernel:
    """
    Heat kernel expansion for the Wu-Sprung Hamiltonian.

    Computes the coefficients A₀…A₄ of the small-t asymptotics of
    Tr(e^{-tH}) using the Laplace–Stieltjes transform of N_smooth(E).
    """

    def __init__(self) -> None:
        self._pi = math.pi
        self._gamma = EULER_GAMMA

    # ------------------------------------------------------------------
    # Analytical coefficient formulas
    # ------------------------------------------------------------------

    @property
    def A0(self) -> float:
        """Coefficient of ln(1/t)/t: A₀ = 1/(2π)."""
        return 1.0 / (2.0 * self._pi)

    @property
    def A1(self) -> float:
        """Coefficient of 1/t: A₁ = -(γ + ln(2π))/(2π)."""
        return -(self._gamma + math.log(2.0 * self._pi)) / (2.0 * self._pi)

    @property
    def A2(self) -> float:
        """Constant term: A₂ = 7/8."""
        return 7.0 / 8.0

    @property
    def A3(self) -> float:
        """Coefficient of t·ln(1/t): A₃ = 1/(48π)."""
        return 1.0 / (48.0 * self._pi)

    @property
    def A4(self) -> float:
        """Coefficient of t: A₄ = -γ/(48π)."""
        return -self._gamma / (48.0 * self._pi)

    def coefficients(self) -> HeatKernelCoefficients:
        """
        Return all heat kernel expansion coefficients.

        Returns:
            HeatKernelCoefficients dataclass with A0–A4 and γ.
        """
        return HeatKernelCoefficients(
            A0=self.A0,
            A1=self.A1,
            A2=self.A2,
            A3=self.A3,
            A4=self.A4,
            euler_gamma=self._gamma,
        )

    # ------------------------------------------------------------------
    # Trace evaluation
    # ------------------------------------------------------------------

    def trace_expansion(self, t: float, n_terms: int = 5) -> float:
        """
        Evaluate the asymptotic expansion of Tr(e^{-tH}) at time t.

        Expansion:
            Tr(e^{-tH}) ≈ A₀·ln(1/t)/t + A₁/t + A₂ + A₃·t·ln(1/t) + A₄·t

        Args:
            t: Heat-kernel time t > 0.
            n_terms: Number of terms to include (1 to 5).

        Returns:
            Approximate value of Tr(e^{-tH}).

        Raises:
            ValueError: If t ≤ 0 or n_terms not in 1..5.
        """
        if t <= 0.0:
            raise ValueError(f"t must be positive, got {t}")
        if not (1 <= n_terms <= 5):
            raise ValueError(f"n_terms must be between 1 and 5, got {n_terms}")

        log_inv_t = math.log(1.0 / t)
        result = 0.0
        if n_terms >= 1:
            result += self.A0 * log_inv_t / t
        if n_terms >= 2:
            result += self.A1 / t
        if n_terms >= 3:
            result += self.A2
        if n_terms >= 4:
            result += self.A3 * t * log_inv_t
        if n_terms >= 5:
            result += self.A4 * t
        return result

    def trace_numerical(self, t: float, E_max: float = 1e4,
                        n_points: int = 100000) -> float:
        """
        Numerically estimate Tr(e^{-tH}) via Laplace transform of N_smooth.

        Decomposes the integral as:

            t · ∫₀^∞ e^{-tE} · N_smooth_extended(E) dE
              = t · ∫₀^∞ e^{-tE} · N_smooth(E) dE
                + (1/(48π)) · t · ∫₀^∞ e^{-tE}/E dE

        The first term is computed numerically with trapezoidal integration
        (N_smooth is smooth and non-singular).  The second term uses the
        exponential integral E₁(t) = ∫_t^∞ e^{-u}/u du ≈ -ln t - γ.

        Args:
            t: Heat-kernel time t > 0.
            E_max: Upper integration cutoff for the smooth part.
            n_points: Number of quadrature points for the smooth part.

        Returns:
            Numerical estimate of Tr(e^{-tH}).

        Raises:
            ValueError: If t ≤ 0.
        """
        if t <= 0.0:
            raise ValueError(f"t must be positive, got {t}")

        # Smooth part: N_smooth(E) = (E/2π)·ln(E/2π) - E/(2π) + 7/8
        # (no singularity at E = 0 for E > 0)
        E = np.linspace(0.0, E_max, n_points + 1)
        E[0] = 1e-12  # avoid log(0)
        N_smooth = (E / (2.0 * self._pi)) * np.log(E / (2.0 * self._pi)) \
            - E / (2.0 * self._pi) \
            + 7.0 / 8.0
        integrand = np.exp(-t * E) * N_smooth
        smooth_integral = np.trapezoid(integrand, E)

        # 1/E part: (1/(48π)) · t · E₁(t)  where E₁(t) = ∫_t^∞ e^{-u}/u du
        e1_contribution = (1.0 / (48.0 * self._pi)) * t * float(exp1(t))

        return t * smooth_integral + e1_contribution

    # ------------------------------------------------------------------
    # Validation
    # ------------------------------------------------------------------

    def validate_coefficients(
        self,
        t_values: np.ndarray,
        rtol: float = 0.05,
    ) -> Dict[str, Any]:
        """
        Validate asymptotic expansion against numerical integration.

        For each t in t_values, compares the 5-term expansion with a
        numerical Laplace transform.  Small t (t < 0.01) is where the
        expansion should be accurate.

        Args:
            t_values: Array of t values to test (recommend t in (0.001, 0.1)).
            rtol: Relative-tolerance threshold for a "pass".

        Returns:
            Dictionary with keys:
                ``t_values``, ``expansion``, ``numerical``,
                ``relative_errors``, ``all_passed``, ``n_passed``.
        """
        expansion = np.array([self.trace_expansion(float(t)) for t in t_values])
        numerical = np.array([self.trace_numerical(float(t)) for t in t_values])

        rel_errors = np.abs(expansion - numerical) / (np.abs(numerical) + 1e-30)
        passed = rel_errors < rtol

        return {
            "t_values": t_values,
            "expansion": expansion,
            "numerical": numerical,
            "relative_errors": rel_errors,
            "all_passed": bool(np.all(passed)),
            "n_passed": int(np.sum(passed)),
        }

    def generate_certificate(self) -> Dict[str, Any]:
        """
        Generate a QCAL validation certificate for the heat kernel coefficients.

        Returns:
            Certificate dictionary with analytical coefficients, numerical
            checks, and QCAL metadata.
        """
        coeffs = self.coefficients()

        # Quick numerical check at t = 0.005
        t_check = 0.005
        exp_val = self.trace_expansion(t_check)
        num_val = self.trace_numerical(t_check)
        rel_err = abs(exp_val - num_val) / (abs(num_val) + 1e-30)

        return {
            "protocol": "QCAL-WU-SPRUNG-HEAT-KERNEL",
            "version": "v1.0",
            "status": "✅ VALIDATED" if rel_err < 0.05 else "⚠️ CHECK NEEDED",
            "coefficients": {
                "A0": coeffs.A0,
                "A1": coeffs.A1,
                "A2": coeffs.A2,
                "A3": coeffs.A3,
                "A4": coeffs.A4,
            },
            "formulas": {
                "A0": "1/(2*pi)",
                "A1": "-(gamma + log(2*pi)) / (2*pi)",
                "A2": "7/8",
                "A3": "1/(48*pi)",
                "A4": "-gamma/(48*pi)",
            },
            "expansion": (
                "Tr(exp(-t*H)) ~ A0*ln(1/t)/t + A1/t + A2 "
                "+ A3*t*ln(1/t) + A4*t + O(t^2)"
            ),
            "validation": {
                "t_check": t_check,
                "expansion_value": exp_val,
                "numerical_value": num_val,
                "relative_error": rel_err,
            },
            "euler_gamma": coeffs.euler_gamma,
            "qcal_signature": "∴𓂀Ω∞³Φ",
            "frequency_base": F0_QCAL,
            "coherence": C_COHERENCE,
            "doi": "10.5281/zenodo.17379721",
            "author": "José Manuel Mota Burruezo Ψ ✧ ∞³",
            "orcid": "0009-0002-1923-0773",
            "institution": "Instituto de Conciencia Cuántica (ICQ)",
        }


# ---------------------------------------------------------------------------
# Module-level convenience function
# ---------------------------------------------------------------------------

def compute_heat_kernel_coefficients() -> HeatKernelCoefficients:
    """
    Convenience function: return the Wu-Sprung heat kernel coefficients.

    Returns:
        HeatKernelCoefficients with A0–A4 analytically computed.
    """
    return WuSprungHeatKernel().coefficients()


if __name__ == "__main__":  # pragma: no cover
    import json

    hk = WuSprungHeatKernel()
    coeffs = hk.coefficients()

    print("=" * 70)
    print("Wu-Sprung Heat Kernel Expansion Coefficients")
    print("=" * 70)
    print(f"\nTr(e^{{-tH}}) ~ A0·ln(1/t)/t + A1/t + A2 + A3·t·ln(1/t) + A4·t")
    print()
    print(f"  A0 = 1/(2π)                    = {coeffs.A0:.8f}  (≈ 0.15915)")
    print(f"  A1 = -(γ+ln(2π))/(2π)          = {coeffs.A1:.8f}  (≈ -0.38437)")
    print(f"  A2 = 7/8                        = {coeffs.A2:.8f}  (= 0.875)")
    print(f"  A3 = 1/(48π)                    = {coeffs.A3:.8f}  (≈ 0.00663)")
    print(f"  A4 = -γ/(48π)                   = {coeffs.A4:.8f}  (≈ -0.00383)")
    print(f"\n  γ  = {coeffs.euler_gamma:.15f}")

    print("\n--- Numerical validation ---")
    t_vals = np.array([0.001, 0.005, 0.01, 0.02, 0.05])
    for tv in t_vals:
        exp_v = hk.trace_expansion(tv)
        num_v = hk.trace_numerical(tv)
        rel = abs(exp_v - num_v) / (abs(num_v) + 1e-30)
        print(f"  t={tv:.3f}: expansion={exp_v:12.4f}  numerical={num_v:12.4f}  "
              f"rel_err={rel:.2%}")

    cert = hk.generate_certificate()
    print(f"\nStatus: {cert['status']}")
    print(f"{cert['qcal_signature']}")
    print(f"f₀ = {cert['frequency_base']} Hz · C = {cert['coherence']}")
    print("=" * 70)
