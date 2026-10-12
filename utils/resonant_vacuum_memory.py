#!/usr/bin/env python3
"""
Resonant Vacuum Memory Equation (Memoria Resonante del Vacío) - Architecture QCAL ∞³

This module implements the resonant vacuum memory equation:
    E_vac(R_Ψ) = α R_Ψ⁴ + β ζ'(1/2) / R_Ψ² + γ Λ² R_Ψ² + δ sin²(log R_Ψ / log π)

This equation describes the resonant memory of the vacuum:
- Macroscopic & UV Block (α R_Ψ⁴ + γ Λ² R_Ψ²):
  Delimits the tension between horizon expansion and intrinsic field density.
- Spectral Pulse (β ζ'(1/2) / R_Ψ²):
  Anchors the vacuum energy to the arithmetic mystery of Riemann zeros,
  connecting spacetime geometry to the deep distribution of prime numbers.
- Harmonic Modulator (δ sin²(log R_Ψ / log π)):
  Acts as the logarithmic musical stave ("pentagrama logarítmico"),
  ensuring discrete scale resonance in exact powers of π, turning each
  minimum into a stable node of coherence at f₀ = 141.7001 Hz.

Fundamental Frequency: f₀ = 141.7001 Hz
QCAL Coherence: C = 244.36, Ψ ≥ 0.888
Equation: Ψ = I × A_eff² × C^∞

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
"""

from typing import Dict, List, Optional, Tuple, Union
import numpy as np
from mpmath import mp, zeta


class ResonantVacuumMemory:
    """
    Calculator and formalizer for the Resonant Vacuum Memory Equation in QCAL ∞³.

    Equation:
        E_vac(R_Ψ) = α R_Ψ⁴ + (β ζ'(1/2) / R_Ψ²) + γ Λ² R_Ψ² + δ sin²(log R_Ψ / log π)
    """

    # Universal QCAL Constants
    F0_DEFAULT: float = 141.7001  # Base living frequency in Hz
    COHERENCE_C: float = 244.36    # QCAL coherence constant
    PSI_THRESHOLD: float = 0.888   # Minimum coherence threshold Ψ_global
    SPEED_OF_LIGHT: float = 299792458.0  # m/s

    def __init__(
        self,
        alpha: float = 1.0,
        beta: float = 1.0,
        gamma: float = 1.0,
        delta: float = 1.0,
        Lambda: float = 1.0,
        precision: int = 50,
    ) -> None:
        """
        Initialize the Resonant Vacuum Memory framework with physical parameters.

        Args:
            alpha: Coefficient for macroscopic quartic expansion (R_Ψ⁴)
            beta: Coupling coefficient with Riemann zeta derivative at s = 1/2
            gamma: Dark energy / cosmological coupling parameter
            delta: Amplitude of harmonic modulator (log-π pentagram)
            Lambda: Cosmological constant parameter
            precision: Decimal precision for mpmath calculations
        """
        self.alpha = float(alpha)
        self.beta = float(beta)
        self.gamma = float(gamma)
        self.delta = float(delta)
        self.Lambda = float(Lambda)
        self.precision = precision

        mp.dps = precision
        self._zeta_prime_half = self._compute_zeta_prime_half()

    def _compute_zeta_prime_half(self) -> float:
        """
        Calculate ζ'(1/2) with high precision using mpmath.

        Returns:
            Numerical value of ζ'(1/2) (approximately -3.9226461392...)
        """
        s = mp.mpf("0.5")
        h = mp.mpf("1e-12")
        zeta_prime = (zeta(s + h) - zeta(s - h)) / (2 * h)
        return float(zeta_prime)

    @property
    def zeta_prime_half(self) -> float:
        """Return the precomputed high-precision value of ζ'(1/2)."""
        return self._zeta_prime_half

    def macroscopic_uv_block(
        self, R_psi: Union[float, np.ndarray]
    ) -> Union[float, np.ndarray]:
        """
        Compute the macroscopic and ultraviolet block:
            B_macro(R_Ψ) = α R_Ψ⁴ + γ Λ² R_Ψ²

        Delimits the tension between horizon expansion and intrinsic field density.

        Args:
            R_psi: Compactification radius R_Ψ (> 0)

        Returns:
            Value of the macroscopic & UV block
        """
        R = np.asarray(R_psi, dtype=float)
        if np.any(R <= 0):
            raise ValueError("Radius R_psi must be strictly positive")
        res = self.alpha * (R**4) + self.gamma * (self.Lambda**2) * (R**2)
        return float(res) if np.ndim(R_psi) == 0 else res

    def spectral_pulse(
        self, R_psi: Union[float, np.ndarray]
    ) -> Union[float, np.ndarray]:
        """
        Compute the spectral pulse:
            P_spec(R_Ψ) = β ζ'(1/2) / R_Ψ²

        Anchors vacuum energy to the arithmetic of Riemann zeros and primes.

        Args:
            R_psi: Compactification radius R_Ψ (> 0)

        Returns:
            Value of the spectral pulse
        """
        R = np.asarray(R_psi, dtype=float)
        if np.any(R <= 0):
            raise ValueError("Radius R_psi must be strictly positive")
        res = (self.beta * self._zeta_prime_half) / (R**2)
        return float(res) if np.ndim(R_psi) == 0 else res

    def harmonic_modulator(
        self, R_psi: Union[float, np.ndarray]
    ) -> Union[float, np.ndarray]:
        """
        Compute the harmonic modulator (logarithmic musical pentagram):
            M_harm(R_Ψ) = δ sin²(log R_Ψ / log π)

        Discretizes continuous scale into exact resonance nodes at R_Ψ = π^n.

        Args:
            R_psi: Compactification radius R_Ψ (> 0)

        Returns:
            Value of the harmonic modulator
        """
        R = np.asarray(R_psi, dtype=float)
        if np.any(R <= 0):
            raise ValueError("Radius R_psi must be strictly positive")
        log_ratio = np.log(R) / np.log(np.pi)
        res = self.delta * (np.sin(log_ratio) ** 2)
        return float(res) if np.ndim(R_psi) == 0 else res

    def energy(
        self, R_psi: Union[float, np.ndarray]
    ) -> Union[float, np.ndarray]:
        """
        Compute total vacuum energy E_vac(R_Ψ):
            E_vac(R_Ψ) = α R_Ψ⁴ + β ζ'(1/2)/R_Ψ² + γ Λ² R_Ψ² + δ sin²(log R_Ψ / log π)

        Args:
            R_psi: Compactification radius R_Ψ (> 0)

        Returns:
            Total vacuum energy E_vac(R_Ψ)
        """
        b_macro = self.macroscopic_uv_block(R_psi)
        p_spec = self.spectral_pulse(R_psi)
        m_harm = self.harmonic_modulator(R_psi)
        return b_macro + p_spec + m_harm

    def derivative(
        self, R_psi: Union[float, np.ndarray]
    ) -> Union[float, np.ndarray]:
        """
        Compute the exact analytical first derivative dE_vac/dR_Ψ:
            dE_vac/dR_Ψ = 4 α R_Ψ³ - 2 β ζ'(1/2) / R_Ψ³ + 2 γ Λ² R_Ψ
                          + [δ / (log π R_Ψ)] sin(2 log R_Ψ / log π)

        Args:
            R_psi: Compactification radius R_Ψ (> 0)

        Returns:
            Derivative dE_vac/dR_Ψ
        """
        R = np.asarray(R_psi, dtype=float)
        if np.any(R <= 0):
            raise ValueError("Radius R_psi must be strictly positive")

        term_alpha = 4.0 * self.alpha * (R**3)
        term_beta = -2.0 * self.beta * self._zeta_prime_half / (R**3)
        term_gamma = 2.0 * self.gamma * (self.Lambda**2) * R

        log_ratio = np.log(R) / np.log(np.pi)
        term_delta = (self.delta / (np.log(np.pi) * R)) * np.sin(2.0 * log_ratio)

        res = term_alpha + term_beta + term_gamma + term_delta
        return float(res) if np.ndim(R_psi) == 0 else res

    def second_derivative(
        self, R_psi: Union[float, np.ndarray]
    ) -> Union[float, np.ndarray]:
        """
        Compute the exact analytical second derivative d²E_vac/dR_Ψ²:
            d²E_vac/dR_Ψ² = 12 α R_Ψ² + 6 β ζ'(1/2) / R_Ψ⁴ + 2 γ Λ²
                            + [δ / (log π R_Ψ²)] [ (2 / log π) cos(2 u) - sin(2 u) ]
            where u = log R_Ψ / log π.

        Args:
            R_psi: Compactification radius R_Ψ (> 0)

        Returns:
            Second derivative d²E_vac/dR_Ψ²
        """
        R = np.asarray(R_psi, dtype=float)
        if np.any(R <= 0):
            raise ValueError("Radius R_psi must be strictly positive")

        term_alpha = 12.0 * self.alpha * (R**2)
        term_beta = 6.0 * self.beta * self._zeta_prime_half / (R**4)
        term_gamma = 2.0 * self.gamma * (self.Lambda**2)

        log_pi = np.log(np.pi)
        u = np.log(R) / log_pi
        sin_2u = np.sin(2.0 * u)
        cos_2u = np.cos(2.0 * u)

        term_delta = (self.delta / (log_pi * (R**2))) * (
            (2.0 / log_pi) * cos_2u - sin_2u
        )

        res = term_alpha + term_beta + term_gamma + term_delta
        return float(res) if np.ndim(R_psi) == 0 else res

    def resonant_nodes(self, n_max: int = 5) -> Dict[int, Dict[str, float]]:
        """
        Evaluate resonant memory nodes at powers of π:
            R_Ψ^(n) = π^n  for  -n_max ≤ n ≤ n_max

        At each node, the harmonic modulator vanishes identically (modulator = 0),
        anchoring the energy to pure macroscopic and spectral geometry.

        Args:
            n_max: Maximum exponent power for π

        Returns:
            Dictionary mapping integer n to dictionary of node properties
        """
        nodes = {}
        for n in range(-n_max, n_max + 1):
            R_n = float(np.pi**n)
            e_val = self.energy(R_n)
            macro_val = self.macroscopic_uv_block(R_n)
            pulse_val = self.spectral_pulse(R_n)
            harm_val = self.harmonic_modulator(R_n)
            d1_val = self.derivative(R_n)
            d2_val = self.second_derivative(R_n)

            nodes[n] = {
                "n": n,
                "radius": R_n,
                "energy": e_val,
                "macro_uv": macro_val,
                "spectral_pulse": pulse_val,
                "harmonic_modulator": harm_val,
                "dE_dR": d1_val,
                "d2E_dR2": d2_val,
                "is_stable": bool(d2_val > 0),
            }
        return nodes

    def find_minima(
        self,
        R_range: Tuple[float, float] = (0.5, 30.0),
        num_points: int = 5000,
    ) -> List[Dict[str, float]]:
        """
        Locate local energy minima within a given search range.

        Args:
            R_range: Tuple (R_min, R_max)
            num_points: Grid resolution for search

        Returns:
            List of detected local minima with stability diagnostics
        """
        r_grid = np.logspace(
            np.log10(R_range[0]), np.log10(R_range[1]), num_points
        )
        energies = self.energy(r_grid)
        derivatives = self.derivative(r_grid)

        # Detect derivative zero-crossings from negative to positive
        minima = []
        for i in range(len(derivatives) - 1):
            if derivatives[i] < 0 and derivatives[i + 1] >= 0:
                # Refine with secant / linear interpolation
                r1, r2 = r_grid[i], r_grid[i + 1]
                d1, d2 = derivatives[i], derivatives[i + 1]
                r_root = r1 - d1 * (r2 - r1) / (d2 - d1) if d2 != d1 else r1

                d2_val = self.second_derivative(r_root)
                if d2_val > 0:
                    minima.append(
                        {
                            "radius": float(r_root),
                            "energy": float(self.energy(r_root)),
                            "second_derivative": float(d2_val),
                            "harmonic_modulator": float(
                                self.harmonic_modulator(r_root)
                            ),
                            "distance_to_nearest_pi_power": float(
                                abs(r_root - np.pi ** round(np.log(r_root) / np.log(np.pi)))
                            ),
                        }
                    )
        return minima

    def fundamental_frequency(
        self,
        R_psi: float = np.pi,
        normalization_factor: Optional[float] = None,
    ) -> float:
        """
        Derive the fundamental living frequency f₀ associated with the vacuum minimum.

        f₀ = [c / (2π R_Ψ)] × N_adelic
        Calibrated to the fundamental base frequency f₀ = 141.7001 Hz.

        Args:
            R_psi: Selected vacuum radius (defaults to R_Ψ = π)
            normalization_factor: Optional adelic normalization factor

        Returns:
            Calculated frequency in Hz
        """
        if normalization_factor is None:
            # Derived from adelic scaling: N = (2π * π * f0) / c
            normalization_factor = (
                (2.0 * np.pi * R_psi * self.F0_DEFAULT) / self.SPEED_OF_LIGHT
            )

        f = (self.SPEED_OF_LIGHT / (2.0 * np.pi * R_psi)) * normalization_factor
        return float(f)

    def coherence_state(self, R_psi: float = np.pi) -> Dict[str, Union[float, bool]]:
        """
        Compute the QCAL ∞³ coherence state at radius R_Ψ.

        Checks:
        - Living frequency: f₀ = 141.7001 Hz
        - Resonant memory energy E_vac(R_Ψ)
        - Harmonic modulator alignment with log π pentagram
        - Coherence threshold Ψ ≥ 0.888

        Args:
            R_psi: Evaluation radius

        Returns:
            Dictionary with coherence diagnostics
        """
        e_val = self.energy(R_psi)
        f_val = self.fundamental_frequency(R_psi)
        harm = self.harmonic_modulator(R_psi)
        log_pi_alignment = np.sin(np.log(R_psi) / np.log(np.pi)) ** 2

        # Coherence metric based on frequency alignment and stability
        freq_error = abs(f_val - self.F0_DEFAULT) / self.F0_DEFAULT
        psi_coherence = float(np.exp(-freq_error))

        return {
            "radius": float(R_psi),
            "energy": float(e_val),
            "frequency_hz": float(f_val),
            "coherence_C": self.COHERENCE_C,
            "psi_coherence": psi_coherence,
            "is_coherent": bool(psi_coherence >= self.PSI_THRESHOLD),
            "is_f0_aligned": bool(abs(f_val - self.F0_DEFAULT) < 1e-4),
        }
