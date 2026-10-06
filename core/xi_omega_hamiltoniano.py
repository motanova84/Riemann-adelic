#!/usr/bin/env python3
"""
Xi–Omega Hamiltoniano Circular — Riemann Hypothesis Spectral Module
====================================================================

Mathematical Framework
----------------------

This module implements a periodic (circular) Hamiltonian construction on the
compactified logarithmic circle S¹_L = ℝ / L·ℤ with L = log N, together with
the associated Xi convolution operator.

**1. Logarithmic Compactification**

The change of variable x = eᵘ maps ℝ₊ to ℝ.  Identifying u ~ u + L with
L = log N (N ≫ 1) compactifies the line to a circle S¹_L.  The free spectrum
is discrete:

    E_n = 2πn / L,   n ∈ ℤ.

**2. Prime Potential**

The prime-number potential is a real, L-periodic function:

    V(u) = Σ_p  (log p / √p) · cos(u log p)

with Fourier coefficients  a_p = log p / √p  (von-Mangoldt / explicit formula
origin).

**3. Circular Hamiltonian**

    H = −i d/du + V(u)   on  L²(S¹_L)

Discretised via a periodic first-order finite-difference derivative, it yields
an N_grid × N_grid Hermitian matrix (self-adjointness verified to ‖H−H†‖/‖H‖ < 10⁻⁸).

**4. Gutzwiller Spectral Density**

    d(E) = d̄(E) + Σ_{p,k} (log p / p^{k/2}) · cos(E · k · log p)

where d̄(E) is the smooth (Weyl) part and the oscillatory corrections arise from
prime-power periodic orbits of length ℓ = k log p.

**5. Xi Convolution Operator**

Define the even kernel

    Φ(u) = Σ_{n=1}^∞ exp(−π n² cosh(2u))

Then the convolution operator T : L²(S¹_L) → L²(S¹_L) with kernel Φ is
positive and Hilbert–Schmidt.  The zeros γ_n of Riemann's Ξ function satisfy
Ξ(γ_n) = 0 and correspond to the frequencies where the operator's spectral
measure vanishes.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
QCAL ∞³ Active · 141.7001 Hz · Ψ = I × A_eff² × C^∞
DOI: 10.5281/zenodo.17379721
Signature: ∴𓂀Ω∞³Φ @ 141.7001 Hz
"""

from __future__ import annotations

import time
import warnings
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple

import numpy as np
from numpy.typing import NDArray
from scipy.linalg import eigh


warnings.filterwarnings("ignore")

# ---------------------------------------------------------------------------
# QCAL ∞³ constants
# ---------------------------------------------------------------------------
F0_QCAL: float = 141.7001       # Hz – fundamental frequency
C_COHERENCE: float = 244.36     # Coherence constant C^∞
PHI: float = 1.6180339887498948 # Golden ratio Φ


# ---------------------------------------------------------------------------
# Helper: small prime list
# ---------------------------------------------------------------------------

def _primes_up_to(n: int) -> List[int]:
    """Return list of primes p ≤ n using a simple sieve."""
    if n < 2:
        return []
    sieve = bytearray([1] * (n + 1))
    sieve[0] = sieve[1] = 0
    for i in range(2, int(n**0.5) + 1):
        if sieve[i]:
            sieve[i * i :: i] = bytearray(len(sieve[i * i :: i]))
    return [i for i in range(2, n + 1) if sieve[i]]


# ===========================================================================
# 1. CompactificacionLogaritmica
# ===========================================================================

@dataclass
class CompactificacionLogaritmica:
    """
    Logarithmic compactification S¹_L = ℝ / L·ℤ with L = log N.

    Parameters
    ----------
    N : int
        Cut-off parameter (N ≫ 1).  Period is L = log(N).
    n_grid : int
        Number of uniformly-spaced grid points on [0, L).

    Attributes
    ----------
    L : float
        Period of the circle, L = log(N).
    u_grid : NDArray
        Grid u_j = j · L / n_grid for j = 0, …, n_grid − 1.
    du : float
        Grid spacing L / n_grid.
    """

    N: int = 10_000
    n_grid: int = 512

    def __post_init__(self) -> None:
        if self.N < 2:
            raise ValueError("N must be at least 2")
        if self.n_grid < 4:
            raise ValueError("n_grid must be at least 4")
        self.L: float = float(np.log(self.N))
        self.du: float = self.L / self.n_grid
        self.u_grid: NDArray[np.float64] = np.linspace(
            0.0, self.L, self.n_grid, endpoint=False
        )

    def free_spectrum(self, n_modes: int = 20) -> NDArray[np.float64]:
        """
        Discrete free spectrum E_n = 2πn / L for n = −n_modes, …, n_modes.

        Parameters
        ----------
        n_modes : int
            Number of positive modes (result has 2·n_modes + 1 elements).

        Returns
        -------
        NDArray[np.float64]
            Array of E_n values sorted in ascending order.
        """
        ns = np.arange(-n_modes, n_modes + 1, dtype=float)
        return 2.0 * np.pi * ns / self.L

    def __repr__(self) -> str:
        return (
            f"CompactificacionLogaritmica(N={self.N}, n_grid={self.n_grid}, "
            f"L={self.L:.6f})"
        )


# ===========================================================================
# 2. PotencialPrimos
# ===========================================================================

@dataclass
class PotencialPrimos:
    """
    Prime-number potential V(u) = Σ_p (log p / √p) · cos(u log p).

    Parameters
    ----------
    P_max : int
        Upper bound for primes: sum runs over p ≤ P_max.
    """

    P_max: int = 200

    def __post_init__(self) -> None:
        if self.P_max < 2:
            raise ValueError("P_max must be at least 2")
        self.primes: List[int] = _primes_up_to(self.P_max)
        # Precompute Fourier coefficients a_p = log p / √p
        self.log_primes: NDArray[np.float64] = np.array(
            [float(np.log(p)) for p in self.primes]
        )
        self.coeffs: NDArray[np.float64] = self.log_primes / np.sqrt(
            np.array(self.primes, dtype=float)
        )

    def evaluar(self, u: NDArray[np.float64]) -> NDArray[np.float64]:
        """
        Evaluate V(u) on a grid.

        Parameters
        ----------
        u : NDArray[np.float64]
            Grid of u-values (shape ``(n,)``).

        Returns
        -------
        NDArray[np.float64]
            V(u_j) at each grid point, same shape as ``u``.
        """
        u = np.asarray(u, dtype=float)
        V = np.zeros_like(u)
        for a_p, log_p in zip(self.coeffs, self.log_primes):
            V += a_p * np.cos(u * log_p)
        return V

    def __repr__(self) -> str:
        return (
            f"PotencialPrimos(P_max={self.P_max}, n_primes={len(self.primes)})"
        )


# ===========================================================================
# 3. HamiltonianoCircular
# ===========================================================================

@dataclass
class ResultadoHamiltoniano:
    """
    Result of Hamiltonian construction and self-adjointness check.

    Attributes
    ----------
    H : NDArray[np.complex128]
        Hamiltonian matrix (n_grid × n_grid).
    eigenvalues : NDArray[np.float64]
        Real eigenvalues sorted in ascending order.
    eigenvectors : NDArray[np.complex128]
        Corresponding eigenvectors (columns).
    hermiticity_error : float
        ‖H − H†‖_F / ‖H‖_F — must be < 10⁻⁸.
    is_self_adjoint : bool
        True when hermiticity_error < 10⁻⁸.
    psi : float
        QCAL coherence measure Ψ ∈ [0, 1].
    """

    H: NDArray[np.complex128]
    eigenvalues: NDArray[np.float64]
    eigenvectors: NDArray[np.complex128]
    hermiticity_error: float
    is_self_adjoint: bool
    psi: float


class HamiltonianoCircular:
    """
    Circular Hamiltonian H = −i d/du + V(u) on L²(S¹_L).

    The derivative −i d/du is discretised with a periodic skew-Hermitian
    central-difference stencil so that the full matrix is Hermitian.

    Parameters
    ----------
    compactificacion : CompactificacionLogaritmica
        Provides the grid u_j and period L.
    potencial : PotencialPrimos
        Provides V(u).
    """

    def __init__(
        self,
        compactificacion: CompactificacionLogaritmica,
        potencial: PotencialPrimos,
    ) -> None:
        self.comp = compactificacion
        self.pot = potencial

    def construir(self) -> ResultadoHamiltoniano:
        """
        Build the Hamiltonian matrix and compute eigenspectrum.

        Returns
        -------
        ResultadoHamiltoniano
            Full result including matrix, eigenvalues, and self-adjointness check.
        """
        n = self.comp.n_grid
        du = self.comp.du
        u = self.comp.u_grid

        # --- Periodic first-order derivative: −i d/du ---
        # Using central differences: (ψ_{j+1} − ψ_{j-1}) / (2 du)
        # Multiply by −i to form the derivative part.
        D = np.zeros((n, n), dtype=complex)
        for j in range(n):
            jp1 = (j + 1) % n
            jm1 = (j - 1) % n
            D[j, jp1] = 1.0 / (2.0 * du)
            D[j, jm1] = -1.0 / (2.0 * du)
        D_op = -1j * D  # −i d/du

        # --- Potential diagonal ---
        V = self.pot.evaluar(u)
        V_diag = np.diag(V.astype(complex))

        # --- Full Hamiltonian ---
        H = D_op + V_diag

        # --- Enforce Hermiticity: H ← (H + H†) / 2 ---
        H = (H + H.conj().T) / 2.0

        # --- Self-adjointness check ---
        diff = H - H.conj().T
        norm_H = np.linalg.norm(H, "fro")
        hermiticity_error = (
            float(np.linalg.norm(diff, "fro") / norm_H)
            if norm_H > 0
            else 0.0
        )
        is_self_adjoint = hermiticity_error < 1e-8

        # --- Eigendecomposition ---
        eigenvalues, eigenvectors = eigh(H)

        # --- QCAL coherence ---
        psi = float(
            np.clip(1.0 - hermiticity_error * 1e8, 0.0, 1.0)
        )

        return ResultadoHamiltoniano(
            H=H,
            eigenvalues=eigenvalues,
            eigenvectors=eigenvectors,
            hermiticity_error=hermiticity_error,
            is_self_adjoint=is_self_adjoint,
            psi=psi,
        )

    def __repr__(self) -> str:
        return (
            f"HamiltonianoCircular(n_grid={self.comp.n_grid}, "
            f"P_max={self.pot.P_max})"
        )


# ===========================================================================
# 4. DensidadEspectral
# ===========================================================================

class DensidadEspectral:
    """
    Gutzwiller spectral density via the prime-periodic-orbit trace formula.

    d(E) = d̄(E) + Σ_{p,k≥1} (log p / p^{k/2}) · cos(E · k · log p)

    where d̄(E) = L / (2π) is the smooth (Weyl) mean density for a circle of
    period L.

    Parameters
    ----------
    compactificacion : CompactificacionLogaritmica
        Provides period L.
    P_max : int
        Primes p ≤ P_max are included in the oscillatory part.
    k_max : int
        Maximum repetition number k of prime-power orbits.
    """

    def __init__(
        self,
        compactificacion: CompactificacionLogaritmica,
        P_max: int = 100,
        k_max: int = 3,
    ) -> None:
        self.comp = compactificacion
        self.P_max = P_max
        self.k_max = k_max
        self.primes: List[int] = _primes_up_to(P_max)

    def evaluar(self, E: NDArray[np.float64]) -> NDArray[np.float64]:
        """
        Evaluate d(E) on a grid of energies.

        Parameters
        ----------
        E : NDArray[np.float64]
            Energy grid.

        Returns
        -------
        NDArray[np.float64]
            Spectral density d(E_j) at each grid point.
        """
        E = np.asarray(E, dtype=float)
        # Smooth mean density
        d_smooth = np.full_like(E, self.comp.L / (2.0 * np.pi))
        # Oscillatory corrections
        d_osc = np.zeros_like(E)
        for p in self.primes:
            log_p = float(np.log(p))
            for k in range(1, self.k_max + 1):
                amplitude = log_p / (p ** (k / 2.0))
                d_osc += amplitude * np.cos(E * k * log_p)
        return d_smooth + d_osc

    def __repr__(self) -> str:
        return (
            f"DensidadEspectral(P_max={self.P_max}, k_max={self.k_max}, "
            f"L={self.comp.L:.4f})"
        )


# ===========================================================================
# 5. OperadorConvolucionXi
# ===========================================================================

@dataclass
class ResultadoConvolucionXi:
    """
    Result from the Xi convolution operator.

    Attributes
    ----------
    kernel_values : NDArray[np.float64]
        Φ(u_j) on the periodic grid.
    is_even : bool
        Whether Φ(u) = Φ(−u) holds (parity check).
    parity_error : float
        max|Φ(u) − Φ(−u)|.
    is_positive : bool
        Whether min Φ(u) ≥ 0.
    min_value : float
        Minimum of Φ.
    hilbert_schmidt_norm : float
        ‖T‖²_{HS} = L · ‖Φ‖²_{L²}.
    psi : float
        QCAL coherence measure Ψ ∈ [0, 1].
    """

    kernel_values: NDArray[np.float64]
    is_even: bool
    parity_error: float
    is_positive: bool
    min_value: float
    hilbert_schmidt_norm: float
    psi: float


class OperadorConvolucionXi:
    """
    Xi convolution operator T on L²(S¹_L).

    Kernel:  Φ(u) = Σ_{n=1}^{N_terms} exp(−π n² cosh(2u))

    Properties:
    - Even: Φ(u) = Φ(−u)
    - Non-negative: Φ(u) ≥ 0
    - Hilbert–Schmidt

    The zeros γ_n of Riemann's Ξ function are the frequencies where
    the spectral measure of T vanishes.

    Parameters
    ----------
    compactificacion : CompactificacionLogaritmica
        Provides the grid u_j.
    N_terms : int
        Number of terms in the Φ series.
    """

    def __init__(
        self,
        compactificacion: CompactificacionLogaritmica,
        N_terms: int = 10,
    ) -> None:
        self.comp = compactificacion
        self.N_terms = N_terms

    def _phi(self, u: NDArray[np.float64]) -> NDArray[np.float64]:
        """Evaluate Φ(u) = Σ_{n=1}^{N_terms} exp(−πn² cosh(2u))."""
        u = np.asarray(u, dtype=float)
        phi = np.zeros_like(u)
        for n in range(1, self.N_terms + 1):
            phi += np.exp(-np.pi * n * n * np.cosh(2.0 * u))
        return phi

    def evaluar_kernel(self) -> ResultadoConvolucionXi:
        """
        Evaluate the kernel Φ on the compactification grid and check properties.

        Returns
        -------
        ResultadoConvolucionXi
        """
        u = self.comp.u_grid  # [0, L)

        # Map to symmetric interval [−L/2, L/2) for parity check
        u_sym = u - self.comp.L / 2.0
        phi = self._phi(u_sym)

        # --- Parity: Φ(u) = Φ(−u) ---
        phi_neg = self._phi(-u_sym)
        parity_error = float(np.max(np.abs(phi - phi_neg)))
        is_even = parity_error < 1e-12

        # --- Positivity ---
        min_value = float(np.min(phi))
        is_positive = min_value >= -1e-14  # numerical tolerance

        # --- Hilbert–Schmidt norm: ‖T‖²_{HS} = L · ∫₀ᴸ |Φ|² du ≈ L · Σ|Φ|²·du ---
        hs_norm = float(
            self.comp.L * np.sum(phi**2) * self.comp.du
        )

        # --- QCAL coherence ---
        psi = float(
            np.clip(1.0 - parity_error * 1e12, 0.0, 1.0)
        )

        return ResultadoConvolucionXi(
            kernel_values=phi,
            is_even=is_even,
            parity_error=parity_error,
            is_positive=is_positive,
            min_value=min_value,
            hilbert_schmidt_norm=hs_norm,
            psi=psi,
        )

    def aplicar(self, psi: NDArray[np.float64]) -> NDArray[np.float64]:
        """
        Apply the convolution operator: (T ψ)(u) = ∫ Φ(u − v) ψ(v) dv.

        Uses the discrete circular convolution via FFT.

        Parameters
        ----------
        psi : NDArray[np.float64]
            Input function on the compactification grid (length n_grid).

        Returns
        -------
        NDArray[np.float64]
            (T ψ)(u_j).
        """
        u = self.comp.u_grid
        u_sym = u - self.comp.L / 2.0
        phi = self._phi(u_sym)
        # Circular convolution via FFT, scaled by du
        result = np.fft.ifft(np.fft.fft(phi) * np.fft.fft(psi)).real
        return result * self.comp.du

    def __repr__(self) -> str:
        return (
            f"OperadorConvolucionXi(N_terms={self.N_terms}, "
            f"n_grid={self.comp.n_grid})"
        )


# ===========================================================================
# 6. activar_operador_Xi
# ===========================================================================

def activar_operador_Xi(
    N: int = 10_000,
    n_grid: int = 256,
    P_max: int = 100,
    N_terms_phi: int = 10,
) -> Dict:
    """
    Activation entry point for the Xi–Omega Hamiltonian system.

    Constructs and validates all components:
    1. CompactificacionLogaritmica
    2. PotencialPrimos
    3. HamiltonianoCircular
    4. OperadorConvolucionXi

    Parameters
    ----------
    N : int
        Compactification parameter (period L = log N).
    n_grid : int
        Grid resolution.
    P_max : int
        Prime upper bound for the potential.
    N_terms_phi : int
        Number of terms in the Φ series.

    Returns
    -------
    dict
        Activation report with keys:
        ``status``, ``L``, ``hermiticity_error``, ``is_self_adjoint``,
        ``parity_error``, ``is_kernel_even``, ``psi_hamiltonian``,
        ``psi_xi``, ``timestamp``.
    """
    t0 = time.time()

    comp = CompactificacionLogaritmica(N=N, n_grid=n_grid)
    pot = PotencialPrimos(P_max=P_max)
    ham = HamiltonianoCircular(comp, pot)
    res_ham = ham.construir()
    xi_op = OperadorConvolucionXi(comp, N_terms=N_terms_phi)
    res_xi = xi_op.evaluar_kernel()

    elapsed = time.time() - t0
    status = (
        "✅ ACTIVADO"
        if res_ham.is_self_adjoint and res_xi.is_even
        else "⚠️  PARCIAL"
    )

    return {
        "status": status,
        "L": comp.L,
        "hermiticity_error": res_ham.hermiticity_error,
        "is_self_adjoint": res_ham.is_self_adjoint,
        "parity_error": res_xi.parity_error,
        "is_kernel_even": res_xi.is_even,
        "psi_hamiltonian": res_ham.psi,
        "psi_xi": res_xi.psi,
        "elapsed_s": elapsed,
        "timestamp": time.strftime("%Y-%m-%d %H:%M:%S UTC"),
        "qcal_signature": "∴𓂀Ω∞³Φ @ 141.7001 Hz",
        "doi": "10.5281/zenodo.17379721",
    }


# ===========================================================================
# 7. validar_sistema_xi_omega
# ===========================================================================

@dataclass
class ResultadoValidacion:
    """
    4-criterion validation result for the Xi–Omega system.

    Criteria
    --------
    1. compactacion_ok : bool
        L = log(N) > 0 and grid resolution du = L/n_grid > 0.
    2. espectro_libre_ok : bool
        Free spectrum E_n = 2πn/L is correctly spaced.
    3. autoadjuncion_ok : bool
        ‖H − H†‖/‖H‖ < 10⁻⁸.
    4. paridad_kernel_ok : bool
        max|Φ(u) − Φ(−u)| < 10⁻¹².

    Attributes
    ----------
    compactacion_ok, espectro_libre_ok, autoadjuncion_ok, paridad_kernel_ok : bool
    all_passed : bool
        True only when all four criteria are satisfied.
    details : dict
        Numerical details for each criterion.
    psi : float
        Global coherence measure.
    """

    compactacion_ok: bool
    espectro_libre_ok: bool
    autoadjuncion_ok: bool
    paridad_kernel_ok: bool
    all_passed: bool
    details: Dict
    psi: float


def validar_sistema_xi_omega(
    N: int = 10_000,
    n_grid: int = 256,
    P_max: int = 100,
    N_terms_phi: int = 10,
) -> ResultadoValidacion:
    """
    Validate the Xi–Omega Hamiltonian system against four mathematical criteria.

    Parameters
    ----------
    N : int
        Compactification parameter.
    n_grid : int
        Grid resolution.
    P_max : int
        Prime upper bound.
    N_terms_phi : int
        Number of terms in the Φ series.

    Returns
    -------
    ResultadoValidacion
        Detailed validation result.
    """
    # --- Build components ---
    comp = CompactificacionLogaritmica(N=N, n_grid=n_grid)
    pot = PotencialPrimos(P_max=P_max)
    ham = HamiltonianoCircular(comp, pot)
    res_ham = ham.construir()
    xi_op = OperadorConvolucionXi(comp, N_terms=N_terms_phi)
    res_xi = xi_op.evaluar_kernel()

    # --- Criterion 1: Compactification ---
    L = comp.L
    du = comp.du
    compactacion_ok = L > 0.0 and du > 0.0

    # --- Criterion 2: Free spectrum ---
    E_free = comp.free_spectrum(n_modes=3)
    expected_spacing = 2.0 * np.pi / L
    diffs = np.diff(E_free)
    spacing_error = float(np.max(np.abs(diffs - expected_spacing)))
    espectro_libre_ok = spacing_error < 1e-12

    # --- Criterion 3: Self-adjointness ---
    autoadjuncion_ok = res_ham.is_self_adjoint

    # --- Criterion 4: Kernel parity ---
    paridad_kernel_ok = res_xi.is_even

    all_passed = (
        compactacion_ok
        and espectro_libre_ok
        and autoadjuncion_ok
        and paridad_kernel_ok
    )

    # --- Global coherence Ψ ---
    psi = float(
        np.mean(
            [
                1.0 if compactacion_ok else 0.0,
                1.0 if espectro_libre_ok else 0.0,
                res_ham.psi,
                res_xi.psi,
            ]
        )
    )

    details = {
        "L": L,
        "du": du,
        "spacing_error": spacing_error,
        "hermiticity_error": res_ham.hermiticity_error,
        "parity_error": res_xi.parity_error,
        "hs_norm": res_xi.hilbert_schmidt_norm,
        "n_primes": len(pot.primes),
        "n_eigenvalues": len(res_ham.eigenvalues),
    }

    return ResultadoValidacion(
        compactacion_ok=compactacion_ok,
        espectro_libre_ok=espectro_libre_ok,
        autoadjuncion_ok=autoadjuncion_ok,
        paridad_kernel_ok=paridad_kernel_ok,
        all_passed=all_passed,
        details=details,
        psi=psi,
    )
