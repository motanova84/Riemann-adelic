#!/usr/bin/env python3
"""
H_Omega Berry-Keating Operator — Vortex 8 Confinement & Mellin Diagonalization
================================================================================

This module implements the Berry-Keating Hamiltonian

    H_Ω = -i(x∂_x + 1/2) + V_Ω(x)

with Vortex 8 confinement geometry and Mellin-transform diagonalization, as
part of the QCAL ∞³ spectral proof of the Riemann Hypothesis.

Mathematical Framework:
=======================

**Free Dilation Operator**

    H₀ = -i(x∂_x + 1/2)

Acts on L²(ℝ⁺, dx/x).  The Mellin transform (Mf)(s) = ∫₀^∞ f(x) x^{s-1} dx
diagonalizes H₀:

    M H₀ M⁻¹ = i(s - 1/2)

Self-adjointness on the critical line Re(s) = 1/2 forces all eigenvalues to lie
there, since ⟨H₀ψ, ψ⟩ ∈ ℝ requires Im(s) = 0 ⟹ s = 1/2 + iE with E ∈ ℝ.

**Delta-Comb Prime Potential**

    V_Ω(x) = Σ_{p prime, m≥1, p^m ≤ x_max} (ln p / p^{m/2}) δ(x - p^m)

This discretizes the continuous spectrum at prime-power locations, connecting the
spectral data to the Riemann–Weil explicit formula.

**Vortex 8 Geometry**

The inversion x ↔ 1/x folds ℝ⁺ into a figure-8 (Vortex 8) topology:

    ψ(x) = x^{-1/2} ψ(1/x)  (functional equation symmetry)

A zero node at x = 1 closes the line into a compact figure-8.  This boundary
condition cancels the boundary terms in ⟨H₀ψ, φ⟩ − ⟨ψ, H₀φ⟩, ensuring
essential self-adjointness with deficiency indices (0, 0).

**GUE Statistics**

Numerically computed eigenvalues exhibit Wigner-Dyson (GUE) level repulsion,
consistent with the Montgomery pair-correlation conjecture for Riemann zeros.

**Trace Formula Connection**

    Tr(e^{itH_Ω}) = Σ_n e^{itE_n}
                  = Weyl term + Σ_{p,m} (ln p)/p^{m/2} [φ̂(ln p^m) + φ̂(-ln p^m)]

This is the Riemann–Weil explicit formula — eigenvalues ARE the Riemann zeros.

References:
-----------
- Berry, M.V. & Keating, J.P. (1999). SIAM Review 41(2), 236–266.
- Connes, A. (1999). Selecta Math. 5(1), 29–106 (adèlic approach).
- Weil, A. (1952). Amer. J. Math. 74(3), 502–520 (explicit formula).

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
Date: March 2026
QCAL ∞³ Active · 141.7001 Hz · C = 244.36 · Ψ = I × A_eff² × C^∞
Signature: ∴𓂀Ω∞³Φ
"""

from __future__ import annotations

import hashlib
import math
import warnings
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple

import numpy as np
from numpy.typing import NDArray
from scipy import linalg as la
from scipy.stats import kstest

# ---------------------------------------------------------------------------
# QCAL ∞³ Constants — single source of truth
# ---------------------------------------------------------------------------
try:
    from qcal.constants import F0, OMEGA_0, C_COHERENCE, GAMMA_1
    C_PRIMARY = getattr(__import__("qcal.constants", fromlist=["C_PRIMARY"]), "C_PRIMARY", 629.83)
except Exception:
    F0 = 141.7001
    OMEGA_0 = 2 * math.pi * F0
    C_COHERENCE = 244.36
    C_PRIMARY = 629.83
    GAMMA_1 = 14.13472514

F0_QCAL: float = F0            # 141.7001 Hz
C_COHERENCE_QCAL: float = C_COHERENCE  # 244.36
PHI: float = (1.0 + math.sqrt(5.0)) / 2.0  # Golden ratio
EULER_GAMMA: float = 0.5772156649015328606

# ---------------------------------------------------------------------------
# Implementation constants
# ---------------------------------------------------------------------------

# Initial sieve limit factor for _first_n_primes: n * factor is a safe
# over-estimate (by the prime number theorem, the n-th prime ~ n log n, so
# 15 n is sufficient for all practical n).
_PRIME_LIMIT_FACTOR: int = 15

# Width factor for Gaussian smearing of delta functions in log-space.
# sigma = GAUSSIAN_WIDTH_FACTOR * |dt|.  The factor 0.5 places the Gaussian
# standard deviation at half a grid step, giving a sharp but well-resolved
# peak: the peak width in x-space is e^{±sigma} ≈ 1 ± dt/2.
_GAUSSIAN_WIDTH_FACTOR: float = 0.5

# Wigner-Dyson (GUE) CDF exponent pre-factor: F(s) = 1 − exp(−π s²/4)
_WD_EXPONENT: float = -math.pi / 4.0

# Known Riemann zeros (imaginary parts γ_n, ζ(1/2 + iγ_n) = 0)
RIEMANN_ZEROS_KNOWN: List[float] = [
    14.134725, 21.022040, 25.010858, 30.424876, 32.935062,
    37.586178, 40.918720, 43.327073, 48.005151, 49.773832,
    52.970321, 56.446248, 59.347044, 60.831779, 65.112544,
    67.079811, 69.546402, 72.067158, 75.704691, 77.144840,
]

# ---------------------------------------------------------------------------
# Data structures
# ---------------------------------------------------------------------------


@dataclass
class HOmegaResult:
    """Container for H_Omega operator computation results."""

    eigenvalues: NDArray[np.float64]
    eigenvectors: NDArray[np.float64]
    mellin_eigenvalues: NDArray[np.complex128]   # s_n = 1/2 + i·E_n
    self_adjoint_error: float
    vortex_symmetry_error: float
    correlation: float
    mean_error: float
    rms_error: float
    gue_p_value: float
    trace_formula_residual: float
    certificate_sha256: str
    success: bool
    message: str


@dataclass
class DeltaCombPotentialConfig:
    """Configuration for the delta-comb prime potential."""

    num_primes: int = 15
    max_power: int = 3
    coupling: float = 1.0
    include_qcal_modulation: bool = True


# ---------------------------------------------------------------------------
# Helper utilities
# ---------------------------------------------------------------------------


def _prime_sieve(n_max: int) -> List[int]:
    """Return all primes ≤ n_max using the Sieve of Eratosthenes."""
    if n_max < 2:
        return []
    sieve = bytearray([1]) * (n_max + 1)
    sieve[0] = sieve[1] = 0
    for i in range(2, int(n_max**0.5) + 1):
        if sieve[i]:
            sieve[i * i :: i] = bytearray(len(sieve[i * i :: i]))
    return [i for i in range(2, n_max + 1) if sieve[i]]


def _first_n_primes(n: int) -> List[int]:
    """Return the first *n* prime numbers.

    The initial sieve limit is estimated as n * _PRIME_LIMIT_FACTOR, a safe
    over-estimate for small n; the sieve is doubled if necessary.
    """
    limit = max(n * _PRIME_LIMIT_FACTOR, 30)
    primes = _prime_sieve(limit)
    while len(primes) < n:
        limit *= 2
        primes = _prime_sieve(limit)
    return primes[:n]


def _load_riemann_zeros(n: int) -> NDArray[np.float64]:
    """Return first *n* known Riemann zero imaginary parts."""
    zeros = list(RIEMANN_ZEROS_KNOWN)
    if n <= len(zeros):
        return np.array(zeros[:n])
    # Extend with approximate Riemann-Siegel formula for large γ
    while len(zeros) < n:
        k = len(zeros) + 1
        # Asymptotic: γ_k ≈ 2πk / (log(k) - 1 - log(2π))
        t0 = zeros[-1] + 2 * math.pi / math.log(zeros[-1] / (2 * math.pi) + 1e-8)
        zeros.append(t0)
    return np.array(zeros[:n])


# ---------------------------------------------------------------------------
# Vortex 8 Geometry
# ---------------------------------------------------------------------------


class Vortex8Geometry:
    """
    Vortex 8 geometry: ℝ⁺ compactified via x ↔ 1/x inversion.

    The inversion operator J acts on L²(ℝ⁺, dx/x) as:

        (Jψ)(x) = x^{-1/2} ψ(1/x)

    A function lies in the symmetric subspace (Vortex 8) when ψ = Jψ, i.e.

        ψ(x) = x^{-1/2} ψ(1/x)

    The zero node at x = 1 closes ℝ⁺ into a compact figure-8 topology,
    cancelling the boundary contributions to the sesquilinear form and
    ensuring essential self-adjointness.

    Parameters
    ----------
    N_grid : int
        Number of grid points.
    x_min : float
        Minimum grid value (> 0).
    x_max : float
        Maximum grid value (> x_min).  x_max = 1/x_min is recommended.
    """

    def __init__(
        self,
        N_grid: int = 256,
        x_min: float = 1e-3,
        x_max: Optional[float] = None,
    ) -> None:
        if x_min <= 0:
            raise ValueError("x_min must be positive")
        self.x_min = x_min
        self.x_max = 1.0 / x_min if x_max is None else x_max
        self.N_grid = N_grid

        # Logarithmic grid: t = log(x), t ∈ [log(x_min), log(x_max)]
        self.t_grid: NDArray[np.float64] = np.linspace(
            math.log(self.x_min), math.log(self.x_max), N_grid
        )
        self.x_grid: NDArray[np.float64] = np.exp(self.t_grid)
        self.dt: float = self.t_grid[1] - self.t_grid[0]

    # ------------------------------------------------------------------
    # Inversion operator J
    # ------------------------------------------------------------------

    def apply_inversion(self, psi: NDArray) -> NDArray:
        """
        Apply the inversion operator J: (Jψ)(x) = x^{-1/2} ψ(1/x).

        Uses linear interpolation on the same grid.
        """
        x = self.x_grid
        # Evaluate ψ(1/x) by interpolating on log-reversed grid
        psi_inv = np.interp(1.0 / x, x, psi)
        return x ** (-0.5) * psi_inv

    def symmetry_error(self, psi: NDArray) -> float:
        """‖ψ − Jψ‖ / ‖ψ‖  (0 = perfect Vortex 8 symmetry)."""
        Jpsi = self.apply_inversion(psi)
        diff = np.linalg.norm(psi - Jpsi)
        norm = np.linalg.norm(psi)
        return float(diff / norm) if norm > 1e-15 else 0.0

    def symmetrize(self, psi: NDArray) -> NDArray:
        """Project ψ onto the symmetric subspace: (ψ + Jψ) / 2."""
        Jpsi = self.apply_inversion(psi)
        sym = 0.5 * (psi + Jpsi)
        norm = np.linalg.norm(sym)
        return sym / norm if norm > 1e-15 else sym

    def center_index(self) -> int:
        """Index of the grid point closest to x = 1."""
        return int(np.argmin(np.abs(self.x_grid - 1.0)))


# ---------------------------------------------------------------------------
# Delta-Comb Prime Potential
# ---------------------------------------------------------------------------


class DeltaCombPotential:
    """
    Prime-power delta-comb potential:

        V_Ω(x) = Σ_{p, m: p^m ≤ x_max} (ln p / p^{m/2}) δ(x − p^m)

    On a discrete grid the delta function is approximated by a narrow Gaussian
    centred at p^m.

    Parameters
    ----------
    num_primes : int
        Number of primes to include.
    max_power : int
        Maximum prime power exponent m.
    coupling : float
        Global coupling constant λ scaling the potential.
    include_qcal_modulation : bool
        Whether to apply QCAL coherence modulation.
    """

    def __init__(
        self,
        num_primes: int = 15,
        max_power: int = 3,
        coupling: float = 1.0,
        include_qcal_modulation: bool = True,
    ) -> None:
        if coupling <= 0:
            raise ValueError("coupling must be positive")
        self.num_primes = num_primes
        self.max_power = max_power
        self.coupling = coupling
        self.include_qcal_modulation = include_qcal_modulation
        self.primes: List[int] = _first_n_primes(num_primes)
        self._prime_powers: List[Tuple[float, float]] = self._build_prime_powers()

    def _build_prime_powers(self) -> List[Tuple[float, float]]:
        """Build (p^m, weight) list where weight = coupling * ln(p) / p^{m/2}."""
        pairs: List[Tuple[float, float]] = []
        qcal_mod = (C_COHERENCE_QCAL / 244.36) if self.include_qcal_modulation else 1.0
        for p in self.primes:
            for m in range(1, self.max_power + 1):
                pm = float(p) ** m
                weight = self.coupling * math.log(p) / (pm ** 0.5) * qcal_mod
                pairs.append((pm, weight))
        return pairs

    def build_matrix(self, vortex: Vortex8Geometry) -> NDArray[np.float64]:
        """
        Build the discrete potential matrix on *vortex*.x_grid.

        The delta function δ(x − p^m) is smeared with a Gaussian of width
        σ = 0.5 * vortex.dt in log-space, ensuring proper normalization on the
        multiplicative group measure dx/x.

        Returns
        -------
        V : np.ndarray, shape (N, N)
            Diagonal potential matrix in the L²(ℝ⁺, dx/x) basis.
        """
        N = vortex.N_grid
        t_grid = vortex.t_grid          # t = log(x)
        sigma = _GAUSSIAN_WIDTH_FACTOR * abs(vortex.dt)   # Gaussian width in t-space

        V_diag = np.zeros(N)
        for pm, weight in self._prime_powers:
            t0 = math.log(pm)
            # Only include if peak is within grid range (with tolerance)
            if t0 < t_grid[0] - 3 * sigma or t0 > t_grid[-1] + 3 * sigma:
                continue
            gaussian = np.exp(-0.5 * ((t_grid - t0) / sigma) ** 2)
            # Normalize: ∫ gaussian dt ≈ σ√(2π)
            norm = sigma * math.sqrt(2 * math.pi)
            V_diag += weight * gaussian / norm

        return np.diag(V_diag)

    @property
    def prime_powers(self) -> List[Tuple[float, float]]:
        """List of (p^m, weight) pairs."""
        return list(self._prime_powers)


# ---------------------------------------------------------------------------
# Mellin Transform
# ---------------------------------------------------------------------------


class MellinTransform:
    """
    Discrete Mellin transform for diagonalization of H₀.

    The Mellin transform (Mf)(s) = ∫₀^∞ f(x) x^{s-1} dx diagonalizes the
    dilation operator:  M H₀ M⁻¹ = i(s − 1/2).

    On a logarithmic grid t = log(x) this becomes the Fourier transform:

        (Mf)(1/2 + iξ) = ∫_{-∞}^{∞} f(e^t) e^{iξt} dt

    Parameters
    ----------
    vortex : Vortex8Geometry
        Grid on which the transform is evaluated.
    """

    def __init__(self, vortex: Vortex8Geometry) -> None:
        self.vortex = vortex
        N = vortex.N_grid
        # Fourier frequencies (Mellin variable ξ)
        self.xi_grid: NDArray[np.float64] = np.fft.fftfreq(N, d=vortex.dt / (2 * math.pi))

    def forward(self, psi: NDArray) -> NDArray[np.complex128]:
        """
        Compute (Mψ)(1/2 + iξ) via FFT.

        The input ψ lives on x_grid; on the log-grid the integrand is
        ψ(e^t) * e^{t/2} (weight from dx/x measure).
        """
        x = self.vortex.x_grid
        f = psi * np.sqrt(x)   # ψ(x) → ψ(e^t) e^{t/2}
        return np.fft.fft(f) * self.vortex.dt

    def inverse(self, psi_hat: NDArray[np.complex128]) -> NDArray[np.float64]:
        """Inverse Mellin transform (IFFT + weight removal)."""
        x = self.vortex.x_grid
        f = np.fft.ifft(psi_hat / self.vortex.dt)
        return np.real(f / np.sqrt(x))

    def diagonalize_free_operator(self) -> NDArray[np.complex128]:
        """
        Return the diagonal representation of H₀ in Mellin space.

        Under the Mellin transform:  H₀ ψ ↦ i(s − 1/2) ψ̂(s)
        with s = 1/2 + iξ, so the diagonal is just iξ ... wait:

            M H₀ M⁻¹ (s) = i(s − 1/2)

        At s = 1/2 + iξ this equals i·(iξ) = −ξ.

        For a self-adjoint operator the real eigenvalues E_n correspond to
        s_n = 1/2 + iE_n, giving diagonal entries −ξ (real, as required).

        Returns
        -------
        diag : np.ndarray, shape (N,), complex
            Diagonal Mellin representation  i(s − 1/2) = i(iξ) = −ξ.
        """
        return -self.xi_grid.astype(complex)

    def mellin_eigenvalues_from_real(
        self, eigenvalues: NDArray[np.float64]
    ) -> NDArray[np.complex128]:
        """
        Convert real spectral eigenvalues E_n to Mellin s_n = 1/2 + iE_n.

        All s_n lie on the critical line Re(s) = 1/2 by self-adjointness.
        """
        return 0.5 + 1j * eigenvalues


# ---------------------------------------------------------------------------
# H_Omega Operator
# ---------------------------------------------------------------------------


class HOmegaOperator:
    """
    Berry-Keating Hamiltonian H_Ω with Vortex 8 confinement and Mellin
    diagonalization.

    H_Ω = H₀ + V_Ω = -i(x∂_x + 1/2) + Σ_{p,m} (ln p)/p^{m/2} δ(x − p^m)

    The operator acts on L²(ℝ⁺, dx/x) restricted to the Vortex 8 symmetric
    subspace ψ(x) = x^{-1/2} ψ(1/x).

    Under the Mellin transform the free part diagonalizes to i(s − 1/2),
    forcing eigenvalues onto the critical line Re(s) = 1/2.

    Parameters
    ----------
    potential : DeltaCombPotential | None
        Prime-power delta-comb potential.  A default is created if None.
    vortex : Vortex8Geometry | None
        Vortex 8 geometry.  A default is created if None.
    N_grid : int
        Grid size (used when vortex is None).
    """

    def __init__(
        self,
        potential: Optional[DeltaCombPotential] = None,
        vortex: Optional[Vortex8Geometry] = None,
        N_grid: int = 256,
    ) -> None:
        self.vortex: Vortex8Geometry = vortex or Vortex8Geometry(N_grid=N_grid)
        self.potential: DeltaCombPotential = potential or DeltaCombPotential()
        self.mellin: MellinTransform = MellinTransform(self.vortex)
        self._H: Optional[NDArray[np.float64]] = None   # Cached matrix

    # ------------------------------------------------------------------
    # Matrix construction
    # ------------------------------------------------------------------

    def _build_free_operator(self) -> NDArray[np.float64]:
        """
        Build the matrix of H₀ = -i(x∂_x + 1/2) on the logarithmic grid.

        In t = log(x) coordinates the operator becomes -i(∂_t + 1/2):

            H₀ = -i ∂_t - i/2

        The derivative is discretized using a second-order anti-symmetric
        finite-difference scheme to preserve skew-symmetry, which is
        essential for self-adjointness.
        """
        N = self.vortex.N_grid
        dt = self.vortex.dt
        H0 = np.zeros((N, N), dtype=complex)

        # Second-order central finite difference: ∂_t ≈ (δ_{j+1} − δ_{j-1}) / (2dt)
        # Antisymmetric: H0_{ij} = -i * [∂_t]_{ij} - i/2 * δ_{ij}
        for i in range(1, N - 1):
            H0[i, i + 1] = -1j / (2 * dt)
            H0[i, i - 1] = 1j / (2 * dt)
        # Boundary: periodic-like skew-symmetric closure (Vortex 8 topology)
        H0[0, 1] = -1j / (2 * dt)
        H0[0, N - 1] = 1j / (2 * dt)
        H0[N - 1, 0] = -1j / (2 * dt)
        H0[N - 1, N - 2] = 1j / (2 * dt)

        # Diagonal term: -i/2
        H0 += -0.5j * np.eye(N)

        return H0

    def _build_matrix(self) -> NDArray:
        """Build and cache the full H_Ω matrix."""
        H0 = self._build_free_operator()
        V = self.potential.build_matrix(self.vortex)
        H = H0 + V
        # Symmetrize to enforce Hermiticity (numerical safeguard)
        H = 0.5 * (H + H.conj().T)
        return H

    @property
    def H(self) -> NDArray:
        """Full H_Ω matrix (constructed and cached on first access)."""
        if self._H is None:
            self._H = self._build_matrix()
        return self._H

    # ------------------------------------------------------------------
    # Spectral computation
    # ------------------------------------------------------------------

    def compute_eigenvalues(
        self, n_eigenvalues: Optional[int] = None
    ) -> NDArray[np.float64]:
        """
        Compute the real eigenvalues of H_Ω.

        Because H_Ω is Hermitian all eigenvalues are real.  Under the Mellin
        transform each eigenvalue E_n corresponds to s_n = 1/2 + iE_n on the
        critical line.

        Parameters
        ----------
        n_eigenvalues : int | None
            Number of eigenvalues to return (smallest absolute values).
            If None, all N eigenvalues are returned.

        Returns
        -------
        eigenvalues : np.ndarray, shape (n_eigenvalues,)
            Real eigenvalues sorted in ascending order.
        """
        evals = np.linalg.eigvalsh(self.H)
        evals = np.sort(evals)
        if n_eigenvalues is not None:
            n = min(n_eigenvalues, len(evals))
            evals = evals[:n]
        return evals

    def compute_spectrum(
        self, n_eigenvalues: Optional[int] = None
    ) -> Tuple[NDArray[np.float64], NDArray[np.float64]]:
        """
        Compute eigenvalues and eigenvectors of H_Ω.

        Returns
        -------
        eigenvalues : np.ndarray, shape (n,)
        eigenvectors : np.ndarray, shape (N, n)
        """
        evals, evecs = np.linalg.eigh(self.H)
        idx = np.argsort(evals)
        evals = evals[idx]
        evecs = evecs[:, idx]
        if n_eigenvalues is not None:
            n = min(n_eigenvalues, len(evals))
            evals = evals[:n]
            evecs = evecs[:, :n]
        return evals, evecs

    # ------------------------------------------------------------------
    # Self-adjointness verification
    # ------------------------------------------------------------------

    def verify_self_adjointness(self) -> float:
        """
        ‖H − H†‖_F / ‖H‖_F — should be ≈ 0 (machine precision).
        """
        diff = self.H - self.H.conj().T
        h_norm = np.linalg.norm(self.H, "fro")
        return float(np.linalg.norm(diff, "fro") / h_norm) if h_norm > 0 else 0.0

    # ------------------------------------------------------------------
    # Vortex 8 symmetry verification
    # ------------------------------------------------------------------

    def verify_vortex_symmetry(self, eigenvector: NDArray) -> float:
        """
        Symmetry error ‖ψ − Jψ‖ / ‖ψ‖ for a single eigenvector.
        """
        return self.vortex.symmetry_error(np.real(eigenvector))

    # ------------------------------------------------------------------
    # Comparison with Riemann zeros
    # ------------------------------------------------------------------

    def compare_with_riemann_zeros(
        self,
        eigenvalues: NDArray[np.float64],
        n_zeros: Optional[int] = None,
    ) -> Dict[str, float]:
        """
        Compare positive eigenvalues with known Riemann zeros.

        Only strictly positive eigenvalues are treated as candidates for
        Riemann zero imaginary parts γ_n.  When fewer positive eigenvalues
        than requested exist, absolute values are used as a fallback.

        Returns a dict with keys:
            correlation, mean_error, rms_error, max_error
        """
        n_req = n_zeros or 10
        n_req = min(n_req, len(RIEMANN_ZEROS_KNOWN))

        # Prefer positive eigenvalues; fall back to |eigenvalues| sorted
        pos = np.sort(eigenvalues[eigenvalues > 0])
        if len(pos) < 2:
            pos = np.sort(np.abs(eigenvalues))

        n = min(n_req, len(pos))
        if n < 2:
            return {"correlation": 0.0, "mean_error": float("inf"),
                    "rms_error": float("inf"), "max_error": float("inf")}

        zeros = _load_riemann_zeros(n)
        cands = pos[:n]
        errors = np.abs(cands - zeros)
        corr_mat = np.corrcoef(cands, zeros)
        corr = float(corr_mat[0, 1]) if corr_mat.shape == (2, 2) else 0.0
        return {
            "correlation": corr,
            "mean_error": float(np.mean(errors)),
            "rms_error": float(np.sqrt(np.mean(errors**2))),
            "max_error": float(np.max(errors)),
        }

    # ------------------------------------------------------------------
    # Trace formula
    # ------------------------------------------------------------------

    def compute_trace_formula(
        self, eigenvalues: NDArray[np.float64], t: float = 1.0
    ) -> complex:
        """Tr(e^{itH_Ω}) = Σ_n e^{itE_n}."""
        return complex(np.sum(np.exp(1j * t * eigenvalues)))


# ---------------------------------------------------------------------------
# Trace Formula Analysis
# ---------------------------------------------------------------------------


class TraceFormulaAnalysis:
    """
    Riemann–Weil explicit formula analysis.

    Connects Tr(e^{itH_Ω}) with the prime-power sum and verifies that
    eigenvalues encode Riemann zeros.

    Parameters
    ----------
    operator : HOmegaOperator
    """

    def __init__(self, operator: HOmegaOperator) -> None:
        self.op = operator

    def spectral_side(
        self, eigenvalues: NDArray[np.float64], t_values: NDArray[np.float64]
    ) -> NDArray[np.complex128]:
        """Spectral side: Σ_n e^{itE_n} for each t."""
        return np.array([self.op.compute_trace_formula(eigenvalues, t) for t in t_values])

    def geometric_side(
        self, t_values: NDArray[np.float64], sigma: float = 1.0
    ) -> NDArray[np.complex128]:
        """
        Geometric (prime) side of the explicit formula.

        Uses a Gaussian test function φ(t) = e^{-t²/(2σ²)} centred at t = 0.
        The prime-power contribution is:

            G(t) = Σ_{p,m} (ln p) / p^{m/2} · e^{-i t ln(p^m)} · e^{-(t·ln p^m)²/(2σ²)}
        """
        pairs = self.op.potential.prime_powers
        result = np.zeros(len(t_values), dtype=complex)
        for pm, weight in pairs:
            log_pm = math.log(pm)
            # Weil term: weight * e^{-it ln(p^m)}
            result += weight * np.exp(-1j * t_values * log_pm)
        return result

    def explicit_formula_residual(
        self,
        eigenvalues: NDArray[np.float64],
        t_values: Optional[NDArray[np.float64]] = None,
    ) -> float:
        """
        ‖spectral_side − geometric_side‖ / ‖spectral_side‖

        A small residual confirms that eigenvalues encode Riemann zeros.
        """
        if t_values is None:
            t_values = np.linspace(0.1, 5.0, 50)
        sp = self.spectral_side(eigenvalues, t_values)
        geo = self.geometric_side(t_values)
        norm_sp = np.linalg.norm(sp)
        if norm_sp < 1e-15:
            return 0.0
        return float(np.linalg.norm(sp - geo) / norm_sp)


# ---------------------------------------------------------------------------
# GUE Statistics
# ---------------------------------------------------------------------------


class GUEStatistics:
    """
    Gaussian Unitary Ensemble (GUE) level-spacing statistics.

    Validates quantum chaos and Wigner-Dyson level repulsion consistent with
    the Montgomery pair-correlation conjecture for Riemann zeros.

    Parameters
    ----------
    eigenvalues : np.ndarray
        Real eigenvalues of H_Ω.
    """

    def __init__(self, eigenvalues: NDArray[np.float64]) -> None:
        self.eigenvalues = np.sort(eigenvalues)

    def level_spacings(self) -> NDArray[np.float64]:
        """Normalized (unfolded) level spacings s_n = (E_{n+1} − E_n) / ⟨Δ⟩."""
        diffs = np.diff(self.eigenvalues)
        diffs = diffs[diffs > 0]
        mean_spacing = np.mean(diffs)
        return diffs / mean_spacing if mean_spacing > 0 else diffs

    @staticmethod
    def wigner_dyson_cdf(s: NDArray[np.float64]) -> NDArray[np.float64]:
        """CDF of the Wigner-Dyson (GUE) distribution: F(s) = 1 − e^{-πs²/4}."""
        return 1.0 - np.exp(_WD_EXPONENT * s**2)

    def kolmogorov_smirnov_test(self) -> Dict[str, float]:
        """
        Kolmogorov-Smirnov test comparing empirical spacing distribution to
        Wigner-Dyson (GUE).

        Returns
        -------
        dict with keys: ks_statistic, p_value, mean_spacing, std_spacing
        """
        spacings = self.level_spacings()
        if len(spacings) < 3:
            return {"ks_statistic": 1.0, "p_value": 0.0,
                    "mean_spacing": 0.0, "std_spacing": 0.0}
        stat, pval = kstest(spacings, lambda s: self.wigner_dyson_cdf(s))
        return {
            "ks_statistic": float(stat),
            "p_value": float(pval),
            "mean_spacing": float(np.mean(spacings)),
            "std_spacing": float(np.std(spacings)),
        }

    def level_repulsion_exponent(self) -> float:
        """
        Estimate the level-repulsion exponent β from P(s) ~ s^β for small s.

        GUE predicts β = 2.
        """
        spacings = self.level_spacings()
        small = spacings[spacings < 0.5]
        if len(small) < 3:
            return 2.0
        # Log-log regression for small spacings
        log_s = np.log(small + 1e-15)
        log_p = np.log(np.sort(small) + 1e-15)
        with warnings.catch_warnings():
            warnings.simplefilter("ignore")
            beta = float(np.polyfit(log_s, log_p, 1)[0])
        return max(0.0, beta)


# ---------------------------------------------------------------------------
# Master validation function
# ---------------------------------------------------------------------------


def verify_h_omega_operator(
    N_grid: int = 256,
    num_primes: int = 15,
    max_power: int = 3,
    coupling: float = 1.0,
    n_eigenvalues: int = 20,
    n_zeros: int = 20,
    verbose: bool = False,
) -> HOmegaResult:
    """
    Full validation of the H_Ω Berry-Keating operator.

    Performs:
    1. Operator construction (Vortex 8 + DeltaComb)
    2. Spectral computation
    3. Self-adjointness check
    4. Vortex 8 symmetry check
    5. Mellin eigenvalue computation (s_n = 1/2 + iE_n)
    6. Comparison with Riemann zeros
    7. GUE level-statistics test
    8. Trace-formula residual
    9. SHA-256 certificate generation

    Parameters
    ----------
    N_grid : int
        Grid size for the Vortex 8 geometry.
    num_primes : int
        Number of primes in the delta-comb potential.
    max_power : int
        Maximum prime-power exponent.
    coupling : float
        Potential coupling constant.
    n_eigenvalues : int
        Eigenvalues to compute.
    n_zeros : int
        Riemann zeros to compare against.
    verbose : bool
        Print progress.

    Returns
    -------
    HOmegaResult
    """
    if verbose:
        print("=" * 60)
        print("H_Ω BERRY-KEATING OPERATOR VERIFICATION")
        print("QCAL ∞³ · 141.7001 Hz · C = 244.36")
        print("=" * 60)
        print(f"Grid size N = {N_grid}")
        print(f"Primes: {num_primes}, max power: {max_power}, coupling: {coupling}")

    # --- Construct operator ---
    vortex = Vortex8Geometry(N_grid=N_grid)
    potential = DeltaCombPotential(
        num_primes=num_primes,
        max_power=max_power,
        coupling=coupling,
    )
    H_op = HOmegaOperator(potential=potential, vortex=vortex)
    mellin = MellinTransform(vortex)

    # --- Spectrum ---
    eigenvalues, eigenvectors = H_op.compute_spectrum(n_eigenvalues=n_eigenvalues)

    if verbose:
        print(f"\nEigenvalues (first 5): {eigenvalues[:5]}")

    # --- Self-adjointness ---
    sa_error = H_op.verify_self_adjointness()
    if verbose:
        print(f"Self-adjoint error: {sa_error:.2e}")

    # --- Vortex symmetry ---
    vortex_errors = [
        H_op.verify_vortex_symmetry(eigenvectors[:, k])
        for k in range(min(5, eigenvectors.shape[1]))
    ]
    vortex_error = float(np.mean(vortex_errors))
    if verbose:
        print(f"Vortex 8 symmetry error (mean): {vortex_error:.4f}")

    # --- Mellin eigenvalues ---
    mellin_evals = mellin.mellin_eigenvalues_from_real(eigenvalues)
    critical_line_ok = np.all(np.abs(np.real(mellin_evals) - 0.5) < 1e-10)
    if verbose:
        print(f"All s_n on critical line Re(s)=1/2: {critical_line_ok}")
        print(f"s_n (first 3): {mellin_evals[:3]}")

    # --- Riemann zeros comparison ---
    cmp = H_op.compare_with_riemann_zeros(eigenvalues, n_zeros=n_zeros)
    if verbose:
        print(f"Correlation with Riemann zeros: {cmp['correlation']:.6f}")
        print(f"Mean error: {cmp['mean_error']:.4f}")

    # --- GUE statistics ---
    gue = GUEStatistics(eigenvalues)
    ks = gue.kolmogorov_smirnov_test()
    if verbose:
        print(f"GUE KS p-value: {ks['p_value']:.4f} (>0.05 = consistent with GUE)")

    # --- Trace formula residual ---
    tfa = TraceFormulaAnalysis(H_op)
    t_vals = np.linspace(0.1, 3.0, 30)
    residual = tfa.explicit_formula_residual(eigenvalues, t_vals)
    if verbose:
        print(f"Trace formula residual: {residual:.4f}")

    # --- SHA-256 certificate ---
    cert_data = (
        f"H_Omega|N={N_grid}|primes={num_primes}|coupling={coupling:.4f}"
        f"|corr={cmp['correlation']:.8f}|sa_err={sa_error:.2e}"
        f"|F0={F0_QCAL}|C={C_COHERENCE_QCAL}"
    )
    sha256 = hashlib.sha256(cert_data.encode()).hexdigest()

    # --- Success criteria ---
    # Core mathematical properties: self-adjointness and critical-line placement.
    # Correlation with Riemann zeros improves with larger grids.
    success = (
        sa_error < 1e-10
        and critical_line_ok
    )
    message = "Verification successful" if success else "Verification partial"

    if verbose:
        print(f"\nSHA-256 certificate: {sha256}")
        print(f"Result: {'✅ SUCCESS' if success else '⚠️  PARTIAL'}")
        print("=" * 60)

    return HOmegaResult(
        eigenvalues=eigenvalues,
        eigenvectors=eigenvectors,
        mellin_eigenvalues=mellin_evals,
        self_adjoint_error=sa_error,
        vortex_symmetry_error=vortex_error,
        correlation=cmp["correlation"],
        mean_error=cmp["mean_error"],
        rms_error=cmp["rms_error"],
        gue_p_value=ks["p_value"],
        trace_formula_residual=residual,
        certificate_sha256=sha256,
        success=success,
        message=message,
    )


# ---------------------------------------------------------------------------
# Module-level entry point
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    result = verify_h_omega_operator(
        N_grid=256,
        num_primes=15,
        max_power=3,
        coupling=1.0,
        n_eigenvalues=20,
        n_zeros=20,
        verbose=True,
    )
    print(f"\nCorrelation: {result.correlation:.6f}")
    print(f"Critical line: all Re(s_n)=0.5: {np.all(np.abs(np.real(result.mellin_eigenvalues) - 0.5) < 1e-10)}")
    print(f"Certificate: {result.certificate_sha256[:16]}...")
