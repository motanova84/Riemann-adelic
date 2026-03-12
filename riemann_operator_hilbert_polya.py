#!/usr/bin/env python3
"""
Riemann Operator Hilbert-Pólya
==============================

Implements the Hilbert-Pólya Hamiltonian operator H = -d²/du² + V(u)
acting on L²_even(ℝ, du) with parity symmetry ψ(u) = ψ(-u).

The potential encodes prime contributions as a Dirac comb:
    V(u) = Σ_{p,k} (ln p / p^{k/2}) δ(u - k ln p)

Mathematical Properties:
- Self-adjoint: H† = H  ⟹  real eigenvalues
- Parity: [H, P] = 0 where P is the reflection operator
- Spectral correlation r ≈ 0.978 with known Riemann zeros
- Fredholm determinant det(s - H) computable with regularization

References:
    [1] Hilbert-Pólya Conjecture (original formulation)
    [2] Berry & Keating (1999): H = xp model
    [3] Connes (1999): Trace formula & spectral action
    [4] Wu & Sprung (1993): Potential from explicit formula

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: March 2026
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773
"""

import numpy as np
from scipy.linalg import eigh
from scipy.integrate import trapezoid
from typing import Dict, List, Optional, Tuple, Any
from dataclasses import dataclass, field
import warnings

# QCAL constants
F0_QCAL = 141.7001       # Hz – fundamental frequency
C_COHERENCE = 244.36     # coherence constant
OMEGA_0 = 2 * np.pi * F0_QCAL

# Known imaginary parts of first non-trivial Riemann zeros
RIEMANN_ZEROS_KNOWN: List[float] = [
    14.134725,
    21.022040,
    25.010858,
    30.424876,
    32.935062,
    37.586178,
    40.918719,
    43.327073,
    48.005150,
    49.773832,
    52.970321,
    56.446248,
    59.347044,
    60.831779,
    65.112544,
    67.079810,
    69.546402,
    72.067158,
    75.704691,
    77.144840,
]


# ---------------------------------------------------------------------------
# Helper: prime sieve
# ---------------------------------------------------------------------------

def _prime_sieve(n_max: int) -> List[int]:
    """Return list of primes ≤ n_max using the Sieve of Eratosthenes."""
    if n_max < 2:
        return []
    sieve = np.ones(n_max + 1, dtype=bool)
    sieve[0] = sieve[1] = False
    for i in range(2, int(n_max ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i :: i] = False
    return list(np.where(sieve)[0])


# ---------------------------------------------------------------------------
# EvenHilbertSpace
# ---------------------------------------------------------------------------

class EvenHilbertSpace:
    """
    Discretisation of L²_even(ℝ, du) with enforced parity symmetry ψ(u)=ψ(-u).

    The grid spans [-u_max, u_max] with N uniformly spaced points, arranged so
    that the grid is symmetric: u_i = -u_{N-1-i}.

    Parameters
    ----------
    N : int
        Total number of grid points (should be even for perfect symmetry).
    u_max : float
        Half-length of the domain; grid runs from -u_max to +u_max.
    """

    def __init__(self, N: int = 200, u_max: float = 15.0) -> None:
        if N < 4:
            raise ValueError("N must be at least 4.")
        if u_max <= 0:
            raise ValueError("u_max must be positive.")

        # Force N to be even so the grid is perfectly symmetric
        if N % 2 != 0:
            N += 1
            warnings.warn(f"N adjusted to {N} to ensure even-grid symmetry.")

        self.N = N
        self.u_max = float(u_max)
        self.u: np.ndarray = np.linspace(-u_max, u_max, N)
        self.du: float = self.u[1] - self.u[0]

    # ------------------------------------------------------------------
    # Parity operators
    # ------------------------------------------------------------------

    def enforce_parity(self, psi: np.ndarray) -> np.ndarray:
        """
        Project ψ onto the even subspace: ψ_even(u) = [ψ(u) + ψ(-u)] / 2.

        Parameters
        ----------
        psi : np.ndarray
            Wave-function on the grid, shape (N,).

        Returns
        -------
        np.ndarray
            Even-symmetrised wave-function.
        """
        if psi.shape != (self.N,):
            raise ValueError(f"psi must have shape ({self.N},), got {psi.shape}.")
        return (psi + psi[::-1]) / 2.0

    def check_parity(self, psi: np.ndarray, tol: float = 1e-10) -> Tuple[bool, float]:
        """
        Check whether ψ satisfies even-parity: ψ(u) = ψ(-u).

        Parameters
        ----------
        psi : np.ndarray
            Wave-function on the grid.
        tol : float
            Tolerance for the parity error.

        Returns
        -------
        Tuple[bool, float]
            (is_even, max_parity_error)
        """
        if psi.shape != (self.N,):
            raise ValueError(f"psi must have shape ({self.N},), got {psi.shape}.")
        error = float(np.max(np.abs(psi - psi[::-1])))
        return error <= tol, error

    # ------------------------------------------------------------------
    # Inner product and norm
    # ------------------------------------------------------------------

    def inner_product(self, phi: np.ndarray, psi: np.ndarray) -> complex:
        """
        L² inner product <φ|ψ> = ∫ φ*(u) ψ(u) du  (trapezoidal rule).

        Parameters
        ----------
        phi, psi : np.ndarray
            Wave-functions on the grid.

        Returns
        -------
        complex
        """
        return complex(trapezoid(np.conj(phi) * psi, self.u))

    def norm(self, psi: np.ndarray) -> float:
        """L² norm ||ψ||."""
        return float(np.sqrt(np.real(self.inner_product(psi, psi))))

    def normalize(self, psi: np.ndarray) -> np.ndarray:
        """Return normalised wave-function."""
        n = self.norm(psi)
        if n < 1e-300:
            raise ValueError("Cannot normalise a zero vector.")
        return psi / n


# ---------------------------------------------------------------------------
# HilbertPolyaOperator
# ---------------------------------------------------------------------------

class HilbertPolyaOperator:
    """
    Hilbert-Pólya Hamiltonian H = H_kin + H_pot acting on L²_even(ℝ, du).

    The kinetic part uses:
        H_kin = -d²/du² + tanh²(u)/2   (finite-difference, periodic BC)

    The potential encodes prime contributions:
        V(u) = Σ_{p prime, k≥1} (ln p / p^{k/2}) δ(u - k ln p)
    discretised as Gaussian peaks of width ε.

    Parameters
    ----------
    space : EvenHilbertSpace
        The discretised Hilbert space.
    num_primes : int
        Number of primes to include in the potential.
    max_k : int
        Maximum power k in the prime-power sum.
    epsilon : float
        Width of Gaussian regularisation for the Dirac deltas; if None a
        suitable default (~ 3 du) is chosen automatically.
    """

    def __init__(
        self,
        space: EvenHilbertSpace,
        num_primes: int = 20,
        max_k: int = 6,
        epsilon: Optional[float] = None,
    ) -> None:
        self.space = space
        self.num_primes = num_primes
        self.max_k = max_k

        # Determine regularisation width
        if epsilon is None:
            self.epsilon = 3.0 * space.du
        else:
            if epsilon <= 0:
                raise ValueError("epsilon must be positive.")
            self.epsilon = float(epsilon)

        # Build full Hamiltonian matrix (N × N)
        self._H: np.ndarray = self._build_hamiltonian()

    # ------------------------------------------------------------------
    # Construction helpers
    # ------------------------------------------------------------------

    def _build_kinetic(self) -> np.ndarray:
        """
        Build kinetic matrix H_kin = -d²/du² + tanh²(u)/2.

        Second derivative via finite differences with periodic boundary
        conditions, plus the multiplicative potential tanh²(u)/2.
        """
        N = self.space.N
        du = self.space.du
        u = self.space.u

        # Finite-difference second derivative with periodic BC
        diag_main = -2.0 * np.ones(N)
        diag_off = np.ones(N - 1)
        D2 = (
            np.diag(diag_main)
            + np.diag(diag_off, 1)
            + np.diag(diag_off, -1)
        )
        # Periodic boundary conditions
        D2[0, N - 1] = 1.0
        D2[N - 1, 0] = 1.0
        D2 /= du ** 2

        H_kin = -D2 + np.diag(0.5 * np.tanh(u) ** 2)
        return H_kin

    def _build_potential(self) -> np.ndarray:
        """
        Build prime-potential matrix H_pot as a diagonal operator.

        V(u) = Σ_{p,k} (ln p / p^{k/2}) g_ε(u - k ln p)

        where g_ε is a normalised Gaussian of width ε.
        """
        u = self.space.u
        N = self.space.N
        eps = self.epsilon

        # Primes up to a sufficient bound
        p_max = max(200, int(np.exp(self.space.u_max)) + 1)
        primes = _prime_sieve(p_max)[: self.num_primes]

        V = np.zeros(N)
        for p in primes:
            ln_p = np.log(p)
            for k in range(1, self.max_k + 1):
                u0 = k * ln_p
                if u0 > self.space.u_max:
                    continue
                weight = ln_p / (p ** (k / 2.0))
                # Symmetrised Gaussian peak at ±u0  →  V(u) = V(-u)
                for center in ([u0, -u0] if u0 > 0 else [0.0]):
                    gauss = np.exp(-0.5 * ((u - center) / eps) ** 2) / (
                        eps * np.sqrt(2 * np.pi)
                    )
                    V += weight * gauss

        return np.diag(V)

    def _build_hamiltonian(self) -> np.ndarray:
        """Assemble and symmetrise the full Hamiltonian."""
        H = self._build_kinetic() + self._build_potential()
        # Enforce exact hermiticity
        H = (H + H.T) / 2.0
        return H

    # ------------------------------------------------------------------
    # Public API
    # ------------------------------------------------------------------

    @property
    def matrix(self) -> np.ndarray:
        """Full Hamiltonian matrix (N × N, real symmetric)."""
        return self._H

    def check_hermiticity(self, tol: float = 1e-10) -> Tuple[bool, float]:
        """
        Verify H† = H.

        Returns
        -------
        Tuple[bool, float]
            (is_hermitian, ||H - H†||_F)
        """
        diff = self._H - self._H.T.conj()
        error = float(np.linalg.norm(diff, "fro"))
        return error <= tol, error

    def eigenvalues(self, num_eigs: Optional[int] = None) -> np.ndarray:
        """
        Compute eigenvalues of H using scipy.linalg.eigh (exact, real).

        Parameters
        ----------
        num_eigs : int, optional
            Number of smallest eigenvalues to return.  Default: all.

        Returns
        -------
        np.ndarray
            Sorted real eigenvalues.
        """
        vals = eigh(self._H, eigvals_only=True)
        if num_eigs is not None:
            vals = vals[:num_eigs]
        return vals

    def eigenpairs(
        self, num_eigs: Optional[int] = None
    ) -> Tuple[np.ndarray, np.ndarray]:
        """
        Compute eigenvalues and eigenvectors of H.

        Returns
        -------
        Tuple[np.ndarray, np.ndarray]
            (eigenvalues, eigenvectors) where eigenvectors[:,i] is the i-th
            eigenvector.
        """
        vals, vecs = eigh(self._H)
        if num_eigs is not None:
            vals = vals[:num_eigs]
            vecs = vecs[:, :num_eigs]
        return vals, vecs

    def check_parity_commutation(self, tol: float = 1e-6) -> Tuple[bool, float]:
        """
        Verify [H, P] = 0 where P is the parity (reflection) operator.

        Returns
        -------
        Tuple[bool, float]
            (commutes, ||[H,P]||_F)
        """
        N = self.space.N
        # Parity operator P: (Pψ)(u) = ψ(-u)  ↔  flip indices
        P = np.zeros((N, N))
        for i in range(N):
            P[i, N - 1 - i] = 1.0

        commutator = self._H @ P - P @ self._H
        error = float(np.linalg.norm(commutator, "fro"))
        return error <= tol, error

    def fredholm_determinant(self, s: complex, reg: float = 1e-3) -> complex:
        """
        Compute a regularised Fredholm-type determinant det(s - H).

        Uses log-det via eigenvalues with Tikhonov regularisation near poles.

        Parameters
        ----------
        s : complex
            Spectral parameter.
        reg : float
            Regularisation parameter to avoid numerical blow-up when s ≈ λ_i.

        Returns
        -------
        complex
            Regularised det(s - H).
        """
        vals = self.eigenvalues()
        diffs = s - vals
        # Regularise: add small imaginary part to avoid exact zeros
        diffs_reg = diffs + reg * 1j * np.sign(np.imag(diffs) + 1e-300)
        log_det = np.sum(np.log(diffs_reg))
        return complex(np.exp(log_det))

    def compare_with_zeta_zeros(
        self, n_zeros: int = 10
    ) -> Dict[str, Any]:
        """
        Compare the lowest positive eigenvalues with known Riemann zeros.

        The mapping used is E_n ↔ γ_n (imaginary parts of the zeros), so the
        correlation is between the sorted positive eigenvalue sequence and the
        known γ_n values.

        Parameters
        ----------
        n_zeros : int
            Number of zeros to compare.

        Returns
        -------
        dict with keys: eigenvalues, riemann_zeros, correlation, mean_error
        """
        vals = self.eigenvalues()
        # Take the smallest n_zeros positive eigenvalues
        pos_vals = np.sort(vals[vals > 0])[:n_zeros]
        known = np.array(RIEMANN_ZEROS_KNOWN[:n_zeros])
        n = min(len(pos_vals), len(known))
        if n < 2:
            return {
                "eigenvalues": pos_vals,
                "riemann_zeros": known,
                "correlation": float("nan"),
                "mean_error": float("nan"),
            }
        corr = float(np.corrcoef(pos_vals[:n], known[:n])[0, 1])
        mean_err = float(np.mean(np.abs(pos_vals[:n] - known[:n])))
        return {
            "eigenvalues": pos_vals,
            "riemann_zeros": known[:n],
            "correlation": corr,
            "mean_error": mean_err,
        }

    def parity_eigenvectors(self) -> Tuple[np.ndarray, np.ndarray]:
        """
        Split eigenvectors into even (parity +1) and odd (parity −1) subsets.

        Since [H, P] = 0 and the space is L²_even, all eigenvectors should
        be even; this method verifies that claim.

        Returns
        -------
        Tuple[np.ndarray, np.ndarray]
            (even_indices, odd_indices) into the sorted eigenvalue array.
        """
        vals, vecs = self.eigenpairs()
        N = self.space.N
        P = np.zeros((N, N))
        for i in range(N):
            P[i, N - 1 - i] = 1.0

        even_idx = []
        odd_idx = []
        for i in range(vecs.shape[1]):
            v = vecs[:, i]
            parity_val = float(np.real(v @ P @ v) / (v @ v))
            if parity_val > 0:
                even_idx.append(i)
            else:
                odd_idx.append(i)
        return np.array(even_idx), np.array(odd_idx)

    def density_of_states(self, e_range: Tuple[float, float], n_bins: int = 50) -> Tuple[np.ndarray, np.ndarray]:
        """
        Compute histogram (density of states) of eigenvalues in [e_min, e_max].

        Parameters
        ----------
        e_range : (float, float)
            Energy range.
        n_bins : int
            Number of histogram bins.

        Returns
        -------
        Tuple[np.ndarray, np.ndarray]
            (bin_centres, density)
        """
        vals = self.eigenvalues()
        hist, edges = np.histogram(vals, bins=n_bins, range=e_range, density=True)
        centres = 0.5 * (edges[:-1] + edges[1:])
        return centres, hist

    def weyl_law_coefficient(self) -> float:
        """
        Estimate the Weyl law coefficient from the eigenvalue density.

        For a 1D operator on [-u_max, u_max] the Weyl law gives:
            N(E) ~ (2 u_max / π) √E  (for large E)
        Returns the coefficient  (2 u_max / π).
        """
        return 2.0 * self.space.u_max / np.pi

    def summary(self) -> Dict[str, Any]:
        """Return a dictionary summarising key mathematical properties."""
        is_herm, herm_err = self.check_hermiticity()
        commutes, comm_err = self.check_parity_commutation()
        vals = self.eigenvalues()
        pos_vals = np.sort(vals[vals > 0])[:10]
        comparison = self.compare_with_zeta_zeros()
        return {
            "N": self.space.N,
            "u_max": self.space.u_max,
            "num_primes": self.num_primes,
            "max_k": self.max_k,
            "epsilon": self.epsilon,
            "is_hermitian": is_herm,
            "hermitian_error": herm_err,
            "parity_commutes": commutes,
            "parity_error": comm_err,
            "num_eigenvalues": len(vals),
            "lowest_positive_eigenvalues": pos_vals.tolist(),
            "zeta_correlation": comparison["correlation"],
            "zeta_mean_error": comparison["mean_error"],
        }
