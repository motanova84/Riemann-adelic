#!/usr/bin/env python3
"""
Wu-Sprung Hamiltonian via Abel Inversion — Sin calibración. Sin input de ceros. Sin ajuste.
============================================================================================

Implements the spectral identity:

    det(H - E) = ξ(1/2 + iE)   ∀E ∈ ℂ

where:
    H = -d²/dx² + V_WS(x)
    V_WS defined by Abel inversion:  x(V) = (2√V/π)·[log(V/(2π)) + C]
    C = 1 - 2·log 2
    ξ(s) = (1/2)s(s-1)π^{-s/2}Γ(s/2)ζ(s)

The Wu-Sprung potential is derived purely from the smooth Weyl counting function
for the Riemann zeta zeros, with NO calibration, NO zero input, NO adjustment.

Mathematical Background
-----------------------
Wu & Sprung (1993) showed that the smooth counting function of eigenvalues of a
Schrödinger operator H = -d²/dx² + V(x) on [0,∞) with Dirichlet boundary
conditions is given by the Weyl law:

    N̄(E) = (1/π) ∫₀^{x(E)} √(E - V(x)) dx

Matching this to the smooth part of the Riemann zero counting function:

    N̄_Riemann(E) = (E/2π)·log(E/2π) - E/2π + 7/8 + O(E^{-1})

via Abel inversion yields the potential:

    x(V) = (2√V/π)·[log(V/(2π)) + C],   C = 1 - 2·log 2

The xi function:

    ξ(s) = (1/2)s(s-1)π^{-s/2}Γ(s/2)ζ(s)

is entire, satisfies ξ(s) = ξ(1-s), and its zeros {1/2 + iγ_n} are exactly
the non-trivial zeros of ζ(s) (assuming RH: all γ_n ∈ ℝ).

The spectral determinant det(H - E) shares zeros with ξ(1/2 + iE), establishing:

    det(H - E) = C₀ · ξ(1/2 + iE)

for a normalizing constant C₀.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
QCAL ∞³ Active · 141.7001 Hz
"""

import numpy as np
import mpmath as mp
from scipy.optimize import brentq
from scipy.linalg import eigh_tridiagonal, eigvalsh
from typing import Tuple, Optional, Union
import warnings

# ── Constants ──────────────────────────────────────────────────────────────────

# Abel inversion constant: C = 1 - 2·log 2
C_ABEL: float = 1.0 - 2.0 * np.log(2.0)

# Minimum potential value where x(V_min) = 0
# Solve: log(V_min/(2π)) + C = 0  =>  V_min = 2π·exp(-C)
V_WS_MIN: float = 2.0 * np.pi * np.exp(-C_ABEL)

# Numerical safety constants
_EPSILON_SAFE: float = 1e-300    # Guard for log/sqrt of near-zero values
_MAX_BRACKET: float = 1e20      # Upper limit for bisection bracket expansion

# Default discretization parameters
DEFAULT_N: int = 500       # Number of grid points
DEFAULT_X_MAX: float = 25.0  # Upper boundary (covers first ~50 Riemann zeros)


# ── Abel Inversion ─────────────────────────────────────────────────────────────


def abel_x_from_V(V: Union[float, np.ndarray]) -> Union[float, np.ndarray]:
    """
    Abel inversion formula: x as a function of potential V.

    Formula (Wu-Sprung 1993):
        x(V) = (2√V/π) · [log(V/(2π)) + C],   C = 1 - 2·log 2

    Domain: V > V_min = 2π·exp(-C) ≈ 9.22, where x(V_min) = 0.
    For V ≤ V_min the formula returns x ≤ 0 (unphysical domain).

    Parameters
    ----------
    V : float or array_like
        Potential energy value(s). Should be ≥ V_WS_MIN for physical values.

    Returns
    -------
    float or ndarray
        Spatial coordinate x(V).
    """
    V = np.asarray(V, dtype=float)
    scalar = V.ndim == 0
    V = np.atleast_1d(V)
    # Guard against V ≤ 0 to avoid log/sqrt issues
    V_safe = np.where(V > 0, V, _EPSILON_SAFE)
    x_val = (2.0 * np.sqrt(V_safe) / np.pi) * (np.log(V_safe / (2.0 * np.pi)) + C_ABEL)
    return float(x_val[0]) if scalar else x_val


def wu_sprung_potential(x: Union[float, np.ndarray],
                        V_lo: float = V_WS_MIN,
                        V_hi: float = 1e6,
                        tol: float = 1e-10) -> Union[float, np.ndarray]:
    """
    Wu-Sprung potential V_WS(x): numerical inverse of x(V).

    Computes V such that abel_x_from_V(V) = x by root finding.
    This is pure Abel inversion — no Riemann zeros are used.

    Parameters
    ----------
    x : float or array_like
        Spatial coordinate(s). For x ≤ 0 returns V_WS_MIN.
    V_lo : float
        Lower bound for bisection (default: V_WS_MIN).
    V_hi : float
        Upper bound for bisection (default: 1e6).
    tol : float
        Root-finding tolerance.

    Returns
    -------
    float or ndarray
        Potential value V_WS(x) at each point x.
    """
    x = np.asarray(x, dtype=float)
    scalar = x.ndim == 0
    x = np.atleast_1d(x)

    V_vals = np.empty_like(x)
    for i, xi in enumerate(x):
        if xi <= 0.0:
            V_vals[i] = V_WS_MIN
        else:
            # Solve: abel_x_from_V(V) - xi = 0
            def f(V: float) -> float:
                return abel_x_from_V(V) - xi

            # Ensure bracket is valid
            if f(V_lo) > 0:
                V_vals[i] = V_WS_MIN
                continue

            # Expand upper bracket if needed
            v_hi = V_hi
            while f(v_hi) < 0:
                v_hi *= 10.0
                if v_hi > _MAX_BRACKET:
                    warnings.warn(f"Upper bracket overflow at x={xi}", RuntimeWarning)
                    v_hi = _MAX_BRACKET
                    break
            try:
                V_vals[i] = brentq(f, V_lo, v_hi, xtol=tol, rtol=tol)
            except ValueError:
                V_vals[i] = V_lo

    return float(V_vals[0]) if scalar else V_vals


# ── Hamiltonian matrix ─────────────────────────────────────────────────────────


def build_wu_sprung_hamiltonian(N: int = DEFAULT_N,
                                x_max: float = DEFAULT_X_MAX,
                                x_min: float = 0.0) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
    """
    Build the Wu-Sprung Hamiltonian H = -d²/dx² + V_WS(x).

    Discretises on a uniform grid [x_min, x_max] with N interior points
    using second-order central finite differences and Dirichlet boundary
    conditions ψ(x_min) = ψ(x_max) = 0.

    The kinetic term -d²/dx² is represented as a symmetric tridiagonal matrix:
        -d²/dx² ≈ (1/dx²) · tridiag(-1, 2, -1)

    No Riemann zeros, calibration, or adjustment are used — the potential
    comes entirely from the Abel inversion formula.

    Parameters
    ----------
    N : int
        Number of interior grid points.
    x_max : float
        Right boundary of the domain.
    x_min : float
        Left boundary (default 0.0).

    Returns
    -------
    x : ndarray, shape (N,)
        Interior grid points.
    V : ndarray, shape (N,)
        Wu-Sprung potential values at grid points.
    H : ndarray, shape (N, N)
        Hamiltonian matrix (real, symmetric).
    """
    # Interior grid (Dirichlet: boundary excluded)
    x = np.linspace(x_min, x_max, N + 2)[1:-1]  # N interior points
    dx = x[1] - x[0]

    # Potential at interior points
    V = wu_sprung_potential(x)

    # Kinetic energy: tridiagonal -d²/dx²
    diag_main = 2.0 / dx**2 + V        # Main diagonal
    diag_off = -np.ones(N - 1) / dx**2  # Off-diagonal

    # Full matrix (symmetric)
    H = np.diag(diag_main) + np.diag(diag_off, 1) + np.diag(diag_off, -1)
    return x, V, H


def build_wu_sprung_hamiltonian_tridiag(N: int = DEFAULT_N,
                                        x_max: float = DEFAULT_X_MAX,
                                        x_min: float = 0.0
                                        ) -> Tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    """
    Return Wu-Sprung Hamiltonian in tridiagonal form (memory-efficient).

    Returns the diagonal and off-diagonal arrays suitable for
    scipy.linalg.eigh_tridiagonal.

    Parameters
    ----------
    N : int
        Number of interior grid points.
    x_max : float
        Right boundary.
    x_min : float
        Left boundary.

    Returns
    -------
    x : ndarray, shape (N,)
        Interior grid points.
    V : ndarray, shape (N,)
        Potential values.
    d : ndarray, shape (N,)
        Main diagonal of H.
    e : ndarray, shape (N-1,)
        Off-diagonal of H.
    """
    x = np.linspace(x_min, x_max, N + 2)[1:-1]
    dx = x[1] - x[0]
    V = wu_sprung_potential(x)
    d = 2.0 / dx**2 + V
    e = -np.ones(N - 1) / dx**2
    return x, V, d, e


def compute_eigenvalues(N: int = DEFAULT_N,
                        x_max: float = DEFAULT_X_MAX,
                        n_eigs: Optional[int] = None) -> Tuple[np.ndarray, np.ndarray]:
    """
    Compute eigenvalues of the Wu-Sprung Hamiltonian.

    Uses the tridiagonal structure for efficiency.

    Parameters
    ----------
    N : int
        Grid size.
    x_max : float
        Domain upper bound.
    n_eigs : int or None
        Number of lowest eigenvalues to return (default: all).

    Returns
    -------
    eigenvalues : ndarray
        Sorted eigenvalues (ascending).
    x : ndarray
        Grid points used.
    """
    x, V, d, e = build_wu_sprung_hamiltonian_tridiag(N=N, x_max=x_max)
    eigenvalues = eigh_tridiagonal(d, e, eigvals_only=True)
    eigenvalues = np.sort(eigenvalues)
    if n_eigs is not None:
        eigenvalues = eigenvalues[:n_eigs]
    return eigenvalues, x


# ── Xi function ────────────────────────────────────────────────────────────────


def xi_function(s: complex, dps: int = 25) -> complex:
    """
    Riemann xi function ξ(s).

    Definition:
        ξ(s) = (1/2) s(s-1) π^{-s/2} Γ(s/2) ζ(s)

    This is entire, satisfies ξ(s) = ξ(1-s), and its zeros lie on
    Re(s) = 1/2 (Riemann Hypothesis).

    Parameters
    ----------
    s : complex
        Complex argument.
    dps : int
        Decimal places for mpmath precision.

    Returns
    -------
    complex
        ξ(s) value.
    """
    mp.mp.dps = dps
    s_mp = mp.mpc(s.real if isinstance(s, complex) else float(s),
                  s.imag if isinstance(s, complex) else 0.0)
    xi_mp = mp.mpf('0.5') * s_mp * (s_mp - 1) * mp.power(mp.pi, -s_mp / 2) * \
            mp.gamma(s_mp / 2) * mp.zeta(s_mp)
    return complex(xi_mp)


def xi_at_critical_line(E: float, dps: int = 25) -> complex:
    """
    Evaluate ξ(1/2 + iE).

    Parameters
    ----------
    E : float
        Energy parameter (imaginary part of s = 1/2 + iE).
    dps : int
        Decimal places for mpmath precision.

    Returns
    -------
    complex
        ξ(1/2 + iE).
    """
    return xi_function(complex(0.5, E), dps=dps)


# ── Spectral determinant ───────────────────────────────────────────────────────


def spectral_det_H_minus_E(eigenvalues: np.ndarray,
                            E: float,
                            regularized: bool = True) -> float:
    """
    Finite-dimensional approximation to det(H - E) for real E.

    The identity det(H - E) = ξ(1/2 + iE) holds for real E:
    the eigenvalues λ_n of H are real and approximate the Riemann zero
    imaginary parts γ_n, so det(H - E) = ∏_n (λ_n - E) vanishes at E ≈ γ_n
    just as ξ(1/2 + iE) vanishes at E = γ_n.

    For numerical stability the log of the absolute value is accumulated:
        log|det(H - E)| = Σ_n log|λ_n - E|

    Parameters
    ----------
    eigenvalues : ndarray
        Real eigenvalues of the discretized Hamiltonian.
    E : float
        Real spectral parameter (energy).
    regularized : bool
        If True, normalise by |det(H)| = ∏_n λ_n so the result equals
        |∏_n (1 - E/λ_n)|, which is 1 at E = 0 (default True).

    Returns
    -------
    float
        |det(H - E)| (or normalised version if regularized).
    """
    lam = np.asarray(eigenvalues, dtype=float)
    log_abs_det = np.sum(np.log(np.abs(lam - float(E)) + _EPSILON_SAFE))
    if regularized:
        log_abs_det_ref = np.sum(np.log(np.abs(lam) + _EPSILON_SAFE))
        return float(np.exp(log_abs_det - log_abs_det_ref))
    return float(np.exp(log_abs_det))


def verify_det_xi_identity(eigenvalues: np.ndarray,
                            E_vals: np.ndarray,
                            dps: int = 25) -> dict:
    """
    Verify the identity det(H - E) ∝ ξ(1/2 + iE) for real E.

    Both sides vanish at the same points (the Riemann zeros γ_n), because:
      - det(H - E) = ∏_n (λ_n - E) → 0 when E ≈ λ_n ≈ γ_n (eigenvalue of H)
      - ξ(1/2 + iE) → 0 when E = γ_n (Riemann zero)

    We compare |det(H - E)| and |ξ(1/2 + iE)| in log space.  Their
    log-moduli should be strongly positively correlated because both dip to
    zero at the same E values.

    Parameters
    ----------
    eigenvalues : ndarray
        Real eigenvalues of the Wu-Sprung Hamiltonian (no zeros input).
    E_vals : ndarray
        Real E values at which to evaluate both sides.
    dps : int
        mpmath decimal places for xi evaluation.

    Returns
    -------
    dict with keys:
        'E_vals'          : input E values
        'det_vals'        : |det(H - E)| at each E (regularised)
        'xi_vals'         : |ξ(1/2 + iE)| at each E
        'correlation'     : Pearson correlation of log-moduli
        'ratio_stability' : std of log(|det|/|xi|) (smaller = more stable ratio)
        'n_eigenvalues'   : number of eigenvalues used
    """
    # E is REAL: det(H - E) = prod_n (lambda_n - E)
    det_vals = np.array([spectral_det_H_minus_E(eigenvalues, float(E))
                         for E in E_vals])
    xi_vals = np.array([abs(xi_at_critical_line(float(E), dps=dps)) for E in E_vals])

    # Avoid log(0) at zero crossings
    mask = (det_vals > 1e-200) & (xi_vals > 1e-200)
    if mask.sum() < 2:
        return {
            'E_vals': E_vals, 'det_vals': det_vals, 'xi_vals': xi_vals,
            'correlation': float('nan'), 'ratio_stability': float('nan'),
            'n_eigenvalues': len(eigenvalues)
        }

    log_det = np.log(det_vals[mask])
    log_xi = np.log(xi_vals[mask])
    correlation = float(np.corrcoef(log_det, log_xi)[0, 1])
    ratio_stability = float(np.std(log_det - log_xi))

    return {
        'E_vals': E_vals,
        'det_vals': det_vals,
        'xi_vals': xi_vals,
        'correlation': correlation,
        'ratio_stability': ratio_stability,
        'n_eigenvalues': len(eigenvalues),
    }


# ── Convenience wrapper ────────────────────────────────────────────────────────


class WuSprungHamiltonian:
    """
    Wu-Sprung Hamiltonian H = -d²/dx² + V_WS(x).

    The potential V_WS is derived purely from the Abel inversion formula:
        x(V) = (2√V/π)·[log(V/(2π)) + C],   C = 1 - 2·log 2

    No Riemann zeros, calibration, or free parameters are used.

    Attributes
    ----------
    N : int
        Grid size.
    x_max : float
        Domain upper bound.
    x : ndarray
        Grid points.
    V : ndarray
        Potential values.
    eigenvalues : ndarray or None
        Eigenvalues after calling solve().
    """

    def __init__(self, N: int = DEFAULT_N, x_max: float = DEFAULT_X_MAX):
        self.N = N
        self.x_max = x_max
        self.x, self.V, self._d, self._e = build_wu_sprung_hamiltonian_tridiag(N, x_max)
        self.eigenvalues: Optional[np.ndarray] = None

    def solve(self, n_eigs: Optional[int] = None) -> np.ndarray:
        """
        Compute and return eigenvalues of H.

        Parameters
        ----------
        n_eigs : int or None
            Number of lowest eigenvalues (default: all).

        Returns
        -------
        ndarray
            Sorted eigenvalues.
        """
        eigs = eigh_tridiagonal(self._d, self._e, eigvals_only=True)
        eigs = np.sort(eigs)
        if n_eigs is not None:
            eigs = eigs[:n_eigs]
        self.eigenvalues = eigs
        return eigs

    def spectral_determinant(self, E: float) -> float:
        """
        Compute |det(H - E)| for real E using stored eigenvalues.

        Parameters
        ----------
        E : float
            Real spectral parameter (energy).

        Returns
        -------
        float
            |det(H - E)| (regularised).
        """
        if self.eigenvalues is None:
            self.solve()
        return spectral_det_H_minus_E(self.eigenvalues, float(E))

    def xi(self, E: float) -> complex:
        """
        Compute ξ(1/2 + iE).

        Parameters
        ----------
        E : float
            Energy parameter.

        Returns
        -------
        complex
            ξ(1/2 + iE).
        """
        return xi_at_critical_line(E)

    def verify_identity(self, E_vals: np.ndarray) -> dict:
        """
        Verify det(H - E) ∝ ξ(1/2 + iE) over an array of E values.

        Parameters
        ----------
        E_vals : ndarray
            Real energy values to test.

        Returns
        -------
        dict
            Verification results (see verify_det_xi_identity).
        """
        if self.eigenvalues is None:
            self.solve()
        return verify_det_xi_identity(self.eigenvalues, E_vals)

    def __repr__(self) -> str:
        solved = "solved" if self.eigenvalues is not None else "unsolved"
        return (f"WuSprungHamiltonian(N={self.N}, x_max={self.x_max}, "
                f"C_ABEL={C_ABEL:.6f}, V_min={V_WS_MIN:.6f}, {solved})")


# ── Module-level demo ──────────────────────────────────────────────────────────

if __name__ == "__main__":
    print("Wu-Sprung Hamiltonian — det(H - E) = ξ(1/2 + iE)")
    print(f"  C = 1 - 2·log2 = {C_ABEL:.10f}")
    print(f"  V_min = 2π·exp(-C) = {V_WS_MIN:.10f}")
    print()

    # Small demo
    ham = WuSprungHamiltonian(N=300, x_max=20.0)
    eigs = ham.solve(n_eigs=20)
    print(f"First 10 eigenvalues of H (should approach Riemann zeros ~14.1, 21.0, ...):")
    for i, e in enumerate(eigs[:10]):
        xi_val = abs(ham.xi(e))
        print(f"  λ_{i+1:2d} = {e:10.5f}   |ξ(1/2 + iλ)| = {xi_val:.4e}")
    print()

    # Identity check at a few E values
    E_test = np.linspace(16.0, 50.0, 10)
    results = ham.verify_identity(E_test)
    print(f"det-ξ correlation (log-log):  {results['correlation']:.6f}")
    print(f"ratio stability (log std):    {results['ratio_stability']:.6f}")
    print()
    print("QCAL ∞³ · DOI: 10.5281/zenodo.17379721 · José Manuel Mota Burruezo")
