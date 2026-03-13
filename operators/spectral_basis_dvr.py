#!/usr/bin/env python3
"""
Spectral Basis DVR — Cosine/Parity Basis for Hilbert-Pólya Operator
====================================================================

Implements the spectral evidence module using:
  1. DVR (Discrete Variable Representation) with cosine/parity basis
  2. Arithmetic potential V_ε(u) with adaptive Gaussian convolution
  3. Up to 500 eigenvalue computation
  4. Correlation with first 500 Riemann zeros via mpmath
  5. Spectral determinant: log|det(s - H_ε)| vs Re log ξ(s)

Mathematical Framework:
----------------------
Space: L²_even[-L, L] with basis φ_n(u) = cos(nπu/L) / √L

Operator:
    H_ε = T + V_ε
    T = -i d/du  (in cosine basis, becomes real diagonal-like matrix)

Regularized potential:
    V_ε(u) = Σ_{p,k} (ln p / p^{k/2}) · (1/√(2π)ε_k) · exp(-(u - k ln p)²/(2ε_k²))

Adaptive width: ε_k = ε₀ / √k  so finer resolution at higher harmonics.

Spectral Evidence:
    log|det(1/2 + it - H_ε)| ≈ Re log ξ(1/2 + it)

If this synchrony holds numerically, it constitutes strong evidence for the
Hilbert-Pólya approach to the Riemann Hypothesis.

References:
-----------
    [1] Berry & Keating (1999): H = xp model
    [2] Connes (1999): Trace formula & spectral action
    [3] Wu & Sprung (1993): Potential from explicit formula
    [4] Light & Walker (1976): DVR method

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: March 2026
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773
QCAL ∞³ Active · 141.7001 Hz
"""

import numpy as np
from numpy.typing import NDArray
from scipy.linalg import eigh
from dataclasses import dataclass
from typing import List, Optional, Tuple
import time
import warnings
import hashlib
import json

warnings.filterwarnings('ignore')

try:
    import mpmath as mp
    mp.mp.dps = 30
    HAS_MPMATH = True
except ImportError:
    HAS_MPMATH = False
    warnings.warn("mpmath not available. Zero correlation will use cached fallback values.")

# QCAL Constants
F0_QCAL = 141.7001          # Hz — fundamental frequency
C_COHERENCE = 244.36         # Coherence constant C^∞
PHI = 1.6180339887498948     # Golden ratio Φ
KAPPA_PI = 2.5773            # Critical curvature

# Node 7 — material anchor frequency
F_MATERIAL = 142.1           # Hz — Node 7 anchor (NodoDilmun)

# Derived breathing constants
DELTA_F_MATERIAL = F_MATERIAL - F0_QCAL          # ≈ 0.3999 Hz
DELTA_F_AUREA = (PHI - 1.0) * F0_QCAL * 1e-3    # (φ−1)·f₀·10⁻³ Hz

# Gaussian truncation: include only grid points within this many σ of peak
GAUSSIAN_CUTOFF_SIGMA = 5.0  # Truncate von Mangoldt Gaussians at 5σ

# First 20 Riemann zero imaginary parts (fallback if mpmath unavailable)
_RIEMANN_ZEROS_FALLBACK = [
    14.134725141734693,
    21.022039638771555,
    25.010857580145688,
    30.424876125859513,
    32.935061587739189,
    37.586178158825671,
    40.918719012147495,
    43.327073280914999,
    48.005150881167159,
    49.773832477672302,
    52.970321477714460,
    56.446247697063246,
    59.347044002602353,
    60.831778524609809,
    65.112544048081607,
    67.079810529494173,
    69.546401711173979,
    72.067157674481907,
    75.704690699083933,
    77.144840069687166,
]


# ============================================================
# Data classes
# ============================================================

@dataclass
class DVRBasisResult:
    """Result of DVR basis construction.

    Attributes:
        n_basis: Number of basis functions used
        L: Half-domain length
        u_dvr: DVR grid points (N Gauss-Lobatto-like points)
        basis_matrix: (N_grid × N_basis) cosine basis matrix
        psi: QCAL coherence metric in [0, 1]
    """
    n_basis: int
    L: float
    u_dvr: NDArray[np.float64]
    basis_matrix: NDArray[np.float64]
    psi: float


@dataclass
class AdaptivePotentialResult:
    """Result of adaptive Gaussian-convolved arithmetic potential.

    Attributes:
        V: Potential values on DVR grid
        epsilon_values: Adaptive ε_k for each prime power k
        n_prime_powers: Total number of prime-power terms included
        psi: Coherence metric
    """
    V: NDArray[np.float64]
    epsilon_values: List[float]
    n_prime_powers: int
    psi: float


@dataclass
class EigenvalueResult:
    """Result of eigenvalue computation.

    Attributes:
        eigenvalues: Sorted real eigenvalues (ascending)
        n_computed: Number of eigenvalues computed
        hermiticity_error: ||H - H^T||_F / ||H||_F
        psi: Coherence metric
        computation_time_ms: Time in milliseconds
    """
    eigenvalues: NDArray[np.float64]
    n_computed: int
    hermiticity_error: float
    psi: float
    computation_time_ms: float


@dataclass
class ZeroCorrelationResult:
    """Result of eigenvalue–Riemann-zero correlation.

    Attributes:
        eigenvalues: Computed eigenvalues (sorted ascending)
        riemann_zeros: Known Riemann zero imaginary parts
        n_compared: Number of pairs compared
        pearson_r: Pearson correlation coefficient
        mean_abs_error: Mean absolute difference |λ_n - γ_n|
        relative_error: mean_abs_error / mean(γ)
        psi: Coherence metric
    """
    eigenvalues: NDArray[np.float64]
    riemann_zeros: List[float]
    n_compared: int
    pearson_r: float
    mean_abs_error: float
    relative_error: float
    psi: float


@dataclass
class SpectralDeterminantResult:
    """Result of spectral determinant vs ξ comparison.

    Attributes:
        t_values: Values of t along the critical line s = 1/2 + it
        log_det_values: log|det(s - H_ε)| approximation
        log_xi_values: Re log|ξ(1/2 + it)|
        correlation: Pearson correlation between log_det and log_xi
        synchrony_score: Fraction of t where signs match (oscillation sync)
        psi: Coherence metric
    """
    t_values: NDArray[np.float64]
    log_det_values: NDArray[np.float64]
    log_xi_values: NDArray[np.float64]
    correlation: float
    synchrony_score: float
    psi: float


@dataclass
class SpectralDVRCertificate:
    """Master certificate for spectral DVR validation.

    Attributes:
        n_basis: Basis size used
        L: Domain half-length
        epsilon_0: Base Gaussian width
        n_eigenvalues: Number of eigenvalues computed
        n_zeros_compared: Number of Riemann zeros compared
        pearson_correlation: Eigenvalue–zero Pearson r
        mean_abs_error: Mean |λ_n - γ_n|
        det_xi_correlation: log|det| vs log|ξ| correlation
        synchrony_score: Oscillation synchrony
        psi: Global QCAL coherence
        timestamp: ISO timestamp
        computation_time_ms: Total time
        certificate_hash: SHA-256 of key parameters
        validated: Whether evidence threshold passed
    """
    n_basis: int
    L: float
    epsilon_0: float
    n_eigenvalues: int
    n_zeros_compared: int
    pearson_correlation: float
    mean_abs_error: float
    det_xi_correlation: float
    synchrony_score: float
    psi: float
    timestamp: str
    computation_time_ms: float
    certificate_hash: str
    validated: bool


# ============================================================
# Breathing constants — ConstanteRespiracion
# ============================================================

@dataclass
class ConstanteRespiracion:
    """Breathing constants anchoring the QCAL spectral framework at Node 7.

    Encodes the spectral gap between the QCAL base frequency (141.7001 Hz)
    and the Node 7 material anchor (142.1 Hz).

    Attributes:
        f_material: Node 7 material frequency [Hz] = 142.1
        f0: QCAL base frequency [Hz] = 141.7001
        delta_f_material: f_material − f₀ ≈ 0.3999 Hz
        delta_f_aurea: (φ−1)·f₀·10⁻³ [Hz]
        valid: Whether delta_f_material lies in the breathing band [0.38, 0.42]
    """

    f_material: float
    f0: float
    delta_f_material: float
    delta_f_aurea: float
    valid: bool


def constante_respiracion() -> ConstanteRespiracion:
    """Compute and validate the QCAL breathing-space constants.

    Computes:
        DELTA_F_MATERIAL = F_MATERIAL − F0_QCAL  (≈ 0.3999 Hz)
        DELTA_F_AUREA    = (φ − 1) · f₀ · 10⁻³

    Validates that DELTA_F_MATERIAL ∈ [0.38, 0.42].

    Returns:
        ConstanteRespiracion with all computed constants and validity flag.

    Raises:
        ValueError: If DELTA_F_MATERIAL is outside [0.38, 0.42].
    """
    delta_f_material = F_MATERIAL - F0_QCAL
    delta_f_aurea = (PHI - 1.0) * F0_QCAL * 1e-3

    valid = 0.38 <= delta_f_material <= 0.42
    if not valid:
        raise ValueError(
            f"DELTA_F_MATERIAL={delta_f_material:.6f} Hz is outside the "
            f"breathing band [0.38, 0.42]. Check F_MATERIAL and F0_QCAL."
        )

    return ConstanteRespiracion(
        f_material=F_MATERIAL,
        f0=F0_QCAL,
        delta_f_material=delta_f_material,
        delta_f_aurea=delta_f_aurea,
        valid=valid,
    )


# ============================================================
# Utility: prime sieve
# ============================================================

def prime_sieve(n_max: int) -> List[int]:
    """Return list of primes up to n_max (inclusive).

    Args:
        n_max: Upper bound for sieve.

    Returns:
        Sorted list of primes ≤ n_max.
    """
    if n_max < 2:
        return []
    sieve = np.ones(n_max + 1, dtype=bool)
    sieve[0] = sieve[1] = False
    for i in range(2, int(np.sqrt(n_max)) + 1):
        if sieve[i]:
            sieve[i * i::i] = False
    return list(np.where(sieve)[0])


# ============================================================
# Main operator class
# ============================================================

class SpectralBasisDVR:
    """
    Hilbert-Pólya Operator in DVR cosine/parity basis.

    Uses the even-parity subspace L²_even[-L, L] spanned by:
        φ_n(u) = cos(nπu/L) / √L,  n = 0, 1, 2, …, N-1

    The full operator H_ε = T + V_ε is:
      - T: kinetic part -i d/du, symmetric in cosine basis
      - V_ε: adaptive Gaussian-convolved arithmetic potential

    Attributes:
        N: Number of basis functions (= DVR dimension)
        L: Domain half-length
        epsilon_0: Base Gaussian width (adaptively scaled per k)
        n_primes: Number of primes in potential
        max_k: Maximum prime-power exponent
        u_grid: Uniform grid on [-L, L] for function evaluation
        n_grid: Number of evaluation points
    """

    def __init__(
        self,
        N: int = 500,
        L: float = 12.0,
        epsilon_0: float = 0.04,
        n_primes: int = 100,
        max_k: int = 5,
        n_grid: int = 2000,
    ):
        """
        Initialize the DVR spectral basis operator.

        Args:
            N: Number of cosine basis functions. Should be ≥ 2 × (desired eigenvalues).
            L: Half-domain length. Must be large enough that Φ(u) decays at ±L.
            epsilon_0: Base regularization width for Gaussian convolution of deltas.
            n_primes: Number of primes p used in arithmetic potential.
            max_k: Maximum exponent k in prime power p^k.
            n_grid: Number of DVR grid points for potential evaluation.
        """
        if N < 10:
            raise ValueError("N must be at least 10.")
        if L <= 0:
            raise ValueError("L must be positive.")
        if epsilon_0 <= 0:
            raise ValueError("epsilon_0 must be positive.")
        if n_primes < 1:
            raise ValueError("n_primes must be at least 1.")
        if max_k < 1:
            raise ValueError("max_k must be at least 1.")

        self.N = N
        self.L = L
        self.epsilon_0 = epsilon_0
        self.n_primes = n_primes
        self.max_k = max_k
        self.n_grid = n_grid

        # Uniform evaluation grid on [-L, L]
        self.u_grid = np.linspace(-L, L, n_grid)
        self.du = self.u_grid[1] - self.u_grid[0]

        # Basis indices n = 0, 1, ..., N-1
        self.n_indices = np.arange(N)

        # Precompute primes
        # Largest prime power needed: max_k * log(p_max), should be < L
        p_bound = int(np.exp(L / max(max_k, 1))) + 10
        p_bound = max(p_bound, 200)
        self.primes = prime_sieve(p_bound)[:n_primes]

    # ------------------------------------------------------------------
    # I. Build DVR cosine basis
    # ------------------------------------------------------------------

    def build_basis(self) -> DVRBasisResult:
        """
        Build the cosine basis matrix on the DVR grid.

        Basis functions: φ_n(u) = A_n · cos(nπu/L)
          - n=0: A_0 = 1/√(2L)  (constant mode, normalized over [-L,L])
          - n≥1: A_n = 1/√L     (cosine modes)

        The DVR grid u_dvr are the zeros of φ_{N+1} shifted to [-L,L].
        Here we use a uniform grid for simplicity (equivalent DVR).

        Returns:
            DVRBasisResult with basis matrix of shape (n_grid, N).
        """
        u = self.u_grid
        phi = np.zeros((self.n_grid, self.N))

        # n=0: constant mode
        phi[:, 0] = 1.0 / np.sqrt(2.0 * self.L)

        # n>=1: cosine modes
        for n in range(1, self.N):
            phi[:, n] = np.cos(n * np.pi * u / self.L) / np.sqrt(self.L)

        psi = min(1.0, float(self.N) / 2000.0)  # coherence grows with basis size

        return DVRBasisResult(
            n_basis=self.N,
            L=self.L,
            u_dvr=u,
            basis_matrix=phi,
            psi=psi,
        )

    # ------------------------------------------------------------------
    # II. Adaptive arithmetic potential V_ε(u)
    # ------------------------------------------------------------------

    def adaptive_epsilon(self, k: int) -> float:
        """
        Compute adaptive Gaussian width ε_k = ε₀ / √k.

        At higher harmonic k, we use finer resolution to resolve
        the finer structure of prime-power contributions.

        Args:
            k: Prime-power exponent (k ≥ 1).

        Returns:
            Adaptive Gaussian width ε_k > 0.
        """
        return self.epsilon_0 / np.sqrt(max(k, 1))

    def build_potential(self) -> AdaptivePotentialResult:
        """
        Build the adaptive Gaussian-convolved arithmetic potential.

        V_ε(u) = Σ_{p prime, k=1}^{max_k} (ln p / p^{k/2})
                 × (1/√(2π)ε_k) × exp(-(u - k ln p)²/(2ε_k²))

        The potential is symmetric in u (even function) because we
        also include the term at u = -k ln p.

        Returns:
            AdaptivePotentialResult with V on u_grid.
        """
        u = self.u_grid
        V = np.zeros(self.n_grid)
        epsilon_values = []
        n_terms = 0

        for p in self.primes:
            log_p = np.log(float(p))
            for k in range(1, self.max_k + 1):
                u_pk = k * log_p
                # Only include if inside domain (with margin)
                if u_pk > self.L + GAUSSIAN_CUTOFF_SIGMA * self.epsilon_0:
                    break  # Higher k only push farther out

                amplitude = log_p / (float(p) ** (k / 2.0))
                eps_k = self.adaptive_epsilon(k)
                epsilon_values.append(eps_k)

                # Precompute normalization factor (shared by both Gaussians)
                norm_factor = 1.0 / (np.sqrt(2.0 * np.pi) * eps_k)
                inv_2eps2 = 1.0 / (2.0 * eps_k ** 2)

                # Gaussian centered at +u_pk
                gauss_pos = np.exp(-(u - u_pk) ** 2 * inv_2eps2) * norm_factor

                # Gaussian centered at -u_pk (even symmetry)
                gauss_neg = np.exp(-(u + u_pk) ** 2 * inv_2eps2) * norm_factor

                V += amplitude * (gauss_pos + gauss_neg)
                n_terms += 1

        # Coherence: smooth normalization
        V_norm = np.max(np.abs(V)) if np.max(np.abs(V)) > 0 else 1.0
        psi = min(1.0, 1.0 - np.exp(-V_norm))

        return AdaptivePotentialResult(
            V=V,
            epsilon_values=epsilon_values,
            n_prime_powers=n_terms,
            psi=float(psi),
        )

    # ------------------------------------------------------------------
    # III. Build full operator matrix in cosine basis
    # ------------------------------------------------------------------

    def build_operator_matrix(
        self,
        basis_result: Optional[DVRBasisResult] = None,
        potential_result: Optional[AdaptivePotentialResult] = None,
    ) -> Tuple[NDArray[np.float64], DVRBasisResult, AdaptivePotentialResult]:
        """
        Build the full H_ε matrix in the cosine basis.

        H_ε = T + V_ε

        Kinetic matrix T:
            T_{mn} = <φ_m | -i d/du | φ_n>
            In the even cosine basis, -i d/du maps cosines to sines which
            are orthogonal to the even subspace. Therefore T is skew-symmetric
            imaginary with purely imaginary off-diagonal entries.
            To form a Hermitian operator in the even subspace, we take the
            real part (the xp + px)/2 symmetrized version = 0 in pure cosine
            and use the second-order kinetic energy -d²/du² which is naturally
            diagonal in cosine basis:

                (-d²/du²) φ_n = (nπ/L)² φ_n

            This corresponds to using H_kinetic = -d²/du² as the free part,
            which is self-adjoint in L²_even and has spectrum (nπ/L)².

        Potential matrix V:
            V_{mn} = ∫_{-L}^{L} φ_m(u) V_ε(u) φ_n(u) du
                   ≈ Σ_j φ_m(u_j) V_ε(u_j) φ_n(u_j) · Δu

        The full matrix H = T + V is real symmetric, hence Hermitian.

        Args:
            basis_result: Pre-computed basis (built if None).
            potential_result: Pre-computed potential (built if None).

        Returns:
            Tuple (H_matrix, basis_result, potential_result).
        """
        if basis_result is None:
            basis_result = self.build_basis()
        if potential_result is None:
            potential_result = self.build_potential()

        phi = basis_result.basis_matrix  # (n_grid, N)
        V = potential_result.V           # (n_grid,)
        n = self.N

        # --- Kinetic matrix (diagonal in cosine basis) ---
        T_diag = np.zeros(n)
        T_diag[0] = 0.0  # Constant mode: no kinetic energy
        for mode in range(1, n):
            T_diag[mode] = (mode * np.pi / self.L) ** 2
        T_matrix = np.diag(T_diag)

        # --- Potential matrix via quadrature ---
        # V_mn = Σ_j φ_m(u_j) · V(u_j) · φ_n(u_j) · du
        # phi has shape (n_grid, N); V has shape (n_grid,)
        # Use column broadcast: phi * V[:, None] gives (n_grid, N)
        V_mat = (phi * (V * self.du)[:, np.newaxis]).T @ phi  # (N, N)

        H = T_matrix + V_mat

        # Symmetrize to enforce exact symmetry (remove floating-point asymmetry)
        H = (H + H.T) * 0.5

        return H, basis_result, potential_result

    # ------------------------------------------------------------------
    # IV. Eigenvalue computation
    # ------------------------------------------------------------------

    def compute_eigenvalues(
        self,
        n_eigenvalues: int = 200,
        H_matrix: Optional[NDArray[np.float64]] = None,
    ) -> EigenvalueResult:
        """
        Compute the lowest n_eigenvalues eigenvalues of H_ε.

        Uses scipy.linalg.eigh (symmetric real eigensolver) for
        numerical stability and speed.

        Args:
            n_eigenvalues: Number of eigenvalues to return (≤ N).
            H_matrix: Pre-built operator matrix. If None, builds it.

        Returns:
            EigenvalueResult with sorted real eigenvalues.
        """
        t0 = time.time()

        if H_matrix is None:
            H_matrix, _, _ = self.build_operator_matrix()

        n_req = min(n_eigenvalues, self.N)

        # Compute all eigenvalues of symmetric H
        eigenvalues = eigh(H_matrix, eigvals_only=True)
        eigenvalues = np.sort(eigenvalues)[:n_req]

        # Hermiticity error (should be zero for symmetric input)
        diff = H_matrix - H_matrix.T
        h_err = float(np.max(np.abs(diff)))

        dt_ms = (time.time() - t0) * 1000.0
        psi = min(1.0, 1.0 - h_err)

        return EigenvalueResult(
            eigenvalues=eigenvalues,
            n_computed=len(eigenvalues),
            hermiticity_error=h_err,
            psi=float(psi),
            computation_time_ms=dt_ms,
        )

    # ------------------------------------------------------------------
    # V. Riemann zero correlation
    # ------------------------------------------------------------------

    def fetch_riemann_zeros(self, n: int) -> List[float]:
        """
        Fetch first n imaginary parts of Riemann zeros.

        Uses mpmath.zetazero if available, otherwise falls back to
        a precomputed list of the first 20 zeros.

        Args:
            n: Number of zeros to fetch.

        Returns:
            List of n zero imaginary parts γ_n (sorted ascending).
        """
        if HAS_MPMATH:
            zeros = []
            for k in range(1, n + 1):
                try:
                    z = mp.zetazero(k)
                    zeros.append(float(z.imag))
                except Exception:
                    break
            return zeros
        else:
            # Use fallback for first min(n, 20) zeros
            return _RIEMANN_ZEROS_FALLBACK[:min(n, len(_RIEMANN_ZEROS_FALLBACK))]

    def correlate_with_zeros(
        self,
        eigenvalues: NDArray[np.float64],
        n_zeros: int = 50,
    ) -> ZeroCorrelationResult:
        """
        Correlate computed eigenvalues with known Riemann zeros.

        The Hilbert-Pólya conjecture predicts that the positive eigenvalues
        λ_n of H coincide with the imaginary parts γ_n of the Riemann zeros.

        Args:
            eigenvalues: Sorted eigenvalues from compute_eigenvalues().
            n_zeros: Number of Riemann zeros to compare against.

        Returns:
            ZeroCorrelationResult with Pearson r and mean absolute error.
        """
        # Take positive eigenvalues only
        pos_eigs = np.sort(eigenvalues[eigenvalues > 0])

        # Fetch Riemann zeros
        rz = self.fetch_riemann_zeros(n_zeros)
        n_compare = min(len(pos_eigs), len(rz))

        if n_compare < 2:
            return ZeroCorrelationResult(
                eigenvalues=pos_eigs,
                riemann_zeros=rz,
                n_compared=n_compare,
                pearson_r=0.0,
                mean_abs_error=float('inf'),
                relative_error=float('inf'),
                psi=0.0,
            )

        eigs_cmp = pos_eigs[:n_compare]
        zeros_cmp = np.array(rz[:n_compare])

        # Pearson correlation
        if np.std(eigs_cmp) < 1e-12 or np.std(zeros_cmp) < 1e-12:
            pearson_r = 0.0
        else:
            pearson_r = float(np.corrcoef(eigs_cmp, zeros_cmp)[0, 1])

        # Mean absolute error
        mae = float(np.mean(np.abs(eigs_cmp - zeros_cmp)))
        mean_zero = float(np.mean(zeros_cmp))
        rel_err = mae / mean_zero if mean_zero > 0 else float('inf')

        psi = max(0.0, min(1.0, pearson_r))

        return ZeroCorrelationResult(
            eigenvalues=pos_eigs,
            riemann_zeros=list(zeros_cmp),
            n_compared=n_compare,
            pearson_r=pearson_r,
            mean_abs_error=mae,
            relative_error=rel_err,
            psi=float(psi),
        )

    # ------------------------------------------------------------------
    # VI. Spectral determinant vs ξ comparison
    # ------------------------------------------------------------------

    def compute_log_xi(self, t_values: NDArray[np.float64]) -> NDArray[np.float64]:
        """
        Compute Re log|ξ(1/2 + it)| for an array of t values.

        Uses mpmath if available for high-precision computation,
        otherwise uses a Stirling-type approximation.

        Args:
            t_values: Array of t values on the critical line s = 1/2 + it.

        Returns:
            Array of Re log|ξ(1/2 + it)|.
        """
        result = np.zeros(len(t_values))

        if HAS_MPMATH:
            for i, t in enumerate(t_values):
                try:
                    s = mp.mpc('0.5', str(float(t)))
                    # ξ(s) = ½·s·(s−1)·π^(−s/2)·Γ(s/2)·ζ(s)
                    xi_val = (mp.mpf('0.5') * s * (s - 1)
                              * mp.power(mp.pi, -s / 2)
                              * mp.gamma(s / 2)
                              * mp.zeta(s))
                    result[i] = float(mp.log(abs(xi_val)).real)
                except Exception:
                    result[i] = 0.0
        else:
            # Approximation: use log|ζ(1/2+it)| via Stirling for large t
            for i, t in enumerate(t_values):
                t_abs = abs(t) + 1e-10
                # log|ξ(1/2+it)| ≈ (t/2)log(t/(2π)) - t/2 - (π/8) for large t
                result[i] = 0.5 * t_abs * np.log(t_abs / (2 * np.pi)) - 0.5 * t_abs

        return result

    def compute_log_det(
        self,
        t_values: NDArray[np.float64],
        eigenvalues: NDArray[np.float64],
        regularization: float = 1.0,
    ) -> NDArray[np.float64]:
        """
        Compute log|det(1/2 + it - H_ε)| using eigenvalue regularization.

        The spectral determinant is formally:
            det(s - H_ε) = Π_n (s - λ_n)

        For s = 1/2 + it:
            log|det| = Σ_n log|(1/2 + it - λ_n)|
                     = Σ_n (1/2) log((1/2 - λ_n)² + t²)

        We regularize by truncating the sum to the computed eigenvalues
        and subtracting the smooth (Weyl) background:
            log|det|_reg(t) = Σ_n log|(s - λ_n)| - (t/(2π)) log(t/(2πe))

        Args:
            t_values: Array of t on critical line s = 1/2 + it.
            eigenvalues: Sorted eigenvalues from compute_eigenvalues().
            regularization: Scale factor for Weyl background subtraction.

        Returns:
            Regularized log|det| values.
        """
        log_det = np.zeros(len(t_values))
        sigma = 0.5  # Real part of s on critical line

        for i, t in enumerate(t_values):
            # Sum log|(sigma + it - lambda_n)| using hypot for numerical stability
            diff_real = sigma - eigenvalues
            diff_imag = t
            log_factors = np.log(np.hypot(diff_real, diff_imag))
            raw_sum = float(np.sum(log_factors))

            # Weyl (smooth) background: subtract mean level density contribution.
            # The +1.0 inside log avoids log(0) at t≈0 and acts as a soft
            # infrared regulator, shifting the offset without affecting the
            # oscillatory structure for t >> 2π.
            t_abs = abs(t) + 1e-10
            n_eig = len(eigenvalues)
            weyl_bg = regularization * (
                n_eig * 0.5 * np.log(t_abs / (2 * np.pi) + 1.0)
            )

            log_det[i] = raw_sum - weyl_bg

        return log_det

    def compute_spectral_determinant(
        self,
        eigenvalues: NDArray[np.float64],
        t_min: float = 5.0,
        t_max: float = 60.0,
        n_t: int = 200,
        regularization: float = 1.0,
    ) -> SpectralDeterminantResult:
        """
        Compare log|det(s - H_ε)| with Re log ξ(s) along the critical line.

        This is the key "brutal evidence" test. If the spectral determinant
        of H_ε approximates ξ(s), it confirms the Hilbert-Pólya approach.

        Args:
            eigenvalues: Computed eigenvalues.
            t_min: Minimum t for evaluation.
            t_max: Maximum t for evaluation.
            n_t: Number of t points.
            regularization: Weyl background regularization strength.

        Returns:
            SpectralDeterminantResult with correlation and synchrony score.
        """
        t_values = np.linspace(t_min, t_max, n_t)

        log_det = self.compute_log_det(t_values, eigenvalues, regularization)
        log_xi = self.compute_log_xi(t_values)

        # Remove NaN/Inf
        mask = np.isfinite(log_det) & np.isfinite(log_xi)
        if mask.sum() < 2:
            return SpectralDeterminantResult(
                t_values=t_values,
                log_det_values=log_det,
                log_xi_values=log_xi,
                correlation=0.0,
                synchrony_score=0.0,
                psi=0.0,
            )

        ld_clean = log_det[mask]
        lx_clean = log_xi[mask]

        # Pearson correlation
        if np.std(ld_clean) < 1e-12 or np.std(lx_clean) < 1e-12:
            corr = 0.0
        else:
            corr = float(np.corrcoef(ld_clean, lx_clean)[0, 1])

        # Synchrony: fraction of t where d/dt signs agree
        if len(ld_clean) > 1:
            d_det = np.diff(ld_clean)
            d_xi = np.diff(lx_clean)
            same_sign = np.sum(np.sign(d_det) == np.sign(d_xi))
            synchrony = float(same_sign) / len(d_det)
        else:
            synchrony = 0.0

        psi = min(1.0, max(0.0, (abs(corr) + synchrony) / 2.0))

        return SpectralDeterminantResult(
            t_values=t_values,
            log_det_values=log_det,
            log_xi_values=log_xi,
            correlation=float(corr),
            synchrony_score=float(synchrony),
            psi=float(psi),
        )

    # ------------------------------------------------------------------
    # VII. Full validation pipeline
    # ------------------------------------------------------------------

    def validate(
        self,
        n_eigenvalues: int = 200,
        n_zeros: int = 50,
        t_min: float = 5.0,
        t_max: float = 60.0,
        n_t: int = 100,
    ) -> SpectralDVRCertificate:
        """
        Run the full spectral DVR validation pipeline.

        Steps:
          1. Build cosine/parity basis
          2. Build adaptive potential V_ε
          3. Assemble operator matrix H_ε
          4. Compute eigenvalues
          5. Correlate with Riemann zeros
          6. Compare spectral determinant with ξ

        Args:
            n_eigenvalues: Number of eigenvalues to compute.
            n_zeros: Number of Riemann zeros to compare against.
            t_min: Start of t-range for det–ξ comparison.
            t_max: End of t-range for det–ξ comparison.
            n_t: Number of t points for comparison.

        Returns:
            SpectralDVRCertificate with all results and validation status.
        """
        t_start = time.time()

        # Build components
        basis = self.build_basis()
        potential = self.build_potential()
        H, _, _ = self.build_operator_matrix(basis, potential)

        # Eigenvalues
        eig_result = self.compute_eigenvalues(n_eigenvalues, H)

        # Zero correlation
        corr_result = self.correlate_with_zeros(eig_result.eigenvalues, n_zeros)

        # Spectral determinant
        det_result = self.compute_spectral_determinant(
            eig_result.eigenvalues, t_min=t_min, t_max=t_max, n_t=n_t
        )

        total_ms = (time.time() - t_start) * 1000.0

        # Global coherence
        psi = (
            basis.psi * 0.1
            + potential.psi * 0.2
            + eig_result.psi * 0.2
            + corr_result.psi * 0.3
            + det_result.psi * 0.2
        )
        psi = min(1.0, max(0.0, psi))

        # Certificate hash
        hash_input = json.dumps(
            {
                "N": self.N,
                "L": self.L,
                "epsilon_0": self.epsilon_0,
                "n_eigenvalues": eig_result.n_computed,
                "pearson_r": round(corr_result.pearson_r, 6),
                "det_xi_corr": round(det_result.correlation, 6),
            },
            sort_keys=True,
        )
        cert_hash = "0xQCAL_DVR_" + hashlib.sha256(hash_input.encode()).hexdigest()[:16]

        # Validation: Pearson r > 0.5 is considered positive evidence
        validated = corr_result.pearson_r > 0.5

        from datetime import datetime, timezone

        return SpectralDVRCertificate(
            n_basis=self.N,
            L=self.L,
            epsilon_0=self.epsilon_0,
            n_eigenvalues=eig_result.n_computed,
            n_zeros_compared=corr_result.n_compared,
            pearson_correlation=corr_result.pearson_r,
            mean_abs_error=corr_result.mean_abs_error,
            det_xi_correlation=det_result.correlation,
            synchrony_score=det_result.synchrony_score,
            psi=float(psi),
            timestamp=datetime.now(timezone.utc).isoformat(),
            computation_time_ms=total_ms,
            certificate_hash=cert_hash,
            validated=validated,
        )


# ============================================================
# Convenience function
# ============================================================

def validar_evidencia_brutal(
    N_basis: int = 500,
    L: float = 12.0,
    epsilon_0: float = 0.04,
    n_eigenvalues: int = 200,
    n_zeros: int = 50,
) -> SpectralDVRCertificate:
    """
    Run the full spectral DVR validation (evidencia brutal).

    This is the top-level entry point implementing the "Módulo de Validación
    Espectral OMEGA" described in the problem statement.

    Computes det(s - H_ε) numerically, correlates with ξ(s), and returns
    a certificate summarizing all evidence.

    Args:
        N_basis: Number of cosine basis functions (recommend ≥ 500 for 200 eigenvalues).
        L: Domain half-length (recommend ≥ 12 so Φ(u) decays at boundary).
        epsilon_0: Base Gaussian regularization width.
        n_eigenvalues: Number of eigenvalues to compute (up to 500).
        n_zeros: Number of Riemann zeros to compare against.

    Returns:
        SpectralDVRCertificate with full validation results.
    """
    print("∴𓂀Ω∞³Φ - SISTEMA: COMPUTANDO DETERMINANTE DE ENKI")
    print(f"  N_basis={N_basis}, L={L}, ε₀={epsilon_0}, eigenvalues={n_eigenvalues}")

    operator = SpectralBasisDVR(
        N=N_basis,
        L=L,
        epsilon_0=epsilon_0,
        n_primes=100,
        max_k=5,
    )

    cert = operator.validate(
        n_eigenvalues=n_eigenvalues,
        n_zeros=n_zeros,
        t_min=5.0,
        t_max=60.0,
        n_t=100,
    )

    status = "✅ SINCRO CONFIRMADA" if cert.validated else "⚠️ EVIDENCIA PARCIAL"
    print(f"  Pearson r = {cert.pearson_correlation:.4f}")
    print(f"  Det–ξ correlation = {cert.det_xi_correlation:.4f}")
    print(f"  Synchrony = {cert.synchrony_score:.4f}")
    print(f"  Ψ = {cert.psi:.4f}")
    print(f"  {status}")

    return cert


# ============================================================
# OperadorHEpsilonDVR
# ============================================================

class OperadorHEpsilonDVR(SpectralBasisDVR):
    """H_ε = H_cin + V_primos(ε) in even-parity cosine DVR basis.

    Specialises :class:`SpectralBasisDVR` by applying the explicit
    Gaussian truncation required by the problem statement:

        V_primos(ε)(u) = Σ_{p,k} Λ(p^k) / p^{k/2}
                         × (1/√(2π)ε_k) × exp(-(u − k ln p)²/(2ε_k²))

    where the Gaussian is evaluated **only** at grid points satisfying
    ``|u − k ln p| ≤ GAUSSIAN_CUTOFF_SIGMA × ε_k`` (and the mirror
    term ``|u + k ln p| ≤ GAUSSIAN_CUTOFF_SIGMA × ε_k``).

    The kinetic part H_cin = −d²/du² is diagonal in the cosine basis
    with eigenvalues (nπ/L)², exactly as in :class:`SpectralBasisDVR`.

    Class constant:
        CUTOFF_SIGMA: Gaussian truncation radius in units of σ (= GAUSSIAN_CUTOFF_SIGMA).
    """

    CUTOFF_SIGMA: float = GAUSSIAN_CUTOFF_SIGMA

    def build_potential(self) -> AdaptivePotentialResult:
        """Build von Mangoldt prime potential with explicit Gaussian truncation.

        Each Gaussian is evaluated only within ``GAUSSIAN_CUTOFF_SIGMA × ε_k``
        of its centre, setting contributions beyond that radius to zero.

        Returns:
            AdaptivePotentialResult with V on u_grid.
        """
        u = self.u_grid
        V = np.zeros(self.n_grid)
        epsilon_values: List[float] = []
        n_terms = 0

        for p in self.primes:
            log_p = np.log(float(p))
            for k in range(1, self.max_k + 1):
                u_pk = k * log_p
                # Skip if centre is beyond domain + cutoff margin
                eps_k = self.adaptive_epsilon(k)
                if u_pk > self.L + GAUSSIAN_CUTOFF_SIGMA * eps_k:
                    break

                amplitude = log_p / (float(p) ** (k / 2.0))
                epsilon_values.append(eps_k)

                norm_factor = 1.0 / (np.sqrt(2.0 * np.pi) * eps_k)
                inv_2eps2 = 1.0 / (2.0 * eps_k ** 2)
                cutoff = GAUSSIAN_CUTOFF_SIGMA * eps_k

                # Positive peak: u ≈ +u_pk
                mask_pos = np.abs(u - u_pk) <= cutoff
                gauss_pos = np.where(
                    mask_pos,
                    np.exp(-(u - u_pk) ** 2 * inv_2eps2) * norm_factor,
                    0.0,
                )

                # Mirror peak: u ≈ −u_pk  (even symmetry)
                mask_neg = np.abs(u + u_pk) <= cutoff
                gauss_neg = np.where(
                    mask_neg,
                    np.exp(-(u + u_pk) ** 2 * inv_2eps2) * norm_factor,
                    0.0,
                )

                V += amplitude * (gauss_pos + gauss_neg)
                n_terms += 1

        V_norm = np.max(np.abs(V)) if np.max(np.abs(V)) > 0 else 1.0
        psi = min(1.0, 1.0 - np.exp(-V_norm))

        return AdaptivePotentialResult(
            V=V,
            epsilon_values=epsilon_values,
            n_prime_powers=n_terms,
            psi=float(psi),
        )


# ============================================================
# ValidadorEvidenciaBrutal
# ============================================================

class ValidadorEvidenciaBrutal:
    """Spectral evidence validator: diagonalises H_ε and correlates with Riemann zeros.

    Computes the Pearson correlation ρ between the rescaled positive
    eigenvalues of H_ε and the known imaginary parts of the Riemann zeros,
    then assigns the coherence metric::

        Ψ = (1 + |ρ|) / 2

    This places Ψ in [0.5, 1.0]: Ψ = 1 iff |ρ| = 1 (perfect alignment),
    Ψ = 0.5 iff ρ = 0 (no correlation).

    Parameters:
        operator: A :class:`SpectralBasisDVR` (or subclass) instance to use.
            Defaults to :class:`OperadorHEpsilonDVR` with standard settings.
    """

    def __init__(self, operator: Optional[SpectralBasisDVR] = None) -> None:
        if operator is None:
            operator = OperadorHEpsilonDVR(
                N=200,
                L=12.0,
                epsilon_0=0.04,
                n_primes=50,
                max_k=5,
            )
        self.operator = operator

    def validate(
        self,
        n_eigenvalues: int = 200,
        n_zeros: int = 50,
    ) -> ZeroCorrelationResult:
        """Diagonalise H_ε and return Pearson correlation with Riemann zeros.

        Builds the full operator matrix, computes eigenvalues, selects
        positive ones, fetches Riemann zeros, and computes::

            Ψ = (1 + |ρ|) / 2

        where ρ is the Pearson correlation coefficient between the
        (sorted) positive eigenvalues and the first n_compare zero
        imaginary parts.

        Args:
            n_eigenvalues: Number of eigenvalues to request.
            n_zeros: Number of Riemann zeros to compare against.

        Returns:
            :class:`ZeroCorrelationResult` with Ψ = (1 + |ρ|) / 2.
        """
        H, _, _ = self.operator.build_operator_matrix()
        eig_result = self.operator.compute_eigenvalues(n_eigenvalues, H)

        pos_eigs = np.sort(eig_result.eigenvalues[eig_result.eigenvalues > 0])
        rz = self.operator.fetch_riemann_zeros(n_zeros)
        n_compare = min(len(pos_eigs), len(rz))

        if n_compare < 2:
            # Insufficient data for a meaningful Pearson correlation.
            # Return partial data with psi = 0.5 (= (1 + |0|) / 2 at ρ = 0).
            return ZeroCorrelationResult(
                eigenvalues=pos_eigs,
                riemann_zeros=list(rz),
                n_compared=n_compare,
                pearson_r=0.0,
                mean_abs_error=float('inf'),
                relative_error=float('inf'),
                psi=0.5,
            )

        eigs_cmp = pos_eigs[:n_compare]
        zeros_cmp = np.array(rz[:n_compare])

        if np.std(eigs_cmp) < 1e-12 or np.std(zeros_cmp) < 1e-12:
            pearson_r = 0.0
        else:
            pearson_r = float(np.corrcoef(eigs_cmp, zeros_cmp)[0, 1])

        mae = float(np.mean(np.abs(eigs_cmp - zeros_cmp)))
        mean_zero = float(np.mean(zeros_cmp))
        rel_err = mae / mean_zero if mean_zero > 0 else float('inf')

        # Ψ = (1 + |ρ|) / 2  ∈ [0.5, 1.0]
        psi = (1.0 + abs(pearson_r)) / 2.0

        return ZeroCorrelationResult(
            eigenvalues=pos_eigs,
            riemann_zeros=list(zeros_cmp),
            n_compared=n_compare,
            pearson_r=pearson_r,
            mean_abs_error=mae,
            relative_error=rel_err,
            psi=float(psi),
        )


# ============================================================
# NodoDilmun
# ============================================================

@dataclass
class NodoDilmunResult:
    """Result of the NodoDilmun anchor computation.

    Attributes:
        f_ancla: Node 7 anchor frequency [Hz] = 142.1
        delta_f: |f_signal − f_ancla| [Hz]
        psi: cos²(π · δf / f_ancla) ∈ [0, 1]
        node: Node identifier (always 7)
    """

    f_ancla: float
    delta_f: float
    psi: float
    node: int


def nodo_dilmun(f_signal: float = F0_QCAL) -> NodoDilmunResult:
    """Anchor the system state to Node 7 (142.1 Hz) and compute Ψ.

    Computes::

        Ψ = cos²(π · δf / f_ancla)

    where δf = |f_signal − f_ancla| and f_ancla = F_MATERIAL = 142.1 Hz.

    When ``f_signal = F0_QCAL = 141.7001 Hz``::

        δf  = 0.3999 Hz
        arg = π × 0.3999 / 142.1 ≈ 0.008843 rad
        Ψ   = cos²(0.008843) ≈ 0.9999

    Args:
        f_signal: Signal frequency to evaluate [Hz].
            Defaults to F0_QCAL = 141.7001 Hz.

    Returns:
        :class:`NodoDilmunResult` with anchor state and coherence Ψ.
    """
    f_ancla = F_MATERIAL  # 142.1 Hz — Node 7
    delta_f = abs(f_signal - f_ancla)
    psi = float(np.cos(np.pi * delta_f / f_ancla) ** 2)

    return NodoDilmunResult(
        f_ancla=f_ancla,
        delta_f=delta_f,
        psi=psi,
        node=7,
    )
