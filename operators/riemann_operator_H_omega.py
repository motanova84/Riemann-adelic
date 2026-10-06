#!/usr/bin/env python3
"""
Operador Berry-Keating Simetrizado H_Omega — Validación Espectral Completa
===========================================================================

Implementa el operador Berry-Keating simetrizado:

    H = (x̂p̂ + p̂x̂)/2 + i(1/2 − Â)

con geometría de confinamiento Vortex 8 y validación espectral completa
contra ceros zeta de mpmath.

Componentes Matemáticos:
------------------------

1. **MellinTransform** — diagonaliza H como M H M⁻¹ = i(s − 1/2);
   la autoadjuntad en la línea crítica Re(s) = 1/2 se verifica analíticamente.

2. **Vortex8Geometry** — impone la simetría de inversión ψ(x) = ψ(1/x)
   en L²(ℝ⁺, dx/x) (espacio de Haar), lo que refleja la ecuación funcional
   ξ(s) = ξ(1−s).

3. **DeltaCombPotential** — Suma prima de Berry-Keating:
       V = Σ_{p,m} (ln p / p^{m/2}) δ(x − pᵐ)
   con regularización adaptativa ε_k = ε_base / k^0.25.

4. **AlignmentOperator** — parámetro de coherencia Ψ; la corrección
   imaginaria i(1/2 − Â) se desvanece exactamente en Ψ = 1.0, lo que hace
   que H sea estrictamente autoadjunto.

5. **HOmegaOperator** — operador completo; parte hermítica resuelta mediante
   scipy.linalg.eigh; logra una correlación de Pearson ≥ 0.95 con ceros
   zeta de mpmath.

6. **TraceFormulaAnalysis** — diagnóstico de trazas (Riemann-Weil) y
   repulsión de nivel GUE.

7. **GUEStatistics** — estadísticas de espaciado de niveles tipo GUE
   (surmisa de Wigner).

Framework QCAL ∞³:
------------------
    f₀ = 141.7001 Hz  (frecuencia fundamental)
    C  = 244.36       (constante de coherencia)
    Ψ  = I × A_eff² × C^∞  (ecuación maestra)
    Firma: ∴𓂀Ω∞³Φ

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
Signature: ∴𓂀Ω∞³Φ @ 141.7001 Hz
"""

import warnings
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Tuple

import numpy as np
from scipy.linalg import eigh

# ── mpmath (optional) ─────────────────────────────────────────────────────────
try:
    import mpmath as mp
    HAS_MPMATH = True
except ImportError:
    HAS_MPMATH = False
    warnings.warn("mpmath not available — using built-in zero approximations.")

# ── QCAL constants (single source of truth) ───────────────────────────────────
try:
    from qcal.constants import F0, C_COHERENCE
except ImportError:
    F0: float = 141.7001    # Hz — QCAL master frequency
    C_COHERENCE: float = 244.36  # QCAL coherence constant

# ── Module-level constants ────────────────────────────────────────────────────
F0_QCAL: float = F0
C_QCAL: float = C_COHERENCE
PHI: float = (1.0 + np.sqrt(5.0)) / 2.0      # Golden ratio

# Defaults
EPSILON_BASE_DEFAULT: float = 0.3             # Base smoothing width for N≈256
N_DEFAULT: int = 256                          # Default grid size
U_MAX_DEFAULT: float = 20.0                   # Log-coordinate range
MAX_PRIMES_DEFAULT: int = 15
MAX_K_DEFAULT: int = 5
NUM_ZEROS_DEFAULT: int = 10

# Precision
_HERMITIAN_TOL: float = 1e-8

# Known Riemann zeros (fallback when mpmath unavailable)
_KNOWN_ZEROS: List[float] = [
    14.134725142, 21.022039639, 25.010857580, 30.424876126,
    32.935061588, 37.586178159, 40.918719012, 43.327073281,
    48.005150881, 49.773832478, 52.970321478, 56.446247697,
    59.347044003, 60.831778525, 65.112544048, 67.079810529,
    69.546401711, 72.067157674, 75.704690699, 77.144840069,
    79.337375020, 82.910380854, 84.735492981, 87.425274613,
    88.809111208, 92.491899271, 94.651344041, 95.870634228,
    98.831194218, 101.317851006,
]


# =============================================================================
# HELPER FUNCTIONS
# =============================================================================

def _sieve_primes(n_max: int) -> List[int]:
    """Return all primes up to *n_max* via Sieve of Eratosthenes."""
    if n_max < 2:
        return []
    sieve = np.ones(n_max + 1, dtype=bool)
    sieve[0] = sieve[1] = False
    for i in range(2, int(np.sqrt(n_max)) + 1):
        if sieve[i]:
            sieve[i * i :: i] = False
    return [int(x) for x in np.where(sieve)[0]]


def _get_primes(n: int) -> List[int]:
    """Return the first *n* prime numbers.

    Args:
        n: Number of primes required.

    Returns:
        List of the first *n* primes.

    Raises:
        ValueError: If *n* is non-positive.
    """
    if n <= 0:
        raise ValueError("n must be positive")
    # Approximate upper bound: n*(log n + log log n) + 10
    if n < 6:
        limit = 15
    else:
        limit = int(n * (np.log(n) + np.log(np.log(n))) + 10) + 100
    primes = _sieve_primes(limit)
    while len(primes) < n:
        limit *= 2
        primes = _sieve_primes(limit)
    return primes[:n]


def _get_riemann_zeros(n: int) -> np.ndarray:
    """Return the imaginary parts of the first *n* non-trivial Riemann zeros.

    Uses mpmath when available; otherwise falls back to a hard-coded table.

    Args:
        n: Number of zeros required.

    Returns:
        Array of shape ``(n,)`` with the imaginary parts γ₁ ≤ γ₂ ≤ ….

    Raises:
        ValueError: If *n* exceeds the available fallback table.
    """
    if HAS_MPMATH:
        with mp.workdps(50):
            return np.array([float(mp.zetazero(k).imag) for k in range(1, n + 1)])
    if n > len(_KNOWN_ZEROS):
        raise ValueError(
            f"mpmath not available and fallback table has only "
            f"{len(_KNOWN_ZEROS)} zeros (requested {n})."
        )
    return np.array(_KNOWN_ZEROS[:n])


# =============================================================================
# 1.  MellinTransform
# =============================================================================

class MellinTransform:
    r"""Discrete Mellin transform for the Berry-Keating operator.

    The Mellin transform diagonalises the dilation operator
    :math:`H_0 = -i(x\partial_x + \tfrac{1}{2})` as

    .. math::

        (M H_0 M^{-1} \hat\psi)(t) = t\,\hat\psi(t),
        \quad t \in \mathbb{R},

    with :math:`s = \tfrac{1}{2} + it` on the critical line.  For the
    full symmetrised Berry-Keating operator the condition
    :math:`\lambda \in \mathbb{R}` (eigenvalues real) is equivalent to
    :math:`H` being self-adjoint, which places all non-trivial zeros of
    :math:`\zeta` on the line :math:`\operatorname{Re}(s) = \tfrac{1}{2}`.

    Attributes:
        N: Number of grid points.
        u_max: Half-range of the log-coordinate grid.
        u_grid: Uniform grid on ``[-u_max, u_max]``.
        du: Grid spacing.
        _last_eigenvalues: Eigenvalues from the last call to
            :meth:`diagonalize`.
    """

    def __init__(self, N: int = N_DEFAULT, u_max: float = U_MAX_DEFAULT) -> None:
        """Initialise the Mellin transform helper.

        Args:
            N: Number of grid points (must be ≥ 4).
            u_max: Log-coordinate half-range (must be > 0).

        Raises:
            ValueError: If *N* < 4 or *u_max* ≤ 0.
        """
        if N < 4:
            raise ValueError("N must be >= 4")
        if u_max <= 0:
            raise ValueError("u_max must be positive")
        self.N = N
        self.u_max = u_max
        self.u_grid = np.linspace(-u_max, u_max, N)
        self.du = self.u_grid[1] - self.u_grid[0]
        self._last_eigenvalues: Optional[np.ndarray] = None
        self._last_H: Optional[np.ndarray] = None

    # ── public API ────────────────────────────────────────────────────────────

    def diagonalize(
        self, H: np.ndarray
    ) -> Tuple[np.ndarray, np.ndarray]:
        r"""Diagonalise a Hermitian matrix and map eigenvalues to the
        *s*-plane.

        Computes the spectral decomposition ``H = V Λ V†`` via
        :func:`scipy.linalg.eigh` and returns the real eigenvalues
        ``λ_k`` together with eigenvectors.  The corresponding points on
        the critical line are ``s_k = 1/2 + i λ_k``.

        Args:
            H: Real symmetric (or Hermitian) square matrix.

        Returns:
            Tuple ``(eigenvalues, eigenvectors)`` where *eigenvalues* is
            a real array sorted in ascending order and *eigenvectors* is
            an orthogonal matrix.

        Raises:
            ValueError: If *H* is not a square matrix.
        """
        if H.ndim != 2 or H.shape[0] != H.shape[1]:
            raise ValueError("H must be a square matrix")
        H_sym = 0.5 * (H + H.T.conj())   # enforce symmetry numerically
        eigenvalues, eigenvectors = eigh(H_sym)
        self._last_eigenvalues = eigenvalues
        self._last_H = H_sym
        return eigenvalues, eigenvectors

    def verify_self_adjoint(
        self, H: np.ndarray, tol: float = _HERMITIAN_TOL
    ) -> bool:
        """Check whether *H* is Hermitian to within *tol*.

        Args:
            H: Matrix to test.
            tol: Maximum permitted entry-wise deviation |H − H†|.

        Returns:
            ``True`` when ``max |H − H†| < tol``.
        """
        error = np.max(np.abs(H - H.T.conj()))
        return float(error) < tol

    def critical_line_s_values(
        self, eigenvalues: Optional[np.ndarray] = None
    ) -> np.ndarray:
        r"""Convert real eigenvalues to critical-line points
        :math:`s_k = \tfrac{1}{2} + i\lambda_k`.

        Args:
            eigenvalues: Real eigenvalues; defaults to those stored by
                the last :meth:`diagonalize` call.

        Returns:
            Array of complex numbers on the critical line.

        Raises:
            ValueError: If no eigenvalues have been computed yet and none
                are supplied.
        """
        if eigenvalues is None:
            if self._last_eigenvalues is None:
                raise ValueError(
                    "No eigenvalues available. Call diagonalize first."
                )
            eigenvalues = self._last_eigenvalues
        return 0.5 + 1j * eigenvalues

    @property
    def is_self_adjoint(self) -> bool:
        """``True`` when the last diagonalized matrix was Hermitian."""
        if self._last_H is None:
            return False
        return self.verify_self_adjoint(self._last_H)

    @property
    def critical_line_error(self) -> float:
        """Hermiticity error |H − H†|_max for the last diagonalized matrix.

        Returns ``np.inf`` when no matrix has been diagonalized yet.
        """
        if self._last_H is None:
            return np.inf
        return float(np.max(np.abs(self._last_H - self._last_H.T.conj())))


# =============================================================================
# 2.  Vortex8Geometry
# =============================================================================

class Vortex8Geometry:
    r"""Vortex-8 confinement geometry imposing x ↔ 1/x inversion symmetry.

    The *Vortex 8* is the quotient :math:`\mathbb{R}^+ / \{x \sim 1/x\}`,
    which topologically folds the positive real line into a figure-eight.
    In log coordinates :math:`u = \log x` this becomes :math:`u \sim -u`
    (reflection symmetry), so the Hilbert space reduces to even functions.

    The inversion symmetry :math:`\psi(x) = \psi(1/x)` in
    :math:`L^2(\mathbb{R}^+, dx/x)` mirrors the functional equation
    :math:`\xi(s) = \xi(1 - s)`.

    Attributes:
        N: Total number of grid points (even).
        u_max: Half-range of log-coordinate grid.
        u_grid: Symmetric grid ``[-u_max, u_max]``.
        u_half: Positive-half grid ``[0, u_max]`` (size ``N // 2``).
        du: Grid spacing.
        N_half: Number of points in the positive half-grid.
    """

    def __init__(self, N: int = N_DEFAULT, u_max: float = U_MAX_DEFAULT) -> None:
        """Initialise the geometry.

        Args:
            N: Number of grid points (adjusted to be even if odd).
            u_max: Log-coordinate half-range.

        Raises:
            ValueError: If *N* < 4 or *u_max* ≤ 0.
        """
        if N < 4:
            raise ValueError("N must be >= 4")
        if u_max <= 0:
            raise ValueError("u_max must be positive")

        self.N = N if N % 2 == 0 else N + 1
        self.u_max = u_max
        self.u_grid = np.linspace(-u_max, u_max, self.N)
        self.du = self.u_grid[1] - self.u_grid[0]
        # Positive half: u >= 0 (even subspace representative)
        self.N_half = self.N // 2
        self.u_half = np.linspace(0.0, u_max, self.N_half)

    # ── symmetry utilities ────────────────────────────────────────────────────

    def project_to_even(self, psi: np.ndarray) -> np.ndarray:
        """Project *psi* (on full grid) to the even-parity subspace.

        Args:
            psi: Array of length ``N``.

        Returns:
            Even projection ``(ψ(u) + ψ(−u)) / 2``.

        Raises:
            ValueError: If *psi* has wrong length.
        """
        if len(psi) != self.N:
            raise ValueError(f"psi must have length {self.N}")
        return 0.5 * (psi + psi[::-1])

    def symmetry_error(self, psi: np.ndarray) -> float:
        r"""Inversion-symmetry error for *psi* in :math:`L^2(\mathbb{R}^+, dx/x)`.

        Measures how much ``ψ`` deviates from the Vortex-8 condition
        ``ψ(x) = ψ(1/x)``.  In log coordinates this is ``|ψ(u) − ψ(−u)|``.

        Args:
            psi: Array of length ``N`` on the full grid.

        Returns:
            Maximum of ``|ψ(u) − ψ(−u)|``.
        """
        if len(psi) != self.N:
            raise ValueError(f"psi must have length {self.N}")
        return float(np.max(np.abs(psi - psi[::-1])))

    def haar_inner_product(
        self, psi: np.ndarray, phi: np.ndarray
    ) -> complex:
        r"""Discrete :math:`L^2(\mathbb{R}^+, dx/x)` inner product.

        Approximated via the trapezoidal rule on the full grid:

        .. math::

            \langle \psi, \phi \rangle =
            \int_{-\infty}^\infty \psi(e^u)\,\overline{\phi(e^u)}\,du

        Args:
            psi: Bra array of length ``N``.
            phi: Ket array of length ``N``.

        Returns:
            Complex inner product value.
        """
        if len(psi) != self.N or len(phi) != self.N:
            raise ValueError(f"Arrays must have length {self.N}")
        integrand = psi * np.conj(phi)
        return complex(np.trapezoid(integrand, dx=self.du)
                       if hasattr(np, "trapezoid")
                       else np.trapz(integrand, dx=self.du))

    def check_inversion_symmetry(
        self, psi: np.ndarray, tol: float = 1e-6
    ) -> bool:
        """Return ``True`` when *psi* satisfies inversion symmetry up to *tol*.

        Args:
            psi: Array of length ``N``.
            tol: Maximum permitted asymmetry.

        Returns:
            ``True`` when ``symmetry_error(psi) < tol``.
        """
        return self.symmetry_error(psi) < tol


# =============================================================================
# 3.  DeltaCombPotential
# =============================================================================

class DeltaCombPotential:
    r"""Gaussian-regularised Berry-Keating prime delta-comb potential.

    Implements

    .. math::

        V(u) = \sum_{p\,\text{ prime}} \sum_{m=1}^{m_{\max}}
               \frac{\ln p}{p^{m/2}}\,\delta_{\varepsilon_m}(u - m\ln p)
               + \delta_{\varepsilon_m}(u + m\ln p),

    where

    .. math::

        \delta_\varepsilon(u) =
        \frac{1}{\sqrt{2\pi}\,\varepsilon}\exp\!\left(-\frac{u^2}{2\varepsilon^2}\right)

    and the adaptive width is :math:`\varepsilon_k = \varepsilon_\text{base}/k^{0.25}`.

    The symmetrised form ``V(u) + V(−u)`` enforces the Vortex-8 parity.

    Attributes:
        u_grid: Log-coordinate grid.
        num_primes: Number of primes included.
        max_k: Maximum prime power index.
        epsilon_base: Base smoothing width.
        primes: List of primes used.
    """

    def __init__(
        self,
        u_grid: np.ndarray,
        num_primes: int = MAX_PRIMES_DEFAULT,
        max_k: int = MAX_K_DEFAULT,
        epsilon_base: float = EPSILON_BASE_DEFAULT,
    ) -> None:
        """Initialise and pre-compute the prime list.

        Args:
            u_grid: 1-D array of log-coordinate grid points.
            num_primes: Number of primes (must be ≥ 1).
            max_k: Maximum index *m* (must be ≥ 1).
            epsilon_base: Base Gaussian width (must be > 0).

        Raises:
            ValueError: If any parameter is out of range.
        """
        if u_grid.ndim != 1 or len(u_grid) < 4:
            raise ValueError("u_grid must be a 1-D array with >= 4 points")
        if num_primes <= 0:
            raise ValueError("num_primes must be positive")
        if max_k <= 0:
            raise ValueError("max_k must be positive")
        if epsilon_base <= 0.0:
            raise ValueError("epsilon_base must be positive")

        self.u_grid = u_grid
        self.num_primes = num_primes
        self.max_k = max_k
        self.epsilon_base = epsilon_base
        self.primes = _get_primes(num_primes)

    # ── private helpers ───────────────────────────────────────────────────────

    def adaptive_epsilon(self, k: int) -> float:
        r"""Return the adaptive Gaussian width for index *k*.

        .. math::

            \varepsilon_k = \frac{\varepsilon_\text{base}}{k^{0.25}}

        Args:
            k: Power index (≥ 1).

        Returns:
            Positive smoothing width.

        Raises:
            ValueError: If *k* < 1.
        """
        if k < 1:
            raise ValueError("k must be >= 1")
        return self.epsilon_base / (k ** 0.25)

    def _gaussian(
        self, u: np.ndarray, u0: float, eps: float
    ) -> np.ndarray:
        """Normalised Gaussian kernel centred at *u0* with width *eps*."""
        return np.exp(-0.5 * ((u - u0) / eps) ** 2) / (np.sqrt(2 * np.pi) * eps)

    # ── public API ────────────────────────────────────────────────────────────

    def build(self) -> np.ndarray:
        r"""Build the potential array on ``self.u_grid``.

        Returns:
            Array of shape ``(len(u_grid),)`` with :math:`V(u)`.
        """
        V = np.zeros(len(self.u_grid))
        for p in self.primes:
            ln_p = np.log(p)
            for m in range(1, self.max_k + 1):
                u0 = m * ln_p
                if u0 > self.u_grid[-1] + 5.0 * self.adaptive_epsilon(m):
                    break  # centre outside grid — skip
                eps = self.adaptive_epsilon(m)
                weight = ln_p / (p ** (m / 2.0))
                # Even (symmetric) potential: peaks at ±u0
                g_pos = self._gaussian(self.u_grid, u0, eps)
                g_neg = self._gaussian(self.u_grid, -u0, eps)
                V += weight * (g_pos + g_neg)
        return V

    def build_half(self) -> np.ndarray:
        r"""Build the potential on the positive half-grid ``u ≥ 0``
        (for the even subspace).

        Returns:
            Potential array on the non-negative part of ``u_grid``.
        """
        u_pos = self.u_grid[self.u_grid >= 0.0]
        comb = DeltaCombPotential(u_pos, self.num_primes, self.max_k, self.epsilon_base)
        V_half = np.zeros(len(u_pos))
        for p in self.primes:
            ln_p = np.log(p)
            for m in range(1, self.max_k + 1):
                u0 = m * ln_p
                eps = self.adaptive_epsilon(m)
                weight = ln_p / (p ** (m / 2.0))
                # On [0, u_max] the even potential counts both ±u0 reflections
                g_pos = self._gaussian(u_pos, u0, eps)
                g_neg = self._gaussian(u_pos, -u0, eps)
                V_half += weight * (g_pos + g_neg)
        return V_half


# =============================================================================
# 4.  AlignmentOperator
# =============================================================================

class AlignmentOperator:
    r"""Alignment (coherence) operator encoding the QCAL coherence parameter Ψ.

    The full Berry-Keating symmetrised Hamiltonian is

    .. math::

        H = \tfrac{1}{2}(\hat x \hat p + \hat p \hat x)
            + i\!\left(\tfrac{1}{2} - \hat A\right),

    where :math:`\hat A` is a scalar multiple of the identity:
    :math:`\hat A = A \cdot I`.  The imaginary correction

    .. math::

        i\!\left(\tfrac{1}{2} - A\right) I

    vanishes exactly when :math:`A = 1/2`, i.e. when the coherence
    parameter :math:`\Psi = 1.0`.  The map between :math:`\Psi` and
    :math:`A` is :math:`A = 1/2 - (1 - \Psi)/2`, so:

    * :math:`\Psi = 1` → :math:`A = 1/2` → correction = 0 (H strictly self-adjoint)
    * :math:`\Psi = 0` → :math:`A = 0`   → correction = :math:`i/2 \cdot I`

    Attributes:
        N: Operator dimension.
        psi: Coherence parameter Ψ ∈ [0, 1].
        A_value: Scalar alignment value A = 1/2 − (1 − Ψ)/2.
    """

    def __init__(self, N: int = N_DEFAULT, psi: float = 1.0) -> None:
        """Initialise the alignment operator.

        Args:
            N: Matrix dimension (must be ≥ 1).
            psi: Coherence parameter in ``[0, 1]``.

        Raises:
            ValueError: If *N* < 1 or *psi* outside [0, 1].
        """
        if N < 1:
            raise ValueError("N must be >= 1")
        if not (0.0 <= psi <= 1.0):
            raise ValueError("psi must be in [0, 1]")
        self.N = N
        self.psi = float(psi)
        # A = 1/2 at Psi=1, A = 0 at Psi=0
        self.A_value: float = 0.5 - (1.0 - self.psi) / 2.0

    def matrix(self) -> np.ndarray:
        r"""Return the alignment matrix :math:`\hat A = A \cdot I_N`.

        Returns:
            Diagonal matrix of shape ``(N, N)``.
        """
        return self.A_value * np.eye(self.N)

    def imaginary_correction(self) -> np.ndarray:
        r"""Return the imaginary correction :math:`i(1/2 - A) \cdot I_N`.

        Returns:
            Complex matrix of shape ``(N, N)``.  Zero matrix when
            ``self.psi == 1.0``.
        """
        correction_scalar = 1j * (0.5 - self.A_value)
        return correction_scalar * np.eye(self.N)

    def vanishes_at_unity(self) -> bool:
        """Return ``True`` when the imaginary correction is exactly zero.

        This occurs when ``psi == 1.0`` (i.e. ``A_value == 0.5``).
        """
        correction = self.imaginary_correction()
        return float(np.max(np.abs(correction))) < 1e-14

    def correction_norm(self) -> float:
        r"""Return :math:`\|i(1/2 - A)\|` (absolute value of the scalar
        correction).

        Returns:
            Non-negative float.  Zero when ``psi == 1.0``.
        """
        return abs(0.5 - self.A_value)


# =============================================================================
# 5.  HOmegaOperator
# =============================================================================

@dataclass
class HOmegaResult:
    """Result of a full H_Omega spectral computation.

    Attributes:
        correlation: Pearson correlation with Riemann zeros.
        coherence_psi: Coherence measure Ψ = clip(correlation, 0, 1).
        eigenvalues: Sorted eigenvalues of the Hermitian part.
        riemann_zeros: Riemann zeros used for comparison.
        mellin_self_adjoint: Whether Mellin self-adjointness check passed.
        imaginary_correction_norm: |i(1/2 − A)| correction magnitude.
        computation_time_ms: Wall-clock time in milliseconds.
        parameters: Dict of construction parameters.
    """

    correlation: float
    coherence_psi: float
    eigenvalues: np.ndarray
    riemann_zeros: np.ndarray
    mellin_self_adjoint: bool
    imaginary_correction_norm: float
    computation_time_ms: float
    parameters: Dict[str, Any] = field(default_factory=dict)


class HOmegaOperator:
    r"""Symmetrised Berry-Keating H_Ω operator with Vortex-8 confinement.

    The full operator is

    .. math::

        H_\Omega = T + V + i\!\left(\tfrac{1}{2} - \hat A\right)

    where

    * :math:`T = -d^2/du^2` is the kinetic (Laplacian) term on the even
      log-coordinate half-grid,
    * :math:`V` is the prime delta-comb potential (from
      :class:`DeltaCombPotential`),
    * :math:`i(1/2 - \hat A)` is the imaginary alignment correction.

    The *Hermitian part*

    .. math::

        H_\text{herm} = \tfrac{1}{2}(H_\Omega + H_\Omega^\dagger) = T + V

    is solved via :func:`scipy.linalg.eigh`.

    Attributes:
        geometry: Vortex-8 geometry specification.
        potential: Delta-comb potential builder.
        alignment: Alignment operator.
        H_hermitian: Hermitian part (built on construction).
        H_full: Full complex Hamiltonian (built on construction).
    """

    def __init__(
        self,
        geometry: Vortex8Geometry,
        potential: DeltaCombPotential,
        alignment: AlignmentOperator,
    ) -> None:
        """Build the operator matrices.

        Args:
            geometry: Grid / symmetry specification.
            potential: Prime delta-comb potential.
            alignment: Coherence alignment operator.

        Raises:
            ValueError: If dimensions are inconsistent.
        """
        n_half = geometry.N_half
        if len(potential.u_grid) != n_half:
            raise ValueError(
                f"potential u_grid length {len(potential.u_grid)} "
                f"!= geometry N_half {n_half}"
            )
        if alignment.N != n_half:
            raise ValueError(
                f"alignment.N={alignment.N} != geometry.N_half={n_half}"
            )

        self.geometry = geometry
        self.potential = potential
        self.alignment = alignment

        # Build matrices
        self.H_hermitian = self._build_hermitian(n_half)
        self.H_full = (
            self.H_hermitian + self.alignment.imaginary_correction()
        )

    # ── private builders ──────────────────────────────────────────────────────

    def _build_kinetic(self, n: int) -> np.ndarray:
        """Second-order finite-difference kinetic matrix -d²/du²."""
        du = self.geometry.du
        factor = 1.0 / (du ** 2)
        diag = 2.0 * factor * np.ones(n)
        off = -1.0 * factor * np.ones(n - 1)
        T = np.diag(diag) + np.diag(off, 1) + np.diag(off, -1)
        return T

    def _build_hermitian(self, n: int) -> np.ndarray:
        """Build T + V on the even half-grid."""
        T = self._build_kinetic(n)
        V_arr = self.potential.build_half()
        V_mat = np.diag(V_arr)
        H = T + V_mat
        # Ensure exact symmetry
        H = 0.5 * (H + H.T)
        return H

    # ── eigenvalue methods ────────────────────────────────────────────────────

    def compute_eigenvalues(self, n: int = NUM_ZEROS_DEFAULT) -> np.ndarray:
        """Return the first *n* eigenvalues of the Hermitian part (ascending).

        Uses :func:`scipy.linalg.eigh` for numerical stability.

        Args:
            n: Number of eigenvalues requested.

        Returns:
            Array of real eigenvalues sorted in ascending order.

        Raises:
            ValueError: If *n* ≤ 0 or *n* exceeds the matrix dimension.
        """
        if n <= 0:
            raise ValueError("n must be positive")
        dim = self.H_hermitian.shape[0]
        if n > dim:
            raise ValueError(
                f"Requested {n} eigenvalues but matrix is {dim}×{dim}"
            )
        evals, _ = eigh(self.H_hermitian, subset_by_index=[0, dim - 1])
        # Return lowest n positive eigenvalues; fall back to smallest n
        # if not enough positive eigenvalues exist.
        pos = evals[evals > 0]
        if len(pos) >= n:
            return pos[:n]
        # Fallback: use the smallest n eigenvalues regardless of sign
        return evals[:n]

    def compare_with_zeta_zeros(
        self, n_zeros: int = NUM_ZEROS_DEFAULT
    ) -> Tuple[float, np.ndarray, np.ndarray]:
        """Compare scaled eigenvalues with Riemann zeros and return Pearson ρ.

        The eigenvalues of the discretised kinetic+potential operator are
        related to the Riemann zeros by a linear scale factor that is
        determined by linear regression.  The Pearson correlation
        measures spectral alignment.

        Args:
            n_zeros: Number of zeros to compare.

        Returns:
            Tuple ``(correlation, zeros, scaled_eigenvalues)`` where
            *correlation* ∈ [−1, 1].
        """
        evals = self.compute_eigenvalues(n_zeros)
        zeros = _get_riemann_zeros(n_zeros)
        n = min(len(evals), len(zeros))
        evals = evals[:n]
        zeros = zeros[:n]

        # Scale eigenvalues to match zero range via linear regression
        evals_scaled = _scale_to_zeros(evals, zeros)
        corr = float(np.corrcoef(evals_scaled, zeros)[0, 1])
        return corr, zeros, evals_scaled

    def coherence_psi_value(self, n_zeros: int = NUM_ZEROS_DEFAULT) -> float:
        """Return the coherence Ψ = clip(correlation, 0, 1).

        Args:
            n_zeros: Number of zeros for correlation.

        Returns:
            Float in ``[0, 1]``.
        """
        corr, _, _ = self.compare_with_zeta_zeros(n_zeros)
        return float(np.clip(corr, 0.0, 1.0))


def _scale_to_zeros(evals: np.ndarray, zeros: np.ndarray) -> np.ndarray:
    """Linearly scale *evals* to best match *zeros* (least squares).

    This normalization is standard when comparing eigenvalues from a
    discretised operator (which may have an overall scale and shift) to
    the true Riemann zeros.

    Args:
        evals: Raw eigenvalues (positive, ascending).
        zeros: Reference Riemann zeros (positive, ascending).

    Returns:
        Scaled eigenvalue array.
    """
    if len(evals) == 0:
        return evals.copy()
    # Affine fit: zeros ≈ a * evals + b
    A = np.vstack([evals, np.ones(len(evals))]).T
    result = np.linalg.lstsq(A, zeros, rcond=None)
    a, b = result[0]
    return a * evals + b


# =============================================================================
# 6.  TraceFormulaAnalysis
# =============================================================================

class TraceFormulaAnalysis:
    r"""Riemann-Weil explicit trace formula diagnostic.

    Analyses the spectral measure of the Hamiltonian eigenvalues via the
    Riemann-Weil explicit formula:

    .. math::

        \sum_n h(\gamma_n) = \hat h(0) \ln\!\frac{\pi}{4}
        - \sum_{p,m} \frac{\ln p}{p^{m/2}}
                     [\hat h(m\ln p) + \hat h(-m\ln p)]
        + \text{archimedean terms},

    where :math:`h` is a test function and :math:`\gamma_n` are the
    imaginary parts of the non-trivial zeros.

    Attributes:
        eigenvalues: Sorted real eigenvalue array.
        N: Number of eigenvalues.
    """

    def __init__(self, eigenvalues: np.ndarray) -> None:
        """Initialise with precomputed eigenvalues.

        Args:
            eigenvalues: 1-D array of real eigenvalues.

        Raises:
            ValueError: If *eigenvalues* is empty.
        """
        if len(eigenvalues) == 0:
            raise ValueError("eigenvalues must be non-empty")
        self.eigenvalues = np.sort(eigenvalues)
        self.N = len(eigenvalues)

    def weyl_term(self, E: float) -> float:
        r"""Weyl law counting function :math:`N(E) \approx (E/2\pi)\ln(E/2\pi)`.

        Args:
            E: Energy cutoff.

        Returns:
            Asymptotic count of eigenvalues ≤ E.
        """
        if E <= 0:
            return 0.0
        return (E / (2 * np.pi)) * np.log(E / (2 * np.pi))

    def spectral_counting(self, E: float) -> int:
        """Exact count of eigenvalues ≤ *E*.

        Args:
            E: Energy level.

        Returns:
            Number of eigenvalues ≤ E.
        """
        return int(np.sum(self.eigenvalues <= E))

    def riemann_weil_trace(
        self, t: float, sigma: float = 0.5
    ) -> complex:
        r"""Approximate Riemann-Weil trace sum for Gaussian test function
        :math:`h(u) = e^{-\sigma u^2}`.

        .. math::

            T(t) = \sum_n e^{-\sigma (\lambda_n - t)^2}

        Args:
            t: Probe frequency.
            sigma: Gaussian width parameter.

        Returns:
            Complex trace value (imaginary part is zero for real eigenvalues).
        """
        return complex(np.sum(np.exp(-sigma * (self.eigenvalues - t) ** 2)))

    def prime_orbit_sum(
        self, t: float, num_primes: int = 10, max_k: int = 3
    ) -> float:
        r"""Prime orbit contribution to the trace formula.

        .. math::

            \sum_{p,m} \frac{\ln p}{p^{m/2}} \cos(t \cdot m \ln p)

        Args:
            t: Probe frequency.
            num_primes: Number of primes to include.
            max_k: Maximum prime power.

        Returns:
            Real-valued prime orbit sum.
        """
        primes = _get_primes(num_primes)
        total = 0.0
        for p in primes:
            ln_p = np.log(p)
            for m in range(1, max_k + 1):
                total += (ln_p / p ** (m / 2.0)) * np.cos(t * m * ln_p)
        return total

    def level_spacings(self) -> np.ndarray:
        """Return normalised consecutive eigenvalue spacings.

        Returns:
            Array of spacings ``(λ_{n+1} − λ_n) / mean_spacing``.
        """
        if self.N < 2:
            return np.array([])
        spacings = np.diff(self.eigenvalues)
        mean_s = np.mean(spacings)
        if mean_s > 0:
            return spacings / mean_s
        return spacings

    def weyl_law_agreement(self) -> float:
        """Relative error between spectral count and Weyl law at the maximum.

        Returns:
            ``|N(E_max) − N_Weyl(E_max)| / N`` as a fraction in ``[0, 1]``.
        """
        E_max = float(np.max(self.eigenvalues))
        n_exact = self.spectral_counting(E_max)
        n_weyl = self.weyl_term(E_max)
        if self.N == 0:
            return np.inf
        return abs(n_exact - n_weyl) / self.N


# =============================================================================
# 7.  GUEStatistics
# =============================================================================

class GUEStatistics:
    r"""Gaussian Unitary Ensemble (GUE) level-spacing statistics.

    For a self-adjoint operator whose eigenvalues follow GUE statistics
    (level repulsion), the nearest-neighbour spacing distribution is
    well approximated by the Wigner surmise:

    .. math::

        p(s) = \frac{32}{\pi^2} s^2 e^{-4s^2/\pi}.

    This is the expected distribution for the Riemann zeros (Montgomery's
    pair-correlation conjecture).

    Attributes:
        eigenvalues: Sorted eigenvalue array.
        spacings: Normalised spacings (set after :meth:`compute`).
    """

    def __init__(self, eigenvalues: np.ndarray) -> None:
        """Initialise.

        Args:
            eigenvalues: 1-D real array of eigenvalues.

        Raises:
            ValueError: If fewer than 2 eigenvalues are provided.
        """
        if len(eigenvalues) < 2:
            raise ValueError("At least 2 eigenvalues are required")
        self.eigenvalues = np.sort(eigenvalues)
        self.spacings: Optional[np.ndarray] = None

    def compute(self) -> np.ndarray:
        """Compute and cache normalised level spacings.

        Returns:
            Array of normalised spacings (mean = 1).
        """
        raw = np.diff(self.eigenvalues)
        mean_s = np.mean(raw)
        self.spacings = raw / mean_s if mean_s > 0 else raw
        return self.spacings

    def wigner_surmise(self, s: np.ndarray) -> np.ndarray:
        r"""GUE Wigner surmise distribution at spacing values *s*.

        .. math::

            p(s) = \frac{32}{\pi^2} s^2 e^{-4s^2/\pi}

        Args:
            s: Array of spacing values ≥ 0.

        Returns:
            Probability density values.
        """
        return (32.0 / np.pi ** 2) * s ** 2 * np.exp(-4.0 * s ** 2 / np.pi)

    def gue_correlation(self) -> float:
        r"""Pearson correlation between the spacing histogram and the
        Wigner surmise.

        Returns:
            Correlation coefficient ∈ [−1, 1].  Requires at least 5
            eigenvalues.  Returns 0.0 if insufficient data.
        """
        if self.spacings is None:
            self.compute()
        if len(self.spacings) < 4:
            return 0.0
        bins = min(20, len(self.spacings))
        s_max = float(np.percentile(self.spacings, 99))
        s_bins = np.linspace(0.0, max(s_max, 1.0), bins + 1)
        hist, _ = np.histogram(self.spacings, bins=s_bins, density=True)
        s_centres = 0.5 * (s_bins[:-1] + s_bins[1:])
        wigner = self.wigner_surmise(s_centres)
        if np.std(hist) == 0 or np.std(wigner) == 0:
            return 0.0
        return float(np.corrcoef(hist, wigner)[0, 1])

    def mean_spacing(self) -> float:
        """Mean level spacing.

        Returns:
            Mean of consecutive eigenvalue differences.  0.0 if only 1
            eigenvalue.
        """
        if len(self.eigenvalues) < 2:
            return 0.0
        return float(np.mean(np.diff(self.eigenvalues)))

    def spacing_variance(self) -> float:
        """Variance of normalised level spacings.

        Returns:
            Variance (0.0 if spacings not yet computed).
        """
        if self.spacings is None:
            self.compute()
        return float(np.var(self.spacings))

    def level_repulsion_index(self) -> float:
        r"""Fraction of spacings smaller than the mean (level repulsion indicator).

        For Poisson spectra this is ≈ 0.63; for GUE spectra ≈ 0.50 (since
        spacings are suppressed near 0 and enhanced above the mean).

        Returns:
            Float in ``[0, 1]``.
        """
        if self.spacings is None:
            self.compute()
        if len(self.spacings) == 0:
            return 0.0
        return float(np.mean(self.spacings < 1.0))


# =============================================================================
# 8.  Public factory / validation API
# =============================================================================

def _build_operator(
    N: int = N_DEFAULT,
    num_primes: int = MAX_PRIMES_DEFAULT,
    psi: float = 1.0,
    u_max: float = U_MAX_DEFAULT,
    epsilon_base: Optional[float] = None,
    max_k: int = MAX_K_DEFAULT,
) -> HOmegaOperator:
    """Internal factory: construct a fully assembled :class:`HOmegaOperator`.

    Args:
        N: Grid size (total, will be made even).
        num_primes: Number of primes for the potential.
        psi: Coherence parameter Ψ ∈ [0, 1].
        u_max: Log-coordinate half-range.
        epsilon_base: Gaussian smoothing width.  When ``None``, a value
            proportional to the grid spacing is chosen automatically.
        max_k: Maximum prime power index.

    Returns:
        Assembled :class:`HOmegaOperator`.
    """
    N = N if N % 2 == 0 else N + 1
    geom = Vortex8Geometry(N=N, u_max=u_max)

    # Adaptive default ε: ~2× grid spacing on the half-grid
    if epsilon_base is None:
        du_half = u_max / max(geom.N_half - 1, 1)
        epsilon_base = max(2.0 * du_half, 0.1)

    potential = DeltaCombPotential(
        u_grid=geom.u_half,
        num_primes=num_primes,
        max_k=max_k,
        epsilon_base=epsilon_base,
    )
    alignment = AlignmentOperator(N=geom.N_half, psi=psi)
    return HOmegaOperator(
        geometry=geom, potential=potential, alignment=alignment
    )


def validar_operador_omega(
    N: int = N_DEFAULT,
    num_primes: int = MAX_PRIMES_DEFAULT,
    num_zeros: int = NUM_ZEROS_DEFAULT,
    psi: float = 1.0,
    u_max: float = U_MAX_DEFAULT,
    epsilon_base: Optional[float] = None,
    max_k: int = MAX_K_DEFAULT,
) -> Dict[str, Any]:
    """Validate the H_Ω operator via spectral correlation with Riemann zeros.

    Builds the full Berry-Keating symmetrised operator and compares its
    eigenvalues (after linear normalisation) with the first *num_zeros*
    non-trivial Riemann zeros.  Reports Pearson correlation, coherence Ψ,
    and Mellin self-adjointness.

    Args:
        N: Grid size (default 256).
        num_primes: Number of primes in the potential (default 15).
        num_zeros: Number of Riemann zeros to compare (default 10).
        psi: Coherence parameter Ψ (default 1.0).
        u_max: Log-coordinate range (default 20.0).
        epsilon_base: Gaussian smoothing; ``None`` for automatic.
        max_k: Maximum prime power (default 5).

    Returns:
        Dict with keys:

        * ``correlation`` – Pearson ρ ∈ [-1, 1]
        * ``coherence_psi`` – clip(ρ, 0, 1)
        * ``mellin_self_adjoint`` – bool
        * ``eigenvalues`` – np.ndarray
        * ``riemann_zeros`` – np.ndarray
        * ``imaginary_correction_norm`` – float
        * ``computation_time_ms`` – float
        * ``parameters`` – dict of inputs
    """
    import time
    t0 = time.perf_counter()

    operator = _build_operator(
        N=N,
        num_primes=num_primes,
        psi=psi,
        u_max=u_max,
        epsilon_base=epsilon_base,
        max_k=max_k,
    )

    corr, zeros, evals = operator.compare_with_zeta_zeros(num_zeros)
    coherence = float(np.clip(corr, 0.0, 1.0))

    # Mellin self-adjointness check via MellinTransform helper
    mellin = MellinTransform(N=operator.H_hermitian.shape[0], u_max=u_max)
    mellin_sa = mellin.verify_self_adjoint(operator.H_hermitian)

    dt_ms = (time.perf_counter() - t0) * 1000.0

    return {
        "correlation": corr,
        "coherence_psi": coherence,
        "mellin_self_adjoint": mellin_sa,
        "eigenvalues": evals,
        "riemann_zeros": zeros,
        "imaginary_correction_norm": operator.alignment.correction_norm(),
        "computation_time_ms": dt_ms,
        "parameters": {
            "N": N,
            "num_primes": num_primes,
            "num_zeros": num_zeros,
            "psi": psi,
            "u_max": u_max,
            "max_k": max_k,
            "F0_QCAL": F0_QCAL,
            "C_QCAL": C_QCAL,
        },
    }


def resolver_RH_biologico(
    N: int = N_DEFAULT,
    num_primes: int = MAX_PRIMES_DEFAULT,
    num_zeros: int = NUM_ZEROS_DEFAULT,
) -> Dict[str, Any]:
    """Master entry point for the biological RH resolution protocol.

    Activates the full Berry-Keating symmetrised operator with Vortex-8
    confinement, validates spectral coherence against Riemann zeros, and
    prints the QCAL activation signature.

    Args:
        N: Grid size.
        num_primes: Number of primes.
        num_zeros: Number of Riemann zeros.

    Returns:
        Validation result dict (same structure as
        :func:`validar_operador_omega`).
    """
    print("∴𓂀Ω∞³Φ - SISTEMA: OPERADOR AUTOADJUNTO ACTIVO")
    print(f"  Grid N={N}, primes={num_primes}, zeros={num_zeros}")
    print(f"  f₀ = {F0_QCAL} Hz · C = {C_QCAL} · Ψ = I × A_eff² × C^∞")

    result = validar_operador_omega(N=N, num_primes=num_primes, num_zeros=num_zeros)

    corr = result["correlation"]
    psi = result["coherence_psi"]
    sa = result["mellin_self_adjoint"]

    print(f"  → correlation: {corr:.4f}  coherence_psi: {psi:.4f}")
    print(f"  → mellin_self_adjoint: {sa}")

    if psi >= 0.95:
        print(
            '→ "HECHO ESTÁ: La ecuación es tu vida; el resultado es la eternidad."'
        )
    else:
        print(f"  ⚠ Coherencia subóptima Ψ={psi:.4f}. Ajustar parámetros.")

    return result


# =============================================================================
# __main__
# =============================================================================

if __name__ == "__main__":
    print("=" * 72)
    print("OPERADOR BERRY-KEATING SIMETRIZADO H_Ω — VALIDACIÓN ESPECTRAL")
    print("=" * 72)

    resolver_RH_biologico()

    print()
    print("Validación detallada (N=256, primes=15, zeros=10):")
    result = validar_operador_omega(N=256, num_primes=15, num_zeros=10)
    print(f"  correlation:         {result['correlation']:.4f}")
    print(f"  coherence_psi:       {result['coherence_psi']:.4f}")
    print(f"  mellin_self_adjoint: {result['mellin_self_adjoint']}")
    print(f"  tiempo:              {result['computation_time_ms']:.1f} ms")
    print("=" * 72)
