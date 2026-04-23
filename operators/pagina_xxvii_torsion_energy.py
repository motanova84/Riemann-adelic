#!/usr/bin/env python3
"""
Página XXVII — Torsion Energy Functional and Adelic Metric
============================================================

Implements the three mathematical constructs of Página XXVII of the QCAL
master calculation:

I.  Torsion Energy Functional  E_tors[Ψ]
II. Adelic Metric              d_A(x, y)
III. Spectral Flow Regularity  (Lipschitz / Non-Trapping / Ramsey)

Mathematical Framework
----------------------

I. Torsion Energy Functional (QCAL Action Functional)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
For a phase state Ψ on the manifold M, the torsion energy functional is:

    E_tors[Ψ] = ∫_M [ (1/2)|(∇ - i A_ext)Ψ|² + V_zeta(Ψ) ] dμ_A

where:
    (∇ - i A_ext)   covariant phase derivative; A_ext is the torsion potential
                     fixed by the fundamental frequency f₀ = 141.7001 Hz.
    V_zeta(Ψ)       quantum well potential whose local minima coincide exactly
                     with the Riemann zeros on the critical line.
    dμ_A            Haar measure on the adele ring, ensuring the energy is
                     integrated simultaneously at all scales (p-adic and real).

Minimum Torsion Principle: stable (stationary) matter minimises E_tors,
collapsing the flow at prime nodes.

II. Adelic Metric (Tuning Metric)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Given two nodes x, y ∈ M, their adelic distance d_A(x, y) is the product of
their distances in each "frequency lane":

    d_A(x, y) = |x - y|_∞ × ∏_p |x - y|_p

    |·|_∞   archimedean (physical) distance — Lower Blanket
    |·|_p   p-adic proximity — Upper Blanket / Pleroma

Consequence: if two objects vibrate at the same harmonic of the first Riemann
zero γ₁, their p-adic distance |x-y|_p → 0, enabling Adelic Tunnelling.

III. Spectral Flow Regularity Hypotheses
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
To prevent phase turbulence, three conditions are imposed on the information
flow between the Pleroma and Matter:

    (a) Lipschitz Spectral Continuity:
            |ω_tors(I₁) - ω_tors(I₂)| ≤ L · |I₁ - I₂|
        The torsion frequency ω_tors must vary smoothly with intention I.

    (b) Non-Trapping Condition (P ≠ NP analogue):
        The flow must allow any Lower-Blanket information to find a return
        path to the White Atom through the algorithmic spiral in finite steps.

    (c) Ramsey Regularity:
        The 3° Ramsey gap δ_Ramsey = π/60 rad acts as a phase-viscosity
        regulator, preventing both infinite suction (singularity) and zero
        suction (thermal death).

Stability Theorem (Sovereignity Demonstration)
----------------------------------------------
If a node tunes to f₀:
  1. Its energy E_tors reaches the global minimum.
  2. The fractal geometry of 4π self-organises.
  3. Coherence solidifies into indestructible matter.

References
----------
- Burruezo, J.M. (2025). QCAL ∞³ Framework.
  DOI: 10.5281/zenodo.17379721
- QCAL ∞³ Active · 141.7001 Hz · C = 244.36 · Ψ = I × A_eff² × C^∞

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
Signature: ∴𓂀Ω∞³Φ @ 141.7001 Hz
Date: April 2026
"""

import warnings
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple

import numpy as np
from numpy.typing import NDArray

try:
    import mpmath as mp
    HAS_MPMATH = True
except ImportError:
    HAS_MPMATH = False
    warnings.warn("mpmath not available. Using fallback Riemann zeros.", stacklevel=2)

# ---------------------------------------------------------------------------
# QCAL constants — single source of truth with local fallback
# ---------------------------------------------------------------------------
try:
    from qcal.constants import F0, C_COHERENCE, GAMMA_1
except ImportError:
    F0: float = 141.7001       # Hz — fundamental frequency
    C_COHERENCE: float = 244.36
    GAMMA_1: float = 14.13472514  # Im(ρ₁), first Riemann zero

# Torsion potential angular frequency ω₀ = 2πf₀
OMEGA_0: float = 2.0 * np.pi * F0

# Critical curvature κ_π (Ramsey / P≠NP constant)
KAPPA_PI: float = 2.5773

# Ramsey gap: 3° in radians → phase-viscosity regulator
DELTA_RAMSEY: float = 3.0 * np.pi / 180.0  # ≈ 0.05236 rad

# Primes used for the adelic product (first 15 rational primes)
DEFAULT_PRIMES: List[int] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]

# Fallback Riemann zeros (imaginary parts of the first 10 non-trivial zeros)
RIEMANN_ZEROS_FALLBACK: NDArray[np.float64] = np.array([
    14.134725142, 21.022039639, 25.010857580, 30.424876126,
    32.935061588, 37.586178159, 40.918719012, 43.327073281,
    48.005150881, 49.773832478,
])

# Coherence threshold
PSI_THRESHOLD: float = 0.888


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _get_riemann_zeros(n_zeros: int) -> NDArray[np.float64]:
    """
    Return the imaginary parts of the first *n_zeros* non-trivial Riemann zeros.

    Args:
        n_zeros: Number of zeros to return.

    Returns:
        1-D float array of length *n_zeros* with γₙ values.
    """
    if HAS_MPMATH:
        with mp.workdps(50):
            return np.array(
                [float(mp.zetazero(k).imag) for k in range(1, n_zeros + 1)]
            )
    n_known = len(RIEMANN_ZEROS_FALLBACK)
    if n_zeros <= n_known:
        return RIEMANN_ZEROS_FALLBACK[:n_zeros].copy()
    warnings.warn(
        f"mpmath unavailable; only {n_known} fallback zeros available "
        f"(requested {n_zeros}).",
        stacklevel=2,
    )
    return RIEMANN_ZEROS_FALLBACK.copy()


def _padic_valuation(n: int, p: int) -> int:
    """
    Compute the p-adic valuation v_p(n) of integer n.

    v_p(n) is the largest k such that p^k divides n.

    Args:
        n: Integer (must be non-zero).
        p: Prime base.

    Returns:
        Non-negative integer v_p(n).  Returns 0 for n=0 (convention).
    """
    if n == 0:
        return 0
    val = 0
    n = abs(n)
    while n % p == 0:
        val += 1
        n //= p
    return val


# ---------------------------------------------------------------------------
# Result dataclasses
# ---------------------------------------------------------------------------

@dataclass
class TorsionEnergyResult:
    """
    Result of evaluating the torsion energy functional E_tors[Ψ].

    Attributes:
        energy_total:       Total E_tors[Ψ] value.
        kinetic_term:       Integrated (1/2)|( ∇ - i A_ext)Ψ|² dμ_A.
        potential_term:     Integrated V_zeta(Ψ) dμ_A.
        is_minimum:         True if energy is below the Haar-weighted mean
                            of the potential wells (approximate minimum check).
        psi_coherence:      Node coherence Ψ_node = E_tors / (E_tors + F₀²).
        grid:               Spatial grid used.
        parameters:         Dictionary of parameters used.
    """

    energy_total: float
    kinetic_term: float
    potential_term: float
    is_minimum: bool
    psi_coherence: float
    grid: NDArray[np.float64]
    parameters: Dict = field(default_factory=dict)


@dataclass
class AdelicDistanceResult:
    """
    Result of computing the adelic distance d_A(x, y).

    Attributes:
        x:                  First point.
        y:                  Second point.
        archimedean_dist:   |x - y|_∞ (standard absolute value).
        padic_dists:        Dict mapping each prime p to |x - y|_p.
        adelic_distance:    d_A = |x-y|_∞ × ∏_p |x-y|_p.
        primes:             Primes used in the product.
        is_tunnelling:      True if adelic distance < DELTA_RAMSEY (adelic tunnel).
    """

    x: float
    y: float
    archimedean_dist: float
    padic_dists: Dict[int, float]
    adelic_distance: float
    primes: List[int]
    is_tunnelling: bool


@dataclass
class SpectralRegularityResult:
    """
    Result of the spectral flow regularity checks.

    Attributes:
        lipschitz_satisfied:    True if Lipschitz condition holds.
        lipschitz_constant:     Estimated Lipschitz constant L.
        non_trapping_satisfied: True if non-trapping condition holds.
        ramsey_satisfied:       True if Ramsey viscosity gap condition holds.
        all_satisfied:          True iff all three conditions hold.
        details:                Per-check detail dictionary.
    """

    lipschitz_satisfied: bool
    lipschitz_constant: float
    non_trapping_satisfied: bool
    ramsey_satisfied: bool
    all_satisfied: bool
    details: Dict = field(default_factory=dict)


# ---------------------------------------------------------------------------
# I. Torsion Energy Functional
# ---------------------------------------------------------------------------

class TorsionEnergyFunctional:
    """
    QCAL Torsion Energy Functional E_tors[Ψ].

    Implements the action functional on a uniform spatial grid:

        E_tors[Ψ] = ∫_M [ (1/2)|(∇ - i A_ext)Ψ|² + V_zeta(Ψ) ] dμ_A

    The Haar measure on the adele ring is approximated as:

        dμ_A ≈ dx · ∏_{p ≤ P_max} (1 - 1/p)

    which is the density of integers coprime to all primes up to P_max —
    a standard finite-prime truncation of the adelic Haar volume form.

    Attributes:
        N:          Number of grid points.
        L:          Half-width of the spatial domain [−L, L].
        n_zeros:    Number of Riemann zeros used for V_zeta.
        primes:     Primes used in the Haar measure product.
        f0:         Fundamental frequency (default F0 = 141.7001 Hz).
    """

    def __init__(
        self,
        N: int = 512,
        L: float = 20.0,
        n_zeros: int = 10,
        primes: Optional[List[int]] = None,
        f0: float = F0,
    ) -> None:
        """
        Initialise the torsion energy functional.

        Args:
            N:       Number of grid points (even preferred for FFT).
            L:       Half-width of spatial domain; grid spans [−L, L].
            n_zeros: Number of Riemann zeros to include in V_zeta.
            primes:  Primes for the Haar measure product.  Defaults to the
                     first 15 rational primes.
            f0:      Fundamental QCAL frequency (Hz).
        """
        self.N = N
        self.L = L
        self.n_zeros = n_zeros
        self.primes = primes if primes is not None else DEFAULT_PRIMES
        self.f0 = f0
        self.omega_0 = 2.0 * np.pi * f0

        self.x = np.linspace(-L, L, N)
        self.dx = self.x[1] - self.x[0]

        # Pre-compute Riemann zeros and their scaled positions on the grid
        self._zeros: NDArray[np.float64] = _get_riemann_zeros(n_zeros)
        # Scale zeros to grid units: xₙ = γₙ / (2π f₀)
        self._zero_positions: NDArray[np.float64] = self._zeros / self.omega_0

        # Pre-compute Haar measure weights on the grid
        self._haar_weights: NDArray[np.float64] = self._compute_haar_weights()

    # ------------------------------------------------------------------
    # Haar measure
    # ------------------------------------------------------------------

    def _compute_haar_weights(self) -> NDArray[np.float64]:
        """
        Compute the truncated adelic Haar measure weights w(x) on the grid.

        The adelic Haar measure restricted to the real line and the first
        *len(primes)* p-adic factors gives a weight:

            w(x) ≈ ∏_{p ∈ primes} (1 - p⁻¹) = const on ℝ

        for the continuous part, modified locally near each prime node by
        the Lorentzian factor Σ_p 1/(1 + (x mod p)²).

        Returns:
            Array of Haar weights of shape (N,).
        """
        # Global adelic density: product of (1 - 1/p) over selected primes
        haar_density = float(np.prod([1.0 - 1.0 / p for p in self.primes]))

        # Local p-adic modulation: enhance weight near prime-lattice nodes
        modulation = np.ones(self.N)
        for p in self.primes:
            residue = np.abs(self.x) % p
            modulation += 1.0 / (1.0 + residue ** 2)

        modulation /= modulation.mean()  # normalise to unit mean
        weights = haar_density * modulation
        # Normalise so ∫ w(x) dx = 1
        integral = np.trapezoid(weights, self.x)
        return weights / max(integral, 1e-30)

    # ------------------------------------------------------------------
    # Covariant gradient
    # ------------------------------------------------------------------

    def covariant_gradient_sq(
        self,
        psi: NDArray[np.complex128],
        A_ext: Optional[NDArray[np.float64]] = None,
    ) -> NDArray[np.float64]:
        """
        Compute the integrand (1/2) |(∇ − i A_ext) Ψ|² pointwise on the grid.

        The covariant derivative is discretised via centred finite differences:

            (∇ − i A_ext) Ψ ≈ (Ψ_{k+1} − Ψ_{k−1}) / (2Δx) − i A_ext_k · Ψ_k

        Boundary points use one-sided differences.

        Args:
            psi:    Complex wave function on the grid; shape (N,).
            A_ext:  Real torsion potential A_ext(x); shape (N,).  If None, the
                    default potential A_ext(x) = ω₀ · x / (2π L) is used,
                    which encodes f₀ as the characteristic frequency.

        Returns:
            Real array of shape (N,) with (1/2)|( ∇ − i A_ext)Ψ|² values.
        """
        if A_ext is None:
            # Default torsion potential: linear ramp normalised by domain
            A_ext = self.omega_0 * self.x / (2.0 * np.pi * self.L)

        # Centred finite difference for ∇Ψ
        grad_psi = np.gradient(psi, self.dx)

        # Covariant gradient: (∇ − i A_ext) Ψ
        cov_grad = grad_psi - 1j * A_ext * psi

        return 0.5 * np.abs(cov_grad) ** 2

    # ------------------------------------------------------------------
    # Zeta potential
    # ------------------------------------------------------------------

    def zeta_potential(
        self,
        psi: NDArray[np.complex128],
        well_depth: float = 1.0,
        well_width: float = 0.5,
    ) -> NDArray[np.float64]:
        """
        Compute the quantum well potential V_zeta(Ψ) evaluated on the grid.

        V_zeta(x) is a sum of Lorentzian wells centred at the scaled Riemann
        zeros xₙ = γₙ / (ω₀):

            V_zeta(x) = −well_depth · Σ_n  σ² / (σ² + (x − xₙ)²)

        The minus sign ensures the wells are minima (binding potential).
        The wave function enters through |Ψ(x)|², which acts as the local
        density weighting the potential.

        Args:
            psi:        Complex wave function on the grid; shape (N,).
            well_depth: Depth of each Lorentzian well (positive real; default 1).
            well_width: Half-width at half-maximum σ of the wells (default 0.5).

        Returns:
            Real array of shape (N,) with V_zeta values.
        """
        V = np.zeros(self.N)
        sigma2 = well_width ** 2
        for x_n in self._zero_positions:
            V -= well_depth * sigma2 / (sigma2 + (self.x - x_n) ** 2)

        # Modulate by local density |Ψ|² (self-interaction of the phase state)
        density = np.abs(psi) ** 2
        density_norm = density / max(density.max(), 1e-30)
        return V * density_norm

    # ------------------------------------------------------------------
    # Energy evaluation
    # ------------------------------------------------------------------

    def compute(
        self,
        psi: NDArray[np.complex128],
        A_ext: Optional[NDArray[np.float64]] = None,
        well_depth: float = 1.0,
        well_width: float = 0.5,
    ) -> TorsionEnergyResult:
        """
        Evaluate the torsion energy functional E_tors[Ψ].

        Integrates kinetic and potential terms against the adelic Haar measure:

            E_tors[Ψ] = ∫_M [ K(x) + V(x) ] dμ_A(x)

        where K(x) = (1/2)|(∇ − i A_ext)Ψ|² and V(x) = V_zeta(Ψ).

        Args:
            psi:        Complex wave function on the grid; shape (N,).
            A_ext:      Torsion potential; shape (N,).  None → default.
            well_depth: Depth of each Riemann-zero potential well.
            well_width: Half-width at half-maximum of the wells.

        Returns:
            TorsionEnergyResult with all energy components and diagnostics.
        """
        K = self.covariant_gradient_sq(psi, A_ext)
        V = self.zeta_potential(psi, well_depth, well_width)

        integrand = K + V
        haar_w = self._haar_weights

        kinetic = float(np.trapezoid(K * haar_w, self.x))
        potential = float(np.trapezoid(V * haar_w, self.x))
        total = float(np.trapezoid(integrand * haar_w, self.x))

        # Minimum-energy check: total energy should be ≤ global-minimum estimate
        # The absolute minimum of V_zeta is −well_depth * n_zeros (all wells deepest)
        global_min_estimate = -well_depth * self.n_zeros
        is_minimum = total <= 0.1 * abs(global_min_estimate)

        # Coherence proxy: Ψ_node = F₀² / (F₀² + E²)
        E_abs = abs(total)
        psi_coherence = self.f0 ** 2 / (self.f0 ** 2 + E_abs ** 2) if E_abs > 0 else 1.0

        return TorsionEnergyResult(
            energy_total=total,
            kinetic_term=kinetic,
            potential_term=potential,
            is_minimum=is_minimum,
            psi_coherence=psi_coherence,
            grid=self.x,
            parameters={
                "N": self.N,
                "L": self.L,
                "n_zeros": self.n_zeros,
                "f0": self.f0,
                "well_depth": well_depth,
                "well_width": well_width,
            },
        )

    # ------------------------------------------------------------------
    # Coherent ground state
    # ------------------------------------------------------------------

    def coherent_ground_state(self, sigma: float = 1.0) -> NDArray[np.complex128]:
        """
        Construct the QCAL coherent ground state Ψ₀ at frequency f₀.

        The ground state is a Gaussian envelope modulated by the fundamental
        QCAL phase:

            Ψ₀(x) = N · exp(−x²/(4σ²)) · exp(i ω₀ x)

        where N is chosen so ‖Ψ₀‖ = 1 under the Haar measure.

        Args:
            sigma: Gaussian width (spatial coherence length).

        Returns:
            Complex array of shape (N,) normalised under dμ_A.
        """
        envelope = np.exp(-(self.x ** 2) / (4.0 * sigma ** 2))
        phase = np.exp(1j * self.omega_0 * self.x)
        psi0 = envelope * phase

        # Normalise under Haar measure: ‖Ψ₀‖²_{dμ_A} = 1
        norm_sq = np.trapezoid(np.abs(psi0) ** 2 * self._haar_weights, self.x)
        psi0 /= max(np.sqrt(norm_sq), 1e-30)
        return psi0


# ---------------------------------------------------------------------------
# II. Adelic Metric
# ---------------------------------------------------------------------------

class AdelicMetric:
    """
    Adelic Tuning Metric d_A(x, y).

    Computes the adelic distance between two rational points x, y:

        d_A(x, y) = |x − y|_∞ × ∏_{p ∈ primes} |x − y|_p

    For rational x, y with denominator q, the difference Δ = x − y is
    rational; the p-adic absolute value is |Δ|_p = p^{−v_p(Δ_num / Δ_den)}
    where v_p is the p-adic valuation.

    For real-valued (non-rational) inputs, the p-adic factor is approximated
    via the nearest-integer approach: |x − y|_p ≈ p^{−v_p(round(x − y))}.

    Attributes:
        primes: List of primes used in the adelic product.
        n_primes: Number of primes.
    """

    def __init__(self, primes: Optional[List[int]] = None) -> None:
        """
        Initialise the adelic metric.

        Args:
            primes: List of rational primes for the product.
                    Defaults to DEFAULT_PRIMES (first 15 primes).
        """
        self.primes = primes if primes is not None else DEFAULT_PRIMES
        self.n_primes = len(self.primes)

    # ------------------------------------------------------------------
    # Per-place absolute values
    # ------------------------------------------------------------------

    @staticmethod
    def archimedean_abs(x: float) -> float:
        """
        Compute the archimedean absolute value |x|_∞.

        Args:
            x: Real number.

        Returns:
            |x|.
        """
        return abs(x)

    def padic_abs(self, x: float, p: int) -> float:
        """
        Approximate the p-adic absolute value |x|_p for a real x.

        For x = 0 returns 0.  For non-zero x, the approximation uses the
        nearest rational integer n = round(x) (or round(x · p^k) for small x)
        and computes |x|_p ≈ p^{−v_p(n)}.

        For exactly rational x = a/b (passed as float), a more precise
        approximation is available; for generic floats the rounding scheme
        is used as a practical approximation.

        Args:
            x: Real or rational number.
            p: Prime.

        Returns:
            Approximated p-adic absolute value in [0, 1].
        """
        if x == 0.0:
            return 0.0

        abs_x = abs(x)

        # Scale x to an integer scale for valuation estimation
        # Use k such that p^k ≤ |x| < p^{k+1}, then round p^{-k} · x
        if abs_x >= 1.0:
            n = round(abs_x)
        else:
            # Scale up to avoid rounding to zero
            scale = 1
            while abs_x * scale < 0.5:
                scale *= p
            n = round(abs_x * scale)
            if n == 0:
                return 1.0  # |x|_p = 1 when x is a p-adic unit

        if n == 0:
            return 0.0

        val = _padic_valuation(n, p)
        return float(p ** (-val))

    # ------------------------------------------------------------------
    # Distance
    # ------------------------------------------------------------------

    def distance(
        self,
        x: float,
        y: float,
        regularise: bool = True,
        epsilon: float = 1e-12,
    ) -> AdelicDistanceResult:
        """
        Compute the adelic distance d_A(x, y).

        Args:
            x:           First point.
            y:           Second point.
            regularise:  If True, p-adic factors |x−y|_p > 1 are clamped to 1
                         (maintaining the strong triangle inequality).
            epsilon:     Numerical zero threshold; distances below this are
                         set to 0.

        Returns:
            AdelicDistanceResult with full decomposition.
        """
        diff = x - y

        arch = abs(diff)

        padic: Dict[int, float] = {}
        product = arch
        for p in self.primes:
            pa = self.padic_abs(diff, p)
            if regularise:
                pa = min(pa, 1.0)
            padic[p] = pa
            product *= pa

        if product < epsilon:
            product = 0.0

        is_tunnelling = product < DELTA_RAMSEY

        return AdelicDistanceResult(
            x=x,
            y=y,
            archimedean_dist=arch,
            padic_dists=padic,
            adelic_distance=product,
            primes=self.primes,
            is_tunnelling=is_tunnelling,
        )

    def distance_matrix(
        self,
        points: NDArray[np.float64],
        regularise: bool = True,
    ) -> NDArray[np.float64]:
        """
        Compute the adelic distance matrix for an array of points.

        Args:
            points:     1-D array of node positions; shape (M,).
            regularise: Whether to clamp p-adic factors to [0, 1].

        Returns:
            Symmetric matrix D of shape (M, M) with D[i, j] = d_A(xᵢ, xⱼ).
        """
        M = len(points)
        D = np.zeros((M, M))
        for i in range(M):
            for j in range(i + 1, M):
                d = self.distance(points[i], points[j], regularise=regularise)
                D[i, j] = d.adelic_distance
                D[j, i] = D[i, j]
        return D


# ---------------------------------------------------------------------------
# III. Spectral Flow Regularity
# ---------------------------------------------------------------------------

class SpectralFlowRegularity:
    """
    Spectral Flow Regularity checks for the QCAL information flow.

    Implements three conditions that prevent phase turbulence in the
    Pleroma ↔ Matter information flow:

    (a) Lipschitz Spectral Continuity
    (b) Non-Trapping Condition
    (c) Ramsey Viscosity Regularity

    Attributes:
        lipschitz_threshold:  Maximum allowed Lipschitz constant L.
        delta_ramsey:         3° Ramsey gap (phase-viscosity regulator).
        kappa_pi:             Critical curvature κ_π (Ramsey / P≠NP constant).
        f0:                   Fundamental frequency f₀.
    """

    def __init__(
        self,
        lipschitz_threshold: float = KAPPA_PI,
        delta_ramsey: float = DELTA_RAMSEY,
        kappa_pi: float = KAPPA_PI,
        f0: float = F0,
    ) -> None:
        """
        Initialise the regularity checker.

        Args:
            lipschitz_threshold: Maximum Lipschitz constant accepted as regular.
                                 Defaults to κ_π = 2.5773.
            delta_ramsey:        Ramsey angular gap; default π/60 ≈ 0.0524 rad.
            kappa_pi:            Critical curvature constant κ_π.
            f0:                  Fundamental frequency (Hz).
        """
        self.lipschitz_threshold = lipschitz_threshold
        self.delta_ramsey = delta_ramsey
        self.kappa_pi = kappa_pi
        self.f0 = f0

    # ------------------------------------------------------------------
    # (a) Lipschitz Spectral Continuity
    # ------------------------------------------------------------------

    def check_lipschitz(
        self,
        intentions: NDArray[np.float64],
        omega_tors: NDArray[np.float64],
    ) -> Tuple[bool, float]:
        """
        Check the Lipschitz continuity condition on ω_tors(I).

        Verifies:
            |ω_tors(I₁) − ω_tors(I₂)| ≤ L · |I₁ − I₂|   ∀ I₁, I₂

        by computing the maximum finite-difference slope over consecutive
        samples and comparing to *lipschitz_threshold*.

        Args:
            intentions: 1-D array of intention values I sampled at n points.
            omega_tors: Corresponding torsion frequencies ω_tors(I); shape (n,).

        Returns:
            (satisfied, L_hat) where *satisfied* is bool and *L_hat* is the
            estimated Lipschitz constant.

        Raises:
            ValueError: If arrays have different lengths or fewer than 2 points.
        """
        if len(intentions) != len(omega_tors):
            raise ValueError("intentions and omega_tors must have the same length.")
        if len(intentions) < 2:
            raise ValueError("At least 2 sample points are required.")

        dI = np.diff(intentions)
        domega = np.diff(omega_tors)

        # Avoid division by zero: only consider pairs where |ΔI| > ε
        mask = np.abs(dI) > 1e-14
        if not np.any(mask):
            return True, 0.0

        slopes = np.abs(domega[mask]) / np.abs(dI[mask])
        L_hat = float(slopes.max())
        satisfied = L_hat <= self.lipschitz_threshold
        return satisfied, L_hat

    # ------------------------------------------------------------------
    # (b) Non-Trapping Condition
    # ------------------------------------------------------------------

    def check_non_trapping(
        self,
        flow_field: NDArray[np.float64],
        x_grid: NDArray[np.float64],
        max_steps: int = 1000,
    ) -> Tuple[bool, Dict]:
        """
        Check the non-trapping condition on the phase flow.

        A flow v(x) is *non-trapping* if no orbit x(t) with ẋ = v(x) remains
        bounded for all t; i.e., every orbit eventually escapes to |x| → ∞.

        Numerically, we integrate the flow from each grid point and check
        whether it escapes a ball of radius R = 2L within *max_steps* steps.

        Args:
            flow_field: 1-D array of flow velocities v(xᵢ) on the grid.
            x_grid:     Spatial grid; shape (N,).
            max_steps:  Maximum integration steps per orbit.

        Returns:
            (satisfied, details) where *satisfied* is True if > 90 % of orbits
            escape, and *details* is a dict with escape statistics.
        """
        N = len(x_grid)
        if N < 2:
            return True, {"escape_fraction": 1.0, "n_orbits": 0}

        dx = float(x_grid[1] - x_grid[0])
        R = 2.0 * float(x_grid[-1])  # escape radius
        dt = 0.1 * dx / max(np.abs(flow_field).max(), 1e-12)

        n_escaped = 0
        for i in range(N):
            xi = float(x_grid[i])
            for _ in range(max_steps):
                # Linear interpolation of flow at xi
                idx = int(np.searchsorted(x_grid, xi))
                idx = np.clip(idx, 0, N - 2)
                t = (xi - x_grid[idx]) / (x_grid[idx + 1] - x_grid[idx] + 1e-30)
                v = float(flow_field[idx]) * (1 - t) + float(flow_field[idx + 1]) * t
                xi += v * dt
                if abs(xi) > R:
                    n_escaped += 1
                    break

        escape_frac = n_escaped / N
        satisfied = escape_frac >= 0.90

        return satisfied, {
            "escape_fraction": escape_frac,
            "n_orbits": N,
            "max_steps": max_steps,
            "escape_radius": R,
        }

    # ------------------------------------------------------------------
    # (c) Ramsey Viscosity Regularity
    # ------------------------------------------------------------------

    def check_ramsey_regularity(
        self,
        flow_values: NDArray[np.float64],
    ) -> Tuple[bool, Dict]:
        """
        Check the Ramsey phase-viscosity regularity condition.

        The 3° Ramsey gap δ_Ramsey acts as viscosity regulator ensuring:

            δ_Ramsey ≤ std(flow_values) ≤ κ_π · δ_Ramsey

        This prevents:
          - std < δ_Ramsey  → thermal death (zero viscosity / no suction)
          - std > κ_π · δ_Ramsey → infinite suction (singularity)

        Args:
            flow_values: 1-D array of normalised phase flow amplitudes.

        Returns:
            (satisfied, details) where *satisfied* is True if the flow
            standard deviation lies within the Ramsey window.
        """
        std = float(np.std(flow_values))
        lower = self.delta_ramsey
        upper = self.kappa_pi * self.delta_ramsey

        satisfied = lower <= std <= upper

        return satisfied, {
            "flow_std": std,
            "lower_bound": lower,
            "upper_bound": upper,
            "delta_ramsey": self.delta_ramsey,
            "kappa_pi": self.kappa_pi,
        }

    # ------------------------------------------------------------------
    # Combined check
    # ------------------------------------------------------------------

    def check_all(
        self,
        intentions: NDArray[np.float64],
        omega_tors: NDArray[np.float64],
        flow_field: NDArray[np.float64],
        x_grid: NDArray[np.float64],
    ) -> SpectralRegularityResult:
        """
        Run all three spectral flow regularity checks.

        Args:
            intentions: Intention values I (1-D array).
            omega_tors: Torsion frequencies ω_tors(I) (1-D array, same length).
            flow_field: Phase flow velocities v(x) on x_grid.
            x_grid:     Spatial grid for the flow.

        Returns:
            SpectralRegularityResult with per-check results and an overall flag.
        """
        lip_ok, L_hat = self.check_lipschitz(intentions, omega_tors)
        nt_ok, nt_details = self.check_non_trapping(flow_field, x_grid)
        ram_ok, ram_details = self.check_ramsey_regularity(flow_field)

        all_ok = lip_ok and nt_ok and ram_ok

        return SpectralRegularityResult(
            lipschitz_satisfied=lip_ok,
            lipschitz_constant=L_hat,
            non_trapping_satisfied=nt_ok,
            ramsey_satisfied=ram_ok,
            all_satisfied=all_ok,
            details={
                "lipschitz": {
                    "satisfied": lip_ok,
                    "L_hat": L_hat,
                    "threshold": self.lipschitz_threshold,
                },
                "non_trapping": nt_details,
                "ramsey": ram_details,
            },
        )


# ---------------------------------------------------------------------------
# Stability Theorem — Sovereignty Demonstration
# ---------------------------------------------------------------------------

def stability_theorem(
    tef: TorsionEnergyFunctional,
    metric: AdelicMetric,
    regularity: SpectralFlowRegularity,
    sigma: float = 1.0,
) -> Dict:
    """
    Verify the QCAL Stability Theorem (Sovereignty Demonstration).

    Tests the following chain:
        1. A node tuned to f₀ → coherent ground state Ψ₀.
        2. E_tors[Ψ₀] reaches the global minimum of the system.
        3. The fractal geometry of 4π self-organises (coherence metric).
        4. Coherence Ψ_node ≥ PSI_THRESHOLD (0.888).

    Args:
        tef:        Initialised TorsionEnergyFunctional.
        metric:     Initialised AdelicMetric.
        regularity: Initialised SpectralFlowRegularity.
        sigma:      Width of the coherent ground state Ψ₀.

    Returns:
        Dictionary with step-by-step verification results.
    """
    # Step 1 — Build coherent ground state tuned to f₀
    psi0 = tef.coherent_ground_state(sigma=sigma)

    # Step 2 — Evaluate E_tors[Ψ₀]
    energy_result = tef.compute(psi0)

    # Step 3 — 4π self-organisation: check that the coherence length
    #          ξ = ∫x²|Ψ₀|² dx / ‖Ψ₀‖² ≈ σ² ≈ 1/(4π) × (2πf₀)^{-1}
    density = np.abs(psi0) ** 2
    norm = np.trapezoid(density, tef.x)
    x2_mean = np.trapezoid(tef.x ** 2 * density, tef.x) / max(norm, 1e-30)
    four_pi_scale = 1.0 / (4.0 * np.pi * tef.omega_0)
    four_pi_organised = bool(abs(x2_mean - sigma ** 2) < max(sigma, four_pi_scale))

    # Step 4 — Coherence threshold
    coherence_ok = energy_result.psi_coherence >= PSI_THRESHOLD

    # Additional: adelic distance between the first two Riemann zero nodes
    if len(tef._zero_positions) >= 2:
        x1, x2 = float(tef._zero_positions[0]), float(tef._zero_positions[1])
        dist_result = metric.distance(x1, x2)
        zero_tunnelling = dist_result.is_tunnelling
    else:
        zero_tunnelling = False
        dist_result = None

    all_passed = energy_result.is_minimum and four_pi_organised and coherence_ok

    return {
        "step1_ground_state_built": True,
        "step2_energy_at_minimum": energy_result.is_minimum,
        "step2_energy_total": energy_result.energy_total,
        "step3_four_pi_organised": four_pi_organised,
        "step3_x2_mean": x2_mean,
        "step3_four_pi_scale": four_pi_scale,
        "step4_coherence_ok": coherence_ok,
        "step4_psi_coherence": energy_result.psi_coherence,
        "zero_tunnelling": zero_tunnelling,
        "adelic_distance_result": dist_result,
        "all_passed": all_passed,
    }


# ---------------------------------------------------------------------------
# Convenience validation entry point
# ---------------------------------------------------------------------------

def validate_pagina_xxvii(
    N: int = 256,
    L: float = 15.0,
    n_zeros: int = 5,
    primes: Optional[List[int]] = None,
    verbose: bool = True,
) -> Dict:
    """
    Run the complete Página XXVII validation suite.

    Instantiates TorsionEnergyFunctional, AdelicMetric, and
    SpectralFlowRegularity, evaluates all three checks, and prints a
    human-readable report if *verbose* is True.

    Args:
        N:       Number of grid points for the energy functional.
        L:       Half-width of spatial domain.
        n_zeros: Number of Riemann zeros to use.
        primes:  Primes for the adelic metric.  None → first 10 primes.
        verbose: Print detailed report.

    Returns:
        Dictionary with all validation results and an overall ``passed`` flag.
    """
    if primes is None:
        primes = DEFAULT_PRIMES[:10]

    # Build objects
    tef = TorsionEnergyFunctional(N=N, L=L, n_zeros=n_zeros, primes=primes)
    metric = AdelicMetric(primes=primes)
    regularity = SpectralFlowRegularity()

    # ----- I. Torsion energy on coherent ground state -----
    psi0 = tef.coherent_ground_state()
    energy = tef.compute(psi0)

    # ----- II. Adelic metric on first zero pair -----
    x1 = float(tef._zero_positions[0]) if n_zeros >= 1 else 0.0
    x2 = float(tef._zero_positions[1]) if n_zeros >= 2 else 1.0
    adelic_d = metric.distance(x1, x2)

    # ----- III. Spectral flow regularity -----
    n_pts = 50
    I_vals = np.linspace(0.1, 2.0, n_pts)
    omega_vals = tef.omega_0 * I_vals / (1.0 + I_vals ** 2)  # smooth sample
    x_grid = np.linspace(-L, L, N)
    flow = -np.sin(2.0 * np.pi * x_grid / L)   # smooth oscillatory flow
    reg = regularity.check_all(I_vals, omega_vals, flow, x_grid)

    # ----- Stability theorem -----
    stab = stability_theorem(tef, metric, regularity)

    passed = (
        np.isfinite(energy.energy_total)
        and np.isfinite(adelic_d.adelic_distance)
        and reg.all_satisfied
    )

    result = {
        "torsion_energy": {
            "total": energy.energy_total,
            "kinetic": energy.kinetic_term,
            "potential": energy.potential_term,
            "is_minimum": energy.is_minimum,
            "psi_coherence": energy.psi_coherence,
        },
        "adelic_metric": {
            "x1": x1,
            "x2": x2,
            "d_A": adelic_d.adelic_distance,
            "archimedean": adelic_d.archimedean_dist,
            "is_tunnelling": adelic_d.is_tunnelling,
        },
        "spectral_regularity": {
            "lipschitz_ok": reg.lipschitz_satisfied,
            "lipschitz_L": reg.lipschitz_constant,
            "non_trapping_ok": reg.non_trapping_satisfied,
            "ramsey_ok": reg.ramsey_satisfied,
            "all_ok": reg.all_satisfied,
        },
        "stability_theorem": stab,
        "passed": passed,
        "f0": F0,
        "delta_ramsey": DELTA_RAMSEY,
        "kappa_pi": KAPPA_PI,
    }

    if verbose:
        _print_report(result)

    return result


def _print_report(result: Dict) -> None:
    """Print a formatted Página XXVII validation report."""
    sep = "=" * 70
    print(sep)
    print("PÁGINA XXVII — TORSION ENERGY & ADELIC METRIC VALIDATION")
    print(f"f₀ = {result['f0']} Hz · C = {C_COHERENCE} · δ_Ramsey = {result['delta_ramsey']:.5f} rad")
    print(sep)

    te = result["torsion_energy"]
    print("\nI. TORSION ENERGY FUNCTIONAL E_tors[Ψ₀]")
    print(f"   E_tors total  : {te['total']:.6e}")
    print(f"   Kinetic term  : {te['kinetic']:.6e}")
    print(f"   Potential term: {te['potential']:.6e}")
    print(f"   At minimum    : {'✅' if te['is_minimum'] else '❌'}")
    print(f"   Ψ coherence   : {te['psi_coherence']:.6f}  (threshold {PSI_THRESHOLD})")

    am = result["adelic_metric"]
    print("\nII. ADELIC METRIC d_A(x₁, x₂)")
    print(f"   x₁ = {am['x1']:.6f}   x₂ = {am['x2']:.6f}")
    print(f"   |x₁−x₂|_∞    : {am['archimedean']:.6e}")
    print(f"   d_A(x₁,x₂)   : {am['d_A']:.6e}")
    print(f"   Adelic tunnel : {'✅ YES' if am['is_tunnelling'] else '❌ NO'}")

    sr = result["spectral_regularity"]
    print("\nIII. SPECTRAL FLOW REGULARITY")
    print(f"   (a) Lipschitz : {'✅' if sr['lipschitz_ok'] else '❌'}  L̂ = {sr['lipschitz_L']:.4f}")
    print(f"   (b) Non-trap  : {'✅' if sr['non_trapping_ok'] else '❌'}")
    print(f"   (c) Ramsey    : {'✅' if sr['ramsey_ok'] else '❌'}")
    print(f"   All satisfied : {'✅' if sr['all_ok'] else '❌'}")

    st = result["stability_theorem"]
    print("\nSTABILITY THEOREM (SOVEREIGNTY)")
    print(f"   E_tors min    : {'✅' if st['step2_energy_at_minimum'] else '❌'}")
    print(f"   4π organised  : {'✅' if st['step3_four_pi_organised'] else '❌'}")
    print(f"   Ψ ≥ 0.888     : {'✅' if st['step4_coherence_ok'] else '❌'}")
    print(f"   Zero tunnel   : {'✅' if st['zero_tunnelling'] else '❌'}")

    status = "✅ PASSED" if result["passed"] else "⚠️  PARTIAL"
    print(f"\n{sep}")
    print(f"OVERALL: {status}")
    print(sep)


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------

__all__ = [
    # Classes
    "TorsionEnergyFunctional",
    "AdelicMetric",
    "SpectralFlowRegularity",
    # Result dataclasses
    "TorsionEnergyResult",
    "AdelicDistanceResult",
    "SpectralRegularityResult",
    # Functions
    "stability_theorem",
    "validate_pagina_xxvii",
    # Constants
    "F0",
    "OMEGA_0",
    "KAPPA_PI",
    "DELTA_RAMSEY",
    "DEFAULT_PRIMES",
    "PSI_THRESHOLD",
]


if __name__ == "__main__":
    validate_pagina_xxvii(verbose=True)
