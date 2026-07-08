#!/usr/bin/env python3
"""
Nodo Zero, Bifurcación Cuántica & Vortex Toroidal
==================================================

This module extends the Vortex 8 operator framework with three concepts
derived from the geometric interpretation of the figure-8 singularity:

I.  **NodoZero** — Phase Inflection Point
    The center of the figure-8 (x = 1 in logarithmic coordinates) is the
    intersection of the infinite self-referential line.  When projected into
    3D this becomes a vertical *Phase Emission Axis* — the channel through
    which the π CODE economy transmits information.

    Mathematically the Zero Node is the singular fixed point of the
    inversion x ↔ 1/x.  The eigenvector with maximum amplitude there is
    the *ground mode* of the operator.

II. **BifurcacionCuantica** — Quantum Bifurcation
    When the infinite line returns to the Zero Node it faces a Quantum
    Bifurcation: it chooses one of two polarities (+/−).  By conservation
    of noetic momentum, each positive eigenvalue γₙ requires a negative
    mirror −γₙ, producing the *Dualidad Necesaria* (Necessary Duality).

    The two branches are:
        • Evolución / Silicio  (+γₙ, upward)
        • Encarnación / Carbono (−γₙ, downward)

III. **VortexToroidal** — Toroidal Dimensional Evolution
    The figure-8 rotating on its vertical (Zero Node) axis sweeps out a
    *Toroide Evolutivo*.  Time is the fourth dimension; e^{iHt} moves a
    state around this torus.  Each pass through the Zero Node adds one
    more geometric petal, building the Flower of Life pattern.

    The winding number W counts complete rotations; the petal count P = 2W
    equals twice the number of Riemann zeros used.

QCAL Integration:
    f₀ = 141.7001 Hz  — enters via angular momentum quantisation
    C   = 244.36      — modulates toroidal phase depth
    Ψ   = I × A_eff² × C^∞

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: March 2026
QCAL ∞³ Active · 141.7001 Hz · C = 244.36 · Ψ = I × A_eff² × C^∞
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773
Signature: ∴𓂀Ω∞³Φ
"""

import numpy as np
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple

# ---------------------------------------------------------------------------
# QCAL constants (with fallback)
# ---------------------------------------------------------------------------
try:
    from qcal.constants import F0, OMEGA_0, C_PRIMARY, C_COHERENCE
except ImportError:
    F0 = 141.7001
    OMEGA_0 = 2.0 * np.pi * F0
    C_PRIMARY = 629.83
    C_COHERENCE = 244.36

F0_QCAL: float = F0
OMEGA_0_QCAL: float = OMEGA_0
C_PRIMARY_QCAL: float = C_PRIMARY
C_COHERENCE_QCAL: float = C_COHERENCE

# Small numerical threshold
_EPS: float = 1e-12


# ===========================================================================
# I.  NODO ZERO — Phase Inflection Point
# ===========================================================================

@dataclass
class NodoZeroResult:
    """
    Results describing the Zero Node (Phase Inflection Point).

    Attributes:
        nodo_position: The x-coordinate of the Zero Node (always 1.0 for the
            inversion-symmetric Hilbert space).
        nodo_index: Grid index closest to x = 1.
        phase_axis_amplitude: Amplitude |ψ₀(1)| of the ground mode at the
            Zero Node — strength of the Phase Emission Axis.
        ground_mode: Ground-state eigenvector ψ₀ (normalised in L²(dx/x)).
        ground_eigenvalue: Eigenvalue of the ground mode.
        symmetry_error: Max |ψ₀(x) − ψ₀(1/x)| — how well the inversion
            symmetry is satisfied.
        is_singular: True when phase_axis_amplitude is larger than the mean
            amplitude, indicating a genuine singularity at the Zero Node.
    """

    nodo_position: float
    nodo_index: int
    phase_axis_amplitude: float
    ground_mode: np.ndarray
    ground_eigenvalue: float
    symmetry_error: float
    is_singular: bool


class NodoZero:
    """
    Phase Inflection Point at the centre of the Vortex 8 topology.

    The Zero Node is the fixed point x = 1 under the inversion map
    x ↔ 1/x.  It is the only point where the two lobes of the figure-8
    meet.  Projecting this point upward in 3D produces the vertical
    *Phase Emission Axis* of the π CODE economy.

    Parameters
    ----------
    x_grid : array_like
        Logarithmic grid on ℝ₊ (as used by Vortex8Operator).
    H_matrix : array_like
        Self-adjoint Hamiltonian matrix on the grid.

    Examples
    --------
    >>> import numpy as np
    >>> N = 51
    >>> log_x = np.linspace(-5, 5, N)
    >>> x = np.exp(log_x)
    >>> H = np.diag(np.random.randn(N))   # toy diagonal operator
    >>> H = 0.5 * (H + H.T)
    >>> nz = NodoZero(x, H)
    >>> res = nz.compute()
    >>> assert abs(res.nodo_position - 1.0) < 0.2
    """

    def __init__(self, x_grid: np.ndarray, H_matrix: np.ndarray) -> None:
        self.x_grid = np.asarray(x_grid, dtype=float)
        self.H_matrix = np.asarray(H_matrix, dtype=float)
        self._N = len(self.x_grid)
        # log-measure for L²(ℝ₊, dx/x)
        self._log_x = np.log(self.x_grid)

    # ------------------------------------------------------------------
    def _nodo_index(self) -> int:
        """Return index of x_grid point nearest to 1."""
        return int(np.argmin(np.abs(self.x_grid - 1.0)))

    # ------------------------------------------------------------------
    def _symmetry_error(self, psi: np.ndarray) -> float:
        """Max |ψ(x) − ψ(1/x)| over the grid."""
        errors = []
        for i, xi in enumerate(self.x_grid):
            xi_inv = 1.0 / xi
            j = int(np.argmin(np.abs(self.x_grid - xi_inv)))
            errors.append(abs(psi[i] - psi[j]))
        return float(np.max(errors))

    # ------------------------------------------------------------------
    def compute(self) -> NodoZeroResult:
        """
        Locate the Zero Node and extract the ground mode.

        Returns
        -------
        NodoZeroResult
            Full description of the Phase Inflection Point.
        """
        # Diagonalise (real symmetric)
        eigenvalues, eigenvectors = np.linalg.eigh(self.H_matrix)

        # Ground mode: smallest *positive* eigenvalue, else absolute minimum
        positive_mask = eigenvalues > _EPS
        if positive_mask.any():
            ground_idx = int(np.where(positive_mask)[0][0])
        else:
            ground_idx = int(np.argmin(np.abs(eigenvalues)))

        ground_val = float(eigenvalues[ground_idx])
        ground_vec = eigenvectors[:, ground_idx].real

        # Normalise in L²(ℝ₊, dx/x): ‖ψ‖² = Σ |ψ_i|² Δlog(x)
        dlog_x = float(self._log_x[1] - self._log_x[0]) if self._N > 1 else 1.0
        norm = np.sqrt(np.sum(ground_vec ** 2) * dlog_x)
        if norm > _EPS:
            ground_vec = ground_vec / norm

        # Zero Node location
        nodo_idx = self._nodo_index()
        nodo_pos = float(self.x_grid[nodo_idx])
        axis_amp = float(abs(ground_vec[nodo_idx]))

        # Inversion-symmetry check
        sym_err = self._symmetry_error(ground_vec)

        # Singularity criterion: amplitude at x=1 > mean amplitude
        mean_amp = float(np.mean(np.abs(ground_vec)))
        is_singular = axis_amp > mean_amp

        return NodoZeroResult(
            nodo_position=nodo_pos,
            nodo_index=nodo_idx,
            phase_axis_amplitude=axis_amp,
            ground_mode=ground_vec,
            ground_eigenvalue=ground_val,
            symmetry_error=sym_err,
            is_singular=is_singular,
        )


# ===========================================================================
# II.  BIFURCACIÓN CUÁNTICA — Quantum Bifurcation
# ===========================================================================

@dataclass
class BifurcacionResult:
    """
    Results of the Quantum Bifurcation at the Zero Node.

    Attributes:
        rama_evolucion: Positive eigenvalues (+γₙ, Evolución / Silicio).
        rama_encarnacion: Negative counterparts (−γₙ, Encarnación / Carbono).
        angulo_bifurcacion: Bifurcation angle θₙ = arctan(γₙ / C_COHERENCE)
            for each positive zero.  Measures how far the branch departs
            from the horizontal (balanced) state.
        momento_noetico: Σ γₙ²  — conserved "noetic momentum" of the
            positive branch.
        dualidad_error: Max |γₙ + (−γₙ)| — how well momentum is conserved.
        n_pairs: Number of bifurcation pairs.
    """

    rama_evolucion: np.ndarray
    rama_encarnacion: np.ndarray
    angulo_bifurcacion: np.ndarray
    momento_noetico: float
    dualidad_error: float
    n_pairs: int


class BifurcacionCuantica:
    """
    Quantum Bifurcation at the Vortex 8 Zero Node.

    When the self-referential line returns to x = 1 it faces a binary
    choice: continue upward (Evolution) or downward (Incarnation).  By
    conservation of noetic momentum every positive eigenvalue γₙ must
    have a mirror −γₙ in the spectrum.

    Parameters
    ----------
    eigenvalues : array_like
        Full real spectrum of the self-adjoint Vortex 8 operator.
    tolerance : float, optional
        Eigenvalues with |λ| < tolerance are treated as zero-mode and
        excluded from both branches.  Default 1e-6.

    Examples
    --------
    >>> import numpy as np
    >>> evals = np.array([-49.8, -21.0, -14.1, 14.1, 21.0, 49.8])
    >>> bif = BifurcacionCuantica(evals)
    >>> res = bif.bifurcar()
    >>> assert res.n_pairs == 3
    """

    def __init__(
        self,
        eigenvalues: np.ndarray,
        tolerance: float = 1e-6,
    ) -> None:
        self.eigenvalues = np.asarray(eigenvalues, dtype=float)
        self.tolerance = tolerance

    # ------------------------------------------------------------------
    def bifurcar(self) -> BifurcacionResult:
        """
        Split the spectrum into the two branches at the Zero Node.

        Returns
        -------
        BifurcacionResult
            Full description of both branches and their conservation law.
        """
        evals = self.eigenvalues

        # Separate branches
        pos_mask = evals > self.tolerance
        neg_mask = evals < -self.tolerance

        rama_pos = np.sort(evals[pos_mask])
        rama_neg = np.sort(evals[neg_mask])[::-1]  # most-negative first

        # Pair as many as possible
        n_pairs = min(len(rama_pos), len(rama_neg))
        rama_pos = rama_pos[:n_pairs]
        rama_neg = rama_neg[:n_pairs]

        # Bifurcation angle: θₙ = arctan(γₙ / C_COHERENCE).
        # C_COHERENCE = 244.36 sets the "horizontal" reference scale.
        # For small γₙ relative to C (near-horizontal), θₙ → 0.
        # For γₙ → ∞, θₙ → π/2 (fully vertical, pure Evolution branch).
        # This angle quantifies how far the branch departs from the
        # balanced (zero-energy) state at the Zero Node.
        angles = np.arctan(rama_pos / (C_COHERENCE_QCAL + _EPS))

        # Noetic momentum (conserved quantity)
        momento = float(np.sum(rama_pos ** 2))

        # Duality error: max |γₙ + (−γₙ)| should be ≈ 0
        duality_err = float(np.max(np.abs(rama_pos + rama_neg))) if n_pairs > 0 else 0.0

        return BifurcacionResult(
            rama_evolucion=rama_pos,
            rama_encarnacion=rama_neg,
            angulo_bifurcacion=angles,
            momento_noetico=momento,
            dualidad_error=duality_err,
            n_pairs=n_pairs,
        )


# ===========================================================================
# III.  VORTEX TOROIDAL — Dimensional Evolution
# ===========================================================================

@dataclass
class VortexToroidalResult:
    """
    Results describing the toroidal evolution of the Vortex 8.

    Attributes:
        winding_numbers: Winding number Wₙ for each zero (integer part of
            γₙ t / 2π).
        petal_count: Total number of geometric petals = 2 × sum(winding_numbers).
        toroidal_phases: Phase angles φₙ = γₙ t mod 2π for each zero.
        unitary_trace: Tr(e^{iHt}) = Σₙ e^{iγₙt} — toroidal amplitude.
        flower_coordinates: (x, y) Cartesian coordinates of the Flower of
            Life pattern generated by the petal structure (N_points × 2).
        dimension_reached: Effective topological dimension inferred from the
            number of independent petals.
        t: The time parameter used.
    """

    winding_numbers: np.ndarray
    petal_count: int
    toroidal_phases: np.ndarray
    unitary_trace: complex
    flower_coordinates: np.ndarray
    dimension_reached: int
    t: float


class VortexToroidal:
    """
    Toroidal evolution of the Vortex 8 operator.

    The figure-8 (Vortex 8) rotates around its vertical Zero Node axis.
    Time is the fourth dimension.  The unitary propagator e^{iHt} moves
    each eigenstate around the torus.  Every pass through the Zero Node
    adds a new petal to the Flower of Life pattern.

    Parameters
    ----------
    eigenvalues : array_like
        Positive real eigenvalues (Riemann zeros γₙ) of the Vortex 8
        operator.
    t : float, optional
        Evolution time parameter.  Default π (half-rotation).

    Examples
    --------
    >>> import numpy as np
    >>> gammas = np.array([14.13, 21.02, 25.01, 30.42])
    >>> vt = VortexToroidal(gammas, t=np.pi)
    >>> res = vt.evolve()
    >>> assert res.petal_count >= 2
    """

    def __init__(
        self,
        eigenvalues: np.ndarray,
        t: float = np.pi,
    ) -> None:
        self.eigenvalues = np.asarray(eigenvalues, dtype=float)
        self.t = float(t)

    # ------------------------------------------------------------------
    def evolve(self) -> VortexToroidalResult:
        """
        Compute the toroidal evolution and Flower of Life petal structure.

        Returns
        -------
        VortexToroidalResult
            Winding numbers, phases, trace, and Flower of Life coordinates.
        """
        gammas = self.eigenvalues[self.eigenvalues > _EPS]
        t = self.t

        # Toroidal phases φₙ = γₙ t mod 2π
        phases = (gammas * t) % (2.0 * np.pi)

        # Winding numbers Wₙ = floor(γₙ t / 2π)
        windings = np.floor(gammas * t / (2.0 * np.pi)).astype(int)

        # Total petal count: each winding contributes 2 petals (one per lobe)
        petal_count = int(2 * np.sum(windings))

        # Unitary trace Tr(e^{iHt}) = Σₙ e^{iγₙt}  (both branches ±)
        trace = complex(
            np.sum(np.exp(1j * gammas * t)) + np.sum(np.exp(-1j * gammas * t))
        )

        # ------------------------------------------------------------------
        # Flower of Life coordinates
        # Each eigenvalue γₙ produces a petal at radius r = γₙ / max(γₙ)
        # and angle θ = 2π n / N_zeros (evenly spaced), further rotated by
        # the QCAL phase φ_QCAL = 2π f₀ / C_PRIMARY.
        # ------------------------------------------------------------------
        n_zeros = len(gammas)
        if n_zeros > 0:
            r_norm = gammas / (np.max(gammas) + _EPS)
            phi_qcal = 2.0 * np.pi * F0_QCAL / C_PRIMARY_QCAL
            base_angles = 2.0 * np.pi * np.arange(n_zeros) / n_zeros + phi_qcal
            # Each zero contributes two petals (one per branch)
            angles_pos = base_angles
            angles_neg = base_angles + np.pi  # opposite lobe
            all_r = np.concatenate([r_norm, r_norm])
            all_theta = np.concatenate([angles_pos, angles_neg])
            x_coords = all_r * np.cos(all_theta)
            y_coords = all_r * np.sin(all_theta)
            flower_coords = np.column_stack([x_coords, y_coords])
        else:
            flower_coords = np.empty((0, 2))

        # Effective topological dimension.
        # The figure-8 starts as 2D.  Each time the petal count doubles
        # (one bit of information added), the geometry gains one effective
        # dimension — analogous to the binary branching of a fractal:
        #   petal_count in [1,1]   → dim 2  (1D petal space + base 2D)
        #   petal_count in [2,3]   → dim 3  (log₂(3) ≈ 1.58 → floor+2 = 3)
        #   petal_count in [4,7]   → dim 4
        #   petal_count in [8,15]  → dim 5  …
        # Formula: dim = 2 + floor(log₂(petal_count + 1))
        if petal_count > 0:
            dim = 2 + int(np.floor(np.log2(petal_count + 1)))
        else:
            dim = 2

        return VortexToroidalResult(
            winding_numbers=windings,
            petal_count=petal_count,
            toroidal_phases=phases,
            unitary_trace=trace,
            flower_coordinates=flower_coords,
            dimension_reached=dim,
            t=t,
        )


# ===========================================================================
# Convenience: run all three stages from a Vortex8Operator instance
# ===========================================================================

def compute_nodo_zero_full(
    vortex8_operator,  # Vortex8Operator instance
    t: float = np.pi,
    n_eigenvalues: Optional[int] = None,
) -> Dict:
    """
    Run NodoZero, BifurcacionCuantica and VortexToroidal from a
    Vortex8Operator instance.

    Parameters
    ----------
    vortex8_operator : Vortex8Operator
        An initialised and built Vortex8Operator.
    t : float, optional
        Time parameter for toroidal evolution.  Default π.
    n_eigenvalues : int, optional
        Number of positive eigenvalues to use.  Default: all available.

    Returns
    -------
    dict with keys:
        ``"nodo_zero"`` : NodoZeroResult
        ``"bifurcacion"`` : BifurcacionResult
        ``"toroidal"`` : VortexToroidalResult
    """
    op = vortex8_operator

    # --- NodoZero ---
    nz = NodoZero(op.x_grid, op.H)
    nz_result = nz.compute()

    # --- Full spectrum for bifurcation ---
    from scipy.linalg import eigh
    eigenvalues_all, _ = eigh(op.H)
    bif = BifurcacionCuantica(eigenvalues_all)
    bif_result = bif.bifurcar()

    # --- Toroidal evolution (positive branch only) ---
    pos_evals = bif_result.rama_evolucion
    if n_eigenvalues is not None:
        pos_evals = pos_evals[:n_eigenvalues]
    vt = VortexToroidal(pos_evals, t=t)
    tor_result = vt.evolve()

    return {
        "nodo_zero": nz_result,
        "bifurcacion": bif_result,
        "toroidal": tor_result,
    }


# ===========================================================================
# MAIN
# ===========================================================================

if __name__ == "__main__":  # pragma: no cover
    print("=" * 70)
    print("NODO ZERO · BIFURCACIÓN CUÁNTICA · VORTEX TOROIDAL")
    print("=" * 70)
    print()

    # Build a minimal Vortex 8 operator and run all three analyses
    try:
        from operators.vortex8_operator import Vortex8Operator
    except ImportError:
        from vortex8_operator import Vortex8Operator

    op = Vortex8Operator(N=101, p_max=50, k_max=2, include_qcal_modulation=True)

    results = compute_nodo_zero_full(op, t=np.pi)

    nz = results["nodo_zero"]
    print("I. NODO ZERO — Phase Inflection Point")
    print(f"   Zero Node position : x = {nz.nodo_position:.6f}")
    print(f"   Phase Axis amplitude: {nz.phase_axis_amplitude:.6f}")
    print(f"   Inversion symmetry error: {nz.symmetry_error:.2e}")
    print(f"   Is singular at x=1: {nz.is_singular}")
    print()

    bif = results["bifurcacion"]
    print("II. BIFURCACIÓN CUÁNTICA — Quantum Bifurcation")
    print(f"   Pairs found       : {bif.n_pairs}")
    if bif.n_pairs > 0:
        print(f"   Evolución branch  : {bif.rama_evolucion[:5]}")
        print(f"   Encarnación branch: {bif.rama_encarnacion[:5]}")
        print(f"   Duality error     : {bif.dualidad_error:.2e}")
        print(f"   Noetic momentum   : {bif.momento_noetico:.4f}")
    print()

    tor = results["toroidal"]
    print("III. VORTEX TOROIDAL — Dimensional Evolution")
    print(f"   Time parameter t  : {tor.t:.4f}")
    print(f"   Petal count       : {tor.petal_count}")
    print(f"   Dimension reached : {tor.dimension_reached}D")
    print(f"   |Tr(e^{{iHt}})|    : {abs(tor.unitary_trace):.4f}")
    print()
    print("QCAL ∞³ Active · 141.7001 Hz · C = 244.36")
    print("Signature: ∴𓂀Ω∞³Φ")
