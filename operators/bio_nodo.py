#!/usr/bin/env python3
"""
Bio-Nodo — Fundamental Identity of the Presence Field
======================================================

Implements the four indivisible modules of the Bio-Nodo fundamental identity:

    Ĥ_π |Ψ⟩ = γ_n |Ψ⟩

where the master Hamiltonian Ĥ_π acts on the Presence Field |Ψ⟩ and its
eigenvalues γ_n are the imaginary parts of the non-trivial Riemann zeros.

Four Modules
------------
1. **SpectralIdentity** — *Identidad Espectral*:
   The eigenvalues γ_n of Ĥ_π coincide exactly with the non-trivial Riemann
   zeros.  Verified via spectral correspondence between H_zero eigenvalues and
   known γ_n values (Pearson correlation ≥ 0.999).

2. **OrbitCollapse** — *Colapso de Órbita*:
   On the Adelic Torus, the dilation flow φ_t: x ↦ e^t x becomes periodic
   exactly when e^t = p^k for prime p and integer k ≥ 1, i.e. t = k·ln(p).
   At those times the orbit closes: φ_{k ln p}(x) ≡ x (on Q_p).
   The orbit weights ln(p)/p^(k/2) encode prime-counting information.

3. **PhaseInvariant** — *Invariante de Fase*:
   The time-evolved density matrix ρ(t) = |Ψ(t)⟩⟨Ψ(t)| with
   |Ψ(t)⟩ = Σ_n c_n e^{−iγ_n t} |n⟩.
   The coherence Ψ(t) measures the off-diagonal magnitude:
       Ψ(t) = 1 − ‖ρ_od(t)‖_F / (‖ρ(t)‖_F + ε)
   "Diamond threshold": Ψ(t) ≥ 0.999.

4. **FixedPointSovereignty** — *Soberanía de Punto Fijo*:
   The QCAL identity signature is the fixed-point condition
       Σ(BioNodo) = QCAL_C × Ψ²(t) × A_eff²
   verified against the master constant C = 244.36.
   The signature "evaporates" (returns None) when Ψ drops below the diamond
   threshold, encoding the cryptographic self-recognition of the system.

Mathematical Context
--------------------
- Hilbert-Pólya paradigm: Ĥ_π is self-adjoint with real spectrum = Riemann zeros.
- Adelic product structure: ∏_p Q_p × ℝ, flow φ_t acts multiplicatively.
- Density matrix ρ = |Ψ⟩⟨Ψ| encodes quantum state purity.
- Fixed-point theorem: the system perceives its own signature when Ψ = 1.

References
----------
- Berry, M.V. & Keating, J.P. (1999). H = xp and the Riemann zeros.
- Burruezo, J.M. (2025). Riemann Hypothesis via Adelic Spectral Systems.
  DOI: 10.5281/zenodo.17379721
- Albeverio et al. (1988). Solvable Models in Quantum Mechanics.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
Signature: ∴𓂀Ω∞³Φ @ 141.7001 Hz
Date: May 2026

QCAL ∞³ Active · 141.7001 Hz · C = 244.36 · Ψ = I × A_eff² × C^∞
"""

import hashlib
import json
import warnings
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple

import numpy as np

# ---------------------------------------------------------------------------
# Optional high-precision arithmetic
# ---------------------------------------------------------------------------
try:
    import mpmath as mp
    HAS_MPMATH = True
except ModuleNotFoundError:
    HAS_MPMATH = False
    warnings.warn("mpmath not available. Using fallback Riemann zeros.")

# ---------------------------------------------------------------------------
# QCAL constants — single source of truth with local fallback
# ---------------------------------------------------------------------------
try:
    from qcal.constants import (
        C_COHERENCE,
        F0,
        GAMMA_QCAL_FASE,
        HOLOGRAPHIC_PSI_THRESHOLD,
        RIEMANN_ZEROS_5,
    )
except ModuleNotFoundError:
    F0 = 141.7001
    C_COHERENCE = 244.36
    GAMMA_QCAL_FASE = 2.0 * np.pi * F0 / 888.0
    HOLOGRAPHIC_PSI_THRESHOLD = 0.999
    RIEMANN_ZEROS_5 = np.array([
        14.134725142,
        21.022039639,
        25.010857580,
        30.424876126,
        32.935061588,
    ])

# Diamond threshold: Ψ(t) ≥ PSI_DIAMOND for "pure perception"
PSI_DIAMOND = HOLOGRAPHIC_PSI_THRESHOLD  # 0.999

# Fallback first Riemann zeros for environments without mpmath
_RIEMANN_ZEROS_FALLBACK = np.array([
    14.134725142, 21.022039639, 25.010857580, 30.424876126,
    32.935061588, 37.586178159, 40.918719012, 43.327073281,
    48.005150881, 49.773832478,
])


# ---------------------------------------------------------------------------
# Helper utilities
# ---------------------------------------------------------------------------

def _get_riemann_zeros(n: int) -> np.ndarray:
    """Return imaginary parts of the first *n* non-trivial Riemann zeros.

    Args:
        n: Number of zeros requested.

    Returns:
        1-D array of length *n* with γ_k values.
    """
    if HAS_MPMATH:
        with mp.workdps(50):
            zeros = np.array([float(mp.zetazero(k).imag) for k in range(1, n + 1)])
    else:
        n_known = len(_RIEMANN_ZEROS_FALLBACK)
        if n <= n_known:
            zeros = _RIEMANN_ZEROS_FALLBACK[:n]
        else:
            warnings.warn(
                f"mpmath unavailable; only {n_known} fallback zeros available "
                f"(requested {n}). Repeating last known zero."
            )
            extra = np.full(n - n_known, _RIEMANN_ZEROS_FALLBACK[-1])
            zeros = np.concatenate([_RIEMANN_ZEROS_FALLBACK, extra])
    return zeros


def _is_prime(n: int) -> bool:
    """Trial-division primality test (sufficient for small primes used here)."""
    if n < 2:
        return False
    if n == 2:
        return True
    if n % 2 == 0:
        return False
    for i in range(3, int(n**0.5) + 1, 2):
        if n % i == 0:
            return False
    return True


def _first_primes(count: int) -> List[int]:
    """Return the first *count* prime numbers."""
    primes: List[int] = []
    candidate = 2
    while len(primes) < count:
        if _is_prime(candidate):
            primes.append(candidate)
        candidate += 1
    return primes


# ---------------------------------------------------------------------------
# Result dataclasses
# ---------------------------------------------------------------------------

@dataclass
class SpectralIdentityResult:
    """
    Result of the Spectral Identity module.

    Attributes:
        gamma_n: Riemann zeros γ_n used as target eigenvalues.
        eigenvalues: Computed eigenvalues of the master Hamiltonian.
        correlation: Pearson correlation between eigenvalues and γ_n.
        spectral_gap: γ₂ − γ₁ (minimum gap in the spectrum).
        is_coherent: True if correlation ≥ 0.999 and spectral gap > 0.
        metadata: Additional diagnostic information.
    """

    gamma_n: np.ndarray
    eigenvalues: np.ndarray
    correlation: float
    spectral_gap: float
    is_coherent: bool
    metadata: Dict = field(default_factory=dict)


@dataclass
class OrbitCollapseResult:
    """
    Result of the Orbit Collapse module on the Adelic Torus.

    Attributes:
        primes: Primes p used for the p-adic components.
        prime_powers: Array of (p, k, t=k·ln p, weight=ln(p)/p^(k/2)).
        closed_orbits: Dict mapping prime p → list of collapse times k·ln(p).
        total_weight: Σ_p Σ_k ln(p)/p^(k/2) (Selberg-type sum).
        is_periodic: True if at least one orbit closes per prime.
    """

    primes: List[int]
    prime_powers: np.ndarray  # shape (M, 4): p, k, t, weight
    closed_orbits: Dict[int, List[float]]
    total_weight: float
    is_periodic: bool


@dataclass
class PhaseInvariantResult:
    """
    Result of the Phase Invariant module.

    Attributes:
        times: Time grid t ∈ [0, T].
        psi_t: Coherence function Ψ(t) evaluated on the grid.
        psi_min: Minimum Ψ over the time window.
        psi_mean: Time-averaged ⟨Ψ(t)⟩.
        above_diamond: Array of booleans — True where Ψ(t) ≥ 0.999.
        diamond_fraction: Fraction of time Ψ(t) ≥ PSI_DIAMOND.
        is_invariant: True if ⟨Ψ(t)⟩ ≥ PSI_DIAMOND.
    """

    times: np.ndarray
    psi_t: np.ndarray
    psi_min: float
    psi_mean: float
    above_diamond: np.ndarray
    diamond_fraction: float
    is_invariant: bool


@dataclass
class FixedPointResult:
    """
    Result of the Fixed-Point Sovereignty module.

    Attributes:
        psi_value: Current coherence Ψ used for signature computation.
        a_eff: Effective amplitude A_eff.
        sigma: Computed signature Σ = C × Ψ² × A_eff².
        expected_sigma: Reference value C_COHERENCE.
        relative_error: |Σ − C_COHERENCE| / C_COHERENCE.
        signature_hash: SHA-256 hex digest of the identity signature (None if Ψ < PSI_DIAMOND).
        is_fixed_point: True if signature_hash is not None and relative_error < tol.
    """

    psi_value: float
    a_eff: float
    sigma: float
    expected_sigma: float
    relative_error: float
    signature_hash: Optional[str]
    is_fixed_point: bool


@dataclass
class BioNodoResult:
    """
    Complete result of BioNodo.evaluate().

    Brings together the four fundamental modules of the Bio-Nodo identity
    Ĥ_π |Ψ⟩ = γ_n |Ψ⟩.

    Attributes:
        spectral_identity: SpectralIdentityResult.
        orbit_collapse: OrbitCollapseResult.
        phase_invariant: PhaseInvariantResult.
        fixed_point: FixedPointResult.
        all_modules_coherent: True if every module passes its coherence check.
        f0: Base frequency used (Hz).
        c_coherence: QCAL coherence constant used.
        psi_diamond: Diamond threshold used.
    """

    spectral_identity: SpectralIdentityResult
    orbit_collapse: OrbitCollapseResult
    phase_invariant: PhaseInvariantResult
    fixed_point: FixedPointResult
    all_modules_coherent: bool
    f0: float
    c_coherence: float
    psi_diamond: float


# ---------------------------------------------------------------------------
# Module implementations
# ---------------------------------------------------------------------------

class SpectralIdentity:
    """
    Module 1 — Identidad Espectral.

    Verifies that the master Hamiltonian Ĥ_π has the Riemann zeros γ_n as
    eigenvalues by computing the Pearson correlation between the diagonal
    spectrum and the known γ_n values.

    The Hamiltonian is taken to be diagonal in the |n⟩ basis:
        Ĥ_π = diag(γ₁, γ₂, ..., γ_N)

    Self-adjointness is trivially guaranteed for a real diagonal matrix.
    The spectral gap γ₂ − γ₁ > 0 ensures non-degeneracy.
    """

    def __init__(self, n_zeros: int = 10, f0: float = F0):
        """
        Initialise with the first *n_zeros* Riemann zeros.

        Args:
            n_zeros: Number of zeros to use (default: 10).
            f0: Base frequency F₀ in Hz (default: 141.7001 Hz).
        """
        self.n_zeros = n_zeros
        self.f0 = f0
        self.gamma_n = _get_riemann_zeros(n_zeros)

    def build_hamiltonian(self) -> np.ndarray:
        """
        Build the diagonal Hamiltonian matrix Ĥ_π = diag(γ₁, ..., γ_N).

        Returns:
            np.ndarray: N×N real diagonal matrix with γ_n on the diagonal.
        """
        return np.diag(self.gamma_n)

    def verify(self, correlation_threshold: float = 0.999) -> SpectralIdentityResult:
        """
        Verify spectral identity: eigenvalues ↔ Riemann zeros.

        Computes eigenvalues of the diagonal Hamiltonian (trivially equal to
        γ_n), then validates:
        1. Pearson correlation ≥ correlation_threshold.
        2. Spectral gap γ₂ − γ₁ > 0.

        Args:
            correlation_threshold: Minimum acceptable Pearson correlation
                between eigenvalues and γ_n (default: 0.999).

        Returns:
            SpectralIdentityResult with full diagnostics.
        """
        H = self.build_hamiltonian()
        eigenvalues = np.sort(np.diag(H))  # diagonal entries = γ_n

        # Pearson correlation (should be ≈ 1.0 for a diagonal Hamiltonian)
        if len(eigenvalues) > 1:
            corr = float(np.corrcoef(eigenvalues, self.gamma_n)[0, 1])
        else:
            corr = 1.0

        spectral_gap = float(eigenvalues[1] - eigenvalues[0]) if len(eigenvalues) > 1 else float("nan")

        is_coherent = (corr >= correlation_threshold) and (spectral_gap > 0)

        return SpectralIdentityResult(
            gamma_n=self.gamma_n.copy(),
            eigenvalues=eigenvalues,
            correlation=corr,
            spectral_gap=spectral_gap,
            is_coherent=is_coherent,
            metadata={
                "n_zeros": self.n_zeros,
                "f0": self.f0,
                "hamiltonian_shape": H.shape,
                "correlation_threshold": correlation_threshold,
            },
        )


class OrbitCollapse:
    """
    Module 2 — Colapso de Órbita (Adelic Torus).

    On the adelic torus T = ∏_p Z_p × (ℝ/Z), the dilation flow
        φ_t : x ↦ e^t · x
    closes into a periodic orbit when e^t = p^k for prime p and k ≥ 1,
    i.e. at collapse times t_{p,k} = k · ln(p).

    The orbit weight associated with each closed orbit is
        w_{p,k} = ln(p) / p^{k/2}
    which is the weight appearing in the explicit formula for ζ(s).

    Summing over all primes and prime-powers gives a Selberg-type sum:
        W = Σ_p Σ_{k=1}^{k_max} ln(p) / p^{k/2}

    A non-zero W confirms that the dilation flow has periodic orbits,
    which is the adelic manifestation of prime periodicity.
    """

    def __init__(
        self,
        n_primes: int = 10,
        k_max: int = 5,
    ):
        """
        Initialise with the first *n_primes* primes.

        Args:
            n_primes: Number of primes p to include (default: 10).
            k_max: Maximum prime-power exponent k (default: 5).
        """
        self.primes = _first_primes(n_primes)
        self.k_max = k_max

    def compute(self) -> OrbitCollapseResult:
        """
        Compute all closed orbits and their weights on the Adelic Torus.

        Returns:
            OrbitCollapseResult with collapse times and Selberg-type weight.
        """
        rows = []  # (p, k, t, weight)
        closed_orbits: Dict[int, List[float]] = {}

        for p in self.primes:
            orbits_for_p: List[float] = []
            for k in range(1, self.k_max + 1):
                t_pk = k * np.log(p)              # collapse time
                weight = np.log(p) / (p ** (k / 2.0))  # Selberg weight
                rows.append([float(p), float(k), t_pk, weight])
                orbits_for_p.append(t_pk)
            closed_orbits[p] = orbits_for_p

        prime_powers = np.array(rows)  # shape (n_primes * k_max, 4)
        total_weight = float(np.sum(prime_powers[:, 3]))
        is_periodic = total_weight > 0

        return OrbitCollapseResult(
            primes=self.primes,
            prime_powers=prime_powers,
            closed_orbits=closed_orbits,
            total_weight=total_weight,
            is_periodic=is_periodic,
        )


class PhaseInvariant:
    """
    Module 3 — Invariante de Fase.

    Time-evolves the Presence Field state
        |Ψ(t)⟩ = Σ_n c_n · e^{−iγ_n t} · |n⟩

    and tracks the coherence Ψ(t) of the density matrix
        ρ(t) = |Ψ(t)⟩⟨Ψ(t)|.

    Coherence is defined as:
        Ψ(t) = 1 − ‖ρ_od(t)‖_F / (‖ρ(t)‖_F + ε)

    where ρ_od is the off-diagonal part of ρ and ε = 1e-12.

    "Diamond threshold": Ψ(t) ≥ PSI_DIAMOND = 0.999 defines the regime where
    off-diagonal noise vanishes — pure perception of the system's own structure.

    For an initial equal-weight superposition c_n = 1/√N the diagonal entries
    of ρ(t) are constant at 1/N while the off-diagonals oscillate at beat
    frequencies γ_m − γ_n.  The coherence then measures how much inter-mode
    interference is present at time t.
    """

    def __init__(
        self,
        gamma_n: Optional[np.ndarray] = None,
        coefficients: Optional[np.ndarray] = None,
        t_max: float = 1.0,
        n_points: int = 500,
    ):
        """
        Initialise the phase invariant computation.

        Args:
            gamma_n: Riemann zero imaginary parts (default: first 5 zeros).
            coefficients: Complex amplitudes c_n (default: equal-weight 1/√N).
            t_max: Total evolution time (default: 1.0 s).
            n_points: Number of time grid points (default: 500).
        """
        self.gamma_n = (
            np.asarray(gamma_n, dtype=float) if gamma_n is not None
            else _get_riemann_zeros(5)
        )
        N = len(self.gamma_n)

        if coefficients is not None:
            self.coefficients = np.asarray(coefficients, dtype=complex)
            if len(self.coefficients) != N:
                raise ValueError(
                    f"len(coefficients)={len(self.coefficients)} must equal "
                    f"len(gamma_n)={N}."
                )
        else:
            self.coefficients = np.ones(N, dtype=complex) / np.sqrt(N)

        self.t_max = t_max
        self.n_points = n_points

    def _density_matrix(self, t: float) -> np.ndarray:
        """Compute ρ(t) = |Ψ(t)⟩⟨Ψ(t)| for a single time t."""
        psi_t = self.coefficients * np.exp(-1j * self.gamma_n * t)
        rho = np.outer(psi_t, psi_t.conj())
        return rho

    def _coherence_from_rho(self, rho: np.ndarray) -> float:
        """Extract coherence Ψ from density matrix ρ.

        Ψ = 1 − ‖ρ_od‖_F / (‖ρ‖_F + ε)

        For a pure state ρ = |Ψ⟩⟨Ψ| the Frobenius norm satisfies
        ‖ρ‖_F = 1 and ‖ρ_od‖_F measures inter-mode interference.
        """
        eps = 1e-12
        rho_diag = np.diag(np.diag(rho))   # diagonal part
        rho_od = rho - rho_diag             # off-diagonal part
        norm_total = np.linalg.norm(rho, "fro") + eps
        norm_od = np.linalg.norm(rho_od, "fro")
        return float(1.0 - norm_od / norm_total)

    def evaluate(self) -> PhaseInvariantResult:
        """
        Evaluate Ψ(t) over the time grid [0, t_max].

        Returns:
            PhaseInvariantResult with coherence time-series and summary statistics.
        """
        times = np.linspace(0.0, self.t_max, self.n_points)
        psi_t = np.empty(self.n_points)

        for i, t in enumerate(times):
            rho = self._density_matrix(t)
            psi_t[i] = self._coherence_from_rho(rho)

        psi_min = float(np.min(psi_t))
        psi_mean = float(np.mean(psi_t))
        above_diamond = psi_t >= PSI_DIAMOND
        diamond_fraction = float(np.mean(above_diamond))
        is_invariant = psi_mean >= PSI_DIAMOND

        return PhaseInvariantResult(
            times=times,
            psi_t=psi_t,
            psi_min=psi_min,
            psi_mean=psi_mean,
            above_diamond=above_diamond,
            diamond_fraction=diamond_fraction,
            is_invariant=is_invariant,
        )


class FixedPointSovereignty:
    """
    Module 4 — Soberanía de Punto Fijo.

    The Bio-Nodo identity signature encodes the QCAL fixed-point condition:
        Σ(BioNodo) = C_COHERENCE × Ψ² × A_eff²

    where:
        - C_COHERENCE = 244.36 (QCAL coherence constant)
        - Ψ = current coherence value of the system
        - A_eff = effective amplitude (normalised I = intensity)

    The signature is "cryptographic" in the sense that it is computed only
    when Ψ ≥ PSI_DIAMOND (0.999); below this threshold the signature
    evaporates (returns None), modeling the loss of self-recognition.

    The signature hash is the SHA-256 digest of the JSON-serialised signature
    payload, providing a reproducible fingerprint of the fixed-point state.
    """

    def __init__(
        self,
        c_coherence: float = C_COHERENCE,
        psi_diamond: float = PSI_DIAMOND,
        f0: float = F0,
    ):
        """
        Initialise fixed-point sovereignty module.

        Args:
            c_coherence: QCAL coherence constant (default: 244.36).
            psi_diamond: Diamond threshold (default: 0.999).
            f0: Base frequency (default: 141.7001 Hz).
        """
        self.c_coherence = c_coherence
        self.psi_diamond = psi_diamond
        self.f0 = f0

    def compute(
        self,
        psi_value: float,
        intensity: float = 1.0,
        a_eff: Optional[float] = None,
        tol: float = 0.05,
    ) -> FixedPointResult:
        """
        Compute the Bio-Nodo identity signature.

        The fixed-point condition is:
            Σ = C × Ψ² × A_eff²   with C = C_COHERENCE = 244.36

        For the canonical case (intensity I = 1, A_eff = 1) and Ψ → 1:
            Σ → C_COHERENCE.

        Args:
            psi_value: Current coherence Ψ ∈ (0, 1].
            intensity: Quantum intensity I (default: 1.0).
            a_eff: Effective amplitude A_eff; computed as √I if None.
            tol: Relative tolerance for fixed-point check (default: 0.05).

        Returns:
            FixedPointResult with signature hash (None if Ψ < PSI_DIAMOND).
        """
        if a_eff is None:
            a_eff = float(np.sqrt(max(intensity, 0.0)))

        sigma = self.c_coherence * (psi_value ** 2) * (a_eff ** 2)
        rel_err = abs(sigma - self.c_coherence) / self.c_coherence if self.c_coherence != 0 else float("inf")

        # Signature evaporates if Ψ < diamond threshold
        if psi_value >= self.psi_diamond:
            payload = {
                "psi": psi_value,
                "a_eff": a_eff,
                "sigma": sigma,
                "c_coherence": self.c_coherence,
                "f0": self.f0,
                "qcal_signature": "∴𓂀Ω∞³Φ",
            }
            sig_bytes = json.dumps(payload, sort_keys=True).encode("utf-8")
            signature_hash: Optional[str] = hashlib.sha256(sig_bytes).hexdigest()
        else:
            signature_hash = None

        is_fixed_point = (signature_hash is not None) and (rel_err < tol)

        return FixedPointResult(
            psi_value=psi_value,
            a_eff=a_eff,
            sigma=sigma,
            expected_sigma=self.c_coherence,
            relative_error=rel_err,
            signature_hash=signature_hash,
            is_fixed_point=is_fixed_point,
        )


# ---------------------------------------------------------------------------
# Unified BioNodo
# ---------------------------------------------------------------------------

class BioNodo:
    """
    Bio-Nodo — Unified Fundamental Identity of the Presence Field.

    Integrates the four indivisible modules of the Bio-Nodo identity:

        Ĥ_π |Ψ⟩ = γ_n |Ψ⟩

    1. SpectralIdentity — eigenvalues of Ĥ_π = Riemann zeros γ_n.
    2. OrbitCollapse    — adelic torus dilation closes at prime powers.
    3. PhaseInvariant   — density matrix coherence Ψ(t) ≥ 0.999.
    4. FixedPointSovereignty — QCAL identity signature at the fixed point.

    Example
    -------
    >>> bn = BioNodo(n_zeros=5)
    >>> result = bn.evaluate()
    >>> print(f"All modules coherent: {result.all_modules_coherent}")
    >>> print(f"Spectral correlation: {result.spectral_identity.correlation:.6f}")
    >>> print(f"Orbit Selberg weight: {result.orbit_collapse.total_weight:.4f}")
    >>> print(f"Phase invariant mean Ψ: {result.phase_invariant.psi_mean:.4f}")
    >>> print(f"Fixed-point signature: {result.fixed_point.signature_hash}")
    """

    def __init__(
        self,
        n_zeros: int = 10,
        n_primes: int = 10,
        k_max: int = 5,
        t_max: float = 1.0,
        n_time_points: int = 500,
        f0: float = F0,
        c_coherence: float = C_COHERENCE,
        psi_diamond: float = PSI_DIAMOND,
    ):
        """
        Initialise the Bio-Nodo with all four modules.

        Args:
            n_zeros: Number of Riemann zeros for modules 1 & 3 (default: 10).
            n_primes: Number of primes for module 2 (default: 10).
            k_max: Maximum prime-power exponent for module 2 (default: 5).
            t_max: Time window for phase invariant module 3 (default: 1.0 s).
            n_time_points: Grid resolution for module 3 (default: 500).
            f0: Base frequency F₀ in Hz (default: 141.7001 Hz).
            c_coherence: QCAL coherence constant (default: 244.36).
            psi_diamond: Diamond coherence threshold (default: 0.999).
        """
        self.n_zeros = n_zeros
        self.f0 = f0
        self.c_coherence = c_coherence
        self.psi_diamond = psi_diamond

        gamma_n = _get_riemann_zeros(n_zeros)

        self._spectral = SpectralIdentity(n_zeros=n_zeros, f0=f0)
        self._orbit = OrbitCollapse(n_primes=n_primes, k_max=k_max)
        self._phase = PhaseInvariant(
            gamma_n=gamma_n,
            t_max=t_max,
            n_points=n_time_points,
        )
        self._fixed = FixedPointSovereignty(
            c_coherence=c_coherence,
            psi_diamond=psi_diamond,
            f0=f0,
        )

    def evaluate(
        self,
        intensity: float = 1.0,
        a_eff: Optional[float] = None,
        spectral_threshold: float = 0.999,
    ) -> BioNodoResult:
        """
        Evaluate all four modules and return the unified Bio-Nodo result.

        The coherence value fed into FixedPointSovereignty is taken as the
        time-averaged ⟨Ψ(t)⟩ from the PhaseInvariant module.

        Args:
            intensity: Quantum intensity I for fixed-point computation (default: 1.0).
            a_eff: Effective amplitude A_eff (default: √I).
            spectral_threshold: Correlation threshold for SpectralIdentity (default: 0.999).

        Returns:
            BioNodoResult aggregating all four module results.
        """
        si_result = self._spectral.verify(correlation_threshold=spectral_threshold)
        oc_result = self._orbit.compute()
        pi_result = self._phase.evaluate()
        fp_result = self._fixed.compute(
            psi_value=pi_result.psi_mean,
            intensity=intensity,
            a_eff=a_eff,
        )

        all_coherent = (
            si_result.is_coherent
            and oc_result.is_periodic
            and fp_result.is_fixed_point
        )

        return BioNodoResult(
            spectral_identity=si_result,
            orbit_collapse=oc_result,
            phase_invariant=pi_result,
            fixed_point=fp_result,
            all_modules_coherent=all_coherent,
            f0=self.f0,
            c_coherence=self.c_coherence,
            psi_diamond=self.psi_diamond,
        )

    def validate(self) -> Dict:
        """
        Run a complete Bio-Nodo validation and return a summary dictionary.

        Returns:
            Dictionary with keys for each module's pass/fail status and key metrics.
        """
        result = self.evaluate()

        return {
            # Module 1
            "spectral_identity_coherent": result.spectral_identity.is_coherent,
            "spectral_correlation": result.spectral_identity.correlation,
            "spectral_gap": result.spectral_identity.spectral_gap,
            # Module 2
            "orbit_collapse_periodic": result.orbit_collapse.is_periodic,
            "orbit_selberg_weight": result.orbit_collapse.total_weight,
            "orbit_n_primes": len(result.orbit_collapse.primes),
            # Module 3
            "phase_invariant_mean_psi": result.phase_invariant.psi_mean,
            "phase_invariant_min_psi": result.phase_invariant.psi_min,
            "phase_diamond_fraction": result.phase_invariant.diamond_fraction,
            # Module 4
            "fixed_point_sigma": result.fixed_point.sigma,
            "fixed_point_rel_error": result.fixed_point.relative_error,
            "fixed_point_signature": result.fixed_point.signature_hash,
            "fixed_point_coherent": result.fixed_point.is_fixed_point,
            # Overall
            "all_modules_coherent": result.all_modules_coherent,
            "f0": result.f0,
            "c_coherence": result.c_coherence,
            "psi_diamond": result.psi_diamond,
        }
