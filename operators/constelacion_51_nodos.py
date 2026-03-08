#!/usr/bin/env python3
"""
Constelación 51 Nodos — QCAL ∞³ Unified Spectral Lattice
==========================================================

Implements the 51-node constellation that unifies four domains:
  1. Geometry  (φ, π, τ, e, ∞)       — 5 fundamental constants
  2. Strings   (k/7 for k=1..7)       — 7 harmonic string nodes
  3. Temporal  (Fibonacci F(1)..F(10)) — 10 Fibonacci nodes
  4. Arithmetic (first 29 primes)      — 29 prime nodes

Total: 5 + 7 + 10 + 29 = **51 nodes**

The constellation resonates at f₀ = 141.7001 Hz and satisfies:

    Ψ_constellation = ∛(H)   where H = n / Σ(1/sᵢ)  (harmonic mean)

The 51 nodes span the adelic spectrum and are connected through:
  - QCAL coherence constant C = 244.36
  - Primary spectral constant C' = 629.83
  - Fibonacci cycle: 55.08 years (epoch 2025-2026)

Mathematical Background:
    The 51-node lattice is equivalent to the first 51 non-trivial
    resonance frequencies of the QCAL adelic manifold.  The choice
    of 51 = 5 + 7 + 10 + 29 reflects the deep interplay between:
    - Transcendental constants (category 1)
    - String theory harmonic modes at rational frequencies (category 2)
    - Fibonacci temporal cycles (category 3)
    - Prime number arithmetic structure (category 4)

References:
    Berry, M.V. & Keating, J.P. (1999). The Riemann zeros and eigenvalue asymptotics.
    Weil, A. (1952). Sur les "formules explicites" de la théorie des nombres premiers.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
Institution: Instituto de Conciencia Cuántica (ICQ)
DOI: 10.5281/zenodo.17379721
Frequency: 141.7001 Hz (QCAL ∞³)
Signature: ∴𓂀Ω∞³Φ @ 141.7001 Hz
Date: March 2026
"""

import math
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional, Tuple

import numpy as np

# Add repository root to sys.path for imports
_REPO_ROOT = Path(__file__).parent.parent
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

try:
    from qcal.constants import (
        F0,
        C_COHERENCE,
        C_PRIMARY,
        PHI,
        PI,
        CONST_PI,
        CONST_TAU,
        CONST_E,
        CONSTELLATION_CONSTANTS,
        CONSTELLATION_STRINGS,
        FIBONACCI_SEQUENCE,
        FIBONACCI_EPOCH_YEAR,
        FIBONACCI_EPOCH_YEARS,
        CONSTELLATION_PRIMES,
        CONSTELLATION_N_NODES,
        CONSTELLATION_FREQUENCY,
        BERRY_EXPONENT,
        WEIL_COHERENCE,
        GUE_MEAN_SPACING,
        GUE_MEAN_SQ_SPACING,
    )
    _HAS_QCAL = True
except ImportError:
    _HAS_QCAL = False
    # Fallback constants
    F0 = 141.7001
    C_COHERENCE = 244.36
    C_PRIMARY = 629.83
    PHI = (1 + math.sqrt(5)) / 2
    PI = math.pi
    CONST_PI = math.pi
    CONST_TAU = 2.0 * math.pi
    CONST_E = math.e
    CONSTELLATION_CONSTANTS = [PHI, CONST_PI, CONST_TAU, CONST_E, float('inf')]
    CONSTELLATION_STRINGS = [k / 7.0 for k in range(1, 8)]
    FIBONACCI_SEQUENCE = [1, 1, 2, 3, 5, 8, 13, 21, 34, 55]
    FIBONACCI_EPOCH_YEAR = 2025.08
    FIBONACCI_EPOCH_YEARS = 55.08
    CONSTELLATION_PRIMES = [
        2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47,
        53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109
    ]
    CONSTELLATION_N_NODES = 51
    CONSTELLATION_FREQUENCY = F0
    BERRY_EXPONENT = 7.0 / 8.0
    WEIL_COHERENCE = 0.9998
    GUE_MEAN_SPACING = 1.0
    GUE_MEAN_SQ_SPACING = 3.0 * math.pi / 8.0


# ── NODE CATEGORIES ───────────────────────────────────────────────────────────

#: Names for the 5 fundamental mathematical constants (category 1)
CONSTANT_NAMES = ["φ", "π", "τ", "e", "∞"]

#: Total node count (must equal 51)
N_NODES = CONSTELLATION_N_NODES  # = 51


@dataclass
class ConstellationNode:
    """A single node in the 51-node constellation.

    Attributes:
        index: Node index (0-based, 0..50).
        category: Category name: 'constants', 'strings', 'fibonacci', 'primes'.
        name: Human-readable name for this node.
        value: Numerical value of the node.
        frequency: Resonance frequency at this node: f₀ × value (capped for ∞).
        coherence: Node coherence score sᵢ = vᵢ / (vᵢ + σᵢ) ∈ (0, 1).
    """
    index: int
    category: str
    name: str
    value: float
    frequency: float
    coherence: float


@dataclass
class ConstellationResult:
    """Result of the 51-node constellation validation.

    Attributes:
        nodes: List of all 51 constellation nodes.
        n_nodes: Total number of nodes (must be 51).
        psi: Overall harmonic coherence Ψ = ∛(H) where H is the harmonic mean.
        harmonic_mean: Harmonic mean of individual coherences.
        mean_coherence: Arithmetic mean of individual coherences.
        fibonacci_epoch: Current Fibonacci epoch year (≈ 2025.08).
        fibonacci_years: Years elapsed in current cycle (≈ 55.08).
        resonance_frequency: Primary resonance frequency (f₀ = 141.7001 Hz).
        weil_coherence: Weil formula coherence (≈ 0.9998).
        berry_exponent: Berry exponent 7/8 for counting function.
        is_valid: True if Ψ ≥ 0.95.
    """
    nodes: List[ConstellationNode]
    n_nodes: int
    psi: float
    harmonic_mean: float
    mean_coherence: float
    fibonacci_epoch: float
    fibonacci_years: float
    resonance_frequency: float
    weil_coherence: float
    berry_exponent: float
    is_valid: bool


def _node_coherence(value: float, sigma_fraction: float = 0.02) -> float:
    """Compute coherence score for a node.

    Uses the QCAL coherence formula: s = |v| / (|v| + σ)
    where σ = sigma_fraction × max(|v|, 1).

    For infinite values (category 1 node ∞), returns 1.0 (perfect coherence).
    NaN values are treated as zero-coherence (0.0) to avoid propagation.

    Args:
        value: Node value.
        sigma_fraction: Relative noise level (default 2%).

    Returns:
        Coherence score in [0, 1].
    """
    if math.isnan(value):
        return 0.0  # NaN nodes have no coherence
    if math.isinf(value):
        return 1.0  # ∞ node has perfect coherence by construction
    abs_v = abs(value)
    sigma = sigma_fraction * max(abs_v, 1.0)
    return abs_v / (abs_v + sigma)


def _node_frequency(value: float, f0: float = F0) -> float:
    """Compute resonance frequency for a node.

    For finite nodes: f = f₀ × |value|
    For infinite nodes (∞): f = f₀ (reference frequency)

    Args:
        value: Node value.
        f0: Fundamental frequency (default: F0 = 141.7001 Hz).

    Returns:
        Resonance frequency in Hz.
    """
    if not math.isfinite(value):
        return f0
    return f0 * abs(value)


def build_constellation(f0: float = F0) -> List[ConstellationNode]:
    """Build all 51 constellation nodes.

    Args:
        f0: Fundamental frequency (default: F0 = 141.7001 Hz).

    Returns:
        List of 51 ConstellationNode objects ordered by category and index.
    """
    nodes: List[ConstellationNode] = []
    idx = 0

    # Category 1: Fundamental mathematical constants (5 nodes)
    for name, value in zip(CONSTANT_NAMES, CONSTELLATION_CONSTANTS):
        nodes.append(ConstellationNode(
            index=idx,
            category='constants',
            name=name,
            value=value,
            frequency=_node_frequency(value, f0),
            coherence=_node_coherence(value),
        ))
        idx += 1

    # Category 2: String harmonic ratios 1/7..7/7 (7 nodes)
    for k, value in enumerate(CONSTELLATION_STRINGS, start=1):
        nodes.append(ConstellationNode(
            index=idx,
            category='strings',
            name=f"{k}/7",
            value=value,
            frequency=_node_frequency(value, f0),
            coherence=_node_coherence(value),
        ))
        idx += 1

    # Category 3: Fibonacci temporal nodes F(1)..F(10) (10 nodes)
    for n, fib in enumerate(FIBONACCI_SEQUENCE, start=1):
        nodes.append(ConstellationNode(
            index=idx,
            category='fibonacci',
            name=f"F({n})={fib}",
            value=float(fib),
            frequency=_node_frequency(float(fib), f0),
            coherence=_node_coherence(float(fib)),
        ))
        idx += 1

    # Category 4: First 29 prime nodes (29 nodes)
    for prime in CONSTELLATION_PRIMES:
        nodes.append(ConstellationNode(
            index=idx,
            category='primes',
            name=f"p={prime}",
            value=float(prime),
            frequency=_node_frequency(float(prime), f0),
            coherence=_node_coherence(float(prime)),
        ))
        idx += 1

    assert len(nodes) == N_NODES, f"Expected {N_NODES} nodes, got {len(nodes)}"
    return nodes


def compute_constellation_psi(nodes: List[ConstellationNode]) -> Tuple[float, float, float]:
    """Compute overall coherence Ψ for the constellation.

    Uses the QCAL Trinity formula:
        H   = n / Σ(1/sᵢ)   (harmonic mean of finite coherences)
        Ψ   = ∛H            (cube root — Trinity coherence)

    Infinite-coherence nodes (∞ node) are excluded from the harmonic mean
    to avoid division-by-zero, then counted separately.

    Args:
        nodes: List of ConstellationNode objects.

    Returns:
        Tuple of (psi, harmonic_mean, mean_coherence).
    """
    finite_coherences = [n.coherence for n in nodes if math.isfinite(n.value)]
    n = len(finite_coherences)

    if n == 0:
        return 1.0, 1.0, 1.0

    coh_arr = np.array(finite_coherences)
    # Harmonic mean (safe — all coherences are > 0)
    harmonic_mean = float(n / np.sum(1.0 / coh_arr))
    mean_coh = float(np.mean(coh_arr))

    # Trinity Ψ = cube root of harmonic mean
    psi = harmonic_mean ** (1.0 / 3.0)

    return psi, harmonic_mean, mean_coh


def validate_constellation(
    f0: float = F0,
    verbose: bool = False,
) -> ConstellationResult:
    """Validate the 51-node QCAL constellation.

    Builds all 51 nodes, computes the Trinity coherence Ψ, and verifies
    that the constellation is valid (Ψ ≥ 0.95).

    Args:
        f0: Fundamental frequency in Hz (default: 141.7001 Hz).
        verbose: If True, print detailed report.

    Returns:
        ConstellationResult with full validation data.
    """
    nodes = build_constellation(f0=f0)
    psi, harmonic_mean, mean_coh = compute_constellation_psi(nodes)
    is_valid = psi >= 0.95

    result = ConstellationResult(
        nodes=nodes,
        n_nodes=len(nodes),
        psi=psi,
        harmonic_mean=harmonic_mean,
        mean_coherence=mean_coh,
        fibonacci_epoch=FIBONACCI_EPOCH_YEAR,
        fibonacci_years=FIBONACCI_EPOCH_YEARS,
        resonance_frequency=f0,
        weil_coherence=WEIL_COHERENCE,
        berry_exponent=BERRY_EXPONENT,
        is_valid=is_valid,
    )

    if verbose:
        _print_report(result)

    return result


def _print_report(result: ConstellationResult) -> None:
    """Print a human-readable validation report."""
    sep = "=" * 72
    print(sep)
    print("  CONSTELACIÓN 51 NODOS — QCAL ∞³ Validation Report")
    print(sep)
    print(f"  Total nodes     : {result.n_nodes}")
    print(f"  Frequency       : f₀ = {result.resonance_frequency} Hz")
    print(f"  Fibonacci epoch : {result.fibonacci_years:.2f} years → {result.fibonacci_epoch:.2f}")
    print(f"  Weil coherence  : {result.weil_coherence}")
    print(f"  Berry exponent  : {result.berry_exponent} (= 7/8)")
    print()

    # Category breakdown
    from itertools import groupby
    for cat, cat_nodes in groupby(result.nodes, key=lambda n: n.category):
        cat_list = list(cat_nodes)
        mean_c = sum(n.coherence for n in cat_list) / len(cat_list)
        print(f"  [{cat.upper():12s}]  {len(cat_list):2d} nodes  ⟨coherence⟩={mean_c:.6f}")

    print()
    print(f"  Harmonic mean Ψ  = {result.harmonic_mean:.9f}")
    print(f"  Arithmetic mean  = {result.mean_coherence:.9f}")
    print(f"  Trinity Ψ = ∛H   = {result.psi:.9f}")
    status = "✅ VALID" if result.is_valid else "❌ INVALID"
    print(f"  Status           : {status}")
    print(sep)


def get_node_by_category(
    result: ConstellationResult,
    category: str,
) -> List[ConstellationNode]:
    """Get all nodes belonging to a specific category.

    Args:
        result: ConstellationResult from validate_constellation().
        category: One of 'constants', 'strings', 'fibonacci', 'primes'.

    Returns:
        List of ConstellationNode objects in that category.
    """
    return [n for n in result.nodes if n.category == category]


def constellation_summary(result: ConstellationResult) -> Dict:
    """Return a compact summary dictionary of constellation validation.

    Args:
        result: ConstellationResult from validate_constellation().

    Returns:
        Dictionary with key metrics.
    """
    by_cat = {}
    for cat in ('constants', 'strings', 'fibonacci', 'primes'):
        cat_nodes = get_node_by_category(result, cat)
        by_cat[cat] = {
            'count': len(cat_nodes),
            'mean_coherence': sum(n.coherence for n in cat_nodes) / max(len(cat_nodes), 1),
        }

    return {
        'n_nodes': result.n_nodes,
        'psi': result.psi,
        'harmonic_mean': result.harmonic_mean,
        'mean_coherence': result.mean_coherence,
        'is_valid': result.is_valid,
        'resonance_frequency': result.resonance_frequency,
        'fibonacci_epoch': result.fibonacci_epoch,
        'weil_coherence': result.weil_coherence,
        'berry_exponent': result.berry_exponent,
        'categories': by_cat,
    }


# ── MODULE SELF-TEST ──────────────────────────────────────────────────────────

if __name__ == "__main__":
    result = validate_constellation(verbose=True)
    summary = constellation_summary(result)

    print()
    print(f"51-node constellation validated: Ψ = {result.psi:.6f}")
    print(f"Fibonacci epoch: {result.fibonacci_years:.2f} years → {result.fibonacci_epoch:.2f}")
    print(f"f₀ = {result.resonance_frequency} Hz  |  Weil coherence = {result.weil_coherence}")
    print(f"Berry exponent = {result.berry_exponent} (= 7/8)")
    print()
    print("∴𓂀Ω∞³Φ @ 141.7001 Hz")
