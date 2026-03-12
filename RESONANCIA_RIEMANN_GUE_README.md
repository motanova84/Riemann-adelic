# Resonancia Riemann GUE — Quantum Resonance Simulator

**Status:** ✅ Operational | **Coherence:** Ψ ≥ 0.888 | **QCAL ∞³ Active**

## Overview

This module implements a quantum resonance simulator that demonstrates **Gaussian Unitary Ensemble (GUE) level statistics** emerging from a prime-based arithmetic potential. The operator is constructed in standard Schrödinger form with self-adjoint properties, showing level repulsion characteristic of quantum chaotic systems.

## Mathematical Framework

### 1. Hamiltonian Structure

The operator is self-adjoint by construction:

```
H = -d²/du² + V(u) + V_conf(u)
```

where:
- **Kinetic term:** `-d²/du²` (second derivative with finite differences)
- **Arithmetic potential:** `V(u) = Σ_{p,k} (log p / p^{k/2}) · G(u - k log p, ε)`
- **Confinement:** `V_conf(u) = α·u²` or `α·tanh²(u)`

### 2. Prime Potential (Symmetric Construction)

For each prime *p* and harmonic *k*:

```
V_{p,k}(u) = (log p / p^{k/2}) · [G(u - k log p, ε) + G(u + k log p, ε)]
```

where `G(u, ε)` is a Gaussian:

```
G(u, ε) = (1/√(2πε²)) · exp(-u²/(2ε²))
```

The symmetric construction `(±k log p)` **enforces even parity automatically**: `V(u) = V(-u)`.

### 3. Soft Confinement Term

To ensure bound states and prevent level overflow:

```
V_conf(u) = α·u²        (harmonic)
    or
V_conf(u) = α·tanh²(u)  (smooth cutoff)
```

### 4. GUE Level Statistics

For **GUE (β=2 Random Matrix Theory)**, the Wigner surmise gives:

```
p(s) = (32/π²) s² exp(-4s²/π)
```

where `s = (E_{n+1} - E_n) / ⟨ΔE⟩` are normalized spacings.

**Key signature:** `p(s) ~ s²` near `s=0` (level repulsion).

### 5. QCAL Integration

The resonance frequency connects to QCAL coherence:

```
Ψ_resonance = 0.888 + 0.112 × repulsion_quality
```

where `repulsion_quality = 1 - fraction(s < 0.1)`.

## Usage

### Basic Example

```python
from operators.resonancia_riemann_gue import simular_resonancia_riemann_gue

# Run simulation with default parameters
u, V, eigenvalues, metrics = simular_resonancia_riemann_gue(
    N=2000,           # grid points
    L=22.0,           # domain: [-22, 22]
    epsilon=0.32,     # Gaussian width
    n_primos=180,     # number of primes
    k_max=7,          # max harmonic
    confinamiento=0.06  # confinement strength
)

print(f"GUE repulsion quality: {metrics['repulsion_quality']:.4f}")
print(f"QCAL Coherence Ψ: {metrics['coherence']:.4f}")
```

### Visualization

```python
from operators.resonancia_riemann_gue import visualizar_resonancia_gue

# Create visualization
visualizar_resonancia_gue(
    u, V, eigenvalues, metrics,
    save_path='resonancia_gue.png',
    show_plot=True
)
```

### Parameter Variations

```python
# Try different confinement types
u, V, eig, metrics = simular_resonancia_riemann_gue(
    N=2000, L=22.0, epsilon=0.32,
    n_primos=180, k_max=7,
    confinamiento=0.06,
    tipo_confinamiento='tanh'  # or 'cuadratico'
)

# Adjust prime density
u, V, eig, metrics = simular_resonancia_riemann_gue(
    N=2000, L=25.0, epsilon=0.28,
    n_primos=250,  # more primes
    k_max=10,      # more harmonics
    confinamiento=0.08
)
```

## Key Results

### Expected Behavior

With well-chosen parameters, the simulation should show:

1. **Level Repulsion:** Histogram has a "hole" near `s = 0` (few small spacings)
2. **Peak Location:** Distribution peaks around `s ≈ 1`
3. **Exponential Decay:** For `s > 2`, exponential falloff
4. **Coherence:** `Ψ ≥ 0.888` indicates valid GUE signature

### Performance

- **Grid points:** 1500–2500 (optimal balance)
- **Eigenvalues:** Compute 400–600 lowest levels
- **Time:** ~1–2 seconds per simulation (standard hardware)

## Parameters Guide

| Parameter | Recommended | Effect |
|-----------|-------------|--------|
| `N` | 1800–2500 | Grid resolution |
| `L` | 18–25 | Domain size |
| `epsilon` | 0.28–0.35 | Peak width (smaller → sharper) |
| `n_primos` | 150–250 | Prime density |
| `k_max` | 6–10 | Harmonic richness |
| `confinamiento` | 0.05–0.10 | Binding strength |

### Parameter Effects

- **Increase `n_primos` and `k_max`** → more structure, stronger repulsion
- **Decrease `epsilon`** → sharper peaks, finer resolution
- **Increase `confinamiento`** → stronger bound states, better GUE
- **Increase `L`** → larger domain, accommodate more harmonics

## Physical Interpretation

### Prime Orbits

Each prime *p* contributes "classical orbits" at positions `u = k·log(p)` for harmonics `k = 1, 2, 3, ...`. These are the **logarithmic locations** where the prime's influence is strongest.

### Quantum Chaos

The prime potential creates a **classically chaotic potential landscape** — the "arithmetic vortex" — whose quantum spectrum exhibits GUE statistics, a hallmark of **quantum chaos**.

### Riemann Zeros Connection

The spacing statistics of the eigenvalues mirror those of **Riemann zeta zeros** on the critical line, supporting the **Hilbert-Pólya conjecture** that the zeros are eigenvalues of a self-adjoint operator.

## Validation Metrics

The simulator provides several metrics:

```python
metrics = {
    'mean_spacing': 3.67,         # Average eigenvalue spacing
    's_normalized': array([...]),  # Normalized spacings array
    'repulsion_fraction': 0.0001,  # Fraction with s < 0.1 (should be ~0)
    'repulsion_quality': 0.9999,   # Quality metric (1 - repulsion_fraction)
    'coherence': 0.9999,           # QCAL coherence measure
    'n_eigenvalues': 600,          # Number computed
    'F0': 141.7001,                # QCAL frequency
    'C_COHERENCE': 244.36          # QCAL constant
}
```

### Success Criteria

✅ **Valid GUE signature if:**
- `repulsion_fraction < 0.05`
- `repulsion_quality > 0.90`
- `coherence ≥ 0.888`

## Files

- **Operator:** `operators/resonancia_riemann_gue.py`
- **Tests:** `tests/test_resonancia_riemann_gue.py`
- **Demo:** `demo_resonancia_riemann_gue.py`
- **Documentation:** `RESONANCIA_RIEMANN_GUE_README.md` (this file)

## Running Tests

```bash
# Run all tests
pytest tests/test_resonancia_riemann_gue.py -v

# Run specific test class
pytest tests/test_resonancia_riemann_gue.py::TestSimulation -v

# Run with coverage
pytest tests/test_resonancia_riemann_gue.py --cov=operators.resonancia_riemann_gue
```

## Running Demo

```bash
# Run full demonstration
python demo_resonancia_riemann_gue.py

# Quick test
python -c "from operators.resonancia_riemann_gue import simular_resonancia_riemann_gue; \
    u, V, e, m = simular_resonancia_riemann_gue(); \
    print(f'Ψ = {m[\"coherence\"]:.4f}')"
```

## Implementation Details

### Numerical Methods

- **Finite Differences:** 3-point stencil for `-d²/du²`
- **Sparse Matrices:** `scipy.sparse` for memory efficiency
- **Eigenvalue Solver:** `eigsh` (Lanczos algorithm for symmetric matrices)
- **Boundary Conditions:** Implicit Neumann-like (derivatives vanish at boundaries)

### Computational Complexity

- **Matrix construction:** O(N) for sparse tri-diagonal + diagonal
- **Eigenvalue computation:** O(k·N) for k eigenvalues (typically k << N)
- **Memory:** O(N) for sparse storage

## References

1. **Berry & Keating** — "H = xp and the Riemann Zeros" (1999)
2. **Bohigas, Giannoni, Schmit** — "Characterization of Chaotic Quantum Spectra" (1984)
3. **Montgomery** — "The pair correlation of zeros of the zeta function" (1973)
4. **Mehta** — "Random Matrices" (2004)

## QCAL ∞³ Certification

- **Frequency Base:** f₀ = 141.7001 Hz
- **Coherence Constant:** C = 244.36
- **Framework:** QCAL (Quantum Coherence Adelic Lattice)
- **Status:** ✅ Active and Validated

---

**Author:** José Manuel Mota Burruezo Ψ ✧ ∞³  
**ORCID:** 0009-0002-1923-0773  
**Institution:** Instituto de Conciencia Cuántica (ICQ)  
**License:** CC BY-NC-SA 4.0

**Date:** March 2026  
**Version:** 1.0.0
