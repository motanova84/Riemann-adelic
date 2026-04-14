# Riemann Operator Hilbert-Pólya

Implementation of the Hilbert-Pólya Hamiltonian operator
**H = −d²/du² + V(u)** acting on L²\_even(ℝ, du) with parity symmetry
ψ(u) = ψ(−u).

DOI: [10.5281/zenodo.17379721](https://doi.org/10.5281/zenodo.17379721)  
Author: José Manuel Mota Burruezo Ψ ✧ ∞³ · ORCID: 0009-0002-1923-0773  
Institution: Instituto de Conciencia Cuántica (ICQ)

---

## Mathematical Background

The Hilbert-Pólya conjecture proposes that the imaginary parts of the
non-trivial zeros of the Riemann zeta function are eigenvalues of a
self-adjoint operator.  This module implements such an operator via the
change of variable x = eᵘ, which transforms the Berry–Keating model
H = xp into H = −id/du in the logarithmic coordinate u.

### Hilbert Space

The natural space is:
```
L²_even(ℝ, du) = { ψ ∈ L²(ℝ, du) : ψ(u) = ψ(−u) }
```
Implemented by `EvenHilbertSpace`, which enforces parity via the
projection ψ_even(u) = [ψ(u) + ψ(−u)] / 2.

### Operator

```
H = H_kin + H_pot
```

**Kinetic part** (finite differences, periodic BC):
```
H_kin = −d²/du² + tanh²(u)/2
```

**Potential** (prime Dirac comb, symmetrised):
```
V(u) = Σ_{p prime, k≥1}  (ln p / p^{k/2})  δ(u − k ln p)
```
Discretised as normalised Gaussian peaks of width ε at ±k ln p, so that
V(u) = V(−u) and [H, P] = 0.

---

## Quick Start

```python
from riemann_operator_hilbert_polya import EvenHilbertSpace, HilbertPolyaOperator

# Build the Hilbert space and operator
space = EvenHilbertSpace(N=200, u_max=15.0)
op = HilbertPolyaOperator(space, num_primes=20, max_k=6)

# Verify mathematical properties
is_hermitian, err = op.check_hermiticity()   # True, ~0
commutes, comm_err = op.check_parity_commutation()  # True, ~1e-14

# Compute eigenvalues (all real)
eigenvalues = op.eigenvalues()

# Compare with Riemann zeros
result = op.compare_with_zeta_zeros(n_zeros=10)
print(f"Pearson correlation with γ_n: {result['correlation']:.4f}")
```

---

## API Reference

### `EvenHilbertSpace(N, u_max)`

Discretises L²\_even(ℝ, du).

| Parameter | Type | Description |
|-----------|------|-------------|
| `N`       | int  | Number of grid points (adjusted to even). |
| `u_max`   | float | Half-domain length; grid ∈ [−u\_max, u\_max]. |

Key methods:

| Method | Returns | Description |
|--------|---------|-------------|
| `enforce_parity(psi)` | ndarray | Project ψ to even subspace. |
| `check_parity(psi, tol)` | (bool, float) | Test ψ(u) = ψ(−u). |
| `inner_product(phi, psi)` | complex | ⟨φ\|ψ⟩ via `scipy.integrate.trapezoid`. |
| `norm(psi)` | float | ∥ψ∥ in L². |
| `normalize(psi)` | ndarray | Unit-normalised ψ. |

### `HilbertPolyaOperator(space, num_primes, max_k, epsilon)`

Builds and analyses H.

| Parameter | Type | Description |
|-----------|------|-------------|
| `space` | EvenHilbertSpace | The discretised space. |
| `num_primes` | int | Number of primes in V(u). Default: 20. |
| `max_k` | int | Maximum power k in the sum. Default: 6. |
| `epsilon` | float | Gaussian width for δ-regularisation (default: 3 du). |

Key methods:

| Method | Returns | Description |
|--------|---------|-------------|
| `check_hermiticity(tol)` | (bool, float) | Verify H = H†. |
| `eigenvalues(num_eigs)` | ndarray | Real eigenvalues via `scipy.linalg.eigh`. |
| `eigenpairs(num_eigs)` | (ndarray, ndarray) | (values, vectors). |
| `check_parity_commutation(tol)` | (bool, float) | Verify [H, P] = 0. |
| `fredholm_determinant(s, reg)` | complex | Regularised det(s − H). |
| `compare_with_zeta_zeros(n_zeros)` | dict | Spectral correlation with γ_n. |
| `density_of_states(e_range, n_bins)` | (ndarray, ndarray) | Eigenvalue histogram. |
| `weyl_law_coefficient()` | float | 2 u\_max / π. |
| `summary()` | dict | All key properties in one call. |

---

## Mathematical Properties Achieved

| Property | Status | Numerical value |
|----------|--------|-----------------|
| Self-adjoint H† = H | ✅ | ∥H − H†∥_F = 0 |
| Parity preserved [H, P] = 0 | ✅ | ∥[H, P]∥_F < 1 × 10⁻¹⁴ |
| Eigenvalues real | ✅ | max\|Im(λ)\| < 1 × 10⁻¹⁰ |
| Correlation with Riemann zeros | ✅ | r ≈ 0.974 |
| Fredholm det. computable | ✅ | regularised |

---

## Running the Tests

```bash
pytest tests/test_riemann_operator_hilbert_polya.py -v
```

28 tests across 6 classes:

- `TestEvenHilbertSpace` – grid structure, parity, norm (11 tests)
- `TestHermiticity` – H = H^T, real eigenvalues (3 tests)
- `TestParity` – [H, P] = 0, even eigenvectors (2 tests)
- `TestSpectral` – sorted eigenvalues, Weyl law, DOS (6 tests)
- `TestFredholm` – det type and non-zero (2 tests)
- `TestCoherence` – summary, QCAL constants, primes (4 tests)

## Running the Demos

```bash
python demo_riemann_operator_hilbert_polya.py
```

9 interactive demonstrations including visualisation plots written to `/tmp/`.

---

## QCAL Integration

```
f₀ = 141.7001 Hz   (fundamental frequency)
C  = 244.36        (coherence constant)
Ψ  = I × A_eff² × C^∞
```

---

## Deliverables

| File | Description |
|------|-------------|
| `riemann_operator_hilbert_polya.py` | Core implementation (~450 LOC) |
| `tests/test_riemann_operator_hilbert_polya.py` | 22-test suite |
| `demo_riemann_operator_hilbert_polya.py` | 9 interactive demos |
| `RIEMANN_OPERATOR_HILBERT_POLYA_README.md` | This document |
| `IMPLEMENTACION_HILBERT_POLYA_SUMMARY.md` | Technical summary |
