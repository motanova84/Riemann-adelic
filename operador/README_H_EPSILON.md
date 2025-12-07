# Operador H_ε: Spectral Operator with Oscillatory Potential

## Overview

This module implements the perturbed spectral operator **H_ε** that captures the spectral structure related to the Riemann Hypothesis:

```
H_ε = H₀ + λ M_{Ω_{ε,R}}
```

where:
- **H₀ = -d²/dt²** is the base Laplacian operator (kinetic energy)
- **M_{Ω_{ε,R}}** is the multiplication operator by the oscillatory potential
- **λ ≈ 141.7001** is the spectral coupling factor

## Mathematical Foundation

### Oscillatory Potential

The potential combines prime number oscillations with localization:

```
Ω_{ε,R}(t) = [1 / (1 + (t/R)²)] × Σ_{n=1}^∞ cos((log p_n)t) / n^{1+ε}
```

**Properties:**
- Prime oscillations weighted by n^{-(1+ε)} ensure convergence
- Envelope 1/(1 + (t/R)²) provides spatial localization
- Parameters: ε > 0 (convergence), R > 0 (localization scale)

### Spectral Measure

The eigenvalues {λ_n} of H_ε define a spectral measure:

```
μ_ε = Σ_n δ_{λ_n}
```

This measure should correlate with the distribution of Riemann zeta zeros:

```
ν = Σ_ρ δ_{Im(ρ)}    where ζ(ρ) = 0, Re(ρ) = 1/2
```

## Implementation Details

### Discretization

- **Grid**: Uniform discretization on [-T, T] with N points
- **H₀**: Tridiagonal finite difference for -d²/dt²
- **H_ε**: Tridiagonal matrix (H₀ + λ diag(Ω))
- **Solver**: `scipy.linalg.eigh_tridiagonal` for O(N²) efficiency

### Parameters

| Parameter | Symbol | Default | Description |
|-----------|--------|---------|-------------|
| N | N | 200 | Discretization dimension |
| T | T | 20.0 | Half-width of interval [-T, T] |
| epsilon | ε | 0.01 | Convergence parameter |
| R | R | 5.0 | Localization scale |
| lambda_coupling | λ | 141.7001 | Spectral coupling factor |
| n_primes | - | 200 | Number of primes in sum |

## Usage

### Basic Example

```python
from operador.operador_H_epsilon import compute_spectral_measure

# Compute eigenvalues of H_ε
eigenvalues, eigenvectors = compute_spectral_measure(
    N=200, T=20.0, epsilon=0.01, R=5.0, 
    lambda_coupling=141.7001, n_primes=200
)

print(f"First 10 eigenvalues: {eigenvalues[:10]}")
```

### Full Workflow

```python
from operador.operador_H_epsilon import (
    compute_spectral_measure,
    load_riemann_zeros,
    plot_spectral_comparison
)

# 1. Compute H_ε spectrum
eigenvalues, _ = compute_spectral_measure(N=200, T=20.0)

# 2. Load Riemann zeros
zeta_zeros = load_riemann_zeros('zeros/zeros_t1e3.txt', max_zeros=200)

# 3. Visual comparison
plot_spectral_comparison(eigenvalues, zeta_zeros, n_points=50,
                        save_path='comparison.png')
```

### Demonstration Script

Run the complete demonstration:

```bash
python demo_operador_H_epsilon.py --N 200 --T 20 --epsilon 0.01
```

This generates four plots:
1. `demo_H_epsilon_potential.png` - Oscillatory potential visualization
2. `demo_H_epsilon_operator.png` - Operator matrix structure
3. `demo_H_epsilon_spectrum.png` - Eigenvalue distribution
4. `demo_H_epsilon_comparison.png` - Comparison with zeta zeros

## Testing

Comprehensive test suite with 20 tests:

```bash
pytest operador/tests_operador_H_epsilon.py -v
```

**Test Coverage:**
- Potential properties (shape, decay, convergence, ε-effect)
- Operator structure (dimensions, symmetry, boundedness, λ-effect)
- Spectral properties (count, reality, sorting, boundedness)
- Riemann zeros loading (file handling, validation)
- Convergence (N-dependence, T-dependence)
- Integration (full workflow, orthonormality)

## Performance

- **Time Complexity**: O(N²) for eigenvalue computation (tridiagonal)
- **Space Complexity**: O(N²) for eigenvectors, O(N) for eigenvalues only
- **Typical Runtime**: ~1-2 seconds for N=200

## Interpretation

The spectral measure μ_ε captures the following physics:

1. **Base Operator H₀**: Represents kinetic energy (free particle)
2. **Potential Ω**: Encodes prime number distribution through oscillations
3. **Coupling λ**: Controls strength of prime influence on spectrum
4. **Eigenvalues**: Form a discrete measure analogous to zeta zeros

If μ_ε ≈ ν (zeta zeros measure), this provides numerical evidence for:
- Spectral interpretation of Riemann Hypothesis
- Connection between primes and quantum mechanics
- Adelic structure underlying zeta zeros

## Mathematical References

- **Burruezo, J.M. (2025)**. S-Finite Adelic Spectral Systems. DOI: [10.5281/zenodo.17116291](https://doi.org/10.5281/zenodo.17116291)
- **Section 3.2**: Adelic Spectral Systems and H_ε construction
- **Section 6-8**: Connection to Riemann zeta zeros

## Files

- `operador_H_epsilon.py` - Main implementation
- `tests_operador_H_epsilon.py` - Test suite (20 tests)
- `demo_operador_H_epsilon.py` - Demonstration script
- `README_H_EPSILON.md` - This file

## See Also

- `operador_H.py` - Gaussian kernel spectral operator (base H₀)
- `OPERADOR_IMPLEMENTATION.md` - Overall operador module documentation
- `validate_v5_coronacion.py` - Full V5 Coronación validation

## License

This code is part of the Riemann Hypothesis proof repository and follows the repository license.
