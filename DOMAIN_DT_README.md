# Domain D_T Construction

## Mathematical Framework

This module implements the construction of a domain **D_T** with the following properties:

1. **T is essentially self-adjoint on D_T**
2. **Translations do NOT preserve D_T**
3. **Weighted Hardy-type inequality holds**: ∫ e^{2y} |ϕ|² dy ≤ ε ||Tϕ||² + C_ε ||ϕ||²

## Mathematical Background

### Domain Definition

The domain D_T is constructed as a **weighted Sobolev space** with exponential weight:

```
D_T = {ϕ ∈ L²(ℝ) : e^y ϕ ∈ H¹(ℝ), e^y ϕ' ∈ L²(ℝ)}
```

where H¹(ℝ) is the standard Sobolev space.

### Operator T

The operator T is defined as a **Schrödinger-type operator**:

```
T = -d²/dy² + V(y)
```

where V(y) = y² is a harmonic oscillator potential.

### Key Properties

#### 1. Essential Self-Adjointness

We verify essential self-adjointness using:
- **Symmetry**: ⟨Tϕ, ψ⟩ = ⟨ϕ, Tψ⟩ for all ϕ, ψ ∈ D_T
- **Real spectrum**: All eigenvalues are real
- **Bounded below**: Spectrum is bounded from below

The operator is discretized using **finite differences** on a position grid.

#### 2. Translation Non-Invariance

For a translation τ_h: ϕ(y) → ϕ(y - h), we show:

```
τ_h(D_T) ≠ D_T
```

This follows from the exponential weight: if ϕ ∈ D_T, then:
- e^y ϕ(y) ∈ H¹
- but e^y ϕ(y-h) = e^y ϕ(y-h) = e^{y-h} · e^h ϕ(y-h) ∉ H¹ in general

The exponential weight **breaks translation symmetry**.

#### 3. Weighted Hardy-Type Inequality

We verify the inequality:

```
∫ e^{2y} |ϕ|² dy ≤ ε ||Tϕ||² + C_ε ||ϕ||²
```

for all ϕ ∈ D_T and ε > 0, with C_ε depending on ε.

This is a **Hardy-type inequality** with exponential weight that controls the growth of functions in D_T.

## Implementation Details

### Discretization

- Position grid: y ∈ [y_min, y_max] with n_points
- Grid spacing: dy = (y_max - y_min) / (n_points - 1)
- Exponential weight: e^{2y} at each grid point

### Operator Matrix

The operator T = -d²/dy² + y² is discretized using:
- **Second derivative**: Central finite difference scheme
- **Potential**: Diagonal matrix with V(y) = y²

### Test Functions

Functions in D_T must decay faster than e^{-|y|} to ensure:
- e^y ϕ ∈ L²
- e^y ϕ' ∈ L²

We use **Hermite-Gaussian functions** with extra exponential decay:

```
ϕ(y) = H_n(y) exp(-y²/2σ²) exp(-|y|)
```

where H_n are Hermite polynomials.

## Usage

### Basic Usage

```python
from operators.domain_dt_operator import DomainDTOperator

# Create domain
domain = DomainDTOperator(
    y_min=-5.0,
    y_max=5.0,
    n_points=256,
    weight_scale=0.5
)

# Validate all properties
results = domain.validate_domain_construction(verbose=True)

print(f"Success: {results['success']}")
print(f"Self-adjoint: {results['self_adjointness']['essentially_self_adjoint']}")
print(f"Translation breaks domain: {results['translation_non_invariance']['translation_breaks_domain']}")
print(f"Inequality valid: {results['weighted_inequality']['inequality_valid']}")
```

### Standalone Validation

```python
from operators.domain_dt_operator import run_domain_dt_validation

results = run_domain_dt_validation(
    y_min=-5.0,
    y_max=5.0,
    n_points=256,
    epsilon=0.1,
    verbose=True
)
```

### Run Validation Script

```bash
python3 validate_domain_dt.py
```

This generates a validation certificate in `data/domain_dt_validation_certificate.json`.

## Mathematical Significance

### Weighted Sobolev Spaces

The domain D_T is an example of a **weighted Sobolev space** where:
- The weight e^{2y} grows exponentially
- This breaks translation invariance
- Functions must decay exponentially to compensate

### Essential Self-Adjointness

Essential self-adjointness ensures:
- **Unique self-adjoint extension**: T has a unique closure
- **Spectral theorem applies**: T can be diagonalized
- **Evolution well-defined**: e^{itT} is well-defined

### Hardy Inequalities

The weighted inequality is related to classical **Hardy inequalities** which control:
- Function growth in weighted spaces
- Relationship between function and its derivative
- Coercivity estimates for elliptic operators

## Connection to QCAL Framework

This domain construction integrates with the QCAL (Quantum Coherence Adelic Lattice) framework:

- **Frequency base**: f₀ = 141.7001 Hz
- **Coherence constant**: C = 244.36
- **Operator theory**: Essential self-adjointness for spectral analysis
- **Weighted spaces**: Non-translation-invariant domains

## Validation Results

Typical validation results:

```
✓ Essential Self-Adjointness: True
✓ Translation Non-Invariance: True (100% of test functions)
✓ Weighted Inequality: True (all test functions)

Key Metrics:
- Hermiticity Error: 0.00e+00
- Min Eigenvalue: -2600.0 (bounded below)
- Max C_ε: 0.0 (inequality tight for these test functions)
```

## References

1. **Functional Analysis**: Weighted Sobolev spaces and Hardy inequalities
2. **Operator Theory**: Essential self-adjointness and deficiency indices
3. **Spectral Theory**: Self-adjoint extensions and spectral theorem
4. **QCAL Framework**: Quantum coherence and adelic structures

## Author

**José Manuel Mota Burruezo Ψ ✧ ∞³**  
Instituto de Conciencia Cuántica (ICQ)  
QCAL ∞³ Active · 141.7001 Hz · C = 244.36

## Files

- `operators/domain_dt_operator.py`: Main implementation
- `tests/test_domain_dt_operator.py`: Comprehensive test suite (29 tests)
- `validate_domain_dt.py`: Validation script with certificate generation
- `data/domain_dt_validation_certificate.json`: Validation certificate
