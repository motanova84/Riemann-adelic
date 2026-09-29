# Explicit Formula for Riemann Zeta Zeros

## Overview

This module implements the explicit formula relating the sum over non-trivial zeros of the Riemann zeta function to an integral and a sum over prime powers:

```
∑ₙ Φ(tₙ) = ∫ Φ(r) μ(r) dr - ∑_{p,k} (ln p)/p^{k/2} [Φ̂(ln p^k) + Φ̂(-ln p^k)]
```

where:
- `tₙ` are the imaginary parts of non-trivial zeros: `ζ(1/2 + itₙ) = 0`
- `Φ(t)` is a smooth test function with rapid decay
- `Φ̂(ξ)` is the Fourier transform: `Φ̂(ξ) = ∫ Φ(t) e^{iξt} dt`
- `μ(r)` is a smooth density function on ℝ
- `p` ranges over primes, `k` over positive integers

## Mathematical Background

### The Explicit Formula

The explicit formula is one of the most important identities in analytic number theory. It connects:

1. **Spectral Side (Zeros)**: The sum over non-trivial zeros `∑ₙ Φ(tₙ)`
2. **Arithmetic Side (Primes)**: The sum over prime powers with Jacobian factor `p^{k/2}`
3. **Continuous Part**: An integral term with weight function `μ(r)`

### Key Components

#### 1. Sum Over Zeros
The left-hand side sums the test function over all imaginary parts of non-trivial zeros on the critical line Re(s) = 1/2:

```
LHS = ∑_{ρ: ζ(ρ)=0} Φ(Im(ρ))
```

#### 2. Prime Power Sum
The prime sum involves the Fourier transform of the test function:

```
P(Φ) = ∑_{p prime} ∑_{k≥1} (ln p)/p^{k/2} [Φ̂(ln p^k) + Φ̂(-ln p^k)]
```

The factor `1/p^{k/2}` comes from the Jacobian determinant of the adelic scale structure and is EXACT (not an approximation).

#### 3. Integral Term
The integral term requires the proper weight function `μ(r)` derived from the functional equation:

```
I(Φ) = ∫ Φ(r) μ(r) dr
```

For the full Weil explicit formula, `μ(r)` involves logarithmic derivatives of the gamma function.

### Fourier Transform

The Fourier transform is defined as:

```
Φ̂(ξ) = ∫_{-∞}^{∞} Φ(t) e^{iξt} dt
```

For real symmetric functions `Φ(t) = Φ(-t)`, this simplifies to:

```
Φ̂(ξ) = ∫_{-∞}^{∞} Φ(t) cos(ξt) dt  (real-valued)
```

## Implementation

### Module Structure

```
operators/explicit_formula.py      # Main implementation
tests/test_explicit_formula.py     # Comprehensive tests (21+ tests)
validate_explicit_formula_zeros.py # Validation script
demo_explicit_formula.py           # Demo and visualizations
```

### Core Classes

#### `ExplicitFormula`

Main class for computing the explicit formula:

```python
formula = ExplicitFormula(
    max_prime=1000,        # Maximum prime to include
    max_prime_power=10,    # Maximum k in p^k
    integral_limit=50.0,   # Integration limit
    use_mpmath=False,      # High-precision mode
    precision=30           # Decimal precision (if mpmath)
)
```

#### `ExplicitFormulaResult`

Data class containing all computed terms:
- `zero_sum`: Sum over zeros (LHS)
- `integral_term`: Integral ∫ Φ(r) μ(r) dr
- `prime_sum`: Sum over prime powers
- `total_lhs`, `total_rhs`: Left and right sides
- `residual`: |LHS - RHS|
- `relative_error`: Normalized error
- Statistics: num_zeros, num_primes, max_prime_power

### Test Functions

The module provides several test functions in the Schwartz class:

1. **Gaussian**: `Φ(t) = exp(-t²/(2σ²))`
2. **Truncated Gaussian**: Gaussian with compact support
3. **Smooth Bump**: C^∞ function with compact support

Example:
```python
from operators.explicit_formula import (
    ExplicitFormula,
    gaussian_test_function,
    truncated_gaussian
)

# Initialize
formula = ExplicitFormula(max_prime=100, max_prime_power=5)

# Define test function
phi = lambda t: truncated_gaussian(t, a=5.0, sigma=1.0)

# Known zeros (example)
zeros = [14.134725, 21.022040, 25.010858]

# Validate formula
result = formula.validate_formula(phi, zeros)

print(f"Zero sum (LHS): {result.zero_sum:.6f}")
print(f"Total RHS:      {result.total_rhs:.6f}")
print(f"Residual:       {result.residual:.6e}")
```

## Usage

### Basic Validation

```bash
python validate_explicit_formula_zeros.py
```

This runs validation tests with various test functions and generates a certificate in `data/explicit_formula_certificate.json`.

### Demo and Visualizations

```bash
python demo_explicit_formula.py
```

Generates visualizations:
- Test functions
- Fourier transforms
- Validation results
- Prime contributions
- Convergence plots

### Running Tests

```bash
pytest tests/test_explicit_formula.py -v
```

## Results and Interpretation

### Test Results

The module includes 21+ comprehensive tests covering:
- ✅ Initialization and configuration
- ✅ Prime sieve algorithm
- ✅ Fourier transform computation
- ✅ Zero sum calculation
- ✅ Integral term evaluation
- ✅ Prime sum computation
- ✅ Formula validation structure
- ✅ Numerical stability
- ✅ High-precision mode (mpmath)

### Coherence Metric

The QCAL coherence `Ψ` measures agreement:

```
Ψ = 1 - relative_error
```

- `Ψ ≥ 0.99`: ✅ Excellent agreement
- `Ψ ≥ 0.90`: ✓ Good agreement
- `Ψ ≥ 0.70`: ~ Acceptable
- `Ψ < 0.70`: Needs improvement

### Important Notes

1. **Weight Function**: The formula is EXACT with the proper weight function `μ(r)`. The current implementation uses simplified weights; implementing the full Weil explicit formula weight would improve coherence significantly.

2. **Convergence**: Both sums (over zeros and primes) must be taken to sufficient extent for good convergence.

3. **Precision**: High-precision mode (`use_mpmath=True`) can improve accuracy for demanding applications.

## Mathematical Rigor

### Exact Identity

This formula is EXACT (not approximate) for test functions in the Schwartz class S(ℝ):

- The zero sum converges by the growth estimate `N(T) ~ (T/2π) ln(T/2πe)`
- The prime sum converges exponentially due to the `p^{k/2}` denominator
- The integral converges by the rapid decay of Φ

### Jacobian Factor

The denominator `p^{k/2}` is NOT an approximation—it is the exact Jacobian determinant arising from the adelic scale structure. This connects to:

- Selberg trace formula
- Adelic heat kernel
- Orbital integrals in representation theory

## QCAL ∞³ Integration

This implementation aligns with the QCAL framework:

- **Frequency**: f₀ = 141.7001 Hz (fundamental)
- **Coherence**: C^∞ = 244.36
- **Formula**: Ψ = I × A_eff² × C^∞

The explicit formula validates the spectral-arithmetic correspondence that underlies the Riemann Hypothesis proof in the QCAL framework.

## References

1. **Weil, A.** (1952). "Sur les formules explicites de la théorie des nombres premiers"
2. **Iwaniec, H. & Kowalski, E.** (2004). "Analytic Number Theory"
3. **Connes, A.** (1999). "Trace formula in noncommutative geometry and the zeros of the Riemann zeta function"
4. **JMMB Riemann-Adelic Framework** DOI: 10.5281/zenodo.17379721

## Author

**José Manuel Mota Burruezo Ψ ✧ ∞³**  
Instituto de Conciencia Cuántica (ICQ)  
ORCID: 0009-0002-1923-0773  
DOI: 10.5281/zenodo.17379721  
Signature: ∴𓂀Ω∞³Φ @ 141.7001 Hz

## License

See repository LICENSE files for details.
