# Adelic Spectral Ultima Implementation

## Overview

This module implements the **Codex Ultimus** - a spectral computation method with complete adelic kernel for Riemann Hypothesis validation. It combines:

1. **Hermite Basis Functions**: Orthonormal basis for L²(ℝ) with Gaussian weight
2. **Archimedean Kernel**: Gaussian thermal kernel exp(-(t-s)²/(4h))
3. **Adelic Completion**: Prime contributions via exp(i k log_p (t-s))

## Mathematical Foundation

The operator H is constructed as:

```
H_ij = ∫∫ φ_i(t) K_adelic(t,s) φ_j(s) dt ds
```

Where:
- `φ_k(t)` are normalized Hermite functions
- `K_adelic(t,s)` is the complete adelic kernel:
  - Archimedean part: `exp(-h/4)/√(4πh) * exp(-(t-s)²/(4h))`
  - Prime contributions: `∑_p ∑_k log(p) exp(-h(k log p)²/4) / p^(k/2) * exp(i k log_p (t-s))`

The spectrum of H satisfies: `λ = 1/4 + γ²` where γ are the Riemann zeros.

## Usage

### Basic Example

```python
from adelic_spectral_ultima import ultima_spectral_computation

# Compute with small parameters (fast)
N, h = 10, 0.001
zeros, H = ultima_spectral_computation(N, h, max_primes=20)

print(f"Found {len(zeros)} zeros")
for i, z in enumerate(zeros[:5], 1):
    print(f"γ_{i} = {float(z.imag):.6f}")
```

### Full Validation

```python
from adelic_spectral_ultima import validatio_ultima

# Run complete validation (slow - hours)
zeros = validatio_ultima()
```

Or from command line:

```bash
python adelic_spectral_ultima.py
```

### Run Demonstration

```bash
python demo_adelic_spectral_ultima.py
```

## Parameters

- **N**: Number of Hermite basis functions (default: 100 for full validation)
  - Larger N → more accurate but slower
  - Computational cost: O(N⁴) for matrix construction

- **h**: Thermal parameter (default: 0.0001 for full validation)
  - Smaller h → closer to exact zeros
  - Must be > 0 for numerical stability

- **max_primes**: Maximum number of primes in adelic kernel (default: 1000)
  - More primes → more complete adelic representation
  - Limited by P ~ N/log(N) from Prime Number Theorem

## Computational Requirements

### Small Parameters (N=10, h=0.001)
- Time: ~15 seconds
- Memory: < 100 MB
- Accuracy: Moderate (errors ~ 10-20)

### Medium Parameters (N=50, h=0.0001)
- Time: ~10-30 minutes
- Memory: ~1 GB
- Accuracy: Better (errors ~ 1-5)

### Full Theoretical Parameters (N=100, h=0.0001)
- Time: Hours to days
- Memory: Several GB
- Precision: mp.dps=500 (500 decimal digits)
- Accuracy: Theoretical bounds apply

## Files

- `adelic_spectral_ultima.py` - Main implementation
- `tests/test_adelic_spectral_ultima.py` - Test suite
- `demo_adelic_spectral_ultima.py` - Demonstration script
- `ADELIC_SPECTRAL_ULTIMA_README.md` - This file

## Testing

Run tests:

```bash
# Run all tests (excluding slow tests)
pytest tests/test_adelic_spectral_ultima.py -v

# Run all tests including slow ones
pytest tests/test_adelic_spectral_ultima.py -v --run-slow
```

## Implementation Notes

### Hermitian Matrix
The operator H is Hermitian (complex-valued but self-adjoint) due to the complex exponentials in the adelic kernel. The code uses `mp.eigh()` for Hermitian eigenvalue decomposition.

### High Precision Arithmetic
The implementation uses `mpmath` with 500 decimal digits of precision (`mp.dps=500`) to handle:
- Large factorial computations in Hermite polynomials
- Accumulation of quadrature errors
- Near-degenerate eigenvalue separation

### Convergence
The method converges as N→∞ and h→0, but:
- Pure Hermite basis on ℝ has limitations for high-frequency oscillations
- Practical convergence requires balancing N and h
- The error bound: `O(exp(-√(N/log N)))`

## References

1. **Problem Statement**: Theoretical formulation of the adelic spectral method
2. **Thermal Kernel**: See `thermal_kernel_spectral.py` for related approaches
3. **Adelic Theory**: Prime contributions via Tate thesis and adelic analysis

## Known Limitations

1. **Convergence to True Zeros**: The Hermite basis spectral method may not converge to the true Riemann zeros with practical parameters due to the localized nature of Hermite functions vs. the global behavior needed to capture zeros at large heights.

2. **Computational Cost**: The full theoretical parameters (N=100, h=0.0001) require significant computational resources, making practical validation challenging.

3. **Numerical Stability**: For very small h or large N, numerical precision issues may arise despite high-precision arithmetic.

## License

This implementation is part of the Riemann Hypothesis validation project.
See LICENSE for details.
