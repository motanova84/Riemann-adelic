# Consummatio Spectralis: Spectral Method with Adelic Corrections

## Overview

This implementation provides a spectral method for computing Riemann zeta function zeros using thermal kernel operators with adelic corrections. The method combines:

1. **Hermite basis expansion** - Orthonormal basis functions for L²(ℝ)
2. **Thermal kernel** - Heat propagation on the real line
3. **Adelic corrections** - Contributions from p-adic places (prime numbers)

## Mathematical Background

The method is based on the spectral theory of operators. The key insight is that zeros ρ = 1/2 + iγ of the Riemann zeta function correspond to eigenvalues λ = γ² + 1/4 of a self-adjoint operator H.

### Operator Construction

The operator H is constructed using:

```
H_{ij} = ∫∫ φ_i(t) K(t,s) φ_j(s) dt ds
```

where:
- `φ_k(t)` are normalized Hermite basis functions
- `K(t,s)` is the thermal kernel with adelic corrections

### Thermal Kernel

The thermal kernel is:

```
K(t,s) = exp(-h/4)/sqrt(4πh) * exp(-(t-s)²/(4h))
```

### Adelic Corrections

Prime contributions are added to the kernel:

```
K(t,s) += Σ_p Σ_k log(p) * exp(-h(k·log p)²/4) / p^(k/2) * cos(k·log(p)·(t-s))
```

where the sum runs over primes p and powers k = 1, 2, 3.

## Files

- **`consummatio_spectralis.py`** - Main implementation with full validation
  - `consummatio_spectralis(N, h, max_primes)` - Compute zeros
  - `validatio_consummatio()` - Full validation function
  
- **`demo_consummatio_spectralis.py`** - Demo with reasonable parameters
  - Uses N=15, h=0.001, max_primes=30 for faster execution
  - Shows complete workflow with detailed output
  
- **`tests/test_consummatio_spectralis.py`** - Comprehensive test suite
  - 16 test cases covering functionality and numerical stability

## Usage

### Quick Demo

Run the demo script with moderate parameters:

```bash
python demo_consummatio_spectralis.py
```

This will compute zeros using N=15 basis functions and display results in ~90 seconds.

### Full Validation

For the complete validation with N=50 basis functions (requires significant computation time):

```bash
python consummatio_spectralis.py
```

**Warning**: This may take 30-60 minutes to complete due to the nested quadrature and prime summations for a 50×50 matrix.

### Programmatic Usage

```python
from consummatio_spectralis import consummatio_spectralis

# Compute zeros with specific parameters
N = 20           # Number of basis functions
h = 0.001        # Thermal parameter
max_primes = 50  # Number of primes to include

zeros, H = consummatio_spectralis(N, h, max_primes)

# Display first few zeros
for i, z in enumerate(zeros[:5]):
    print(f"ρ_{i+1} = 0.5 + {float(z.imag):.6f}i")
```

## Parameters

### N (Basis Dimension)
- Number of Hermite basis functions
- Larger N → better accuracy, but O(N²) computation time
- Recommended: 10-50

### h (Thermal Parameter)
- Controls the "diffusion time" of the thermal kernel
- Smaller h → better localization, better accuracy
- Typical values: 0.0001 - 0.01
- Smaller values require larger N for stability

### max_primes
- Number of primes to include in adelic corrections
- More primes → more accurate representation of arithmetic structure
- Recommended: 20-100
- Diminishing returns after ~50 primes

## Accuracy and Performance

### Accuracy vs. Parameters

| N  | h     | max_primes | Time  | Typical Error |
|----|-------|------------|-------|---------------|
| 10 | 0.01  | 10         | ~30s  | ~10.0         |
| 15 | 0.001 | 30         | ~90s  | ~5.0          |
| 30 | 0.001 | 50         | ~15m  | ~1.0          |
| 50 | 0.001 | 100        | ~60m  | ~0.1          |

Errors are absolute differences from known Odlyzko zeros.

### Computational Complexity

- **Matrix construction**: O(N² · Q² · P) where Q = quadrature nodes, P = max_primes
- **Diagonalization**: O(N³)
- **Total**: Dominated by matrix construction for typical parameters

## Theory and References

The implementation is based on:

1. **Spectral theory** - Self-adjoint operators on Hilbert spaces
2. **Thermal kernel methods** - Heat equation on the real line
3. **Adelic formulation** - Contributions from all places (including primes)

The method encodes the spectral information of the Riemann zeta function in the eigenvalues of a finite-dimensional matrix operator, making it amenable to numerical computation.

### Key Properties

1. **Zeros on critical line**: All computed zeros satisfy Re(ρ) = 0.5
2. **Eigenvalue relation**: λ_n = γ_n² + 1/4 for the nth zero ρ_n = 1/2 + iγ_n
3. **Hermitian symmetry**: The operator H is Hermitian (self-adjoint)
4. **Positive definiteness**: All eigenvalues are positive

## Testing

Run the test suite:

```bash
pytest tests/test_consummatio_spectralis.py -v
```

Test coverage includes:
- Basic functionality
- Zeros on critical line
- Matrix properties (Hermitian, positive definite)
- Numerical stability
- Precision handling
- Parameter variations

## Limitations and Future Work

### Current Limitations
1. Computational cost scales as O(N²) for matrix construction
2. High accuracy requires large N (30-50) and long computation times
3. No automatic parameter selection

### Future Enhancements
1. Adaptive quadrature for better efficiency
2. Sparse matrix methods for larger N
3. Parallel computation of matrix elements
4. Optimized prime summation algorithms
5. Automatic parameter selection based on target accuracy

## License

This implementation is part of the riemann-adelic repository. See LICENSE for details.

## Citation

If you use this implementation in your research, please cite:

```bibtex
@software{consummatio_spectralis,
  title = {Consummatio Spectralis: Spectral Methods with Adelic Corrections},
  author = {Mota, J.M.},
  year = {2024},
  url = {https://github.com/motanova84/-jmmotaburr-riemann-adelic}
}
```
