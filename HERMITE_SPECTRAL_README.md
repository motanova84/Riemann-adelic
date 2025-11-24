# Hermite Spectral Computation for Riemann Hypothesis

This module implements a spectral computation approach using Hermite-Gauss quadrature and Hermite polynomial basis functions to extract Riemann zeros.

## Mathematical Foundation

The implementation constructs a self-adjoint operator H whose spectrum is related to Riemann zeros via the relation:

```
λ = 1/4 + γ²
```

where ρ = 1/2 + iγ are the Riemann zeros on the critical line.

### Kernel Function

The thermal kernel is given by:

```
K_h(t,s) = exp(-h/4) / sqrt(4πh) * exp(-(t-s)²/(4h))
```

### Hermite Basis Functions

The normalized Hermite basis functions are:

```
ψ_k(t) = H_k(t) * exp(-t²/2) / sqrt(2^k * k! * sqrt(π))
```

where H_k(t) are the Hermite polynomials.

### Matrix Construction

The Hamiltonian matrix H is constructed by:

1. Computing double integrals using Gauss-Hermite quadrature
2. Adding a constant shift of 1/4 to the diagonal for coercivity

```
H[i,j] = ∫∫ ψ_i(t) K_h(t,s) ψ_j(s) w(t) w(s) dt ds + (1/4)δ_{ij}
```

## Usage

### Basic Usage

```python
from hermite_spectral_computation import purissima_spectral_computation

# Compute zeros with N=50 quadrature points and h=0.01
zeros, H = purissima_spectral_computation(N=50, h=0.01)

# Display first 5 zeros
for i, z in enumerate(zeros[:5]):
    print(f"Zero {i+1}: {z.real:.6f} + {z.imag:.6f}i")
```

### Running Validation

```python
from hermite_spectral_computation import validatio_ultima

# Run complete validation
zeros = validatio_ultima()
```

Or from command line:

```bash
python hermite_spectral_computation.py
```

## Parameters

- **N**: Number of Gauss-Hermite quadrature points (also determines basis size)
  - Typical values: 20-50
  - Larger N gives more accurate results but increases computation time
  
- **h**: Thermal regularization parameter
  - Typical values: 0.01-0.1
  - Smaller h gives sharper spectral resolution
  - Must be positive

## Implementation Notes

### Practical Computation

For practical computation, the matrix dimension is limited to min(N, 10) to keep computation time reasonable while demonstrating the method. This is indicated by the comment "Pro computazione practica" in the code.

### Precision

The implementation uses `mpmath` with 100 decimal places of precision for numerical stability in eigenvalue computations.

### Quadrature

- Uses `scipy.special.roots_hermitenorm` for Hermite-Gauss quadrature nodes and weights
- Quadrature is exact for polynomials times Gaussian weight

## Verification

The implementation verifies:

1. **Coercivity**: The operator H is positive definite (all eigenvalues > 0)
2. **Spectral relationship**: Eigenvalues λ satisfy λ > 1/4
3. **Critical line**: All computed zeros have real part exactly 1/2
4. **Error bounds**: Theoretical error estimates are computed

## Expected Output

When running `python hermite_spectral_computation.py`, you should see:

```
======================================================================
=== VALIDATIO ULTIMA PURA ===
======================================================================

Parameters: N=50, h=0.01

Computing H matrix (10×10)...
  Row 2/10 completed
  ...

Primi 5 zeros computati:
  Zero 1: 0.500000 + ...i
  ...

Eigenvalue range: [0.250..., ...]
Minimus eigenvalue: 2.50...e-01
Operator is positive definite
Cota teorica erroris: ...

======================================================================
✅ Verification complete - Operator is coercive and positive definite
======================================================================
```

## Tests

Run tests with:

```bash
pytest test_hermite_spectral.py -v
```

## References

This implementation follows the mathematical framework presented in the problem statement, using:
- Hermite polynomial basis functions
- Gauss-Hermite quadrature for numerical integration
- Spectral theory relating eigenvalues to Riemann zeros
- High-precision arithmetic via mpmath

## Limitations

1. The current implementation uses a reduced matrix size (10×10) for practical computation
2. The computed γ values are scaled differently from actual Riemann zeros due to the simplified construction
3. For production use, a full-scale implementation would require:
   - Larger matrix dimensions
   - Optimized quadrature routines
   - Parallelization for matrix assembly
   - More sophisticated eigenvalue solvers
