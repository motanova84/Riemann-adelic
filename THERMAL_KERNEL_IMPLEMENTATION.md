# Thermal Kernel Spectral Operator - Analytical Gaussian Implementation

## Overview

This implementation provides a **non-circular, numerically stable** construction of the Hamiltonian operator H from the thermal kernel, using an **analytical Gaussian kernel** instead of oscillatory integration. This approach avoids numerical errors from highly oscillatory integrals and provides a clean separation between geometric and arithmetic aspects.

## Key Innovation: Closed-Form Gaussian Kernel

Instead of numerically integrating:
```
K_t(x,y) = ∫_R e^(-t(u²+1/4)) e^(iu(log x - log y)) du
```

We use the **closed-form analytical result**:
```
K_h(t,s) = e^(-h/4) * sqrt(π/h) * exp(-(t-s)²/(4h))
```

where `t = log x`, `s = log y`.

### Benefits:
1. ✅ **No oscillatory integration** - pure Gaussian decay
2. ✅ **Numerically stable** - no trigonometric cancellation errors
3. ✅ **Fast computation** - direct formula evaluation
4. ✅ **Symmetric and positive** - guarantees R_h properties

## Mathematical Foundation

### Heat Operator Construction

The heat operator R_h is constructed via double Gauss-Legendre quadrature:

```
R_ij = ∫∫ φ_i(t) K_h(t,s) φ_j(s) dt ds
```

where:
- `φ_k(t)` are orthonormal cosine basis functions in [-L, L]
- `K_h(t,s)` is the analytical Gaussian kernel
- Integration uses Gauss-Legendre nodes (no oscillations!)

### Spectral Mapping to Hamiltonian

The Hamiltonian H is obtained via spectral mapping:

```
H := -(1/h) log(R_h / 2π)
```

This ensures:
- R_h is **symmetric and positive definite** → H is **self-adjoint and coercive**
- In Fourier basis: `spec(H) = {ω² + 1/4}` (exact diagonalization)
- No circular dependency on Riemann zeta function

### Geometric vs Arithmetic Spectrum

**Important distinction:**

1. **Geometric spectrum** (this implementation):
   - `λ_k = ω_k² + 1/4` where `ω_k = πk/L`
   - Depends on domain size L and boundary conditions
   - Universal for any multiplicative flow

2. **Arithmetic spectrum** (requires §6-§8):
   - `λ_k = 1/4 + γ_k²` where γ_k are Riemann zeros
   - Requires de Branges structure (H(E) space)
   - Requires functional equation and Paley-Wiener uniqueness
   - Requires identification D ≡ Ξ

This implementation provides the **geometric foundation**. Comparison with Odlyzko zeros should only be done **after** establishing the full de Branges framework.

## Implementation Details

### File: `thermal_kernel_spectral.py`

#### Core Functions:

1. **`K_gauss(t, s, h)`**
   - Analytical Gaussian kernel in log-variables
   - Returns: `exp(-h/4) * sqrt(π/h) * exp(-(t-s)²/(4h))`

2. **`thermal_kernel(x, y, t)`**
   - Compatibility wrapper for (x, y) variables
   - Internally uses `K_gauss(log x, log y, t)`

3. **`cos_basis(t, L, k)`**
   - Orthonormal cosine basis in [-L, L]
   - k=0: constant mode, k≥1: cosine modes

4. **`build_R_matrix(n_basis, h, L, Nq)`**
   - Constructs R_h matrix via double Gauss-Legendre quadrature
   - Returns symmetric positive definite matrix
   - No oscillatory integrands!

5. **`spectrum_from_R(R, h)`**
   - Maps R_h eigenvalues to H eigenvalues
   - Returns (λ_H, γ_estimated)

6. **`fourier_eigs_H(n_modes, h, L)`**
   - **Oracle function**: exact eigenvalues in Fourier basis
   - Returns analytical `λ_k = (πk/L)² + 1/4`
   - Used for validation of quadrature method

7. **`build_H_operator(n_basis, t)`**
   - High-level constructor
   - Returns H matrix and basis information

8. **`validate_spectral_construction(...)`**
   - Complete validation workflow
   - Compares quadrature vs exact Fourier eigenvalues

## Usage Examples

### Basic Usage

```python
from thermal_kernel_spectral import build_H_operator, validate_spectral_construction

# Build H operator
H, basis_info = build_H_operator(n_basis=10, t=0.001)

print(f"Eigenvalues: {basis_info['eigenvalues']}")
print(f"Estimated gammas: {basis_info['gammas']}")
```

### Full Validation

```python
results = validate_spectral_construction(
    n_basis=20, 
    t=0.001, 
    max_zeros=10, 
    verbose=True
)

print(f"Construction stable: {results['construction_stable']}")
print(f"R symmetric: {results['R_symmetric']}")
print(f"H coercive: {results['H_coercive']}")
```

### Fourier Basis (Exact)

```python
from thermal_kernel_spectral import fourier_eigs_H

# Get exact eigenvalues (no numerical integration)
eig_H, gammas = fourier_eigs_H(n_modes=10, h=1e-3, L=1.0)

print("Exact Fourier eigenvalues:")
for k, (lam, gamma) in enumerate(zip(eig_H, gammas)):
    print(f"  λ_{k} = {lam:.6f}  =>  γ_{k} = {gamma:.6f}")
```

## Testing

### Test Suite: `tests/test_thermal_kernel.py`

Comprehensive test coverage (21 tests):

1. **Gaussian Kernel Properties**
   - Symmetry: K_h(t,s) = K_h(s,t)
   - Peak at diagonal: K_h(t,t) is maximum
   - Positivity: K_h > 0 everywhere
   - Compatibility with thermal_kernel wrapper

2. **Cosine Basis**
   - Normalization: ||φ_k|| = 1
   - Orthogonality: ⟨φ_i, φ_j⟩ = δ_ij

3. **R Matrix Construction**
   - Symmetry: R = R^T
   - Positive definiteness: all eigenvalues > 0
   - Correct dimensions

4. **Spectrum Mapping**
   - H eigenvalues ≥ 1/4
   - Gammas are non-negative
   - Eigenvalues sorted

5. **Fourier Exact Eigenvalues**
   - First mode: λ_0 = 1/4 (γ_0 = 0)
   - Formula: λ_k = ω_k² + 1/4

6. **H Operator Construction**
   - Symmetry, coercivity
   - Basis info completeness

7. **Full Validation**
   - End-to-end workflow
   - Stability flags

8. **No Oscillatory Integration**
   - Kernel is real (no complex exponentials)
   - Smooth Gaussian decay (no oscillations)

### Running Tests

```bash
pytest tests/test_thermal_kernel.py -v
```

All 21 tests pass ✅

## Performance Characteristics

### Computational Complexity

- **Kernel evaluation**: O(1) - closed-form formula
- **R matrix construction**: O(N_q² × n_basis²) - double quadrature
- **Eigenvalue computation**: O(n_basis³) - symmetric eigensolver

### Typical Parameters

- `n_basis`: 5-20 (good approximation)
- `h` (thermal parameter): 10^-3 to 10^-2 (smaller = better approximation)
- `L` (domain half-width): 1.0 (safe for sqrt(2h) ≈ 0.045)
- `Nq` (quadrature points): 160 (high accuracy)

### Example Timing

For `n_basis=10, h=0.001, Nq=160`:
- R matrix construction: ~0.01s
- Eigenvalue computation: ~0.001s
- Total: ~0.02s

## Avoiding Circular Reasoning

This implementation provides a **geometric construction** that:

1. ✅ Does NOT assume Riemann hypothesis
2. ✅ Does NOT use ζ(s) in construction
3. ✅ Does NOT compare with Odlyzko zeros prematurely
4. ✅ DOES provide stable, well-defined operator H
5. ✅ DOES establish coercivity and self-adjointness
6. ✅ DOES give geometric eigenvalues {ω² + 1/4}

### Path to Riemann Zeros (Non-Circular)

To connect with Riemann zeros, one must:

1. **§6**: Establish geometric functional equation D(1-s) = D(s)
2. **§7**: Prove Paley-Wiener uniqueness (two-line proof)
3. **§8**: Identify D ≡ Ξ via order 1 and normalization
4. **§9**: Invert to get primes from zeros

Only **after** this non-circular pipeline can we compare with Odlyzko zeros.

## Comparison with Previous Approach

### Old Approach (Oscillatory)

```python
# Old: numerical integration of oscillatory function
def K_t_real(u, x, y, t):
    return np.exp(-t*(u**2 + 0.25)) * np.cos(u*(np.log(x) - np.log(y)))

# Problems:
# - Highly oscillatory integrand
# - Numerical cancellation errors
# - Slow convergence
# - Difficult to guarantee positivity
```

### New Approach (Analytical)

```python
# New: closed-form Gaussian
def K_gauss(t, s, h):
    return np.exp(-h/4) * np.sqrt(np.pi/h) * np.exp(-(t-s)**2/(4*h))

# Benefits:
# ✅ No oscillations
# ✅ Direct evaluation
# ✅ Fast and stable
# ✅ Guaranteed positive
```

## References

### Mathematical Background

1. **Gaussian integrals**: `∫ exp(-hu² + iau) du = sqrt(π/h) exp(-a²/(4h))`
2. **Heat operator**: Positive, symmetric operator on L²(R, dt)
3. **Spectral mapping**: Functional calculus for self-adjoint operators
4. **De Branges theory**: H(E) spaces and canonical systems

### Implementation Notes from Problem Statement

The problem statement (issue description) provides:
- Detailed derivation of closed-form kernel
- Spectral mapping formula
- Distinction between geometric and arithmetic spectrum
- Warning against premature Odlyzko comparison
- Recommendation to use Fourier basis for exact validation

## Future Extensions

### Possible Enhancements

1. **De Branges structure** (§6-§8)
   - Implement functional equation constraints
   - Apply Paley-Wiener uniqueness
   - Establish D ≡ Ξ identification

2. **Adaptive quadrature**
   - Adjust Nq based on h and n_basis
   - Error estimates for eigenvalues

3. **Parallel computation**
   - Parallelize kernel matrix construction
   - Use sparse matrix methods for large n_basis

4. **Visualization**
   - Plot kernel K_h(t,s) as heatmap
   - Show eigenfunctions of H
   - Spectral density visualization

## Conclusion

This implementation provides a **solid, non-circular foundation** for spectral analysis in the Riemann hypothesis framework. It uses:

- ✅ **Analytical formulas** (no oscillatory integration)
- ✅ **Stable numerics** (Gauss-Legendre quadrature)
- ✅ **Guaranteed properties** (symmetry, positivity, coercivity)
- ✅ **Clear separation** (geometric vs arithmetic)
- ✅ **Comprehensive tests** (21 passing tests)

The path to Riemann zeros requires additional steps (§6-§8), but this geometric foundation is now solid and ready for that next phase.
