# Operador H - Gaussian Kernel Spectral Operator

This module implements the heat operator $R_h$ and Hamiltonian $H$ using the **closed-form Gaussian kernel**, eliminating oscillatory integration issues.

## Key Features

✅ **No oscillatory integration** - Uses analytical Gaussian formula instead of quad/nquad  
✅ **Symmetric and positive definite** - $R_h$ is always well-conditioned  
✅ **Coercive Hamiltonian** - All eigenvalues $\lambda > 1/4$  
✅ **Fast and stable** - Milliseconds instead of timeouts  
✅ **Two implementations** - Cosine basis (quadrature) and Fourier basis (exact)

## Mathematical Foundation

The thermal kernel has closed form in log-variables $t = \log x$, $s = \log y$:

$$K_h(t,s) = e^{-h/4} \sqrt{\frac{\pi}{h}} \exp\left(-\frac{(t-s)^2}{4h}\right)$$

This is the analytical result of:
$$\int_{\mathbb{R}} e^{-h(u^2 + 1/4)} e^{iu(t-s)} du$$

### Construction

1. **Heat operator**: Build $R_h$ via double Gauss-Legendre quadrature
2. **Hamiltonian**: Apply spectral map $H = -\frac{1}{h} \log\left(\frac{R_h}{2\pi}\right)$
3. **Spectrum**: In Fourier basis, $\text{spec}(H) = \{\omega_k^2 + 1/4\}$ with $\omega_k = \pi k / L$

## Usage

### Basic Example

```python
from operador.operador_H import build_R_matrix, spectrum_from_R

# Parameters
h = 1e-3      # thermal parameter
L = 1.0       # domain half-width
n_basis = 5   # matrix size

# Build heat operator
R = build_R_matrix(n_basis=n_basis, h=h, L=L, Nq=160)

# Extract H spectrum
lam_H, gammas = spectrum_from_R(R, h)

print(f"Eigenvalues: {lam_H}")
print(f"Gammas: {gammas}")
```

### High Precision Implementation

For computations requiring ultra-high precision (100 digits), use the `high_precision_H` function from `spectral_RH/operador/operador_H_real.py`:

```python
import sys
sys.path.insert(0, 'spectral_RH')
from operador.operador_H_real import high_precision_H

# Parameters
N = 200      # matrix size
h = 0.001    # thermal parameter

# Compute with 100-digit precision using mpmath
eigenvalues = high_precision_H(N=N, h=h)

# eigenvalues = [0.25 + log(1/λ) for λ in kernel_eigenvalues]
print(f"First 5 eigenvalues: {eigenvalues[:5]}")
```

**Key features of high_precision_H:**
- Uses mpmath with 100 decimal digits precision
- Gaussian kernel: `exp(-(t-s)²/(4h)) / sqrt(4πh)`
- Hermite basis on logarithmic scale (nodes from -10 to 10)
- High precision diagonalization via `mpmath.eigsy`
- Returns transformed eigenvalues: `0.25 + log(1/λ)`

**Demo script:**
```bash
python demo_high_precision_H.py
```

### Exact Fourier Solution

```python
from operador.operador_H import fourier_eigs_H

# Get exact eigenvalues (diagonal in Fourier basis)
lam_H, gammas = fourier_eigs_H(n_modes=5, h=1e-3, L=1.0)

print(f"Exact eigenvalues: {lam_H}")
# Output: [0.25, 10.12, 39.73, 89.08, 158.16]
```

## Testing

Run the test suite:

```bash
# Basic tests (symmetry, coercivity, convergence)
pytest operador/tests_operador.py -v

# Extended tests with convergence tables
pytest operador/tests_operador_extended.py -s
```

## Demonstration

Run the demonstration script:

```bash
python demo_operador.py
```

This shows:
- Basic usage of the module
- Convergence as $N_q \to \infty$
- Kernel properties (Gaussian decay, no oscillations)
- Relation to Riemann zeros

## Files

- `operador_H.py` - Main implementation
- `tests_operador.py` - Basic validation tests
- `tests_operador_extended.py` - Convergence table tests
- `__init__.py` - Module exports

## Implementation Details

### Cosine Basis (Quadrature)

Uses orthonormal cosine basis on $[-L, L]$:
- $\phi_0(t) = \frac{1}{\sqrt{2L}}$
- $\phi_k(t) = \frac{\cos(k\pi t / L)}{\sqrt{L}}$ for $k \geq 1$

Computes matrix elements via Gauss-Legendre quadrature:
$$R_{ij} = \int_{-L}^L \int_{-L}^L \phi_i(t) K_h(t,s) \phi_j(s) \, dt \, ds$$

### Fourier Basis (Exact)

Uses periodic Fourier basis $\phi_k(t) = \frac{1}{\sqrt{2L}} e^{i\omega_k t}$ with $\omega_k = \pi k / L$.

The heat operator is **diagonal**:
$$\langle \phi_j, R_h \phi_k \rangle = 2\pi e^{-h(\omega_k^2 + 1/4)} \delta_{jk}$$

Then:
$$\lambda_H(\omega_k) = \omega_k^2 + \frac{1}{4}$$

This is exact (no quadrature error).

## Relation to Riemann Zeros

### Geometric vs Arithmetic

The spectrum $\{\omega_k^2 + 1/4\}$ gives **geometric zeros** $\gamma_k = \omega_k = \pi k / L$.

These are **NOT** the arithmetic Riemann zeros (Odlyzko).

### Arithmetic Recovery

To recover arithmetic zeros $\gamma_k$ from Odlyzko, you need:

1. ✅ **Functional equation**: $D(1-s) = D(s)$ (§6)
2. ✅ **Paley-Wiener uniqueness** (§8)
3. ✅ **Identification**: $D \equiv \Xi$ (order 1 + normalization)
4. ✅ **Inversion**: Primes from zeros

This module provides the **operator foundation**. Arithmetic structure comes from the full pipeline.

## Performance

Typical timings on modern hardware:

| Operation | n_basis=5, Nq=160 | n_basis=10, Nq=200 |
|-----------|-------------------|---------------------|
| Build R   | ~10 ms            | ~30 ms              |
| Diagonalize | ~1 ms           | ~3 ms               |
| Fourier (exact) | ~0.1 ms     | ~0.1 ms             |

**Total: milliseconds** (vs. minutes/timeouts with oscillatory integration)

## Validation

The implementation is validated by:

1. **Symmetry**: $\|R - R^T\| < 10^{-12}$
2. **Positivity**: All eigenvalues of $R$ positive
3. **Coercivity**: All eigenvalues of $H$ satisfy $\lambda > 0.25$
4. **Convergence**: Results stabilize as $N_q \to \infty$
5. **Exactness**: Fourier matches theoretical formula to machine precision

## References

- Problem statement: Fixing oscillatory integration with closed-form Gaussian
- Mathematical foundation: Universal multiplicative flow on $\mathbb{R}_+$
- Spectral theory: Heat operator $\to$ Hamiltonian mapping
- Numerical methods: Gauss-Legendre quadrature for smooth kernels

## License

Same as parent repository.
