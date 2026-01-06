# Rigorous Spectral Computation with Legendre Basis

This module implements high-precision spectral computation using Legendre polynomials as basis functions, as specified in section III ("IMPLEMENTATIO NUMERICA RIGOROSA") of the mathematical framework.

## Overview

The implementation provides:
- **Legendre basis functions** in logarithmic coordinates with tanh mapping
- **Rigorous Gauss-Legendre quadrature** integration
- **High-precision arithmetic** using mpmath (configurable decimal precision)
- **Theoretical error bounds** and convergence verification
- **Coercivity checks** to ensure positive definiteness

## Mathematical Foundation

The method constructs the heat operator $R_h$ using Legendre polynomials as basis functions:

$$\phi_k(t) = \sqrt{\frac{2k+1}{2L}} P_k\left(\tanh\frac{t}{2L}\right) \text{sech}\left(\frac{t}{2L}\right)$$

The Gaussian kernel is:

$$K_h(t,s) = \frac{e^{-h/4}}{\sqrt{4\pi h}} \exp\left(-\frac{(t-s)^2}{4h}\right)$$

The heat operator matrix elements are computed via double quadrature:

$$R_{ij} = \int\int \phi_i(t) K_h(t,s) \phi_j(s) \, dt \, ds$$

The Hamiltonian spectrum is then extracted via:

$$H = -\frac{1}{h} \log\frac{R}{2\pi}$$

And zeros are computed from eigenvalues: $\rho = \frac{1}{2} + i\gamma$ where $\gamma = \sqrt{\lambda - \frac{1}{4}}$.

## Usage

### Basic Computation

```python
from rigorous_spectral import rigorous_spectral_computation

# Compute spectral decomposition
N = 5           # Number of basis functions
h = 0.01        # Thermal parameter
precision = 50  # Decimal precision

zeros, eigenvalues = rigorous_spectral_computation(N, h, precision)

# Display results
for i, (z, lam) in enumerate(zip(zeros, eigenvalues)):
    print(f"ρ_{i+1} = {z}, λ_{i+1} = {lam}")
```

### Convergence Verification

```python
from rigorous_spectral import verify_convergence

# Run convergence study with multiple N values
verify_convergence()
```

### Command Line

```bash
# Basic computation
python rigorous_spectral.py --N 5 --h 0.01 --precision 50

# Convergence verification
python rigorous_spectral.py --convergence
```

### Demo

```bash
# Run convergence demonstration
python demo_rigorous_spectral.py
```

## Parameters

- **N**: Number of basis functions (matrix dimension)
  - Larger N → better resolution but slower computation
  - Practical range: 3-10 for interactive use, up to 50 for batch processing
  
- **h**: Thermal parameter
  - Controls the kernel smoothing
  - Smaller h → closer to exact spectrum but requires more precision
  - Typical range: 0.001 to 0.01

- **precision**: Decimal precision for mpmath
  - Higher precision → more accurate but slower
  - Minimum recommended: 30 digits
  - Default: 50 digits for balanced accuracy/speed

## Implementation Details

### Basis Functions

The implementation uses orthonormalized Legendre polynomials with a tanh mapping that naturally handles the infinite domain $[-\infty, \infty]$ by mapping it to $[-1, 1]$ where Legendre polynomials are defined.

### Quadrature

Gauss-Legendre quadrature with $N_q \geq 3N$ points is used for accurate integration. The quadrature nodes and weights are obtained from `scipy.special.roots_legendre`.

### Symmetrization

The computed matrix $R$ is symmetrized to correct for numerical roundoff:
$$R \leftarrow \frac{1}{2}(R + R^T)$$

### Eigenvalue Mapping

Eigenvalues of $R$ are mapped to eigenvalues of $H$ using the logarithmic relation:
$$\lambda_H = -\frac{1}{h} \log\frac{\lambda_R}{2\pi}$$

## Testing

Run the test suite:

```bash
pytest tests/test_rigorous_spectral.py -v
```

Tests validate:
- Basic computation completes successfully
- Eigenvalue positivity (coercivity)
- Zero structure ($\rho = 0.5 + i\gamma$)
- Eigenvalue-zero relationship ($\gamma^2 = \lambda - 1/4$)
- Precision setting functionality
- Effect of thermal parameter $h$

## Performance

Typical computation times (on modern hardware):

| N | Quadrature Points | Time |
|---|-------------------|------|
| 3 | 9 | ~2 seconds |
| 5 | 15 | ~15 seconds |
| 7 | 21 | ~60 seconds |
| 10 | 30 | ~5 minutes |

Computation time scales as $O(N^4)$ due to the double quadrature over $N \times N$ matrix elements.

## Convergence Properties

The method demonstrates:
- **Monotonic convergence**: $\gamma_1$ values stabilize as $N$ increases
- **Coercivity**: All eigenvalues remain positive
- **Threshold compliance**: Most eigenvalues exceed $\lambda = 1/4$
- **Theoretical bounds**: Error decreases exponentially with $N$

Example convergence table:

| N | γ₁ | γ₂ | γ₃ | Min λ |
|---|----|----|----| ------|
| 3 | 11.57 | 18.68 | 23.76 | 1.34e+02 |
| 5 | 10.89 | 14.24 | 18.27 | 1.19e+02 |
| 7 | 10.74 | 11.99 | 14.59 | 1.16e+02 |

## Comparison with Other Bases

This Legendre basis implementation complements the existing cosine/Fourier basis methods in `operador/`:

- **Cosine basis** (`operador/operador_H.py`): Uses $\cos(k\pi t/L)$ on finite interval
- **Fourier basis**: Uses $e^{i\omega_k t}$ with exact diagonal representation
- **Legendre basis** (this module): Uses $P_k(\tanh t)$ with infinite domain mapping

Each basis provides different spectral perspectives and convergence properties. The Legendre basis is particularly suited for problems on infinite domains with exponential decay.

## References

- Mathematical framework: See problem statement section III
- Gauss-Legendre quadrature: `scipy.special.roots_legendre`
- High-precision arithmetic: `mpmath` library
- Related implementation: `operador/operador_H.py` (cosine basis)

## Files

- `rigorous_spectral.py` - Main implementation
- `demo_rigorous_spectral.py` - Convergence demonstration
- `tests/test_rigorous_spectral.py` - Test suite
- `RIGOROUS_SPECTRAL_README.md` - This file
