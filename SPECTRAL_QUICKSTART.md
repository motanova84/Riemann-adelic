# Quick Start Guide - Spectral Framework

## Installation & Setup

```bash
# Clone the repository (if not already done)
git clone https://github.com/motanova84/-jmmotaburr-riemann-adelic.git
cd -jmmotaburr-riemann-adelic

# Install dependencies
pip install -r requirements.txt
```

## Running the Framework

### 1. Quick Demo (Recommended First Step)

```bash
python3 demo_spectral_framework.py
```

This will:
- Load zeros from the repository
- Reconstruct prime information from zeros
- Compute operator spectrum
- Verify Poisson-Radon duality
- Test Paley-Wiener uniqueness
- Generate 4 visualization plots

**Output files:**
- `spectral_inversion_demo.png` - Prime reconstruction
- `operator_spectrum_demo.png` - Eigenvalue spectrum
- `poisson_duality_demo.png` - Involution visualization
- `paley_wiener_demo.png` - Test function

### 2. Integration Test

```bash
python3 test_spectral_integration.py
```

Validates the complete workflow with known zeros and produces a detailed report.

### 3. Unit Tests

```bash
python3 -m pytest tests/test_spectral_framework.py -v
```

Runs 13 comprehensive unit tests covering all modules.

## Basic Usage Examples

### Example 1: Reconstruct Primes from Zeros

```python
import numpy as np
from inversion.inversion_spectral import prime_measure_from_zeros

# Define zeros (in format 1/2 + i*gamma)
zeros = [
    0.5 + 14.1347j, 0.5 - 14.1347j,
    0.5 + 21.0220j, 0.5 - 21.0220j
]

# Compute prime measure
X = np.linspace(0, 4, 200)  # log scale
measure = prime_measure_from_zeros(zeros, X, t=0.01)

# Find peaks
from scipy.signal import find_peaks
peaks, _ = find_peaks(np.abs(measure))
print(f"Peaks at: {X[peaks]}")
```

### Example 2: Compute Operator Spectrum

```python
import numpy as np
from operador.operador_H import approximate_spectrum

# Create grid
grid = np.linspace(1.0, 3.0, 10)

# Compute spectrum
spectrum = approximate_spectrum(grid, t=0.01)

# Convert to zeros: λ = 1/4 + γ²
for lam in spectrum:
    if lam > 0.25:
        gamma = np.sqrt(lam - 0.25)
        print(f"γ ≈ {gamma:.4f}")
```

### Example 3: Test Poisson Involution

```python
import numpy as np
from dualidad.dualidad_poisson import J_operator, check_involution

# Define a test function
f = lambda x: np.exp(-x**2)

# Test at a point
x = 1.5
holds = check_involution(f, x)
print(f"J(J(f)) = f at x={x}: {holds}")

# Compute J(f) explicitly
Jf_value = J_operator(f, x)
print(f"(Jf)({x}) = {Jf_value:.6f}")
```

### Example 4: Paley-Wiener Uniqueness

```python
from unicidad.unicidad_paleywiener import PaleyWienerClass, compare_distributions

# Create test function class
pw = PaleyWienerClass(bandwidth=10.0)

# Define distributions
D1 = lambda phi: sum(phi(x) for x in [1, 2, 3])
D2 = lambda phi: sum(phi(x) for x in [1, 2, 3])

# Compare
tests = [pw.test_function]
are_equal = compare_distributions(D1, D2, tests)
print(f"Distributions equal: {are_equal}")
```

## Module Reference

### `inversion/` - Spectral Inversion
- `K_D(x, y, zeros, t)` - Spectral kernel from zeros
- `prime_measure_from_zeros(zeros, X, t)` - Reconstruct prime measure

### `operador/` - Operator Construction
- `K_t(x, y, t, N)` - Regularized resolvent kernel
- `R_t_matrix(grid, t)` - Discretized operator matrix
- `approximate_spectrum(grid, t)` - Compute eigenvalues

### `dualidad/` - Poisson-Radon Duality
- `J_operator(f, x)` - Poisson involution
- `check_involution(f, x)` - Verify J² = id

### `unicidad/` - Paley-Wiener Uniqueness
- `PaleyWienerClass(bandwidth)` - Test function class
- `compare_distributions(D1, D2, tests)` - Compare distributions

## Parameters

### Regularization Parameter `t`
- Default: `t = 0.01`
- Smaller `t` → sharper features, more computation
- Larger `t` → smoother, faster computation
- Typical range: `0.001` to `0.1`

### Grid Size
- Small computations: 10-20 points
- Medium computations: 50-100 points
- High resolution: 200-500 points

### Number of Zeros
- Minimum: 2-4 zeros (proof of concept)
- Good results: 10-20 zeros
- High accuracy: 50+ zeros (from zeros/zeros_t1e8.txt)

## Common Use Cases

### Use Case 1: Verify Zero Locations
```python
# Load zeros from file
import numpy as np
zeros = []
with open('zeros/zeros_t1e8.txt') as f:
    for i, line in enumerate(f):
        if i >= 10: break
        gamma = float(line.strip())
        zeros.extend([0.5 + 1j*gamma, 0.5 - 1j*gamma])

# Compute spectrum
from operador.operador_H import approximate_spectrum
grid = np.linspace(1.0, 2.0, 15)
spectrum = approximate_spectrum(grid, t=0.01)
print(f"Eigenvalues: {spectrum}")
```

### Use Case 2: Study Functional Equation
```python
# Test that J enforces s ↔ 1-s
from dualidad.dualidad_poisson import J_operator
import numpy as np

# For various test functions
functions = [
    lambda x: np.exp(-x**2),
    lambda x: x**2,
    lambda x: np.sin(x)
]

for f in functions:
    x = 1.0
    # J should be an involution
    from dualidad.dualidad_poisson import check_involution
    print(f"Involution holds: {check_involution(f, x)}")
```

### Use Case 3: Detect Prime Peaks
```python
from inversion.inversion_spectral import prime_measure_from_zeros
from scipy.signal import find_peaks
import numpy as np

# Use many zeros for better resolution
zeros = [...load many zeros...]
X = np.linspace(0, 5, 500)
measure = prime_measure_from_zeros(zeros, X, t=0.005)

# Find and analyze peaks
peaks, properties = find_peaks(np.abs(measure), height=1.0, distance=5)
for peak in peaks:
    print(f"Peak at log(x) = {X[peak]:.3f}, x ≈ {np.exp(X[peak]):.1f}")
```

## Troubleshooting

### Issue: No peaks detected
**Solution:** Use more zeros, smaller `t`, or adjust peak detection threshold

### Issue: Computation too slow
**Solution:** Reduce grid size, use larger `t`, or fewer zeros

### Issue: Eigenvalues don't match zeros
**Solution:** Check grid range, regularization parameter, and number of grid points

### Issue: Involution doesn't hold exactly
**Solution:** This is expected due to numerical precision; check tolerance

## Performance Tips

1. **Start small**: Test with 5-10 zeros before scaling up
2. **Use appropriate `t`**: Match to your resolution needs
3. **Grid spacing**: Logarithmic spacing often works better
4. **Caching**: Precompute matrices for multiple evaluations
5. **Parallel**: Some operations can be parallelized

## Next Steps

1. Read `SPECTRAL_FRAMEWORK_README.md` for mathematical details
2. Examine `demo_spectral_framework.py` for complete examples
3. Study `tests/test_spectral_framework.py` for usage patterns
4. Run `test_spectral_integration.py` for validation

## Support

For issues or questions:
- Check existing repository documentation
- Review test cases for examples
- Examine demo script for patterns

## Integration with Existing Code

This framework integrates with:
- `validate_explicit_formula.py` - Uses same zeros
- `spectral_operators.py` - Compatible operator construction
- `foundational_gl1.py` - Complements GL(1) approach
- `autonomous_uniqueness_verification.py` - Validates uniqueness

## Citation

If using this framework, cite the repository:
```
@software{riemann_adelic,
  title = {Riemann-Adelic: Spectral Framework for Riemann Hypothesis},
  author = {motanova84},
  year = {2024},
  url = {https://github.com/motanova84/-jmmotaburr-riemann-adelic}
}
```
