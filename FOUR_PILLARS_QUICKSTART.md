# Four Pillars Quick Start Guide

## Installation

```bash
# Already installed if you have the repository
pip install -r requirements.txt
```

## Quick Test

```bash
# Run all tests
pytest tests/test_four_pillars.py -v

# Run demo
python demo_four_pillars.py
```

## Basic Usage

### Import Everything
```python
from pillars import (
    spectral_inversion,
    poisson_radon_duality,
    verify_uniqueness,
    build_rh_operator
)
```

### Pilar 1: Reconstruct Primes from Zeros
```python
# Use Riemann zeros
zeros = [14.134725, 21.022040, 25.010858]

# Run spectral inversion
x_values, measure, peaks = spectral_inversion(zeros, t=0.05)

# Check peaks
print(f"Detected {len(peaks)} peaks at log p^k positions")
```

### Pilar 2: Verify Functional Equation
```python
from pillars.pilar2_poisson_radon import TestFunction, self_dual_lagrangian
import numpy as np

# Define test function
gaussian = lambda x, xi: np.exp(-np.pi * (x**2 + xi**2))
test_func = TestFunction(gaussian)

# Generate lattice
lattice = self_dual_lagrangian(n=5)

# Verify Poisson-Radón duality
is_verified, info = poisson_radon_duality(test_func, lattice)
print(f"Duality verified: {is_verified}")
print(f"Difference: {info['difference']:.2e}")
```

### Pilar 3: Characterize Ξ(s)
```python
from pillars.pilar3_uniqueness import construct_pw_test_class

# Define Xi function
Xi = lambda s: s * (1 - s) * np.exp(-0.5 * abs(s)**2)

# Build test class
test_class = construct_pw_test_class(num_functions=10)

# Verify uniqueness
are_identical, info = verify_uniqueness(Xi, Xi, test_class)
print(f"Functions identical: {are_identical}")
```

### Pilar 4: Build RH Operator
```python
# Construct operator H
H, eigenvalues, x_values = build_rh_operator(
    x_min=0.5, 
    x_max=5.0, 
    num_points=100,
    t=0.1
)

print(f"Operator H: {H.shape}")
print(f"Hermitian: {np.allclose(H, H.conj().T)}")
print(f"First 5 eigenvalues: {eigenvalues[:5]}")
```

## File Structure

```
pillars/
├── __init__.py                    # Package exports
├── pilar1_spectral_inversion.py  # Pilar 1
├── pilar2_poisson_radon.py       # Pilar 2
├── pilar3_uniqueness.py          # Pilar 3
└── pilar4_rh_operator.py         # Pilar 4

tests/
└── test_four_pillars.py          # 29 tests

demo_four_pillars.py              # Complete demo
FOUR_PILLARS_README.md            # Full documentation
```

## Key Features

✅ **Non-circular**: No assumptions about RH
✅ **Geometric**: Based on group structure
✅ **Spectral**: Operator/eigenvalue methods  
✅ **Tested**: 29 comprehensive tests
✅ **Documented**: 460+ lines of docs

## Common Parameters

- `t` - Regularization parameter (default: 0.01-0.1)
- `num_points` - Discretization points (default: 100-1000)
- `tolerance` - Numerical tolerance (default: 1e-10 to 1e-12)
- `x_min`, `x_max` - Domain bounds

## Performance Tips

- Start with small `num_points` (20-50) for testing
- Increase `num_points` for production (100-1000)
- Adjust `t` parameter if numerical issues arise
- Use caching for repeated calculations

## Need Help?

- Full docs: `FOUR_PILLARS_README.md`
- Run demo: `python demo_four_pillars.py`
- Run tests: `pytest tests/test_four_pillars.py -v`
- Check examples in test file

## Citation

If using this code, please cite:
- Repository: github.com/motanova84/-jmmotaburr-riemann-adelic
- DOI: 10.5281/zenodo.17116291
- Author: José Manuel Mota Burruezo
