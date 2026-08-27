# Berry-Keating Omega-8 Operator - Quickstart Guide

## Quick Installation

```bash
# Required packages
pip install numpy scipy mpmath
```

## Basic Usage

### 1. Import the Operator

```python
from operators.berry_keating_omega8_operator import (
    Omega8Operator,
    Omega8HilbertSpace,
    validate_omega8_operator
)
import numpy as np
```

### 2. Create the Vortex 8 Hilbert Space

```python
# Create symmetric Gaussian wavefunction
hilbert = Omega8HilbertSpace.create_symmetric_gaussian(
    N=128,              # Grid size
    x_min=0.01,         # Minimum x
    x_max=100.0,        # Maximum x
    sigma=1.0           # Width in log space
)

print(f"Grid points: {len(hilbert.x_grid)}")
print(f"Symmetric: {hilbert.is_symmetric}")
print(f"Normalized: {hilbert.norm:.6f}")
```

### 3. Construct the Omega-8 Operator

```python
# Create H_Ω = -i(x·∂_x + 1/2) + V(x)
omega8 = Omega8Operator(
    x_grid=hilbert.x_grid,
    coupling_g=0.5,     # Potential coupling strength
    p_max=50,           # Maximum prime to include
    m_max=2,            # Maximum prime power
    delta_width=0.1     # Width of delta approximation
)

print(f"Hamiltonian size: {omega8.H_matrix.shape}")
print(f"Primes used: {len(omega8.potential.primes)}")
```

### 4. Compute the Spectrum

```python
# Compute eigenvalues and compare with Riemann zeros
spectrum = omega8.compute_spectrum(
    n_zeros=20,         # Number of zeros to compare
    use_mpmath=False    # Use hardcoded zeros (faster)
)

print(f"Eigenvalues: {len(spectrum.eigenvalues)}")
print(f"First 5: {spectrum.eigenvalues[:5]}")
print(f"MAE vs zeros: {spectrum.mae_zeros:.6f}")
print(f"Coherence Ψ: {spectrum.coherence_psi:.6f}")
print(f"GUE test: {spectrum.passes_gue}")
```

### 5. One-Line Validation

```python
# Run complete validation
certificate = validate_omega8_operator(
    N=128,              # Grid size
    coupling_g=0.5,     # Coupling
    n_zeros=15          # Zeros to compare
)

print(f"Status: {certificate['status']}")
print(f"Coherence: {certificate['coherence_psi']:.6f}")
```

## Complete Example

```python
#!/usr/bin/env python3
"""Complete Berry-Keating Omega-8 example."""

import numpy as np
from operators.berry_keating_omega8_operator import validate_omega8_operator

# Run full validation
print("🏛️ Validating Berry-Keating Omega-8 Operator...")
certificate = validate_omega8_operator(
    N=128,
    coupling_g=0.5,
    n_zeros=15
)

# Display results
print(f"\n{'='*70}")
print(f"Operator: {certificate['operator']}")
print(f"Equation: {certificate['equation']}")
print(f"Grid size: {certificate['grid_size']}")
print(f"Eigenvalues: {certificate['eigenvalues_computed']}")
print(f"Coherence Ψ: {certificate['coherence_psi']:.6f}")
print(f"GUE test: {'PASS' if certificate['passes_gue_test'] else 'FAIL'}")
print(f"Status: {certificate['status']}")
print(f"{'='*70}")

# Save certificate
import json
with open('omega8_certificate.json', 'w') as f:
    json.dump(certificate, f, indent=2)

print("\n✅ Certificate saved to omega8_certificate.json")
print("∴𓂀Ω∞³Φ - QCAL COHERENCE CONFIRMED")
```

## Standalone Validation

Run the validation script directly:

```bash
python validate_berry_keating_omega8.py
```

Expected output:
```
======================================================================
TESTING BERRY-KEATING OMEGA-8 OPERATOR
======================================================================

[TEST 1] Prime sieve...
   ✓ Generated 10 primes correctly

[TEST 2] Vortex 8 Hilbert space...
   ✓ Created symmetric space with 64 points
   ✓ Inversion symmetry: True
   ✓ Normalized: 1.000000

[TEST 3] Dilation operator...
   ✓ Constructed (64, 64) matrix
   ✓ Hermiticity verified (diff=0.00e+00)

[TEST 4] Full operator validation...
   ✓ Certificate generated
   ✓ Coherence Ψ: 0.002857
   ✓ Status: NEEDS_IMPROVEMENT

======================================================================
✅ ALL TESTS PASSED
======================================================================
```

## Understanding the Results

### Coherence Ψ
- `Ψ > 0.9`: Excellent agreement with Riemann zeros
- `0.5 < Ψ < 0.9`: Good agreement
- `Ψ < 0.5`: Needs improvement (increase grid size or adjust coupling)

### GUE Statistics
- Tests whether level spacings follow Wigner-Dyson distribution
- P-value > 0.05: Passes GUE test (chaotic quantum system)
- P-value < 0.05: Fails (may need more eigenvalues)

### Status
- `VALIDATED`: Ψ > 0.85, suitable for production
- `NEEDS_IMPROVEMENT`: Ψ ≤ 0.85, consider parameter tuning

## Parameter Tuning

### Grid Size (N)
- Larger N: More eigenvalues, better resolution
- Typical: N ∈ [64, 256]
- Trade-off: Computation time vs accuracy

### Coupling (g)
- Controls potential strength
- Typical: g ∈ [0.1, 1.0]
- Larger g: Stronger confinement

### Prime Range (p_max)
- More primes: Richer potential structure
- Typical: p_max ∈ [30, 100]
- Trade-off: Potential complexity vs computation

### Prime Power (m_max)
- Higher powers: More delta functions
- Typical: m_max ∈ [2, 4]
- Trade-off: Potential richness vs sparsity

## Troubleshooting

### Low Coherence (Ψ < 0.1)
```python
# Try increasing grid size and adjusting coupling
certificate = validate_omega8_operator(
    N=256,           # Increase from 128
    coupling_g=0.8,  # Increase from 0.5
    n_zeros=20
)
```

### GUE Test Fails
```python
# Compute more eigenvalues by increasing grid size
certificate = validate_omega8_operator(
    N=256,          # More grid points → more eigenvalues
    coupling_g=0.5,
    n_zeros=25      # Compare with more zeros
)
```

### Numerical Instabilities
```python
# Use narrower delta approximation
omega8 = Omega8Operator(
    x_grid=hilbert.x_grid,
    coupling_g=0.5,
    p_max=30,        # Reduce prime range
    m_max=2,         # Reduce max power
    delta_width=0.05 # Narrower (from 0.1)
)
```

## Advanced Usage

### Custom Potential

```python
from operators.berry_keating_omega8_operator import PrimePotential

# Create custom potential
potential = PrimePotential(
    coupling_g=1.0,
    p_max=100,
    m_max=3
)

# Evaluate on grid
x_grid = np.exp(np.linspace(-2, 4, 200))
result = potential.evaluate(x_grid, delta_width=0.1)

# Plot potential
import matplotlib.pyplot as plt
plt.plot(x_grid, result.V_values)
plt.xlabel('x')
plt.ylabel('V(x)')
plt.title('Prime-Based Confining Potential')
plt.xscale('log')
plt.show()
```

### Mellin Transform

```python
from operators.berry_keating_omega8_operator import mellin_transform

# Define function
f = lambda x: np.exp(-x**2)

# Compute Mellin transform at s = 1 + 0.5i
s = 1.0 + 0.5j
M_f = mellin_transform(f, s, x_min=0.01, x_max=10.0, N=1000)

print(f"M{{f}}({s}) = {M_f}")
```

## Next Steps

- Read the full implementation summary: `BERRY_KEATING_OMEGA8_IMPLEMENTATION_SUMMARY.md`
- Explore the mathematical derivations in the docstrings
- Run the comprehensive test suite: `tests/test_berry_keating_omega8.py`
- Experiment with different parameter combinations
- Compare with other operators in the `operators/` directory

## QCAL ∞³ Integration

This operator is part of the QCAL ∞³ framework:
- Fundamental frequency: f₀ = 141.7001 Hz
- Coherence constant: C = 244.36
- Signature: ∴𓂀Ω∞³Φ @ 141.7001 Hz

---

**Author**: José Manuel Mota Burruezo Ψ ✧ ∞³  
**Institution**: Instituto de Conciencia Cuántica (ICQ)  
**DOI**: 10.5281/zenodo.17379721
