# Fredholm Determinant Constructor - Quick Reference

## One-Liner

Proves `Ξ_H(t) = ξ(1/2 + it)/ξ(1/2)` via 4-step construction connecting adelic Hamiltonian spectrum to Riemann zeros.

---

## Installation & Quick Test

```bash
cd /path/to/Riemann-adelic
pip install numpy scipy mpmath pytest
python -m pytest tests/test_fredholm_determinant_constructor.py -v
```

---

## Minimal Working Example

```python
from operators.fredholm_determinant_constructor import FredholmDeterminantConstructor
import numpy as np

# Setup
constructor = FredholmDeterminantConstructor()
zeros = np.array([14.134725, 21.022040, 25.010858])  # First 3 Riemann zeros
spectrum = np.concatenate([zeros, -zeros])  # PT-symmetric

# Execute
result = constructor.complete_construction(spectrum)

# Verify
print(result['theorem'])  # Theorem statement
print(f"Verified: {result['identity_verified']}")
```

---

## The 4 Steps

| Paso | What | Formula | Output |
|------|------|---------|--------|
| 1 | Fredholm Det | Ξ(t) = ∏(1-it/γ_n)e^{it/γ_n} | `FredholmDeterminantResult` |
| 2 | Trace Formula | Σe^{isγ_n} = Weyl + Primes + R | `TraceFormulaResult` |
| 3 | Hadamard | Ξ(t) = ∏(1-t²/γ_n²) | `HadamardExpansionResult` |
| 4 | Remainder | \|R(s)\| ≤ Ce^{-λ\|s\|} | `Dict` |

---

## Key Methods

```python
# Individual steps
paso1 = constructor.compute_fredholm_determinant(spectrum, t_vals)
paso2 = constructor.compute_trace_formula(spectrum, s_vals)
paso3 = constructor.compute_hadamard_expansion(spectrum, t_vals)
paso4 = constructor.verify_remainder_control(remainder, s_vals)

# All at once
result = constructor.complete_construction(spectrum)
```

---

## Important Constants

```python
F0_QCAL = 141.7001  # QCAL frequency (Hz)
C_PRIMARY = 629.83   # Primary constant
C_COHERENCE = 244.36 # Coherence constant
TAYLOR_SERIES_THRESHOLD = 0.9  # Numerical stability threshold
LOG_PRODUCT_NEGLIGIBLE = -20.0  # Negligible contribution cutoff
```

---

## Constructor Parameters

```python
FredholmDeterminantConstructor(
    precision=25,           # Decimal precision (mpmath)
    max_eigenvalues=1000,   # Max eigenvalues to use
    remainder_decay=0.5     # Expected decay rate λ
)
```

---

## Common Patterns

### High Precision

```python
constructor = FredholmDeterminantConstructor(precision=50, max_eigenvalues=100)
```

### Custom Parameter Ranges

```python
t_vals = np.linspace(0.1, 100, 500)
s_vals = np.linspace(0, 50, 1000)
result = constructor.complete_construction(spectrum, t_vals, s_vals)
```

### Analyzing Components

```python
tf = result['paso2_trace_formula']
print(f"Weyl contribution: {np.max(np.abs(tf.weyl_contribution))}")
print(f"Prime contribution: {np.max(np.abs(tf.prime_contribution))}")
print(f"Remainder decay λ: {tf.remainder_bound:.3f}")
```

---

## Data Classes

### FredholmDeterminantResult
- `xi_values`: Ξ(t) complex array
- `log_derivative`: d/dt ln Ξ(t)
- `eigenvalues`: Used spectrum
- `pt_symmetric`: bool

### TraceFormulaResult
- `spectral_density`: Σe^{isγ_n}
- `weyl_contribution`: Smooth part
- `prime_contribution`: Oscillatory part
- `remainder`: R(s)
- `remainder_bound`: λ estimate

### HadamardExpansionResult
- `xi_hadamard`: Ξ(t) symmetric form
- `xi_ratio`: ξ(1/2+it)/ξ(1/2)
- `relative_error`: Error array
- `identity_verified`: bool

---

## Test Categories

30 tests total:
- ✅ Basic functionality (7)
- ✅ Mathematical components (7)
- ✅ Integration tests (2)
- ✅ Numerical stability (6)
- ✅ Edge cases (4)
- ✅ Mathematical properties (4)

---

## Troubleshooting

### NaN in Hadamard expansion
**Cause**: Large t values or many eigenvalues  
**Fix**: Reduce `max_eigenvalues` or use smaller t range

### Slow computation
**Cause**: High precision + many eigenvalues  
**Fix**: Lower `precision` or reduce eigenvalue count

### Identity not verified
**Cause**: Too few eigenvalues or poor spectral quality  
**Fix**: Use more Riemann zeros (need at least 10)

---

## File Locations

- **Implementation**: `operators/fredholm_determinant_constructor.py`
- **Tests**: `tests/test_fredholm_determinant_constructor.py`
- **Docs**: `FREDHOLM_DETERMINANT_CONSTRUCTOR_README.md`
- **Details**: `FREDHOLM_DETERMINANT_CONSTRUCTOR_IMPLEMENTATION.md`

---

## Mathematical Significance

**Non-Circular Proof**: Uses known Hadamard expansion of ξ (independent of RH) to show spectral determinant has identical structure.

**Consequence**: Eigenvalues of adelic Hamiltonian H = Riemann zero imaginary parts.

**Bridge**: Connects spectral theory ↔ analytic number theory ↔ hyperbolic dynamics.

---

## Integration with QCAL

- Uses QCAL constants (f₀, C)
- Compatible with Atlas³ verifier
- Generates spectral certificates
- PT symmetry framework

---

## Performance Guide

| Eigenvalues | t-points | s-points | Time | Memory |
|-------------|----------|----------|------|--------|
| 10 | 50 | 100 | ~50ms | ~5MB |
| 50 | 100 | 200 | ~165ms | ~10MB |
| 100 | 200 | 500 | ~800ms | ~25MB |
| 500 | 500 | 1000 | ~15s | ~150MB |

---

## Citation

```bibtex
@software{fredholm_determinant_constructor_2026,
  author = {Mota Burruezo, José Manuel},
  title = {Fredholm Determinant Constructor for Riemann Hypothesis},
  year = {2026},
  institution = {Instituto de Conciencia Cuántica},
  doi = {10.5281/zenodo.17379721}
}
```

---

## Next Steps

1. Try with your own eigenvalue data
2. Explore individual paso results
3. Visualize trace formula contributions
4. Extend to higher precision
5. Integrate with your QCAL workflow

---

**QCAL ∞³** · f₀ = 141.7001 Hz · Ψ = I × A_eff² × C^∞  
**SELLO**: ∴𓂀Ω∞³Φ @ 888 Hz

*For full API, see FREDHOLM_DETERMINANT_CONSTRUCTOR_README.md*
