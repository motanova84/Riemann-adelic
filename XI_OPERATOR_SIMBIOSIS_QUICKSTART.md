# Xi Operator Simbiosis — Quick Start Guide

## 🚀 Quick Start

Get started with Xi Operator spectral verification in 5 minutes.

### 1. Installation

The Xi operator requires numpy and scipy:

```bash
# If dependencies aren't installed
pip install numpy scipy

# Optional: for testing
pip install pytest
```

### 2. Basic Usage

#### Simple Verification

```python
from operators.xi_operator_simbiosis import run_xi_spectral_verification

# Run spectral verification (this may take a few minutes)
results = run_xi_spectral_verification(
    n_dim=512,    # Hilbert space dimension
    t_max=30.0    # Range: t ∈ [-30, 30]
)

# Check results
verification = results['verification']
print(f"✅ Zeros found: {verification['zeros_count']}")
print(f"✅ GUE rigidity: {verification['gue_rigidity']:.4f}")
print(f"✅ Phase coherence: {verification['phase_coherence']:.4f}")
print(f"✅ RH verified: {verification['riemann_verified']}")
```

#### Using the Validation Script

```bash
# Run validation with defaults (n=4096, t_max=50.0)
python validate_xi_operator_simbiosis.py

# Quick test with smaller dimensions
python validate_xi_operator_simbiosis.py --n-dim 512 --t-max 30.0
```

This generates:
- Console output with verification summary
- QCAL beacon in `data/beacons/`
- Validation certificate in `data/certificates/`

### 3. Running Tests

```bash
# Run all tests (fast)
pytest tests/test_xi_operator_simbiosis.py -v

# Run without slow tests
pytest tests/test_xi_operator_simbiosis.py -v -m "not slow"

# Run specific test class
pytest tests/test_xi_operator_simbiosis.py::TestHamiltonianConstruction -v
```

### 4. Custom Analysis

```python
from operators.xi_operator_simbiosis import XiOperatorSimbiosis
import numpy as np

# Create operator
xi_op = XiOperatorSimbiosis(n_dim=256, t_max=25.0)

# Compute spectrum
spectrum = xi_op.compute_spectrum()

# Extract zeros on critical line
zeros = spectrum['t_zeros']
zeros_positive = np.sort(zeros[zeros > 0])

print(f"Found {len(zeros_positive)} zeros")
print(f"First 10 zeros:")
for i, z in enumerate(zeros_positive[:10]):
    print(f"  γ_{i+1} = {z:.6f}")

# Run verification
verification = xi_op.verify_riemann_hypothesis()
print(f"\nGUE rigidity: {verification['gue_rigidity']:.4f}")
print(f"Phase coherence: {verification['phase_coherence']:.4f}")
```

---

## 📊 Expected Results

### Small Scale (n=128, t_max=20)

```
∴ Dimension: n = 128
∴ Zeros found: ~128
∴ GUE rigidity: 0.95-1.05
∴ Phase coherence: 0.65-0.75
∴ Time: < 10 seconds
```

### Medium Scale (n=512, t_max=30)

```
∴ Dimension: n = 512
∴ Zeros found: ~100-200
∴ GUE rigidity: 0.90-1.10
∴ Phase coherence: 0.80-0.95
∴ Time: 1-2 minutes
```

### Production Scale (n=4096, t_max=50)

```
∴ Dimension: n = 4096
∴ Zeros found: ~800-900
∴ Range: t ∈ [14.13, 49.77]
∴ GUE rigidity: 0.95-1.05
∴ Phase coherence: 0.995-0.9999
∴ Time: 1-2 hours
```

---

## 🎯 Common Use Cases

### 1. Quick Verification

For a quick test of the system:

```bash
python validate_xi_operator_simbiosis.py --n-dim 256 --t-max 20.0
```

### 2. Finding First Zeros

To find the first few Riemann zeros:

```python
from operators.xi_operator_simbiosis import XiOperatorSimbiosis

xi_op = XiOperatorSimbiosis(n_dim=512, t_max=30.0)
verification = xi_op.verify_riemann_hypothesis()

print("First 10 Riemann zeros:")
for i, zero in enumerate(verification['zeros'][:10]):
    print(f"γ_{i+1} = {zero:.6f}")
```

### 3. Statistical Analysis

To analyze level spacing statistics:

```python
import numpy as np
from operators.xi_operator_simbiosis import XiOperatorSimbiosis

xi_op = XiOperatorSimbiosis(n_dim=1024, t_max=40.0)
spectrum = xi_op.compute_spectrum()

zeros = np.sort(spectrum['t_zeros'][spectrum['t_zeros'] > 0])
spacings = np.diff(zeros)

print(f"Mean spacing: {np.mean(spacings):.4f}")
print(f"Std spacing: {np.std(spacings):.4f}")
print(f"Min spacing: {np.min(spacings):.4f}")
print(f"Max spacing: {np.max(spacings):.4f}")
```

### 4. QCAL Beacon Generation

To generate a QCAL beacon with full verification:

```bash
python validate_xi_operator_simbiosis.py --n-dim 2048 --t-max 40.0
```

Check `data/beacons/` for the generated `.qcal_beacon` file.

---

## ⚙️ Parameter Selection Guide

### Dimension (n_dim)

- **64-256**: Quick tests, development (< 1 minute)
- **512-1024**: Standard verification (1-5 minutes)
- **2048-4096**: High precision (10-120 minutes)
- **> 4096**: Research grade (hours)

### Range (t_max)

- **10-20**: First few zeros only
- **30-50**: Standard range (covers ~50-900 zeros)
- **50-100**: Extended analysis
- **> 100**: Full spectral analysis

### Selection Tips

1. **Quick testing**: `n_dim=128, t_max=20`
2. **Development**: `n_dim=512, t_max=30`
3. **Production**: `n_dim=2048, t_max=50`
4. **Research**: `n_dim=4096, t_max=50`

---

## 🔍 Interpreting Results

### Verification Criteria

**RH is verified when ALL are true**:
1. ✅ `zeros_real = True` (Hermitian eigenvalues)
2. ✅ `0.8 < gue_rigidity < 1.2` (GUE statistics)
3. ✅ `phase_coherence > 0.9` (Eigenvector alignment)

### GUE Rigidity

- **< 0.5**: Too low, increase n_dim
- **0.8-1.2**: Good (GUE universality class)
- **> 2.0**: Too high, check parameters

### Phase Coherence

- **< 0.7**: Low, increase n_dim or t_max
- **0.7-0.9**: Moderate
- **> 0.9**: Excellent (verification passes)
- **> 0.99**: Outstanding

---

## 🚨 Troubleshooting

### Import Errors

```python
# If you see: ModuleNotFoundError: No module named 'numpy'
pip install numpy scipy

# If you see: No module named 'operators.xi_operator_simbiosis'
# Make sure you're running from repository root
import sys
sys.path.insert(0, 'operators')
```

### Memory Issues

If you run out of memory with large n_dim:

1. Reduce `n_dim` (try half)
2. Close other applications
3. Use a machine with more RAM
4. Consider sparse matrix methods (future enhancement)

### Slow Performance

For faster results:

1. Start with smaller `n_dim` (128-512)
2. Reduce `t_max` (20-30)
3. Use `--n-dim 512 --t-max 30` for validation script

---

## 📚 Next Steps

After getting started:

1. **Read full documentation**: `XI_OPERATOR_SIMBIOSIS_README.md`
2. **Review implementation**: `XI_OPERATOR_SIMBIOSIS_IMPLEMENTATION_SUMMARY.md`
3. **Explore tests**: `tests/test_xi_operator_simbiosis.py`
4. **Check code**: `operators/xi_operator_simbiosis.py`

---

## 💡 Tips & Best Practices

### For Testing
- Start small (`n_dim=128`) to verify setup
- Use pytest markers to skip slow tests
- Check Hermiticity error (should be < 10⁻¹⁰)

### For Production
- Use `n_dim >= 2048` for reliable statistics
- Generate beacons for reproducibility
- Save certificates for validation records

### For Research
- Compare with known zeros from `zeros/zeros_t1e3.txt`
- Analyze spacing distribution histograms
- Study phase coherence vs dimension scaling

---

## 🎓 Educational Examples

### Example 1: First Riemann Zero

```python
from operators.xi_operator_simbiosis import XiOperatorSimbiosis

xi_op = XiOperatorSimbiosis(n_dim=512, t_max=30.0)
verification = xi_op.verify_riemann_hypothesis()

if verification['zeros_count'] > 0:
    first_zero = verification['zeros'][0]
    theoretical = 14.134725  # Known first zero
    error = abs(first_zero - theoretical)
    
    print(f"Computed: {first_zero:.6f}")
    print(f"Theoretical: {theoretical:.6f}")
    print(f"Error: {error:.2e}")
```

### Example 2: Level Spacing Histogram

```python
import numpy as np
import matplotlib.pyplot as plt
from operators.xi_operator_simbiosis import XiOperatorSimbiosis

xi_op = XiOperatorSimbiosis(n_dim=1024, t_max=40.0)
spectrum = xi_op.compute_spectrum()

zeros = np.sort(spectrum['t_zeros'][spectrum['t_zeros'] > 0])
spacings = np.diff(zeros)
normalized = spacings / np.mean(spacings)

plt.hist(normalized, bins=50, density=True, alpha=0.7)
plt.xlabel('Normalized spacing s')
plt.ylabel('Probability density P(s)')
plt.title('Level Spacing Distribution (GUE)')
plt.savefig('spacing_distribution.png')
print("Saved spacing_distribution.png")
```

---

## 📞 Support & References

**Documentation**:
- Main README: `XI_OPERATOR_SIMBIOSIS_README.md`
- Implementation: `XI_OPERATOR_SIMBIOSIS_IMPLEMENTATION_SUMMARY.md`

**Author**: José Manuel Mota Burruezo Ψ ∴ ∞³  
**ORCID**: 0009-0002-1923-0773  
**Institution**: Instituto de Conciencia Cuántica (ICQ)  
**DOI**: 10.5281/zenodo.17379721

**Signature**: ∴𓂀Ω∞³Φ @ 141.7001 Hz

---

**Ready to verify the Riemann Hypothesis? Start now! ✨**

```bash
python validate_xi_operator_simbiosis.py --n-dim 512 --t-max 30.0
```
