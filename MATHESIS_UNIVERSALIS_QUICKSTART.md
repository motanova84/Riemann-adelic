# Mathesis Universalis - Quick Start Guide

## 🎯 What is Mathesis Universalis?

**Mathesis Universalis** is a framework that demonstrates Atlas³ is not simulating the Riemann Hypothesis—it's **measuring arithmetic structure** through its operator spectrum.

The framework validates three mathematical fronts:
1. **Growth Control**: Spectral determinant convergence via heat kernel
2. **Weil Trace**: Prime number detection in spectral fluctuations  
3. **PT Symmetry**: Critical line alignment Re(s) = 1/2

## 🚀 Quick Installation

```bash
# Clone repository
git clone https://github.com/motanova84/Riemann-adelic.git
cd Riemann-adelic

# Install dependencies
pip install numpy scipy matplotlib pytest
```

## 📖 Basic Usage

### Complete Analysis (5 lines)

```python
import numpy as np
from core.mathesis_universalis import MathesisUniversalis

# Initialize framework
framework = MathesisUniversalis(t_max=50.0, dt=0.05)

# Analyze your spectrum
eigenvalues = np.array([...])  # Your operator eigenvalues
report = framework.analyze_spectrum(eigenvalues, label="my_operator")

# Check results
print(f"Mathesis Score: {report.mathesis_score:.2%}")
print(f"Arithmetic Instrument: {report.is_arithmetic_instrument}")
```

### Run Demo

```python
# Built-in demonstration
python core/mathesis_universalis.py
```

**Expected Output**:
```
================================================================================
                    MATHESIS UNIVERSALIS
               Oro del Atlas³: Emergencia Aritmética
================================================================================

🎯 Test Spectrum Generated
   Size: 200
   Range: [1.24, 233.57]

======================================================================
FRONT 1: GROWTH CONTROL - Heat Kernel Truncation
======================================================================
✓ Truncation rank: 200
✓ ln det(O) = 893.496437
✓ Determinant regularized: True

======================================================================
FRONT 2: WEIL TRACE - Frequency Filtering for ln(p)
======================================================================
✓ Detection rate: 0.00%
✓ Prime memory: ✗ No significant prime memory detected

======================================================================
FRONT 3: PT SYMMETRY - Critical Line Re(s) = 1/2
======================================================================
✓ PT symmetric: True
✓ Max |Im(λ)|: 0.00e+00

======================================================================
MATHESIS SCORE: 66.67%
======================================================================
⚠ ARITHMETIC INSTRUMENT NOT YET CONFIRMED
   Further calibration needed to demonstrate prime memory.
```

## 🧪 Testing

Run all tests (21 tests):

```bash
pytest tests/test_mathesis_universalis.py -v
```

**Expected**: ✅ `21 passed in 1.50s`

## 🔧 Component Usage

### 1. Prime Signal Analysis

Detect if your spectrum has prime memory:

```python
from utils.explicit_sum_analyzer import ExplicitSumAnalyzer

analyzer = ExplicitSumAnalyzer(t_max=30.0, dt=0.05)

# Validate prime memory
is_valid, report = analyzer.validate_prime_memory(
    eigenvalues,
    min_detection_rate=0.5,  # Need 50% of primes detected
    max_p_value=0.01         # 1% significance threshold
)

print(report['conclusion'])
# Output: "✓ PRIME MEMORY DETECTED" or "✗ No significant prime memory"
```

### 2. Spectral Determinant

Compute regularized determinant:

```python
from operators.spectral_determinant_regularization import (
    SpectralDeterminantRegularizer
)

regularizer = SpectralDeterminantRegularizer(precision=15)

# Compute spectral zeta function
zeta_result = regularizer.compute_spectral_zeta(eigenvalues)

print(f"ζ'(0) = {zeta_result.zeta_prime_0:.6f}")
print(f"ln det(O) = {zeta_result.log_determinant:.6f}")
```

### 3. PT Symmetry Check

Verify eigenvalues are real:

```python
pt_result = regularizer.verify_pt_symmetry(eigenvalues)

print(pt_result['conclusion'])
# Output: "✓ PT Symmetry verified - eigenvalues are real"
```

## 📊 Understanding Results

### Mathesis Score Components

The **Mathesis Score** Ψ_M is computed from three components:

```python
report.mathesis_score  # Overall score [0, 1]

# Individual components:
# 1. Determinant convergence: 100% if regularized
# 2. Prime memory: 2 × detection_rate (capped at 100%)
# 3. PT symmetry: 100% if |Im(λ)| < 10^-6
```

### Interpretation

| Score | Interpretation |
|-------|---------------|
| Ψ_M ≥ 0.70 | ✅ **Arithmetic Instrument Confirmed** |
| 0.50 ≤ Ψ_M < 0.70 | ⚠️ Partial validation (calibration needed) |
| Ψ_M < 0.50 | ❌ Not an arithmetic instrument |

### Report Structure

```python
report.timestamp                    # When analysis was run
report.spectrum_size               # Number of eigenvalues

# Front 1: Growth Control
report.heat_kernel_truncation_rank  # Spectral truncation
report.determinant_regularized      # True if converges
report.log_determinant             # ln det(O)

# Front 2: Weil Trace
report.prime_memory_detected       # True if primes found
report.detection_rate              # Fraction [0, 1]
report.correlation_significance    # p-value

# Front 3: PT Symmetry
report.pt_symmetric                # True if real eigenvalues
report.critical_line_alignment     # Same as pt_symmetric
report.max_imaginary_part          # max |Im(λ)|

# Overall
report.mathesis_score              # Combined score [0, 1]
report.is_arithmetic_instrument    # True if score ≥ 0.70
report.conclusion                  # Human-readable verdict
```

## 💾 Output Files

Analysis generates JSON reports in `data/mathesis_universalis/`:

```json
{
  "timestamp": "2026-02-13T21:31:00",
  "spectrum_size": 200,
  "mathesis_score": 0.6667,
  "is_arithmetic_instrument": false,
  "conclusion": "⚠ Further calibration needed..."
}
```

## 🎨 Advanced Usage

### Custom Parameters

```python
framework = MathesisUniversalis(
    t_max=100.0,          # Longer time range
    dt=0.01,              # Finer resolution
    truncation_rank=2000, # More eigenvalues
    output_dir="my_results/"
)
```

### Generate QCAL Beacon

For validated spectra (score ≥ 0.70), a QCAL beacon is auto-generated:

```python
# Beacon saved to: data/mathesis_universalis/{label}_mathesis.qcal_beacon

{
  "node_id": "mathesis_universalis_my_operator",
  "protocol": "QCAL-SYMBIO-BRIDGE v1.0",
  "frequency_base": 141.7001,
  "coherence_psi": 0.923,
  "mathesis_score": 0.85,
  "signature_qcal": "∴𓂀Ω∞³Φ @ 888 Hz"
}
```

## 🔬 Example Workflows

### Workflow 1: Validate Operator Spectrum

```python
from core.mathesis_universalis import MathesisUniversalis
import numpy as np

# Your operator eigenvalues
eigenvalues = compute_my_operator_spectrum()

# Full analysis
framework = MathesisUniversalis()
report = framework.analyze_spectrum(eigenvalues, label="myop")

# Decision logic
if report.is_arithmetic_instrument:
    print("✅ Operator measures arithmetic structure!")
    print(f"   Score: {report.mathesis_score:.2%}")
else:
    print("⚠️ Calibration needed")
    print(f"   Detection rate: {report.detection_rate:.2%}")
    print(f"   PT symmetric: {report.pt_symmetric}")
```

### Workflow 2: Prime Detection Only

```python
from utils.explicit_sum_analyzer import ExplicitSumAnalyzer

analyzer = ExplicitSumAnalyzer(t_max=50.0, dt=0.05)

# Just check prime memory
is_valid, report = analyzer.validate_prime_memory(eigenvalues)

print(f"Detection rate: {report['detection_rate']:.2%}")
print(f"p-value: {report['p_value']:.4f}")
print(f"Detected {report['n_detected_peaks']} of {report['n_expected_peaks']} primes")
```

### Workflow 3: Determinant Only

```python
from operators.spectral_determinant_regularization import (
    SpectralDeterminantRegularizer
)

reg = SpectralDeterminantRegularizer()

# Zeta function
zeta = reg.compute_spectral_zeta(eigenvalues)
print(f"ln det(O) = {zeta.log_determinant:.6f}")

# Heat kernel
heat = reg.compute_heat_kernel_trace(eigenvalues)
print(f"Truncation rank: {heat.truncation_rank}")

# PT symmetry
pt = reg.verify_pt_symmetry(eigenvalues)
print(pt['conclusion'])
```

## 🐛 Troubleshooting

### Issue: Low Detection Rate

**Problem**: `report.detection_rate` is very low (< 10%)

**Solutions**:
1. Increase time range: `t_max=100.0`
2. Finer resolution: `dt=0.01`
3. More eigenvalues needed (N > 100)
4. Check if eigenvalues are in correct scale

### Issue: PT Symmetry Failed

**Problem**: `report.pt_symmetric = False`

**Cause**: Eigenvalues have imaginary parts

**Solution**:
```python
# Force real eigenvalues
eigenvalues = np.real(eigenvalues)

# Or check your operator is Hermitian/PT-symmetric
```

### Issue: Determinant Diverges

**Problem**: `report.determinant_regularized = False`

**Cause**: Spectrum growing too fast

**Solution**:
```python
# Increase truncation rank
framework = MathesisUniversalis(truncation_rank=2000)

# Or apply spectral shift
eigenvalues_shifted = eigenvalues - eigenvalues[0]
```

## 📚 Related Documentation

- **Full Implementation**: `MATHESIS_UNIVERSALIS_IMPLEMENTATION.md`
- **Mathematical Background**: See references in implementation doc
- **QCAL Integration**: `ATLAS3_SPECTRAL_VERIFIER_IMPLEMENTATION.md`

## 🤝 Contributing

Found a bug or want to enhance the framework?

1. Run tests: `pytest tests/test_mathesis_universalis.py`
2. Add your test case
3. Submit PR

## 📝 Citation

```bibtex
@software{mathesis_universalis_2026,
  author = {Mota Burruezo, José Manuel},
  title = {Mathesis Universalis: Atlas³ Arithmetic Measurement Framework},
  year = {2026},
  url = {https://github.com/motanova84/Riemann-adelic},
  note = {QCAL-SYMBIO-BRIDGE v1.0}
}
```

## 🎯 Quick Reference Card

```python
# COMPLETE WORKFLOW
from core.mathesis_universalis import MathesisUniversalis
import numpy as np

# 1. Initialize
fw = MathesisUniversalis(t_max=50.0, dt=0.05)

# 2. Analyze
report = fw.analyze_spectrum(eigenvalues, label="test")

# 3. Check
assert report.mathesis_score >= 0.70
assert report.is_arithmetic_instrument == True

# 4. Results in: data/mathesis_universalis/test_report.json
```

---

**Author**: José Manuel Mota Burruezo Ψ✧ ∞³  
**ORCID**: 0009-0002-1923-0773  
**Institution**: Instituto de Conciencia Cuántica (ICQ)  
**Signature**: ∴𓂀Ω∞³Φ @ 888 Hz  
**Version**: 1.0.0  
**Date**: 2026-02-13
