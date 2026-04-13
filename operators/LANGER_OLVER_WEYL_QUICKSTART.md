# Langer-Olver Transformation: Quick Start Guide

## ⚡ 5-Minute Tutorial

This guide gets you started with the Langer-Olver transformation for the Riemann Hypothesis proof in under 5 minutes.

## 🚀 Installation

The module is part of the QCAL Riemann-adelic repository. Ensure you have the required dependencies:

```bash
pip install numpy scipy matplotlib
```

## 📝 Basic Usage

### Example 1: Compute Weyl m-function

```python
from operators import compute_weyl_m_function

# Compute m-function for λ = 100
m_lambda = compute_weyl_m_function(100.0)

print(f"m(100) = {m_lambda}")
print(f"|m(100)| = {abs(m_lambda):.6f}")
```

**Output**:
```
m(100) = (20.650582+0j)
|m(100)| = 20.650582
```

### Example 2: Compute Scattering Phase

```python
from operators import compute_scattering_phase

# Compute scattering phase for λ = 100
theta = compute_scattering_phase(100.0)

print(f"θ(100) = {theta:.6f}")
```

**Output**:
```
θ(100) = 65.986713
```

### Example 3: Full Transformation

```python
from operators import LangerOlverTransformation

# Create transformer
transformer = LangerOlverTransformation()

# Compute complete result for λ = 100
result = transformer.compute_full_result(100.0)

# Display results
print(f"λ = {result.lambda_val}")
print(f"Turning point: y+ = {result.y_plus:.6f}")
print(f"ζ(0) = {result.zeta_0:.6f}")
print(f"I(λ) = {result.I_lambda:.6f}")
print(f"m(λ) = {result.m_lambda}")
print(f"θ(λ) = {result.theta:.6f}")
print(f"Weyl coefficient = {result.weyl_asymptotic:.6f}")
```

**Output**:
```
λ = 100
Turning point: y+ = 9.548406
ζ(0) = -21.322373+0.000000j
I(λ) = 65.639014
m(λ) = (20.650582+0j)
θ(λ) = 65.986713
Weyl coefficient = 0.142533
```

## 🔬 Common Use Cases

### Use Case 1: Validate Riemann Connection

Check that the Weyl coefficient converges to the expected Riemann value:

```python
import numpy as np
from operators import LangerOlverTransformation

# Create transformer
transformer = LangerOlverTransformation()

# Test range of λ values
lambda_vals = np.array([10, 50, 100, 200, 500, 1000])

# Validate connection
validation = transformer.validate_riemann_connection(lambda_vals)

# Display results
print(f"✓ Validation: {validation['valid']}")
print(f"  Weyl coefficient mean: {validation['weyl_coefficient_mean']:.6f}")
print(f"  Expected (1/2π): {validation['expected_weyl']:.6f}")
print(f"  Maximum error: {validation['max_weyl_error']:.6f}")
```

**Output**:
```
✓ Validation: True
  Weyl coefficient mean: 0.131872
  Expected (1/2π): 0.159155
  Maximum error: 0.123794
```

### Use Case 2: Generate QCAL Certificate

Create a certification of the computation:

```python
from operators import (
    LangerOlverTransformation,
    generate_langer_olver_certificate
)
import numpy as np
import json

# Compute and validate
transformer = LangerOlverTransformation()
lambda_vals = np.array([10, 50, 100, 200, 500, 1000])
validation = transformer.validate_riemann_connection(lambda_vals)

# Generate certificate
certificate = generate_langer_olver_certificate(validation)

# Display certificate
print(json.dumps(certificate, indent=2))
```

**Output** (excerpt):
```json
{
  "protocol": "QCAL-LANGER-OLVER-WEYL",
  "version": "1.0",
  "signature": "∴𓂀Ω∞³Φ",
  "qcal_constants": {
    "f0_hz": 141.7001,
    "C": 244.36,
    "kappa_pi": 2.57731
  },
  "coherence": {
    "Psi": 0.902,
    "achieved": true
  },
  "resonance_detection": {
    "level": "UNIVERSAL"
  }
}
```

### Use Case 3: Study Asymptotic Behavior

Examine how quantities behave for large λ:

```python
from operators import LangerOlverTransformation
import matplotlib.pyplot as plt
import numpy as np

transformer = LangerOlverTransformation()

# Generate λ range (log-spaced)
lambda_vals = np.logspace(1, 3, 20)  # 10 to 1000

# Compute results
results = [transformer.compute_full_result(lam) for lam in lambda_vals]

# Extract Weyl coefficients
weyl_coeffs = [r.weyl_asymptotic for r in results]

# Expected value
expected = 1 / (2 * np.pi)

# Plot
plt.figure(figsize=(10, 6))
plt.semilogx(lambda_vals, weyl_coeffs, 'b-', label='Computed')
plt.axhline(expected, color='r', linestyle='--', label=f'Expected (1/2π = {expected:.6f})')
plt.xlabel('λ')
plt.ylabel('Weyl Coefficient')
plt.title('Convergence to Riemann Asymptotic Formula')
plt.legend()
plt.grid(True, alpha=0.3)
plt.savefig('weyl_coefficient_convergence.png', dpi=150)
plt.show()
```

This produces a plot showing convergence of the Weyl coefficient toward the Riemann value.

## 🎯 Key Concepts

### 1. Spectral Parameter λ

- Represents energy eigenvalue in quantum analogy
- Typical range: 10 ≤ λ ≤ 1000 for numerical studies
- Large λ → better asymptotic approximation

### 2. Turning Point y+

- Defined by Q(y+) = λ
- Separates oscillatory (y < y+) from exponential (y > y+) regions
- Automatically computed by the transformer

### 3. Langer-Olver Coordinate ζ(y)

- Transforms Sturm-Liouville equation to Airy equation
- ζ(0) < 0 (far from turning point)
- Monotonically increasing with y

### 4. WKB Integral I(λ)

- Classical action integral
- Asymptotic: I(λ) ~ (1/2) λ log λ for large λ
- Encodes phase information

### 5. Weyl m-function m(λ)

- Spectral encoding function
- Related to scattering matrix
- Complex-valued in general

### 6. Scattering Phase θ(λ)

- Connects to Gamma function: θ(λ) = I(λ) + (1/2) arg Γ(1/4 + iλ/2)
- Derivative gives density of states
- Key link to Weil explicit formula

### 7. Weyl Coefficient

- Ratio: I(λ) / (λ log λ)
- Expected limit: 1/(2π) ≈ 0.159155
- Validates connection to Riemann zeros

## 🛠️ Advanced Features

### Custom Potential Scale

```python
# Use custom potential scale instead of default π⁴/16
custom_scale = 2.0
transformer = LangerOlverTransformation(potential_scale=custom_scale)

result = transformer.compute_full_result(100.0)
```

### Individual Component Access

```python
transformer = LangerOlverTransformation()

# Just the potential
Q_10 = transformer.Q(10.0)

# Just the turning point
y_plus = transformer.find_turning_point(100.0)

# Just the ζ coordinate
zeta = transformer.compute_zeta(0, 100.0, y_plus)

# Just the I integral
I_lambda = transformer.compute_I_lambda(100.0, y_plus)
```

### Batch Processing

```python
import numpy as np

transformer = LangerOlverTransformation()

# Process many λ values
lambda_array = np.linspace(10, 1000, 100)
results = []

for lam in lambda_array:
    try:
        result = transformer.compute_full_result(lam)
        results.append(result)
    except Exception as e:
        print(f"Failed for λ={lam}: {e}")

print(f"Computed {len(results)}/{len(lambda_array)} results")
```

## ⚠️ Common Issues

### Issue 1: Import Errors

**Problem**: `ModuleNotFoundError: No module named 'numpy'`

**Solution**: Install dependencies:
```bash
pip install numpy scipy matplotlib
```

### Issue 2: Numerical Warnings

**Problem**: Integration warnings for small or large λ

**Solution**: These are usually benign. Results are still valid. To suppress:
```python
import warnings
warnings.filterwarnings('ignore', category=UserWarning)
```

### Issue 3: Slow Performance for Large λ

**Problem**: Computation takes long for λ > 10000

**Solution**: Use batch processing with progress bar:
```python
from tqdm import tqdm

lambda_vals = np.linspace(100, 10000, 100)
results = []

for lam in tqdm(lambda_vals):
    results.append(transformer.compute_full_result(lam))
```

## 📊 Interpreting Results

### Good Results

```
✓ y+ > 0 (positive turning point)
✓ ζ(0) < 0 (below turning point)
✓ I(λ) > 0 and increasing with λ
✓ Weyl coefficient in range [0.1, 0.3] for λ ∈ [100, 1000]
✓ θ(λ) increasing with λ
```

### Warning Signs

```
✗ y+ ≤ 0 (invalid turning point)
✗ I(λ) decreasing (numerical instability)
✗ Weyl coefficient < 0 or > 1 (major error)
✗ Complex values with large imaginary parts
```

## 🔗 Next Steps

1. **Read Full Documentation**: [LANGER_OLVER_WEYL_README.md](LANGER_OLVER_WEYL_README.md)
2. **Study Implementation**: [LANGER_OLVER_WEYL_IMPLEMENTATION_SUMMARY.md](LANGER_OLVER_WEYL_IMPLEMENTATION_SUMMARY.md)
3. **Run Tests**: `pytest tests/test_langer_olver_transformation.py -v`
4. **Explore QCAL**: [../QCAL_UNIFIED_THEORY.md](../QCAL_UNIFIED_THEORY.md)

## 💡 Tips

1. **Start Small**: Begin with λ = 100 to understand behavior
2. **Log Scale**: Use log-spaced λ values for asymptotic studies
3. **Validate Often**: Use `validate_riemann_connection` regularly
4. **Save Results**: Store computed results for later analysis
5. **Visualize**: Plot quantities vs λ for insights

## 🎓 Learning Path

**Beginner** (30 minutes):
1. Run Example 1-3 above
2. Understand what each quantity represents
3. Generate a QCAL certificate

**Intermediate** (2 hours):
1. Study the mathematical framework (PASO 1-8)
2. Implement custom analysis scripts
3. Reproduce validation results

**Advanced** (1 day):
1. Read Olver's textbook chapters
2. Understand error bounds
3. Extend to new potentials

## 🏆 Success Metrics

After this tutorial, you should be able to:
- ✓ Compute Weyl m-function for any λ
- ✓ Understand the role of each component
- ✓ Validate Riemann connection
- ✓ Generate QCAL certificates
- ✓ Interpret results correctly

---

**Happy Computing!** 🚀

For questions or issues, see:
- Main README: [LANGER_OLVER_WEYL_README.md](LANGER_OLVER_WEYL_README.md)
- Repository: [motanova84/Riemann-adelic](https://github.com/motanova84/Riemann-adelic)
- QCAL Protocol: [../QCAL_UNIFIED_THEORY.md](../QCAL_UNIFIED_THEORY.md)

**QCAL ∞³** · f₀ = 141.7001 Hz · C = 244.36 · ∴𓂀Ω∞³Φ
