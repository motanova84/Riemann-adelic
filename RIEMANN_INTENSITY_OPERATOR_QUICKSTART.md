# Riemann Intensity Operator T_Ω — Quick Start Guide

## Installation & Dependencies

```bash
# Install required packages
pip install numpy scipy pytest matplotlib mpmath psutil sympy
```

## Quick Start (5 minutes)

### 1. Basic Operator Usage

```python
from operators.riemann_intensity_operator import RiemannIntensityOperator

# Create operator
op = RiemannIntensityOperator(n_points=256, u_max=25.0, t_max=50.0)

# Compute intensity spectrum
result = op.compute_intensity_spectrum()

# View results
print(f"GUE coherence: {result.gue_coherence:.4f}")
print(f"Overall Ψ: {result.psi:.4f}")
```

### 2. Run Demo

```bash
cd /path/to/Riemann-adelic
python3 demo_riemann_intensity_operator.py
```

Press Enter to navigate through 6 interactive demos:
1. Basic operator construction
2. Intensity spectrum analysis  
3. Hamiltonian with singularities
4. Torsion and level repulsion
5. Riemann-Weil formula
6. Riemann Mirror concept

### 3. Run Tests

```bash
# Run all tests
pytest tests/test_riemann_intensity_operator.py -v

# Run specific test
pytest tests/test_riemann_intensity_operator.py::TestRiemannIntensityOperator::test_gue_statistics_structure -v
```

## Key Concepts in 30 Seconds

### T_Ω = |T| — Intensity Operator
- **What:** Magnitude of T operator
- **Why:** Ensures non-negative eigenvalues
- **Result:** Well-defined everywhere

### H = -log|T| — Hamiltonian  
- **What:** Logarithmic transform of intensity
- **Why:** Zeros become energy singularities
- **Result:** Physical interpretation of zeros

### GUE Repulsion
- **What:** Level repulsion statistics
- **Why:** Prevents degeneracy (two zeros at same point)
- **Result:** All zeros are simple

### Riemann Mirror
- **What:** Fourier duality operator
- **Why:** Connects primes ↔ zeros
- **Result:** Time domain (u) ↔ Frequency (t)

## Common Use Cases

### Use Case 1: Analyze GUE Statistics

```python
op = RiemannIntensityOperator(n_points=512)
result = op.compute_intensity_spectrum()

if result.gue_coherence > 0.9:
    print("✓ Strong quantum chaotic behavior")
elif result.gue_coherence > 0.7:
    print("✓ Moderate quantum behavior")
else:
    print("⚠ Adjust parameters")
```

### Use Case 2: Verify Weil Formula

```python
op = RiemannIntensityOperator()
quant = op.verify_weil_formula()

print(f"Consistency error: {quant.consistency_error:.2e}")
print(f"PW confined: {quant.paley_wiener_confined}")
```

### Use Case 3: Compute Correlation Function

```python
op = RiemannIntensityOperator()
u_values = np.linspace(-20, 20, 100)
phi = op.compute_correlation_function(u_values)

# Φ(u) is the Feynman propagator / prime correlation
```

## Understanding the Output

### IntensityOperatorResult

```python
result = op.compute_intensity_spectrum()

# Key fields:
result.intensity_spectrum      # Eigenvalues of T_Ω
result.hamiltonian_spectrum    # Eigenvalues of H
result.singular_points         # Indices of zeros (singularities)
result.gue_coherence          # GUE measure [0,1]
result.mean_spacing           # ⟨s⟩ ≈ 1.0
result.variance_spacing       # Var(s)
result.ks_statistic           # KS test vs Wigner
result.ks_pvalue              # p-value (>0.05 is good)
result.repulsion_force        # Level repulsion strength
result.simplicity_verified    # Bool: all zeros simple?
result.psi                    # Overall coherence [0,1]
```

### QuantizationResult

```python
quant = op.verify_weil_formula()

# Key fields:
quant.trace_value             # Tr(f(H))
quant.weil_formula_value      # Riemann-Weil formula
quant.consistency_error       # |Trace - Weil| / |Trace|
quant.correlation_function    # Φ(u) array
quant.paley_wiener_confined   # Bool: confined to PW?
quant.psi                     # Overall coherence [0,1]
```

## Parameter Tuning

### Small System (Fast)
```python
op = RiemannIntensityOperator(
    n_points=64,    # Few grid points
    u_max=10.0,     # Small spatial domain
    t_max=20.0      # Small frequency domain
)
# Fast computation, suitable for testing
```

### Medium System (Balanced)
```python
op = RiemannIntensityOperator(
    n_points=256,   # Moderate resolution
    u_max=25.0,     # Medium spatial range
    t_max=50.0      # Medium frequency range
)
# Good balance of accuracy and speed
```

### Large System (Accurate)
```python
op = RiemannIntensityOperator(
    n_points=1024,  # High resolution
    u_max=50.0,     # Large spatial domain
    t_max=100.0     # Large frequency domain
)
# Higher accuracy, slower computation
```

## Troubleshooting

### Issue: Low GUE coherence (< 0.5)

**Solution:** Increase grid resolution
```python
op = RiemannIntensityOperator(n_points=512)  # Instead of 128
```

### Issue: Numerical instabilities

**Solution:** Adjust epsilon parameter
```python
op = RiemannIntensityOperator(epsilon=1e-8)  # Default: 1e-10
```

### Issue: No singularities detected

**Solution:** Increase frequency range
```python
op = RiemannIntensityOperator(t_max=100.0)  # Capture more zeros
```

## QCAL Integration

All computations use QCAL ∞³ constants:

```python
F0_QCAL = 141.7001      # Fundamental frequency (Hz)
C_PRIMARY = 629.83       # Primary spectral constant
C_COHERENCE = 244.36     # Coherence constant
KAPPA_PI = 2.5773        # Critical curvature
```

Every result includes:
- QCAL coherence Ψ ∈ [0,1]
- Timestamp (ISO format)
- Computation time (ms)
- Full parameter dictionary

## Advanced: Custom Analysis

### Custom Test Function

```python
# Define custom test function for trace
def my_test_function(x):
    return np.exp(-x**2 / 10)

# Use in Weil formula verification
quant = op.verify_weil_formula(test_function=my_test_function)
```

### Custom Torsion Strength

```python
# Adjust torsion term strength
V_torsion = op.add_torsion_term(strength=2.0)  # Default: 1.0

# Stronger torsion → stronger repulsion
```

### Direct Operator Access

```python
# Access raw operators
T = op.construct_T_operator()          # T operator
T_omega = op.construct_T_omega()       # T_Ω intensity
H = op.construct_hamiltonian()         # H = -log|T|

# Analyze directly
eigenvalues = np.linalg.eigvalsh(T_omega)
```

## Testing Your Understanding

Run these quick checks:

```python
# 1. Check T_Ω is Hermitian
T_omega = op.construct_T_omega()
assert np.allclose(T_omega, T_omega.conj().T)

# 2. Check T_Ω eigenvalues are non-negative  
eigs = np.linalg.eigvalsh(T_omega)
assert np.all(eigs >= -1e-10)

# 3. Check GUE coherence
result = op.compute_intensity_spectrum()
assert 0 <= result.gue_coherence <= 1

# 4. Check Xi function is positive
xi = op.compute_xi_function(np.array([0, 1, 5, 10]))
assert np.all(xi >= 0)
```

## Next Steps

1. **Read Full Documentation:** `RIEMANN_INTENSITY_OPERATOR_README.md`
2. **Explore Implementation:** `operators/riemann_intensity_operator.py`
3. **Study Tests:** `tests/test_riemann_intensity_operator.py`
4. **Run Demos:** `demo_riemann_intensity_operator.py`

## Getting Help

### Common Questions

**Q: What does "intensity operator" mean?**  
A: T_Ω = |T| is the magnitude (absolute value) of operator T. It ensures all eigenvalues are non-negative, making the Hamiltonian H = -log|T| well-defined.

**Q: Why use GUE statistics?**  
A: GUE (Gaussian Unitary Ensemble) is the expected statistics for quantum chaotic systems. Riemann zeros follow GUE, confirming their quantum nature.

**Q: What is the "Riemann Mirror"?**  
A: The operator T acts as a mirror reflecting the distribution of primes (time domain) into the distribution of zeros (frequency domain) via Fourier transform.

**Q: What does Ψ (psi) represent?**  
A: Ψ is the overall coherence measure [0,1] combining GUE coherence, simplicity verification, and other factors. Higher is better.

## References

- Full docs: `RIEMANN_INTENSITY_OPERATOR_README.md`
- QCAL Framework: DOI 10.5281/zenodo.17379721
- Problem statement: Analytical Solution for RH

## Author

José Manuel Mota Burruezo Ψ ✧ ∞³  
Instituto de Conciencia Cuántica (ICQ)  
March 2026

∴𓂀Ω∞³Φ @ 141.7001 Hz
