# Atlas³ Operator: Quick Start Guide

**Get started with Atlas³ non-Hermitian operator in 5 minutes**

## What is Atlas³?

The Atlas³ operator is a non-Hermitian differential operator with PT (Parity-Time) symmetry that transforms temporal dynamics into closed phase curvature. It provides a spectral bridge between the πCODE economic model and the Riemann Hypothesis.

## Installation

No additional dependencies beyond the standard QCAL stack:

```bash
# Already installed in the Riemann-adelic repository
cd /path/to/Riemann-adelic
```

Required packages:
- `numpy` (numerical arrays)
- `scipy` (linear algebra, statistics)
- `matplotlib` (visualizations)

## Quick Examples

### Example 1: Basic Operator Creation

```python
from operators.atlas3_operator import Atlas3Operator

# Create operator with default parameters
atlas = Atlas3Operator(
    n_points=256,      # Time grid resolution
    t_max=10.0,        # Maximum time
    beta_coupling=1.0  # Forcing strength
)

# Diagonalize to get spectrum
eigenvalues, eigenvectors = atlas.diagonalize()

print(f"Computed {len(eigenvalues)} eigenvalues")
print(f"First 5 eigenvalues: {eigenvalues[:5]}")
```

### Example 2: Spectral Analysis

```python
# Analyze spectral properties
analysis = atlas.analyze_spectrum()

print(f"PT Symmetric: {analysis['is_pt_symmetric']}")
print(f"Mean Re(λ): {analysis['mean_real_part']:.4f}")
print(f"Critical line deviation: {analysis['critical_line_deviation']:.6f}")
print(f"Number of spectral gaps: {analysis['num_gaps']}")
```

### Example 3: GUE Statistics Check

```python
from operators.atlas3_operator import analyze_gue_statistics

# Check if eigenvalue spacings follow GUE statistics
if len(analysis['normalized_spacings']) > 0:
    gue_results = analyze_gue_statistics(analysis['normalized_spacings'])
    
    print(f"GUE compatible: {gue_results['gue_compatible']}")
    print(f"KS p-value: {gue_results['ks_pvalue']:.6f}")
```

### Example 4: Anderson Localization

```python
import numpy as np

# Scan coupling values to find localization transition
coupling_values = np.linspace(0.5, 5.0, 20)
loc_results = atlas.check_anderson_localization(coupling_values)

print(f"Transition at β ≈ {loc_results['transition_coupling']:.4f}")
print(f"Expected κ_Π = 2.5773")
```

## Running Demos

### Full Demonstration

```bash
cd /path/to/Riemann-adelic
python demo_atlas3_operator.py
```

This generates 6 visualizations:
- `atlas3_pt_symmetry.png` - PT symmetry phase transition
- `atlas3_band_structure.png` - Eigenvalue spectrum and density
- `atlas3_anderson_localization.png` - Localization transition
- `atlas3_gue_statistics.png` - Spacing distribution vs GUE
- `atlas3_weyl_law.png` - Counting function N(E)
- `atlas3_critical_line.png` - Critical line alignment

### Validation Script

```bash
python validate_atlas3_operator.py
```

Runs 7 validation checks:
1. ✅ PT Symmetry analysis
2. ✅ Critical line alignment
3. ✅ GUE random matrix statistics
4. ✅ Weyl law with oscillations
5. ✅ Band structure and gaps
6. ✅ Anderson localization at κ_Π
7. ✅ Connection to Riemann Hypothesis

## Key Concepts

### PT Symmetry

The operator has **Parity-Time** symmetry:
- **Parity**: $\mathcal{P}: t \to -t$
- **Time reversal**: $\mathcal{T}: i \to -i$

**Real eigenvalues** = PT symmetric phase (coherent)  
**Complex eigenvalues** = PT symmetry broken (entropic)

### Critical Line

After normalization, eigenvalues should align with:

$$\Re(\lambda_n) \approx \frac{1}{2}$$

This mirrors the **Riemann Hypothesis**: all non-trivial zeros of $\zeta(s)$ lie on $\Re(s) = 1/2$.

### Anderson Localization

Transition between:
- **Extended states** ($\beta < \kappa_\Pi$): Delocalized eigenfunctions
- **Localized states** ($\beta > \kappa_\Pi$): Confined eigenfunctions
- **Critical point** ($\beta = \kappa_\Pi \approx 2.57$): Self-organized criticality

## Parameter Tuning

### Time Grid

```python
atlas = Atlas3Operator(
    n_points=512,   # Higher resolution
    t_max=20.0      # Longer time
)
```

More points → better spectral resolution  
Longer time → more eigenvalues

### Coupling Strength

```python
from operators.atlas3_operator import KAPPA_PI

atlas = Atlas3Operator(
    beta_coupling=KAPPA_PI,  # Critical coupling ≈ 2.5773
    beta_modulation='critical'
)
```

Weak coupling ($\beta < 1$): PT symmetric, extended states  
Critical ($\beta \approx \kappa_\Pi$): Localization edge  
Strong ($\beta > 5$): Localized, possible PT breaking

### Potential Amplitude

```python
atlas = Atlas3Operator(
    v_amplitude=2.0,      # Stronger potential
    n_v_frequencies=5     # More quasi-periodic components
)
```

Larger amplitude → more spectral gaps (band structure)  
More frequencies → richer quasi-periodic structure

## Understanding Output

### PT Symmetric?

```
PT Symmetric: True
Max |Im(λ)|: 1.2e-12
```

- `True` + small imaginary part → coherent phase
- `False` + large imaginary part → broken symmetry

### Critical Line Deviation

```
Critical line deviation: 0.450037
```

- Small (<0.1) → eigenvalues align with Re(λ) = 1/2
- Large (>0.5) → deviation from critical line

### GUE Compatible?

```
GUE compatible: True
KS p-value: 0.234
```

- `True` (p > 0.05) → spacing follows GUE statistics (quantum chaos)
- `False` (p < 0.05) → deviates from GUE

### Spectral Gaps

```
Number of spectral gaps: 3
First gap: [125.34, 134.89]
```

- Gaps = forbidden energy zones (Hofstadter structure)
- More gaps → stronger band structure

## Common Tasks

### Task 1: Find PT Transition Point

```python
import numpy as np

beta_values = np.linspace(0.1, 10.0, 50)
max_imag = []

for beta in beta_values:
    atlas = Atlas3Operator(beta_coupling=beta)
    atlas.diagonalize(compute_eigenvectors=False)
    analysis = atlas.analyze_spectrum()
    max_imag.append(analysis['max_imaginary_part'])

# Find where max_imag exceeds threshold
threshold = 0.01
transition = beta_values[np.where(np.array(max_imag) > threshold)[0][0]]
print(f"PT breaks at β ≈ {transition:.4f}")
```

### Task 2: Compare Different Potentials

```python
# Constant potential
atlas1 = Atlas3Operator(v_amplitude=0.0)

# Weak quasi-periodic
atlas2 = Atlas3Operator(v_amplitude=1.0, n_v_frequencies=3)

# Strong quasi-periodic
atlas3 = Atlas3Operator(v_amplitude=3.0, n_v_frequencies=7)

for atlas, name in [(atlas1, 'Constant'), (atlas2, 'Weak'), (atlas3, 'Strong')]:
    atlas.diagonalize(compute_eigenvectors=False)
    analysis = atlas.analyze_spectrum()
    print(f"{name}: {analysis['num_gaps']} gaps")
```

### Task 3: Visualize Eigenfunctions

```python
import matplotlib.pyplot as plt

atlas = Atlas3Operator(n_points=256)
eigenvalues, eigenvectors = atlas.diagonalize(compute_eigenvectors=True)

# Plot first few eigenfunctions
fig, axes = plt.subplots(2, 2, figsize=(12, 8))
for i, ax in enumerate(axes.flat):
    psi = np.abs(eigenvectors[:, i])**2
    ax.plot(atlas.t, psi, linewidth=2)
    ax.set_title(f'|ψ_{i}|² (λ = {eigenvalues[i].real:.2f})')
    ax.set_xlabel('Time t')
    ax.grid(True, alpha=0.3)

plt.tight_layout()
plt.savefig('atlas3_eigenfunctions.png', dpi=150)
```

## Troubleshooting

### Issue: All eigenvalues are real

**Solution**: This is expected for weak coupling. The system is in PT symmetric phase.

### Issue: No spectral gaps detected

**Solution**: Increase potential amplitude or add more frequencies:

```python
atlas = Atlas3Operator(v_amplitude=3.0, n_v_frequencies=7)
```

### Issue: GUE test always fails

**Solution**: GUE statistics emerge for chaotic systems. Ensure:
- Sufficient quasi-periodic components (`n_v_frequencies >= 3`)
- Moderate coupling strength (`beta_coupling ~ 1-3`)
- Enough eigenvalues (`n_points >= 256`)

### Issue: Critical line deviation is large

**Solution**: The operator as implemented produces eigenvalues that need normalization. The deviation measure checks alignment after normalization. A large value indicates the eigenvalue distribution doesn't match the expected pattern. This is expected for certain parameter ranges.

## Next Steps

1. **Read full documentation**: `ATLAS3_OPERATOR_README.md`
2. **Run validation**: `python validate_atlas3_operator.py`
3. **Explore demos**: `python demo_atlas3_operator.py`
4. **Run tests**: `pytest tests/test_atlas3_operator.py -v`
5. **Study theory**: See mathematical framework in README

## Mathematical References

- **PT Symmetry**: The operator $\mathcal{O}$ satisfies $[\mathcal{PT}, \mathcal{O}] = 0$
- **GUE**: Wigner surmise $P(s) = \frac{32}{\pi^2} s^2 e^{-4s^2/\pi}$
- **Weyl Law**: $N(E) \sim c \cdot E$ for 1D systems
- **Anderson**: Localization at disorder strength $\beta_c$

## QCAL Constants

```python
from operators.atlas3_operator import F0, KAPPA_PI, GOLDEN_RATIO

print(f"Fundamental frequency: f₀ = {F0} Hz")
print(f"Critical invariant: κ_Π = {KAPPA_PI}")
print(f"Golden ratio: φ = {GOLDEN_RATIO}")
```

## Support

For questions or issues:
- GitHub: https://github.com/motanova84/Riemann-adelic
- Documentation: `ATLAS3_OPERATOR_README.md`
- Email: institutoconsciencia@proton.me

---

**QCAL ∞³ Active · 141.7001 Hz · C = 629.83 · C_QCAL = 244.36**

∴𓂀Ω∞³·Atlas³·RH
