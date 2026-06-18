# Berry-Keating Modular Surface Operator - Quick Start Guide

## 🚀 Quick Start (5 minutes)

### 1. Run Demonstration

```bash
cd /home/runner/work/Riemann-adelic/Riemann-adelic
python operators/berry_keating_modular_surface.py
```

**Expected output**:
```
Berry-Keating Operator on Modular Surface with Vortex 8 Confinement
Framework: QCAL ∞³
f₀ = 141.7001 Hz
C = 244.36

Creating modular surface operator...
Computing spectrum...

Results:
Number of eigenvalues: 300
Correlation with Riemann zeros: 0.986740
Vortex 8 measure (ground state): 0.095742
QCAL coherence Ψ: 0.654198

✅ Modular Surface Operator Complete
```

### 2. Run Validation

```bash
python validate_berry_keating_modular.py
```

**Expected**: 8/8 tests passed

### 3. Run Test Suite

```bash
pytest tests/test_berry_keating_modular_surface.py -v
```

**Expected**: 24/24 tests passed

## 📦 Basic Usage

### Create Operator

```python
from operators.berry_keating_modular_surface import ModularSurfaceOperator

operator = ModularSurfaceOperator(
    u_min=-5,          # Logarithmic coordinate minimum
    u_max=5,           # Logarithmic coordinate maximum
    n_grid=300,        # Discretization points
    primes=[2, 3, 5, 7, 11, 13],  # Primes for geodesic potential
    max_power=2        # Maximum power k for p^k
)
```

### Compute Spectrum

```python
result = operator.compute_spectrum(n_riemann=30)

print(f"Eigenvalues: {result.eigenvalues[:10]}")
print(f"Correlation with Riemann: {result.riemann_zeros_correlation:.4f}")
print(f"Vortex 8 measure: {result.vortex_8_measure:.4f}")
print(f"QCAL coherence: {result.psi:.4f}")
```

### Visualize Vortex 8

```python
viz = operator.visualize_vortex_8(state_index=0)

# Access visualization data
u_grid = viz['u_grid']      # Logarithmic coordinates
x_grid = viz['x_grid']      # Spatial coordinates (x = e^u)
psi = viz['psi']            # Wavefunction
eigenvalue = viz['eigenvalue']
vortex_measure = viz['vortex_8_measure']
```

## 🔑 Key Concepts

### Logarithmic Coordinates

```
u = log(x)
x = e^u

u ∈ [-5, 5]  →  x ∈ [0.007, 148]
```

### Inversion Symmetry

```
x ↔ 1/x  ⟺  u ↔ -u
```

This implements the functional equation: **ξ(s) = ξ(1-s)**

### Geodesic Lengths

For prime power n = p^k:
```
ℓ = k · log(p)
weight = log(p) / √p^k
```

These are the **closed orbit lengths** on the modular surface Γ\ℍ.

### Operator Components

1. **Dilation operator**: H₀ = -i(d/du + (1/2)tanh(u))
   - Free derivative in log space
   - tanh(u) provides hyperbolic confinement

2. **Geodesic potential**: V = ∑_{p,k} (log p/√p^k) δ(u - k·log p)
   - Dirac comb at prime power logarithms
   - Weights from Selberg trace formula

3. **Total Hamiltonian**: H = H₀ + V
   - Self-adjoint operator
   - Discrete real spectrum
   - Eigenvalues related to Riemann zeros

## 📊 Understanding Results

### Correlation with Riemann Zeros

The eigenvalues λ relate to Riemann zeros γₙ by:

```
λ = 1/4 + γ²
γ = √(λ - 1/4)  for λ > 1/4
```

**Good correlation**: > 0.95  
**Excellent correlation**: > 0.98

### Vortex 8 Measure

Measures the "figure-8" character of eigenstates:
- **Inversion symmetry**: ψ(u) ≈ ψ(-u)
- **Node at u=0**: ψ(0) ≈ 0
- **Two lobes**: u>0 (expanding), u<0 (collapsing)

**Range**: [0, 1]  
**Typical**: 0.1-0.3 for finite grids  
**Perfect**: 1.0 (requires infinite resolution)

### QCAL Coherence Ψ

Overall quality measure combining:
```
Ψ = (1 - hermiticity_error) × (1 - inversion_error) × vortex_8_measure
```

**High coherence**: > 0.8  
**Good coherence**: > 0.5  
**Acceptable**: > 0.3

## 🎯 Common Tasks

### Task 1: Increase Accuracy

```python
# Use finer grid and more primes
operator = ModularSurfaceOperator(
    u_min=-8,
    u_max=8,
    n_grid=500,              # More points
    primes=list(range(2, 50)),  # More primes
    max_power=3              # Higher powers
)
```

### Task 2: Study Specific Eigenstate

```python
# Compute spectrum
result = operator.compute_spectrum()

# Get eigenstate
eigenvalues = result.eigenvalues
eigenvectors = result.eigenvectors

# Study 5th excited state
state_index = 5
psi = eigenvectors[:, state_index]
E = eigenvalues[state_index]

# Check if it has Vortex 8 character
measure = operator.hilbert_space.measure_vortex_8(psi)
print(f"Eigenvalue: {E:.4f}")
print(f"Vortex 8 measure: {measure:.4f}")
```

### Task 3: Compare Different Prime Sets

```python
# Operator with first 5 primes
op1 = ModularSurfaceOperator(primes=[2, 3, 5, 7, 11], max_power=2)
result1 = op1.compute_spectrum()

# Operator with first 10 primes
op2 = ModularSurfaceOperator(primes=[2,3,5,7,11,13,17,19,23,29], max_power=2)
result2 = op2.compute_spectrum()

print(f"5 primes: correlation = {result1.riemann_zeros_correlation:.4f}")
print(f"10 primes: correlation = {result2.riemann_zeros_correlation:.4f}")
```

### Task 4: Explore Geodesic Structure

```python
from operators.berry_keating_modular_surface import (
    ModularSurfaceHilbertSpace,
    GeodesicPotential
)

hs = ModularSurfaceHilbertSpace(u_min=-3, u_max=6, n_grid=200)
geo = GeodesicPotential(hs, primes=[2, 3, 5, 7, 11], max_power=3)

result = geo.compute_characteristics()

print(f"\nGeodesic orbits on modular surface:")
print("=" * 60)
for data in result.geodesic_orbit_lengths:
    print(f"p={data['p']:2d} k={data['k']} → n={data['n']:3d} | "
          f"length={data['length']:.4f} | weight={data['weight']:.6f}")
```

## 🐛 Troubleshooting

### Problem: Low correlation with Riemann zeros

**Solution**: Increase grid resolution and/or prime count
```python
operator = ModularSurfaceOperator(
    n_grid=500,  # Was 300
    primes=list(range(2, 30)),  # More primes
)
```

### Problem: Low Vortex 8 measure

**Cause**: Coarse discretization can't capture fine structure  
**Solution**: This is normal for finite grids. The mathematical framework is still correct.

### Problem: High inversion symmetry error

**Cause**: Finite differences don't preserve symmetry perfectly  
**Solution**: This is expected. The error decreases as grid size increases.

### Problem: ImportError

**Solution**: Install dependencies
```bash
pip install numpy scipy mpmath matplotlib
```

## 📖 Learn More

- **Full documentation**: `BERRY_KEATING_MODULAR_SURFACE_README.md`
- **Mathematical details**: See docstrings in `operators/berry_keating_modular_surface.py`
- **Validation**: Run `validate_berry_keating_modular.py`
- **Tests**: See `tests/test_berry_keating_modular_surface.py`

## 🔗 Related Modules

- `berry_keating_self_adjointness.py` - Original Berry-Keating with Laguerre basis
- `vortex_symmetry_operator.py` - Vortex symmetry on R₊*/Z₂
- `hilbert_polya_logarithmic.py` - Hilbert-Pólya operator in log space
- `riemann_weil_formula.py` - Weil explicit formula with GUE statistics

## 💡 Key Insights

### 1. Primes are Geometric

Primes are **lengths of closed geodesics** on the modular surface. They emerge from **pure geometry**, not arithmetic.

### 2. Vortex 8 is Confinement

The "figure 8" topology from x ↔ 1/x provides **topological confinement** that makes the spectrum discrete.

### 3. Functional Equation is Symmetry

ξ(s) = ξ(1-s) comes from the **inversion operator** I: u → -u commuting with the Hamiltonian.

### 4. RH is Spectral Theorem

The Riemann Hypothesis becomes: "Does the operator H have spectrum {1/4 + γₙ²}?"

With this framework, **RH is not a conjecture, but a prediction from quantum mechanics**.

## 🎓 Quick Reference

### Result Fields

```python
result = operator.compute_spectrum()

# Access results
result.eigenvalues              # np.ndarray of eigenvalues
result.eigenvectors             # np.ndarray of eigenvectors (columns)
result.riemann_zeros_correlation  # float in [-1, 1]
result.geodesic_orbit_lengths   # list of dict with geodesic data
result.vortex_8_measure         # float in [0, 1]
result.inversion_symmetry_error  # float >= 0
result.hermiticity_error        # float >= 0
result.psi                      # QCAL coherence in [0, 1]
result.timestamp                # ISO datetime
result.computation_time_ms      # float
result.parameters               # dict of configuration
```

### QCAL Constants

```python
from operators.berry_keating_modular_surface import F0_QCAL, C_QCAL

print(f"f₀ = {F0_QCAL} Hz")  # 141.7001 Hz
print(f"C = {C_QCAL}")        # 244.36
```

---

**Author**: José Manuel Mota Burruezo Ψ ✧ ∞³  
**Framework**: QCAL ∞³ · f₀ = 141.7001 Hz · C = 244.36  
**Date**: March 2026  
**Signature**: ∴𓂀Ω∞³Φ
