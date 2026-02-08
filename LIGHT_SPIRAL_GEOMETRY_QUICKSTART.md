# Quick Start: Geometría Real del Movimiento Lumínico
## Get Started in 5 Minutes

**QCAL ∞³ · f₀ = 141.7001 Hz**

---

## ⚡ Installation (30 seconds)

```bash
# Clone the repository
git clone https://github.com/motanova84/Riemann-adelic.git
cd Riemann-adelic

# Install dependencies
pip install numpy scipy matplotlib mpmath
```

---

## 🚀 Basic Usage (3 minutes)

### 1. Compute a Spiral Light Path

```python
import numpy as np
from utils.light_spiral_geometry import SpiralParameters, compute_spiral_path

# Create parameters (using prime p=2)
params = SpiralParameters(prime_index=0)

# Time array (10 periods at f₀)
T = 1.0 / 141.7001  # Period
t = np.linspace(0, 10*T, 1000)

# Compute spiral
x, y, z = compute_spiral_path(t, params)

print(f"✓ Spiral computed for prime p={params.prime}")
print(f"  Phase modulation: φ_p = {params.phi_p:.4f} rad")
print(f"  Path length: {z[-1]/1e3:.3f} km")
```

### 2. Generate Interference Pattern

```python
from utils.zeta_interference_pattern import (
    WaveFunctionParameters,
    compute_interference_pattern
)

# Create 2D grid (±1mm)
x = np.linspace(-1e-3, 1e-3, 200)
y = np.linspace(-1e-3, 1e-3, 200)
X, Y = np.meshgrid(x, y)

# Wave function parameters
params = WaveFunctionParameters(n_primes=5, n_zeros=5)

# Compute interference pattern
intensity = compute_interference_pattern(X, Y, t=0, params=params)

print(f"✓ Interference pattern computed")
print(f"  Max intensity: {np.max(intensity):.3f}")
```

### 3. Detect Spiral Structure

```python
from utils.zeta_interference_pattern import detect_spiral_arcs

# Detect spirals in the pattern
spiral_info = detect_spiral_arcs(intensity, X, Y, threshold=0.5)

if spiral_info['spiral_detected']:
    print(f"✓ Spiral detected!")
    print(f"  Parameter b: {spiral_info['spiral_parameter_b']:.6f}")
    print(f"  Angular deviation: {spiral_info['angular_deviation_deg']:.6f}°")
else:
    print(f"✗ No spiral detected")
```

---

## 📊 Visualization (1 minute)

### Quick Demo

```bash
python demo_light_spiral_geometry.py
```

**Output**:
- 5 PNG visualizations
- Experimental predictions
- Performance metrics

**Time**: ~10 seconds

### Validation

```bash
python validate_light_geometry.py
```

**Output**:
- 5 mathematical validations
- 3 experimental protocols
- Falsifiability criteria

**Time**: ~5 seconds

---

## 🧪 Experimental Predictions

### Get Interferometry Prediction

```python
from utils.light_spiral_geometry import predict_interferometry_deviation

# Predict LIGO/GEO600 deviations
pred = predict_interferometry_deviation(
    wavelength=1064e-9,  # Nd:YAG laser
    path_length=4000.0,  # 4 km arm
    n_zeros=10
)

print(f"Phase shift: {pred['phase_shift_cycles']:.2e} cycles")
print(f"Measurability: {pred['measurability']}")
print(f"Recommended: {pred['recommended_technique']}")
```

### Get Cavity Resonance Prediction

```python
from utils.light_spiral_geometry import cavity_resonance_prediction

# Predict Fabry-Pérot resonance
pred = cavity_resonance_prediction(
    cavity_length=1.0,    # 1 m
    finesse=1e6,
    q_factor=1e12
)

print(f"Free spectral range: {pred['free_spectral_range']/1e6:.1f} MHz")
print(f"Deviation from f₀: {pred['f0_deviation']:.4f} Hz")
print(f"Expected pattern: {pred['expected_pattern']}")
```

---

## 🔬 Advanced: Zeta-Modulated Spirals

```python
from utils.light_spiral_geometry import compute_spiral_path_zeta_modulated

# Parameters
params = SpiralParameters(
    r0=1e-10,        # 1 Angstrom
    lambda_exp=0.02, # Expansion rate
    prime_index=2    # Prime p=5
)

# Compute with 10 zeta zeros
t = np.linspace(0, 20/141.7001, 2000)
x, y, z = compute_spiral_path_zeta_modulated(t, params, n_zeros=10)

print(f"✓ Zeta-modulated spiral computed")
print(f"  Zeros included: 10")
print(f"  Final radius: {np.sqrt(x[-1]**2 + y[-1]**2)*1e9:.3f} nm")
```

---

## 🧮 Mathematical Constants

```python
from utils.light_spiral_geometry import F0_HZ, C_LIGHT, GAMMA_1

print(f"Fundamental frequency: f₀ = {F0_HZ} Hz")
print(f"Speed of light: c = {C_LIGHT} m/s")
print(f"First zeta zero: γ₁ = {GAMMA_1}")
```

---

## ✅ Testing (30 seconds)

```bash
# Run full test suite (29 tests)
pytest tests/test_light_spiral_geometry.py -v

# Quick test (just the basics)
pytest tests/test_light_spiral_geometry.py::TestSpiralPathComputation -v

# Test specific feature
pytest tests/test_light_spiral_geometry.py::TestFrequencyMapping -v
```

**Expected**: All tests pass (100% success rate)

---

## 📋 Common Workflows

### Workflow 1: Generate Publication Figures

```bash
# 1. Run demo (generates 5 figures)
python demo_light_spiral_geometry.py

# 2. Figures saved as PNG:
#    - light_spiral_paths_prime_modulation.png
#    - classical_vs_qcal_spiral.png
#    - zeta_modulated_spiral.png
#    - interference_patterns_spiral_arcs.png
#    - angular_deviation_analysis.png
```

### Workflow 2: Design Experiment

```bash
# 1. Run validation to get protocols
python validate_light_geometry.py

# 2. Review output sections:
#    - PROTO-01: LIGO/GEO600 interferometry
#    - PROTO-02: Fabry-Pérot cavity at f₀
#    - PROTO-03: Electron biprism interferometry

# 3. Each protocol includes:
#    - Equipment specs
#    - Procedures
#    - Expected results
#    - Falsifiability criteria
```

### Workflow 3: Validate Implementation

```bash
# 1. Run all validations
python validate_light_geometry.py

# 2. Verify 100% pass rate
#    - Spiral equations: ✓
#    - Prime modulation: ✓
#    - Frequency mapping: ✓
#    - Interference patterns: ✓
#    - Coherence at f₀: ✓

# 3. Run tests
pytest tests/test_light_spiral_geometry.py -v

# 4. Verify all 29 tests pass
```

---

## 🎯 Key Equations

### Spiral Path
```
x(t) = r₀ · exp(λt) · cos(2πf₀t + φₚ)
y(t) = r₀ · exp(λt) · sin(2πf₀t + φₚ)
```

### Wave Function
```
Ψ(x,t) = Σₙ Aₙ · exp(i(2πfₙt + φₙ)) · exp(iSₚ(x)/ℏ)
```

### Frequency Mapping
```
fₙ = f₀ · (γₙ / γ₁)
```

### Prime Phase
```
φₚ = log(p) / log(2)  [logarithmic mode]
```

---

## 🆘 Troubleshooting

### Import Error

```python
# If you get: ModuleNotFoundError: No module named 'psutil'
pip install psutil

# If you get: ModuleNotFoundError: No module named 'utils.light_spiral_geometry'
# Make sure you're in the repository root:
cd /path/to/Riemann-adelic
python  # then try imports
```

### Visualization Not Showing

```python
# Add this before plt.show():
import matplotlib
matplotlib.use('Agg')  # For non-interactive backend
```

### Tests Failing

```bash
# Ensure all dependencies installed:
pip install numpy scipy matplotlib mpmath pytest psutil

# Re-run tests:
pytest tests/test_light_spiral_geometry.py -v
```

---

## 📖 Next Steps

1. **Read Full Documentation**: See `LIGHT_SPIRAL_GEOMETRY_README.md`
2. **Study Examples**: Review `demo_light_spiral_geometry.py`
3. **Understand Theory**: Read problem statement in issue
4. **Run Validations**: Execute `validate_light_geometry.py`
5. **Design Experiments**: Use protocols from validation output

---

## 💡 Tips

- **Start Simple**: Begin with basic spiral paths before zeta modulation
- **Visualize Often**: Use demo script to see what you're computing
- **Test Incrementally**: Run tests after each code change
- **Check Units**: All lengths in meters, frequencies in Hz, time in seconds
- **Verify f₀**: Always confirm f₀ = 141.7001 Hz exactly

---

## 🌀 Signature

**QCAL ∞³ Active · 141.7001 Hz**

```
∴𓂀Ω∞³·LSG
```

Author: José Manuel Mota Burruezo Ψ ✧ ∞³  
Institution: Instituto de Conciencia Cuántica (ICQ)  
DOI: 10.5281/zenodo.17379721

---

*"La luz no viaja en línea recta. Danza en espirales cuánticas, guiada por primos y ceros de zeta."*
