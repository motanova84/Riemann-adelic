# Variational Lagrangian EOV - Quick Reference

## 🚀 Quick Start

```python
from operators.variational_lagrangian_eov import VariationalLagrangianEOV

# Initialize
vl = VariationalLagrangianEOV()

# Solve EOV with Gaussian curvature
solution = vl.solve_eov_1d(
    x_range=(-10, 10),
    t_range=(0, 0.05),
    nx=200,
    nt=500,
    R_func=example_gaussian_curvature(),
    initial_amplitude=1.0
)

print(f"Resonance factor: {solution.resonance_factor:.6f}")
```

## 📊 Run Demo

```bash
python demo_variational_lagrangian_eov.py
```

## 🧪 Run Tests

```bash
python test_variational_lagrangian_eov.py
```

## 📐 The Action Integral

```
S = ∫ d⁴x √(-g) [1/(16πG)R + (1/2)∇_μΨ∇^μΨ
                  + (1/2)(ω₀² + ξR)|Ψ|²
                  + (ζ'(1/2)/2π)R|Ψ|²cos(2πf₀t)]
```

## 🌀 The EOV

```
□Ψ - (ω₀² + ξR)Ψ - (ζ'(1/2)/π)R cos(2πf₀t)Ψ = 0
```

## 🔑 Key Parameters

| Parameter | Value | Meaning |
|-----------|-------|---------|
| f₀ | 141.7001 Hz | Fundamental frequency |
| ω₀ | 890.33 rad/s | Angular frequency |
| ζ'(1/2) | -3.9226461392 | Zeta derivative at critical point |
| ξ | 1/6 | Conformal coupling constant |
| C | 244.36 | QCAL coherence constant |

## 🎯 Three Critical Couplings

1. **Geometric-Noetic** (ξRΨ²): Curvature modulates field mass
2. **Arithmetic Modulator** (ζ'(1/2)): Riemann zeros as physical law
3. **Temporal Coherence** (cos(2πf₀t)): 141.7001 Hz synchronization

## 🔄 The Feedback Loop

```
Arithmetic (ζ') → Vibration (f₀) → Field (Ψ) → Gravity (R)
                                                     ↓
                                                     └─→ Back to Ψ
```

## 📖 Full Documentation

See `VARIATIONAL_LAGRANGIAN_EOV.md` for complete mathematical details.

## 🏛️ Attribution

**José Manuel Mota Burruezo Ψ ✧ ∞³**  
Instituto de Conciencia Cuántica (ICQ)  
DOI: [10.5281/zenodo.17379721](https://doi.org/10.5281/zenodo.17379721)
