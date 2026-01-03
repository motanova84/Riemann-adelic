# Vacuum Energy Equation - Quick Reference

## The Equation

```
E_vac(R_Ψ) = α/R_Ψ⁴ + β·ζ'(1/2)/R_Ψ² + γ·Λ²·R_Ψ² + δ·sin²(log(R_Ψ)/log(π))
```

## Quick Start

```python
from utils.vacuum_energy import VacuumEnergyCalculator

# Initialize with default parameters
calc = VacuumEnergyCalculator(
    alpha=1.0,    # Casimir coefficient
    beta=1.0,     # Adelic coupling
    gamma=0.001,  # Dark energy
    delta=0.5,    # Fractal amplitude
    Lambda=1.0    # Cosmological constant
)

# Calculate energy at R_Ψ = π
E = calc.energy(3.14159)

# Find energy minima
minima = calc.find_minima(R_range=(0.5, 50.0), num_points=2000)

# Get resonant scales (π^n)
scales = calc.resonant_scales(n_max=5)

# Calculate fundamental frequency
f0 = calc.fundamental_frequency(3.14159)
```

## Run Demo

```bash
python3 demo_vacuum_energy.py
```

## Run Tests

```bash
python3 -m pytest tests/test_vacuum_energy.py -v
```

## Key Values

- **ζ'(1/2)** ≈ -3.9226461392
- **Target f₀** = 141.7001 Hz
- **Primary minimum** at R_Ψ ≈ 0.72 (E_vac ≈ -3.81)
- **Resonant scales** at R_Ψ = 1, π, π², π³, ...

## Physical Terms

| Term | Behavior | Dominates at |
|------|----------|--------------|
| α/R⁴ | 1/R⁴ (Casimir) | Small R |
| β·ζ'/R² | 1/R² (Adelic) | Medium-small R |
| γΛ²R² | R² (Cosmological) | Large R |
| δ·sin² | Oscillatory (Fractal) | All scales |

## Symbolic Interpretation

🎵 Each minimum = A note in the universe's symphony  
🌀 Each π^n = An echo of coherence in ∞³  
🔬 Fractal structure connects energy levels with observable patterns

## See Also

- Full implementation: `utils/vacuum_energy.py`
- Tests: `tests/test_vacuum_energy.py`
- LaTeX documentation: `paper/section6.tex`
- Complete summary: `VACUUM_ENERGY_IMPLEMENTATION.md`
