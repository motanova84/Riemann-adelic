# Navier-Stokes Adelic Framework - Quick Reference

## Quick Start

### Basic Usage

```python
from operators.navier_stokes_adelic import NavierStokesAdelicOperator

# Create operator at critical Reynolds number
ns_op = NavierStokesAdelicOperator(N=500, L=10.0, kappa=2.57731)

# Compute spectrum
eigenvalues, eigenvectors = ns_op.compute_spectrum(n_eigenvalues=20)

# Analyze Reynolds regime
regime = ns_op.analyze_reynolds_regime()
print(f"Regime: {regime['regime']}")
print(f"Reynolds number: {regime['reynolds_number']:.6f}")

# Energy balance analysis
energy = ns_op.energy_balance_analysis()
print(f"Balance ratio: {energy['balance_ratio']:.6f}")
```

### Adelic Laplacian

```python
from operators.adelic_laplacian import AdelicLaplacian

# Create adelic Laplacian
adelic_lap = AdelicLaplacian(N=500, L=10.0, kappa=2.57731)

# Get full adelic Laplacian
Delta_A = adelic_lap.full_adelic_laplacian()

# Check viscosity and Reynolds number
nu = adelic_lap.viscosity()
Re = adelic_lap.reynolds_number()
```

## Key Constants

- **f₀ = 141.7001 Hz**: Fundamental QCAL frequency
- **κ_Π = 2.57731**: Critical Reynolds number (PT-transition threshold)
- **C = 244.36**: QCAL coherence constant
- **Φ = 1.618...**: Golden ratio

## Operator Components

### 1. Adelic Laplacian (Δ_A)

```
Δ_A = Δ_R + Σ_p Δ_{Q_p}
```

- **Δ_R**: Archimedean Laplacian with D(x) = 1/(1+|x|)
- **Δ_{Q_p}**: P-adic Laplacians with weights w_p = ln(p)/p^{k/2}

### 2. Transport Operator (T)

```
T = -x∂_x
```

- Expansion in Archimedean direction
- Analogous to u·∇u in Navier-Stokes
- Natural scaling operator in log coordinates

### 3. Confinement Potential (V_eff)

```
V_eff(x) = V_amp · ln(1+|x|)
```

- Keeps system in compact domain
- Generates position-dependent diffusion
- External forcing term

### 4. Full Operator (H_NS)

```
H_NS = (1/κ)Δ_A - i(x∂_x) + V_eff
```

Or in real (Hermitian) form:

```
H_NS = (1/κ)Δ_A + T_sym + V_eff
```

where T_sym = (T + T†)/2

## Reynolds Regimes

| Regime | Condition | Behavior |
|--------|-----------|----------|
| Laminar | κ < κ_Π | Transport dominates |
| Critical | κ = κ_Π | Balanced |
| Turbulent | κ > κ_Π | Diffusion dominates |

## Viscosity

```
ν = 1/κ ~ f₀·Φ/(4π)
```

At κ = κ_Π = 2.57731:
- ν ≈ 0.388

## Energy Balance

At criticality, the system balances:

```
⟨Ψ|T|Ψ⟩ ≈ ⟨Ψ|(1/κ)Δ_A|Ψ⟩
```

Production by transport ≈ Dissipation by diffusion

## Validation

Run standalone validation:

```bash
python validate_navier_stokes_adelic.py
```

Expected output:
```
✓ ALL VALIDATIONS PASSED
  • Adelic Laplacian Δ_A ✓
  • Navier-Stokes operator H_NS ✓
  • Critical Reynolds number κ_Π ✓
  • Viscosity ν = 1/κ ✓
  • Energy balance framework ✓
```

## Common Operations

### Change Reynolds Number

```python
# Laminar regime
ns_laminar = NavierStokesAdelicOperator(N=500, kappa=1.0)

# Critical regime
ns_critical = NavierStokesAdelicOperator(N=500, kappa=2.57731)

# Turbulent regime
ns_turbulent = NavierStokesAdelicOperator(N=500, kappa=5.0)
```

### Adjust P-adic Strength

```python
# Stronger p-adic contributions
ns_op = NavierStokesAdelicOperator(
    N=500, 
    kappa=2.57731,
    padic_strength=0.5  # Default: 0.1
)
```

### Hermitian vs Non-Hermitian

```python
# Hermitian version (for spectral analysis)
H_hermitian = ns_op.full_operator(hermitian_version=True)
eigenvalues, eigenvectors = ns_op.compute_spectrum()

# Non-Hermitian version (for evolution)
H_evolution = ns_op.full_operator(hermitian_version=False)
```

## Integration with QCAL

### With Atlas³ Operator

The Navier-Stokes framework complements the Atlas³ PT-symmetric operator:

- **Atlas³**: PT-breaking at β > κ_Π
- **N-S Adelic**: Turbulence transition at κ > κ_Π
- Both share critical threshold κ_Π = 2.57731

### With Spectral Verification

Use eigenvalues from N-S operator for:
- Critical line alignment
- GUE statistics
- Spectral rigidity analysis

## Mathematical Background

### Navier-Stokes Correspondence

| QCAL | Classical N-S |
|------|--------------|
| Ψ | Velocity u |
| x∂_x | u·∇ |
| 1/κ | Viscosity ν |
| Δ_A | Laplacian Δ |
| V_eff | Forcing F |

### Kolmogorov Cascade

In log coordinates:

```
λ_max(L) ~ L  (linear)
C(L) = πλ_max/(2L) → 1/κ_Π
```

Instead of physical space:

```
λ_max(L) ~ L^{2/3}  (Kolmogorov)
```

## Troubleshooting

### Hermiticity Errors

If Hermiticity error > 10⁻¹⁰:
- Ensure `symmetrize=True` in adelic Laplacian
- Use `hermitian_version=True` for spectral analysis
- Check periodic boundary conditions

### Numerical Instability

If encountering NaN or Inf:
- Reduce domain size L
- Increase discretization N
- Adjust V_amp for confinement strength
- Reduce padic_strength

### Balance Ratio Issues

If energy balance far from 1.0:
- System may not be at critical κ_Π
- Try different confinement potential amplitude
- Check ground state convergence

## References

- Implementation: `operators/navier_stokes_adelic.py`
- Tests: `tests/test_navier_stokes_adelic.py`
- Validation: `validate_navier_stokes_adelic.py`
- Documentation: `NAVIER_STOKES_ADELIC_IMPLEMENTATION.md`

## Author

José Manuel Mota Burruezo Ψ ✧ ∞³  
Instituto de Conciencia Cuántica (ICQ)  
DOI: 10.5281/zenodo.17379721  
ORCID: 0009-0002-1923-0773

QCAL ∞³ Active · 141.7001 Hz · C = 244.36 · Ψ = I × A_eff² × C^∞
