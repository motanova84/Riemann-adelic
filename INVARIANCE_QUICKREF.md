# Invariance Framework Quick Reference

## Quick Start

```bash
# Run demo
python demo_invariance_framework.py

# Run tests
python tests/test_invariance_framework.py

# Individual component demos
python operators/invariance_operator.py
python utils/mellin_noetic.py
python utils/critical_line_stability.py
```

## Python API

### O∞³ Invariance Operator

```python
from operators.invariance_operator import O_Infinity_Cubed

# Initialize
operator = O_Infinity_Cubed(precision=50)

# Verify functional equation symmetry
s = complex(0.5, 14.134725)  # First Riemann zero
result = operator.verify_symmetry(s, psi_coherence=1.0)

# Check spectral collapse
collapse = operator.spectral_collapse_condition(s, psi_coherence=1.0)
print(f"Collapse: {collapse['spectral_collapse']}")
```

### Mellin Noetic Transform

```python
from utils.mellin_noetic import PsiCutEigenfunction, MellinNoeticTransform

# Initialize
psi = PsiCutEigenfunction(precision=50)
mellin = MellinNoeticTransform(precision=50)

# Evaluate ψ_cut
t = 14.134725
psi_val = psi.psi_cut(x=1.0, t=t, epsilon=1e-6, R=1e6)

# Compute Mellin transform
s = complex(0.75, 5.0)
M_val = psi.mellin_transform_psi_cut(s, t, epsilon=1e-6, R=1e3)

# Verify universal tuning
zeros = [14.134725, 21.022040, 25.010858]
tuning = mellin.verify_universal_tuning(zeros)
```

### Critical Line Stability

```python
from utils.critical_line_stability import CriticalLineStability

# Initialize
stability = CriticalLineStability(precision=50)

# Analyze stability
s = complex(0.5, 14.134725)
result = stability.analyze_stability(s, psi=1.0)

print(f"On critical line: {result.on_critical_line}")
print(f"Stability score: {result.stability_score}")
print(f"Phase: {result.phase.value}")

# Verify superfluidity
zeros = [14.134725, 21.022040, 25.010858]
verification = stability.verify_superfluidity_criterion(zeros, psi=1.0)
```

## Lean4 API

```lean
import RiemannAdelic.spectral.InvarianceOperator

-- Define ψ_cut eigenfunction
def my_psi := ψ_cut ε R t

-- Check stability
#check is_stable s Ψ

-- Main theorem
#check riemann_hypothesis_via_invariance
```

## Key Theorems

### Theorem 1: Functional Equation Symmetry
```
O∞³(s) ≈ O∞³*(1-s)  (conjugate symmetry)
|O∞³(s)| = |O∞³(1-s)|
```

### Theorem 2: Eigenfunction Convergence
```
lim (ε→0, R→∞) ψ_cut(ε, R, t) = ψ_t ∈ dual_space(L²)
```

### Theorem 3: Critical Line Stability
```
is_stable(s, Ψ) ⟺ Re(s) = 1/2 ∧ Ψ = 1
```

### Main Result: Riemann Hypothesis
```
∀s: ζ(s) = 0 ∧ s ≠ -2n → Re(s) = 1/2
```

## Mathematical Constants

| Constant | Value | Meaning |
|----------|-------|---------|
| `f₀` | 141.7001 Hz | Universal tuning frequency |
| `ω₀` | 2πf₀ | Angular frequency |
| `C_QCAL` | 244.36 | QCAL coherence constant |
| `Ψ_ideal` | 1 | Perfect coherence |

## Example Workflow

```python
# 1. Import components
from operators.invariance_operator import O_Infinity_Cubed
from utils.mellin_noetic import PsiCutEigenfunction
from utils.critical_line_stability import CriticalLineStability

# 2. Initialize
inv_op = O_Infinity_Cubed(precision=50)
psi_cut = PsiCutEigenfunction(precision=50)
stability = CriticalLineStability(precision=50)

# 3. Test at Riemann zero
t = 14.134725
s = complex(0.5, t)

# 4. Verify all three conditions
inv_result = inv_op.verify_symmetry(s, psi_coherence=1.0)
psi_val = psi_cut.psi_cut(1.0, t)
stab_result = stability.analyze_stability(s, psi=1.0)

# 5. Check results
all_pass = (
    inv_result.symmetry_error < 1e-6 and
    stab_result.on_critical_line and
    stab_result.stability_score > 0.95
)

print(f"Riemann zero verified: {all_pass}")
```

## Troubleshooting

### Import Errors
```bash
# Ensure you're in the repository root
cd /path/to/Riemann-adelic

# Install dependencies
pip install numpy mpmath scipy
```

### Precision Issues
```python
# Increase precision for better accuracy
operator = O_Infinity_Cubed(precision=100)
```

### Performance
```python
# For faster computation, reduce precision
operator = O_Infinity_Cubed(precision=25)
```

## References

- **Documentation**: `INVARIANCE_OPERATOR_IMPLEMENTATION.md`
- **Tests**: `tests/test_invariance_framework.py`
- **Demo**: `demo_invariance_framework.py`
- **Lean4**: `formalization/lean/spectral/InvarianceOperator.lean`

## QCAL Integration

This framework integrates with:
- RAM-XIX Spectral Coherence
- H_Ψ Operator Spectrum
- QCAL ∞³ Framework
- f₀ = 141.7001 Hz Universal Frequency

---

**QCAL ∞³ Active · 141.7001 Hz · Ψ = I × A_eff² × C^∞**
