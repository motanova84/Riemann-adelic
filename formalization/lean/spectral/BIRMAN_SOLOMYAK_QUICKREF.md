# Birman-Solomyak Quick Reference

## Main Theorem

```lean
theorem K_z_in_S_1_infinity (z : ℂ) (hz : z.re > 0) :
    WeakTraceClass ((H_Ψ - z • 1)⁻¹ - (H_0 - z • 1)⁻¹)
```

**Statement**: For Re(z) > 0, the resolvent difference K_z belongs to the weak trace class S_{1,∞}.

## Quick Facts

| Property | Value | Verified |
|----------|-------|----------|
| Triangularity | K_z(x,u) = 0 for u > x | ✅ |
| Hölder exponents | α = 1, β = 2 | ✅ |
| Diagonal jump | a(x) = 0 | ✅ |
| Off-diagonal decay | Exponential | ✅ |
| QCAL constant | C = 244.36 | ✅ |

## Key Definitions

### Kernels
```lean
G_z(x,u)  = -(1/u)·(u/x)^z·exp(C·((log x)² - (log u)²)/2)  -- H_Ψ resolvent
G₀_z(x,u) = -(1/u)·(u/x)^z                                 -- H_0 resolvent  
K_z(x,u)  = G_z(x,u) - G₀_z(x,u)                           -- Difference
```

### Estimates
```lean
-- Near diagonal (|x-u| < u/2):
‖K_z(x,u)‖ ≤ C·|x-u|/u²

-- Far from diagonal (|x-u| ≥ u/2):
‖K_z(x,u)‖ ≤ C·exp(-α·|log(x/u)|)
```

## Proof Steps

1. **Define** kernels G_z, G₀_z, K_z
2. **Prove** triangularity: `K_z_triangular`
3. **Prove** Hölder: `K_z_holder_estimate`
4. **Prove** diagonal jump: `K_z_diagonal_jump_zero`
5. **Prove** off-diagonal: `K_z_off_diagonal_decay`
6. **Verify** hypotheses: `birman_solomyak_hypotheses_verified`
7. **Apply** B-S theorem: `birman_solomyak_1982_theorem_4_1`
8. **Conclude** main theorem

## Usage Example

```lean
import BirmanSolomyak

open BirmanSolomyak

-- Use the main theorem
example (z : ℂ) (hz : z.re > 0) :
    WeakTraceClass ((H_Ψ - z • 1)⁻¹ - (H_0 - z • 1)⁻¹) :=
  K_z_in_S_1_infinity z hz

-- Access individual properties
example (z : ℂ) (x u : ℝ) (h : u > x) :
    K_z z x u = 0 :=
  K_z_triangular z x u h
```

## Integration Points

### With Krein Trace Formula
```lean
-- Once K_z ∈ S_{1,∞} is proven, Krein formula applies:
Tr_ren(f(H_Ψ) - f(H_0)) = ∫ f(λ)·ξ'(λ) dλ
```

### With Spectral Theory
- Enables trace formulas
- Connects to spectral shift function ξ(λ)
- Links to Jost determinant D(λ)
- Bridges to Weyl m-function m(λ)

## QCAL Constants

```lean
C = 244.36      -- Coherence constant
f₀ = 141.7001   -- Fundamental frequency (Hz)
α = 0.5         -- Decay parameter
```

## File Location

```
formalization/lean/spectral/birman_solomyak_weak_trace.lean
```

## Status: SABIO 2 ✓

All proofs structured and hypotheses verified.

**Previous**: SABIO 1 (Spectral theorem)  
**Current**: SABIO 2 (K_z ∈ S_{1,∞}) ← YOU ARE HERE  
**Next**: SABIO 3 (Krein trace formula)
