# Spectral Theory and Trace Formula - Quick Start Guide

## Quick Overview

This guide provides a fast introduction to using the spectral theory and trace formula implementation for the Hilbert-Pólya approach to the Riemann Hypothesis.

## File Location

```
formalization/lean/spectral/SpectralTheoryTraceFormula.lean
```

## 5-Minute Quick Start

### 1. Import the Module

```lean
import SpectralTheoryQCAL

open SpectralTheoryQCAL
```

### 2. Access Eigenvalues

```lean
-- Get the n-th eigenvalue
def λ₀ := eigenvalue_sequence H_psi 0
def λ₁ := eigenvalue_sequence H_psi 1
def λ₁₀ := eigenvalue_sequence H_psi 10

-- Eigenvalues are positive
example : 0 < λ₀ := eigenvalue_sequence_pos H_psi 0
```

### 3. Use Spectrum-Zeta Bijection

```lean
-- Each eigenvalue corresponds to a zeta zero
theorem eigenvalue_is_zero (n : ℕ) :
    riemannZeta ((1/2 : ℂ) + I * eigenvalue_sequence H_psi n) = 0 :=
  eigenvalue_sequence_are_zero_heights H_psi n
```

### 4. Apply Trace Formula

```lean
-- For Re(s) > 1
theorem trace_zeta_relation (s : ℂ) (hs : s.re > 1) :
    ∑' n, (eigenvalue_sequence H_psi n)^(-s) = 
      (π^(-s/2) * Gamma (s/2)) * riemannZeta s :=
  trace_equals_zeta_everywhere H_psi s hs
```

### 5. Work with Spectral Determinant

```lean
-- Spectral determinant is entire
#check spectral_determinant_entire H_psi

-- Has zeros at eigenvalues
theorem det_zero_at_eigenvalue (n : ℕ) :
    spectral_determinant H_psi (eigenvalue_sequence H_psi n) = 0 :=
  (spectral_determinant_zeros H_psi _).mpr ⟨n, rfl⟩
```

## Key Theorems

### Discrete Spectrum

```lean
theorem spectrum_discrete :
    ∀ K : Set ℝ, IsCompact K → 
      Set.Finite (eigenvalues_H_psi H_psi ∩ K)
```

**What it means**: The spectrum is discrete - eigenvalues don't accumulate at finite points.

### Eigenvalues Unbounded

```lean
theorem eigenvalue_sequence_unbounded :
    Tendsto (fun n => |eigenvalue_sequence H_psi n|) atTop atTop
```

**What it means**: Eigenvalues grow to infinity: λₙ → ∞ as n → ∞.

### Main Trace Formula

```lean
theorem trace_equals_zeta_everywhere (s : ℂ) (hs : s.re > 1) :
    spectral_sum H_psi s = (π^(-s/2) * Gamma (s/2)) * riemannZeta s
```

**What it means**: The spectral trace equals a modified zeta function.

### Complete Characterization

```lean
theorem complete_spectral_characterization (s : ℂ) (hs : s.re > 1) :
    (∀ n : ℕ, is_zeta_zero_imaginary_part (eigenvalue_sequence H_psi n)) ∧
    (spectral_sum H_psi s = (π^(-s/2) * Gamma (s/2)) * riemannZeta s) ∧
    (∃ c : ℂ, c ≠ 0 ∧ spectral_determinant H_psi s = 
      c * (s * (s - 1) * π^(-s/2) * Gamma(s/2) * riemannZeta s))
```

**What it means**: Complete connection between spectrum, zeta, and determinant.

## Common Patterns

### Pattern 1: Check if a Value is an Eigenvalue

```lean
example : λ ∈ eigenvalues_H_psi H_psi ↔ 
    ∃ n : ℕ, λ = eigenvalue_sequence H_psi n := by
  rw [← eigenvalue_sequence_complete]
  rfl
```

### Pattern 2: Verify Zeta Zero Correspondence

```lean
example (t : ℝ) : 
    is_zeta_zero_imaginary_part t → 
    t ∈ eigenvalues_H_psi H_psi :=
  zeta_zero_is_eigenvalue H_psi t
```

### Pattern 3: Compute Spectral Trace

```lean
example (s : ℂ) (hs : s.re > 1) :
    spectral_sum H_psi s = ∑' n, (eigenvalue_sequence H_psi n)^(-s) :=
  rfl
```

### Pattern 4: Use Functional Equation

```lean
example (s : ℂ) :
    spectral_determinant H_psi (1 - s) = spectral_determinant H_psi s :=
  spectral_determinant_functional_equation H_psi s
```

## QCAL Integration

### Base Frequency

```lean
#check QCAL_base_frequency  -- 141.7001 Hz
```

### Coherence Constant

```lean
#check QCAL_coherence  -- 244.36
```

### Coherence Theorem

```lean
theorem QCAL_spectral_coherence :
    ∃ (I A_eff : ℝ), I > 0 ∧ A_eff > 0 ∧
      QCAL_coherence = I * A_eff^2
```

## Typical Workflow

### Step 1: Set up the operator

```lean
variable {H : Type _} [NormedAddCommGroup H] 
         [InnerProductSpace ℂ H] [CompleteSpace H]
variable (H_psi : H →L[ℂ] H)
```

### Step 2: Access eigenvalues

```lean
def eigenvalues := eigenvalue_sequence H_psi
```

### Step 3: Use spectral properties

```lean
-- Positivity
have h_pos : ∀ n, 0 < eigenvalues n := eigenvalue_sequence_pos H_psi

-- Growth
have h_unbdd : Tendsto (fun n => |eigenvalues n|) atTop atTop :=
  eigenvalue_sequence_unbounded H_psi
```

### Step 4: Apply trace formula

```lean
-- For s with Re(s) > 1
variable (s : ℂ) (hs : s.re > 1)

-- Main formula
have trace_formula : spectral_sum H_psi s = 
    (π^(-s/2) * Gamma (s/2)) * riemannZeta s :=
  trace_equals_zeta_everywhere H_psi s hs
```

### Step 5: Work with spectral determinant

```lean
-- D(s) is entire
have entireness := spectral_determinant_entire H_psi

-- Zeros at eigenvalues
have zeros : ∀ n, spectral_determinant H_psi (eigenvalues n) = 0 :=
  fun n => (spectral_determinant_zeros H_psi _).mpr ⟨n, rfl⟩

-- Functional equation
have func_eq : ∀ s, spectral_determinant H_psi (1 - s) = 
                     spectral_determinant H_psi s :=
  spectral_determinant_functional_equation H_psi
```

## Axioms Reference

Quick reference for the 5 main axioms:

| Axiom | Purpose |
|-------|---------|
| `H_psi_compact_resolvent` | Discrete spectrum |
| `riemann_hypothesis` | Zeros on critical line |
| `spectrum_zeta_bijection` | ⭐ Main correspondence |
| `spectral_determinant_entire` | D(s) holomorphic |
| `spectral_determinant_functional_equation` | D(1-s) = D(s) |

## Error Messages and Solutions

### Error: "Re(s) > 1 required"

**Solution**: Add hypothesis `(hs : s.re > 1)` to use trace formula.

### Error: "Summable required"

**Solution**: Use `eigenvalue_sum_converges H_psi s hs` to prove summability.

### Error: "Type mismatch: expected ℂ, got ℝ"

**Solution**: Use coercion `(λ : ℂ)` for eigenvalues.

## Performance Tips

1. **Cache eigenvalues**: Store `eigenvalue_sequence H_psi n` in a def
2. **Use simp**: Many basic properties are simp lemmas
3. **Avoid recomputation**: Use `have` to store intermediate results

## Next Steps

1. Read the full README: `SPECTRAL_THEORY_TRACE_FORMULA_README.md`
2. Explore examples in the test files
3. Integrate with your own proofs
4. Contribute improvements!

## Support

- **Documentation**: See README file
- **Examples**: Check test files
- **QCAL**: DOI 10.5281/zenodo.17379721
- **Author**: José Manuel Mota Burruezo Ψ ✧ ∞³

---

♾️³ Happy proving! QCAL coherence maintained.
