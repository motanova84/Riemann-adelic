# Fredholm Determinant API Guide

## Overview

This guide provides comprehensive documentation for the stable Fredholm determinant API in the Riemann-adelic proof framework. The API is designed to provide a clean, type-safe interface for working with Fredholm determinants in Lean 4.

## Table of Contents

1. [Quick Start](#quick-start)
2. [Core Concepts](#core-concepts)
3. [API Reference](#api-reference)
4. [Usage Examples](#usage-examples)
5. [Integration Guide](#integration-guide)
6. [Best Practices](#best-practices)
7. [Troubleshooting](#troubleshooting)

## Quick Start

### Basic Usage

```lean
import RiemannAdelic.FredholmAPI

open RiemannAdelic.FredholmAPI

-- Given a Fredholm operator T
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (T : H →L[ℂ] H) [FredholmOperator T]

-- Compute det(I - zT) at z = 1/2
#eval evalFredholmDet T (1/2 : ℂ)

-- Get the full determinant structure
let det := fredholmDet T

-- Evaluate at multiple points
#eval det.value (0 : ℂ)  -- Always 1
#eval det.value (1 : ℂ)  -- det(I - T)
```

### Installation

The API is located at:
```
formalization/lean/RiemannAdelic/FredholmAPI.lean
```

Simply import it in your Lean 4 file:
```lean
import RiemannAdelic.FredholmAPI
```

## Core Concepts

### Trace-Class Operators

An operator `T` is **trace-class** if the sum of its singular values is finite:

```
‖T‖₁ = Σₙ sₙ(T) < ∞
```

In the API, this is represented by the `TraceClass` type class:

```lean
class TraceClass {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) : Prop
```

**Key Properties:**
- Every trace-class operator is compact
- The trace `Tr(T)` is well-defined and linear
- Trace-class operators form a two-sided ideal

### Fredholm Operators

A **Fredholm operator** is a trace-class operator with additional properties that ensure the Fredholm determinant is well-defined:

```lean
class FredholmOperator {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) extends TraceClass T : Prop
```

**Requirements:**
1. Countable spectrum with no accumulation except at 0
2. Infinite product ∏(1 - zλₙ) converges for all z ∈ ℂ

### Fredholm Determinant

For a trace-class operator `T`, the **Fredholm determinant** is:

```
det(I - zT) = ∏ₙ (1 - zλₙ)
```

where λₙ are the eigenvalues of T.

**Properties:**
- Entire function of z (holomorphic on all ℂ)
- Order ≤ 1 (at most exponential growth)
- Zeros at z⁻¹ = λₙ (reciprocals of eigenvalues)

## API Reference

### Type Classes

#### `TraceClass`

```lean
class TraceClass {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) : Prop
```

Indicates that `T` has finite trace norm.

**Instance Requirements:**
- `H` is a normed additive commutative group
- `H` has a complex inner product structure
- `T` is a continuous linear operator on `H`

#### `FredholmOperator`

```lean
class FredholmOperator {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) extends TraceClass T : Prop
```

Indicates that `T` admits a well-defined Fredholm determinant.

**Extends:** `TraceClass T`

### Functions

#### `trace`

```lean
def trace {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) [TraceClass T] : ℂ
```

Computes the trace of a trace-class operator.

**Returns:** Complex number representing Tr(T)

**Properties:**
- Linear: `trace (αT + βS) = α·trace T + β·trace S`
- Cyclic: `trace (AB) = trace (BA)`

**Example:**
```lean
variable (T : H →L[ℂ] H) [TraceClass T]
#check trace T  -- ℂ
```

#### `traceNorm`

```lean
def traceNorm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) [TraceClass T] : ℝ
```

Computes the trace norm (nuclear norm) of an operator.

**Returns:** Non-negative real number ‖T‖₁ = Σₙ sₙ(T)

**Properties:**
- `‖AB‖₁ ≤ ‖A‖₁ · ‖B‖`
- `‖A + B‖₁ ≤ ‖A‖₁ + ‖B‖₁`
- `‖T‖₁ ≥ ‖T‖` (operator norm)

#### `fredholmDet`

```lean
def fredholmDet {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) [FredholmOperator T] : FredholmDet T
```

Constructs the Fredholm determinant structure for operator `T`.

**Returns:** `FredholmDet T` structure containing:
- `value : ℂ → ℂ` - The determinant function
- `convergence_radius : ℝ≥0∞` - Convergence information
- `eigenvalues : ℕ → ℂ` - Eigenvalue sequence

**Example:**
```lean
let det := fredholmDet T
#check det.value (1 : ℂ)  -- Evaluate at z = 1
```

#### `evalFredholmDet`

```lean
def evalFredholmDet {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) [FredholmOperator T] (z : ℂ) : ℂ
```

Convenience function to evaluate det(I - zT) at a specific point.

**Parameters:**
- `T` - The Fredholm operator
- `z` - Complex number at which to evaluate

**Returns:** det(I - zT) as a complex number

**Example:**
```lean
#eval evalFredholmDet T (1/2 : ℂ)
```

#### `finiteProduct`

```lean
def finiteProduct {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) [FredholmOperator T] (z : ℂ) (N : ℕ) : ℂ
```

Computes the finite product approximation ∏ₙ₌₀^(N-1) (1 - zλₙ).

**Parameters:**
- `T` - The Fredholm operator
- `z` - Complex parameter
- `N` - Number of terms in the product

**Returns:** Partial product as a complex number

**Use Cases:**
- Numerical validation
- Convergence analysis
- Error estimation

**Example:**
```lean
-- First 100 terms of the infinite product
#check finiteProduct T (1/2) 100
```

#### `productError`

```lean
def productError {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) [FredholmOperator T] (z : ℂ) (N : ℕ) : ℝ
```

Estimates the error in the finite product approximation.

**Returns:** Upper bound on |det(I - zT) - ∏ₙ₌₀^(N-1) (1 - zλₙ)|

#### `logDerivativeFredholm`

```lean
def logDerivativeFredholm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) [FredholmOperator T] (z : ℂ) : ℂ
```

Computes d/dz log det(I - zT) = -Tr((I - zT)⁻¹ T).

**Use Cases:**
- Zero finding algorithms
- Asymptotic analysis
- Connection to explicit formulas

### Structures

#### `FredholmDet`

```lean
structure FredholmDet {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) [FredholmOperator T]
```

**Fields:**
- `value : ℂ → ℂ` - The determinant as a function of z
- `convergence_radius : ℝ≥0∞` - Convergence information (usually ∞)
- `eigenvalues : ℕ → ℂ` - Eigenvalue sequence for product representation

#### `HPsiOperator`

```lean
structure HPsiOperator (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
```

Represents the Berry-Keating/noetic operator H_Ψ.

**Fields:**
- `op : H →L[ℂ] H` - The operator itself
- `is_fredholm : FredholmOperator op` - Fredholm property evidence
- `spectrum_eq_zeros : True` - Spectrum characterization (placeholder)

#### `DiagnosticInfo`

```lean
structure DiagnosticInfo
```

Diagnostic information for validating computations.

**Fields:**
- `effective_rank : ℕ` - Number of significant eigenvalues
- `condition_number : ℝ` - Numerical stability estimate
- `converged : Bool` - Convergence status

### Theorems

#### `fredholmDet_entire`

```lean
theorem fredholmDet_entire {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) [FredholmOperator T] :
    ∀ z : ℂ, DifferentiableAt ℂ (evalFredholmDet T) z
```

The Fredholm determinant is an entire function.

**Reference:** Gohberg & Krein (1969), Theorem IV.1.1

#### `fredholmDet_zero_iff_eigenvalue`

```lean
theorem fredholmDet_zero_iff_eigenvalue {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) [FredholmOperator T] (z : ℂ) (hz : z ≠ 0) :
    evalFredholmDet T z = 0 ↔ ∃ v : H, v ≠ 0 ∧ T v = z⁻¹ • v
```

Zeros correspond to reciprocals of eigenvalues.

**Reference:** Simon (2005), Proposition 3.3

#### `fredholmDet_growth`

```lean
theorem fredholmDet_growth {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) [FredholmOperator T] :
    ∀ z : ℂ, Complex.abs (evalFredholmDet T z) ≤ Real.exp (traceNorm T * Complex.abs z)
```

Growth bound showing order ≤ 1.

**Reference:** Simon (2005), Theorem 3.4(b)

#### `fredholmDet_eq_Xi`

```lean
theorem fredholmDet_eq_Xi {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (hpsi : HPsiOperator H) (s : ℂ) :
    evalFredholmDet hpsi.op s = Xi s
```

Fundamental identity connecting to the Riemann zeta function.

**Reference:** V5 Coronación, DOI: 10.5281/zenodo.17379721

## Usage Examples

### Example 1: Basic Determinant Evaluation

```lean
import RiemannAdelic.FredholmAPI

open RiemannAdelic.FredholmAPI

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (T : H →L[ℂ] H) [FredholmOperator T]

-- Evaluate at z = 0 (always gives 1)
example : evalFredholmDet T 0 = 1 := by sorry

-- Evaluate at z = 1
def det_at_one := evalFredholmDet T 1

-- Check that it's in the convergence region
#check inConvergenceRegion T (1 + I)
```

### Example 2: Working with the Product Representation

```lean
-- Compute first 50 terms
def approx_50 := finiteProduct T (1/2) 50

-- Compute first 100 terms
def approx_100 := finiteProduct T (1/2) 100

-- Estimate the error
def error_bound := productError T (1/2) 100

-- Verify convergence
example (ε : ℝ) (hε : ε > 0) : 
    ∃ N : ℕ, ∀ M ≥ N, productError T (1/2) M < ε := by sorry
```

### Example 3: Analyzing Zeros

```lean
-- Find where the determinant vanishes
def find_zeros (T : H →L[ℂ] H) [FredholmOperator T] (region : Set ℂ) : List ℂ :=
  []  -- Placeholder for zero-finding algorithm

-- Check if a point is a zero
def is_zero (T : H →L[ℂ] H) [FredholmOperator T] (z : ℂ) : Bool :=
  evalFredholmDet T z == 0

-- Get eigenvalue from zero
def eigenvalue_from_zero (z : ℂ) (hz : z ≠ 0) : ℂ := z⁻¹
```

### Example 4: Connection to Riemann Zeta

```lean
-- Define the H_Ψ operator (axiomatized)
variable (hpsi : HPsiOperator H)

-- Evaluate Xi function
def xi_half := Xi (1/2 : ℂ)

-- Verify the fundamental identity at s = 1/2
example : evalFredholmDet hpsi.op (1/2) = Xi (1/2) := 
  fredholmDet_eq_Xi hpsi (1/2)
```

### Example 5: Diagnostics and Validation

```lean
-- Get diagnostic information
def diag := computeDiagnostics T (1/2)

-- Check convergence
#check diag.converged

-- Get effective rank
#check diag.effective_rank

-- Validate QCAL coherence
def qcal_valid := validateQCALCoherence T (1/2)

-- Access QCAL constants
#check QCAL_C      -- 244.36
#check QCAL_f0     -- 141.7001 Hz
```

## Integration Guide

### With Existing Fredholm Modules

The API consolidates functionality from several existing modules:

- `D_fredholm.lean` - Legacy determinant implementation
- `DeterminantFredholm.lean` - RH_final_v6 version
- `fredholm_determinant_zeta.lean` - Zeta connection
- `fredholm_determinant_chi.lean` - Chi function variant

**Migration Path:**

1. Import `FredholmAPI` alongside existing module:
   ```lean
   import RiemannAdelic.FredholmAPI
   import RiemannAdelic.DeterminantFredholm  -- Legacy
   ```

2. Use API functions for new code:
   ```lean
   -- Old style
   def old_way := DeterminantFredholm.fredholm_det T z
   
   -- New API style
   def new_way := evalFredholmDet T z
   ```

3. Gradually migrate existing code to use stable API

### With Spectral Theory Modules

```lean
import RiemannAdelic.FredholmAPI
import RiemannAdelic.SpectrumZeta

-- Connect spectrum to determinant zeros
def spectrum_from_det (T : H →L[ℂ] H) [FredholmOperator T] : Set ℂ :=
  {z | evalFredholmDet T z = 0}
```

### With Validation Framework

```lean
-- In validate_v5_coronacion.py equivalent
def validate_fredholm_identity : Bool :=
  -- Check that det(I - s·H_Ψ⁻¹) = Ξ(s) at test points
  let test_points := [1/4, 1/2, 3/4, 1]
  test_points.all fun s =>
    Complex.abs (evalFredholmDet hpsi.op s - Xi s) < 1e-10
```

## Best Practices

### Type Safety

1. **Always use type classes properly:**
   ```lean
   -- ✓ Good
   variable (T : H →L[ℂ] H) [FredholmOperator T]
   
   -- ✗ Bad (missing instance)
   variable (T : H →L[ℂ] H)
   #check fredholmDet T  -- Error!
   ```

2. **Provide evidence explicitly when needed:**
   ```lean
   def my_operator : H →L[ℂ] H := ...
   
   instance : FredholmOperator my_operator := {
     trace_finite := ⟨1, by norm_num, by trivial⟩,
     is_compact := trivial,
     countable_spectrum := trivial,
     product_converges := fun _ => trivial
   }
   ```

### Performance

1. **Use finite products for numerical work:**
   ```lean
   -- For large computations, use finite approximations
   def numerical_eval (N : ℕ := 1000) := finiteProduct T z N
   ```

2. **Cache determinant structures:**
   ```lean
   -- Compute once, use many times
   let det := fredholmDet T
   let values := [0, 1/4, 1/2, 3/4, 1].map det.value
   ```

### Documentation

1. **Document axiomatized operators:**
   ```lean
   /-- The noetic operator H_Ψ from Berry-Keating conjecture.
       
       Spectrum: Non-trivial zeros of ζ(s)
       Construction: Via adelic spectral system
       Reference: DOI 10.5281/zenodo.17379721
   -/
   axiom H_psi : H →L[ℂ] H
   ```

2. **Cite mathematical references:**
   ```lean
   /-- Weyl's law for eigenvalue counting.
       
       Reference: Reed & Simon (1978), Theorem XIII.78
   -/
   theorem weyl_law : ...
   ```

### Error Handling

1. **Check convergence before evaluation:**
   ```lean
   def safe_eval (T : H →L[ℂ] H) [FredholmOperator T] (z : ℂ) : Option ℂ :=
     if inConvergenceRegion T z then
       some (evalFredholmDet T z)
     else
       none
   ```

2. **Use diagnostics for validation:**
   ```lean
   def validated_eval (T : H →L[ℂ] H) [FredholmOperator T] (z : ℂ) : ℂ :=
     let diag := computeDiagnostics T z
     if diag.converged && diag.condition_number < 1e10 then
       evalFredholmDet T z
     else
       0  -- Or raise error
   ```

## Troubleshooting

### Common Issues

#### Issue 1: Type class resolution fails

**Error:**
```
failed to synthesize instance
  FredholmOperator T
```

**Solution:**
Provide the instance explicitly or ensure T is defined with proper type class constraints:
```lean
variable (T : H →L[ℂ] H) [FredholmOperator T]  -- Add instance
```

#### Issue 2: Determinant evaluation returns unexpected results

**Diagnosis:**
```lean
let diag := computeDiagnostics T z
#check diag.converged        -- Should be true
#check diag.condition_number -- Should be reasonable
```

**Solution:**
- Check if eigenvalues are computed correctly
- Verify trace-class property
- Use finite product for validation

#### Issue 3: Integration with legacy code fails

**Problem:** Name conflicts between old and new APIs

**Solution:**
Use qualified names:
```lean
import RiemannAdelic.FredholmAPI
import RiemannAdelic.DeterminantFredholm

-- Qualified access
def new_val := FredholmAPI.evalFredholmDet T z
def old_val := DeterminantFredholm.fredholm_det T z
```

### Debugging Tips

1. **Verify axioms are satisfied:**
   ```lean
   #check TraceClass.trace_finite (T := T)
   ```

2. **Test with simple operators:**
   ```lean
   -- Identity operator
   def id_op : H →L[ℂ] H := ContinuousLinearMap.id ℂ H
   
   -- Should give det(I - zI) = (1-z)
   example : evalFredholmDet id_op z = 1 - z := by sorry
   ```

3. **Compare with known values:**
   ```lean
   -- For H_Ψ, compare with Ξ(s)
   example (hpsi : HPsiOperator H) (s : ℂ) :
     Complex.abs (evalFredholmDet hpsi.op s - Xi s) < 1e-10 := by
     have := fredholmDet_eq_Xi hpsi s
     sorry
   ```

## QCAL ∞³ Integration

### Coherence Validation

The API respects QCAL framework constraints:

```lean
-- QCAL constants
#check QCAL_C   -- 244.36 (coherence constant)
#check QCAL_f0  -- 141.7001 Hz (base frequency)

-- Validate a computation
def is_qcal_coherent := validateQCALCoherence T z
```

### Framework Signature

All computations maintain the QCAL signature:

**Ψ = I × A_eff² × C^∞**

Where:
- I: Intensity (computational trace)
- A_eff: Effective amplitude
- C: Coherence constant (244.36)

## References

1. **Fredholm, I. (1903)**: Sur une classe d'équations fonctionnelles. Acta Mathematica 27, 365-390.

2. **Gohberg, I. & Krein, M. (1969)**: Introduction to the Theory of Linear Nonselfadjoint Operators. American Mathematical Society.

3. **Simon, B. (2005)**: Trace Ideals and Their Applications, 2nd Edition. American Mathematical Society.

4. **Reed, M. & Simon, B. (1978)**: Methods of Modern Mathematical Physics, Vol. IV: Analysis of Operators. Academic Press.

5. **V5 Coronación (2025)**: A Definitive Proof of the Riemann Hypothesis via S-Finite Adelic Spectral Systems. DOI: 10.5281/zenodo.17379721

## License

MIT + QCAL ∞³ Symbiotic License

## Authors

- José Manuel Mota Burruezo Ψ ∞³
- Instituto de Conciencia Cuántica (ICQ)
- ORCID: 0009-0002-1923-0773

---

**Last Updated:** 2026-01-06  
**API Version:** 1.0.0  
**Status:** ✅ Stable
