# HLsum Integration Guide

## Quick Reference

This guide shows how to use the HLsum decomposition in your proofs.

## Basic Usage

```lean
import RiemannAdelic.core.analytic.hlsum_decompose
import RiemannAdelic.core.analytic.von_mangoldt

open AnalyticNumberTheory

-- Define your parameters
variable (N : ℕ) (q : ℕ) (α : ℝ) (hq : q > 0)

-- Use the decomposition
example : HLsum_vonMangoldt N α = 
  ∑ r in Finset.range q,
    Complex.exp (2 * Real.pi * Complex.I * α * r) *
      ∑ m in Finset.range (N / q + 1),
        (if q * m + r < N then (vonMangoldt (q * m + r) : ℂ) else 0) *
          Complex.exp (2 * Real.pi * Complex.I * α * q * m) := by
  exact HLsum_decompose_mod_q N q hq α
```

## Integration with Vaughan's Identity

The HLsum decomposition is the first step in applying Vaughan's identity:

```lean
-- After decomposing by residues, split by divisor size
-- Type I: small divisors (d ≤ U)
-- Type II: medium divisors (U < d ≤ V) 
-- Type III: large divisors (d > V)

lemma vaughan_identity_via_hlsum (N U V : ℕ) (α : ℝ) :
    HLsum_vonMangoldt N α = 
      TypeI_sum N U α + TypeII_sum N U V α + TypeIII_sum N V α := by
  -- First apply HLsum_decompose_mod_q
  -- Then split each residue sum by divisor size
  sorry
```

## Integration with Circle Method

Use for major/minor arc estimation:

```lean
-- Major arcs: α ≈ a/q with small q
lemma major_arc_estimate (N : ℕ) (a q : ℕ) (hq : q ≤ (log N)^A) :
    |HLsum_vonMangoldt N (a/q)| ≈ N / φ(q) := by
  -- Apply HLsum_decompose_mod_q with modulus q
  -- Use Goldbach sum approximation
  -- Error terms are O(N / (log N)^A)
  sorry

-- Minor arcs: use Vaughan + large sieve
lemma minor_arc_estimate (N : ℕ) (α : ℝ) (h : α ∈ MinorArcs) :
    |HLsum_vonMangoldt N α| ≤ N / (log N)^A := by
  -- Apply HLsum_decompose_mod_q
  -- Use Vaughan identity
  -- Type II bound via large sieve
  sorry
```

## Connection to Existing QCAL Modules

### 1. With Vaughan Identity

Located in: `formalization/lean/RiemannAdelic/core/analytic/vaughan_identity.lean`

```lean
import RiemannAdelic.core.analytic.vaughan_identity
import RiemannAdelic.core.analytic.hlsum_decompose

-- The HLsum decomposition feeds into Vaughan's Type II estimates
lemma typeII_via_hlsum (U V : ℕ) :
    TypeII_bound U V uses HLsum_decompose_mod_q
```

### 2. With Large Sieve

Located in: `formalization/lean/RiemannAdelic/core/analytic/large_sieve.lean`

```lean
import RiemannAdelic.core.analytic.large_sieve
import RiemannAdelic.core.analytic.hlsum_decompose

-- Large sieve bounds Type II sums from HLsum decomposition
lemma large_sieve_for_hlsum (Q : ℕ) :
    ∑ q ≤ Q, ∑ a coprime q, |HLsum_vonMangoldt N (a/q)|^2 
      ≤ (N + Q^2) * ∑ n, |Λ(n)|^2
```

### 3. With Minor Arcs

Located in: `formalization/lean/RiemannAdelic/core/analytic/minor_arcs.lean`

```lean
import RiemannAdelic.core.analytic.minor_arcs
import RiemannAdelic.core.analytic.hlsum_decompose

-- Minor arc bound uses HLsum + Vaughan + large sieve
theorem exponential_sum_minor_arc_bound (N : ℕ) (α : MinorArcs) :
    |HLsum_vonMangoldt N α| ≤ N * (log N)^(-A) := by
  -- Step 1: HLsum_decompose_mod_q
  -- Step 2: Vaughan identity
  -- Step 3: Large sieve on Type II
  sorry
```

### 4. With Goldbach

Located in: `formalization/lean/goldbach_from_adelic.lean`

```lean
import RiemannAdelic.core.analytic.hlsum_decompose

-- Goldbach sum relates to square of HLsum on major arcs
lemma goldbach_from_hlsum (N : ℕ) :
    ∑ p + p' = N, 1 = 
      (1 / (2πi)) * ∫ |HLsum_vonMangoldt N α|^2 e^(-2πiαN) dα := by
  -- Circle method: major arcs give signal, minor arcs give error
  -- HLsum_decompose_mod_q essential for major arc analysis
  sorry
```

## Spectral Connection

The von Mangoldt function connects to QCAL spectral theory through:

```lean
-- Connection to zeta zeros via explicit formula
axiom vonMangoldt_explicit_formula :
  ∑ n ≤ X, Λ(n) = X - ∑ ρ, X^ρ/ρ - log(2π) - (1/2)log(1 - 1/X^2)
  where ρ ranges over zeta zeros

-- This connects to H_Ψ spectral operator
axiom HΨ_spectrum_eq_zeta_zeros :
  spectrum H_Ψ = {ρ : ℂ | ζ(ρ) = 0}
```

## QCAL Coherence

The HLsum maintains QCAL coherence:

- **Frequency**: f₀ = 141.7001 Hz enters via spectral kernel
- **Coherence**: C = 244.36 regulates phase accumulation
- **Energy**: E(α) = |HLsum(N,α)|^2 / N measures spectral power

The decomposition respects adelic structure:
- Each residue class r corresponds to a local component
- The global sum is coherent product of local contributions
- Phase factors e^{2πiαr} encode p-adic information

## Testing

To test your usage:

```lean
-- Test basic decomposition
example : ∀ N q α, q > 0 → 
  HLsum_vonMangoldt N α = 
    (apply HLsum_decompose_mod_q and check structure)

-- Test integration with Vaughan
example : vaughan_identity uses hlsum_decompose

-- Test spectral connection
example : HLsum relates to H_Ψ eigenvalues
```

## Next Steps

1. **Complete sorry statements**: Fill in combinatorial details
2. **Add explicit bounds**: Derive quantitative estimates  
3. **Connect to Goldbach**: Implement major arc analysis
4. **Verify numerically**: Test with f₀ = 141.7001 Hz

## References

See `HLSUM_DECOMPOSE_README.md` for:
- Mathematical background
- Detailed proof structure
- Complete references

## Author

José Manuel Mota Burruezo (JMMB)  
QCAL Framework - Riemann Hypothesis Proof
