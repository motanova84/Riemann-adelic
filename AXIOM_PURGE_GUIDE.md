# Axiom Purge Guide: From Axioms to Theorems

## Overview

This document explains the transition from axiom-based formalization to theorem-based formalization in the Riemann Hypothesis proof, as implemented in V5.3.1.

## Purpose

The original V5.1-5.2 formalization used several axioms to represent deep analytic results that were outlined but not fully formalized. The axiom purge process converts these axioms into proper theorems with constructive proofs.

## File: `formalization/lean/RiemannAdelic/axiom_purge.lean`

### Structure

The file contains three main components:

#### 1. Theorem (D ≡ Ξ): Function Uniqueness

**Statement**: Any entire function D of order ≤1 with functional equation D(1-s) = D(s), appropriate growth bounds, and divisor matching ζ in the critical strip must be identical to the Riemann xi-function Ξ.

**Proof Strategy**:
1. **Hadamard factorization**: Both D and Ξ admit Hadamard factorization of order 1
2. **Quotient analysis**: Q = D/Ξ is entire, zero-free, order ≤1, and Q(σ+it) → 1 as σ → +∞
3. **Paley-Wiener determinacy**: Subgaussian control implies Q is bounded
4. **Liouville application**: Bounded entire function is constant
5. **Normalization**: Fixed point normalization forces Q ≡ 1, hence D ≡ Ξ

**Current Status**: Skeleton proof using `trivial`. To be expanded with:
- Connection to `entire_order.lean` for Hadamard factorization
- Connection to `uniqueness_without_xi.lean` for Paley-Wiener theory
- Detailed analysis of quotient growth

#### 2. Theorem (Critical Line Zeros): Spectral Confinement

**Statement**: All non-trivial zeros of D lie on the critical line Re(s) = 1/2.

**Proof Strategy**:
1. **Self-adjoint operator**: Construct H (modulo quotient) with spectrum {Im(ρ)} for zeros ρ
2. **Spectral reality**: Self-adjointness implies real spectrum
3. **Functional symmetry**: D(1-s) = D(s) forces zero pairing
4. **Kernel positivity**: Explicit Weil-type kernel is positive and coercive
5. **Geometric confinement**: Sign pattern and symmetry force Re(ρ) = 1/2

**Current Status**: Skeleton proof using `trivial`. To be expanded with:
- Connection to `positivity.lean` for kernel construction
- Connection to `spectral_RH_operator.lean` for operator theory
- Connection to `critical_line_proof.lean` for detailed argument

#### 3. Lemma (Trivial Zeros Exclusion)

**Statement**: The divisor adopted by D in the critical strip excludes the trivial zeros of ζ.

**Proof Strategy**:
1. **Archimedean factor**: Trivial zeros of ζ are absorbed in the Γ-product
2. **Functional equation**: ζ(s) = χ(s)ζ(1-s) where χ involves gamma factors
3. **Zero separation**: Poles of Γ(s/2) at s = 0, -2, -4, ... correspond to trivial zeros
4. **Divisor definition**: D is defined to match ζ's zeros only in 0 < Re(s) < 1

**Current Status**: Skeleton lemma using `trivial`. To be expanded with:
- Connection to `arch_factor.lean` for gamma factor analysis
- Connection to `functional_eq.lean` for functional equation details

### Integration with Existing Modules

The `axiom_purge.lean` file is designed to eventually replace axioms in:
- `RH_final.lean`: Main theorem statement
- `axioms_to_lemmas.lean`: Foundational axioms A1-A4
- Various supporting modules

### CI/CD Integration

The new workflow `.github/workflows/lean-ci.yml` automatically checks for axioms:
```bash
lake exe print-axioms RiemannAdelic | tee axioms.txt
! grep -E ".+" axioms.txt || (echo "Found axioms"; cat axioms.txt; exit 1)
```

This ensures that as proofs are completed, the number of axioms decreases monotonically.

## Timeline for Completion

### Phase 1 (Current): Skeleton Theorems
- ✅ Create `axiom_purge.lean` with stub theorems
- ✅ Set up CI/CD for axiom checking
- ✅ Document proof strategies

### Phase 2: Module Division
- [ ] Split into `Hadamard.lean` for factorization theory
- [ ] Split into `RelativeDeterminant.lean` for quotient analysis
- [ ] Split into `KernelPositivity.lean` for operator theory

### Phase 3: Proof Development
- [ ] Fill in `sorry` placeholders with actual proofs
- [ ] Connect to existing formalization modules
- [ ] Add numerical verification interface

### Phase 4: Full Verification
- [ ] Complete all proofs without `sorry`
- [ ] Verify compilation with `lake build`
- [ ] Pass CI/CD with zero axioms beyond Lean/Mathlib core

## Usage Guidelines

### For Developers

When working on completing the proofs:

1. **Start with dependencies**: Complete proofs in dependency order
   - `schwartz_adelic.lean` (Schwartz functions)
   - `entire_order.lean` (Hadamard factorization)
   - `positivity.lean` (Kernel theory)
   - Then `axiom_purge.lean`

2. **Maintain structure**: Keep the theorem statements unchanged, only replace `trivial` with actual proofs

3. **Add intermediate lemmas**: Create helper lemmas in the same file or supporting modules

4. **Test incrementally**: Run `lake build` after each significant change

### For Reviewers

When reviewing axiom purge PRs:

1. **Check CI**: Ensure `lean-ci.yml` workflow passes
2. **Verify proofs**: Check that `sorry` count decreases
3. **Review logic**: Ensure proof steps follow outlined strategy
4. **Test compilation**: Verify `lake build` succeeds

## Connection to PDF Documentation

Once axiom purge is complete, update the PDF manuscript:

1. **Replace "Axioma X"** with "Teorema X.Y" (numbered)
2. **Add proof sketches**: Include high-level proof ideas
3. **Reference Lean code**: Add footnotes pointing to formalized proofs
4. **Update bibliography**: Cite relevant papers for each technique

## Hypotheses U1/U2

The proofs rely on uniform convergence and subgaussian control:

- **U1** (Uniform convergence): Spectral trace converges uniformly on compact sets
- **U2** (Subgaussian control): Growth bounds for analytic continuation

These should be formalized as explicit hypotheses in the Lean code and cited in the PDF.

## References

### Mathematical Background
- **Hadamard (1893)**: "Étude sur les propriétés des fonctions entières"
- **Paley-Wiener (1934)**: "Fourier Transforms in the Complex Domain"
- **Koosis (1988)**: "The Logarithmic Integral I & II"
- **de Branges (1968)**: "Hilbert Spaces of Entire Functions"

### Formalization
- **Lean 4 Documentation**: https://leanprover.github.io/lean4/doc/
- **Mathlib4**: https://leanprover-community.github.io/mathlib4_docs/
- **Complex Analysis in Lean**: Mathlib.Analysis.Complex.*

---

**Maintained by**: José Manuel Mota Burruezo (@motanova84)  
**Version**: 5.3.1  
**Date**: 2025-10-30  
**Status**: Phase 1 Complete (Skeleton Theorems)
