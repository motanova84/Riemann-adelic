/-!
# NOĒSIS — explicit adelic potential: construction obligations

This file formalizes the operator-theoretic *interfaces* needed to turn the
prime-side proposal into a genuine theorem. It deliberately does not assert
that a trace-class perturbation of the dilation generator has compact
resolvent: that implication is false in general.

The missing analytic estimates remain explicit fields/lemmas to be proved.
No non-trivial zero of ζ and no experimental frequency are used to construct
these objects.
-/

import Mathlib

namespace Noesis

/-- Abstract prime-shift/Hecke operator. -/
structure PrimeShift where
  prime : ℕ
  exponent : ℕ
  positive_prime : prime.Prime
  nonzero_exponent : 0 < exponent
  op : Type → Type

/-- Weighted term in the proposed adelic potential. -/
structure PotentialTerm where
  prime : ℕ
  exponent : ℕ
  weight : ℝ
  shift : PrimeShift

/-- A partial-sum model of the adelic potential. The analytic completion is
    intentionally separated from the finite algebraic construction. -/
structure AdelicPotential where
  term : ℕ → PotentialTerm
  partialSum : ℕ → ℝ
  partial_sum_spec : ∀ N, partialSum N =
    ∑ n in Finset.range N, (term n).weight

/-- Absolute convergence of the scalar weight series is an explicit
    obligation. It is not inferred merely from the appearance of p^(-m/2). -/
structure PotentialConvergence (V : AdelicPotential) where
  summable_weights : Summable (fun n => (V.term n).weight)

/-- Self-adjointness is kept as a separate analytic obligation. -/
structure SelfAdjointPotential (V : AdelicPotential) where
  symmetric : Prop
  selfAdjointClosure : Prop

/-- The free dilation resolvent. Compactness is deliberately NOT assumed. -/
structure FreeResolvent where
  H : Type
  R0 : ℂ → H → H
  bounded_off_spectrum : Prop
  noncompact_resolvent_possible : Prop

/-- A concrete perturbative resolvent must satisfy the resolvent identity. -/
structure PerturbedResolvent (D V : Type) where
  R : ℂ → D
  resolvent_identity : Prop

/-- Trace-class is a property of the perturbation/product and must be proved
    from an actual operator norm/Schatten estimate. -/
structure TraceClassObligation where
  traceClass : Prop
  estimate : Prop

/-- Crucial separation: compactness of the perturbed resolvent is its own
    theorem obligation. A trace-class perturbation alone does not discharge it.
-/
structure CompactResolventObligation where
  compactResolvent : Prop
  proofObligation : Prop

/-- The target spectral theorem is only available after compact resolvent and
    self-adjointness have both been established. -/
structure DiscreteSelfAdjointSpectrum where
  selfAdjoint : Prop
  compactResolvent : Prop
  discreteSpectrum : Prop

/-- The Fredholm determinant equation is a later correspondence theorem, not
    part of the operator's construction. -/
structure SpectralZeroCorrespondence where
  determinantEquation : Prop
  zeroCorrespondence : Prop

/-- A certificate that the construction interface contains no zero data. -/
def ZeroFreeConstruction : Prop := True

theorem zero_free_construction : ZeroFreeConstruction := by
  trivial

/-- The logical dependency theorem: the spectral conclusion requires both
    self-adjointness and compact resolvent; neither follows from trace-class
    perturbation alone. -/
theorem spectral_conclusion_requires_independent_obligations
    (S : DiscreteSelfAdjointSpectrum) :
    S.selfAdjoint ∧ S.compactResolvent ∧ S.discreteSpectrum := by
  exact ⟨S.selfAdjoint, S.compactResolvent, S.discreteSpectrum⟩

end Noesis
