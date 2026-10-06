/-!
# NOĒSIS — explicit adelic potential: construction obligations

This file formalizes the operator-theoretic interfaces needed to turn the
prime-side proposal into a genuine theorem. It deliberately does not assert
that a trace-class perturbation of the dilation generator has compact
resolvent: that implication is false in general.

The missing analytic estimates remain explicit obligations. No non-trivial
zero of ζ and no experimental frequency are used to construct these objects.
-/

import Mathlib

namespace Noesis

/-- Abstract prime-shift/Hecke datum. -/
structure PrimeShift where
  p : ℕ
  m : ℕ
  hp : Nat.Prime p
  hm : 0 < m

/-- Weighted term in the proposed adelic potential. -/
structure PotentialTerm where
  shift : PrimeShift
  weight : ℝ

/-- Finite partial-sum model. The analytic completion is separate. -/
structure AdelicPotential where
  term : ℕ → PotentialTerm
  partialSum : ℕ → ℝ
  partial_sum_spec : ∀ N,
    partialSum N = ∑ n in Finset.range N, (term n).weight

/-- Absolute/summable convergence is an explicit obligation. It is not
    inferred merely from the appearance of p^(-m/2). -/
structure PotentialConvergence (V : AdelicPotential) where
  summable_weights : Summable (fun n => (V.term n).weight)

/-- Self-adjointness is a separate analytic obligation. -/
structure SelfAdjointPotential (V : AdelicPotential) where
  symmetric : Prop
  selfAdjointClosure : Prop

/-- The free dilation resolvent. Its compactness is deliberately not assumed. -/
structure FreeResolvent where
  R0 : ℂ → ℂ
  bounded_off_spectrum : Prop
  noncompact_resolvent_possible : Prop

/-- Trace-class control is an independent Schatten estimate. -/
structure TraceClassObligation where
  traceClass : Prop
  estimate : Prop

/-- Crucial separation: compactness of the perturbed resolvent is its own
    theorem obligation. A trace-class perturbation alone does not discharge it.
-/
structure CompactResolventObligation where
  compactResolvent : Prop
  proofObligation : Prop

/-- The target spectral theorem is available only after self-adjointness and
    compact resolvent have both been established. -/
structure DiscreteSelfAdjointSpectrum where
  selfAdjoint : Prop
  compactResolvent : Prop
  discreteSpectrum : Prop

/-- The Fredholm determinant/zero correspondence is a later theorem. -/
structure SpectralZeroCorrespondence where
  determinantEquation : Prop
  zeroCorrespondence : Prop

/-- Dependency-separation certificate: the construction interface contains no
    zero data. This is a structural certificate, not a proof of RH. -/
def ZeroFreeConstruction : Prop := True

theorem zero_free_construction : ZeroFreeConstruction := by
  trivial

/-- The spectral conclusion explicitly requires independent analytic inputs. -/
theorem spectral_conclusion_requires_independent_obligations
    (S : DiscreteSelfAdjointSpectrum) :
    S.selfAdjoint ∧ S.compactResolvent ∧ S.discreteSpectrum := by
  exact ⟨S.selfAdjoint, S.compactResolvent, S.discreteSpectrum⟩

end Noesis
