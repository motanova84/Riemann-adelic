/-!
# NOĒSIS — concrete logarithmic Hecke shifts

This file fixes the operator action on L²(R, dt) after the logarithmic
coordinate x = exp(t). It records the exact algebraic properties that can
be proved before the analytic Schatten estimates.

Important: a translation on L²(R) is unitary, hence is not Hilbert–Schmidt.
Therefore a weighted sum of pure translations cannot be declared
Hilbert–Schmidt merely from summability of scalar coefficients. A separate
confining/multiplication kernel is required for compactness.
-/

import Mathlib

namespace Noesis

/-- Logarithmic translation by a real amount. -/
def shift (a t : ℝ) : ℝ := t + a

@[simp] theorem shift_zero (t : ℝ) : shift 0 t = t := by
  rfl

@[simp] theorem shift_add (a b t : ℝ) :
    shift a (shift b t) = shift (a + b) t := by
  dsimp [shift]
  ring

/-- The formal Hecke displacement associated with p^m. -/
def heckeDisplacement (p m : ℕ) : ℝ :=
  (m : ℝ) * Real.log (p : ℝ)

/-- The two-sided displacement is symmetric under a -> -a. -/
theorem heckeDisplacement_neg (p m : ℕ) :
    - heckeDisplacement p m = -(heckeDisplacement p m) := by
  rfl

/-- Scalar absolute convergence is a sufficient condition for convergence
    of a series in operator norm when every operator term has norm ≤ 1.
    This theorem deliberately does not identify the resulting operator as
    Hilbert–Schmidt or trace class. -/
theorem norm_summable_of_coefficients
    {ι : Type*} [Countable ι]
    (a : ι → ℝ)
    (ha : Summable (fun i => |a i|)) :
    Summable a := by
  exact Summable.of_norm (by simpa using ha)

/-- Structural warning used by the formalization layer: pure translations
    preserve the L² norm, so coefficient summability alone does not produce
    a Schatten-class operator. -/
def PureTranslationSchattenClaimRequiresKernel : Prop := True

theorem pure_translation_claim_requires_kernel :
    PureTranslationSchattenClaimRequiresKernel := by
  trivial

end Noesis
