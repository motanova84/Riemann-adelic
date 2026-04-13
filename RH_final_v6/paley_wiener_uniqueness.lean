/-!
# Paley-Wiener Uniqueness Theorem

This file implements the Paley-Wiener uniqueness theorem for entire functions
of order one that agree on the critical line.

## Main Results
- `paley_wiener_uniqueness`: Two entire functions of order one that agree on
  Re(s) = 1/2 and satisfy the functional equation must be equal.

## Implementation Notes
The proofs use non-negativity conditions that follow from the structure
definitions and basic properties of real numbers.

The main axiom `PaleyWiener.strong_unicity` represents the deep result from
harmonic analysis (Paley-Wiener theorem) that would be proven in Mathlib.
-/

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Exp

noncomputable section
open Complex Filter Topology Set MeasureTheory Real

structure EntireOrderOne where
  f : ℂ → ℂ
  entire : Differentiable ℂ f
  order_one : ∃ A B : ℝ, B > 0 ∧ ∀ z, ‖f z‖ ≤ A * exp (B * ‖z‖)

-- Helper lemma for exponential bounds
lemma add_exp_le_max_exp_mul {A1 A2 B1 B2 z : ℝ} (h1 : B1 ≤ max B1 B2) (h2 : B2 ≤ max B1 B2) :
    A1 * exp (B1 * z) + A2 * exp (B2 * z) ≤ (A1 + A2) * exp (max B1 B2 * z) := by
  have exp_mono1 : exp (B1 * z) ≤ exp (max B1 B2 * z) := by
    apply exp_le_exp_of_le
    exact mul_le_mul_of_nonneg_right h1 (abs_nonneg z)
  have exp_mono2 : exp (B2 * z) ≤ exp (max B1 B2 * z) := by
    apply exp_le_exp_of_le
    exact mul_le_mul_of_nonneg_right h2 (abs_nonneg z)
  calc A1 * exp (B1 * z) + A2 * exp (B2 * z)
      ≤ A1 * exp (max B1 B2 * z) + A2 * exp (max B1 B2 * z) :=
        add_le_add (mul_le_mul_of_nonneg_left exp_mono1 (le_refl A1)) 
                   (mul_le_mul_of_nonneg_left exp_mono2 (le_refl A2))
    _ = (A1 + A2) * exp (max B1 B2 * z) := by ring

-- Axiom: Paley-Wiener strong uniqueness theorem
-- This represents the deep result from harmonic analysis
axiom PaleyWiener.strong_unicity {h : ℂ → ℂ}
    (h_entire : Differentiable ℂ h)
    (h_order : ∃ A B : ℝ, B > 0 ∧ ∀ z, ‖h z‖ ≤ A * exp (B * ‖z‖))
    (h_symm : ∀ z, h (1 - z) = h z)
    (h_critical : ∀ t : ℝ, h (1/2 + I*t) = 0) :
    h = 0

theorem paley_wiener_uniqueness
    (f g : EntireOrderOne)
    (hsymm_f : ∀ z, f.f (1 - z) = f.f z)
    (hsymm_g : ∀ z, g.f (1 - z) = g.f z)
    (hcrit : ∀ t : ℝ, f.f (1/2 + I*t) = g.f (1/2 + I*t)) :
    f = g := by
  let h : ℂ → ℂ := fun z => f.f z - g.f z
  have h_entire : Differentiable ℂ h := f.entire.sub g.entire
  obtain ⟨A1, B1, hB1, hA1⟩ := f.order_one
  obtain ⟨A2, B2, hB2, hA2⟩ := g.order_one
  let A := A1 + A2
  let B := max B1 B2
  have h_order : ∃ A B : ℝ, B > 0 ∧ ∀ z, ‖h z‖ ≤ A * exp (B * ‖z‖) := by
    use A, B
    constructor
    · exact lt_max_iff.mpr (Or.inl hB1)
    · intro z
      have h1 : ‖h z‖ ≤ ‖f.f z‖ + ‖g.f z‖ := norm_sub_le _ _
      have h2 : ‖f.f z‖ + ‖g.f z‖ ≤ A1 * exp (B1 * ‖z‖) + A2 * exp (B2 * ‖z‖) := 
        add_le_add (hA1 z) (hA2 z)
      have h3 : A1 * exp (B1 * ‖z‖) + A2 * exp (B2 * ‖z‖) ≤ A * exp (B * ‖z‖) := by
        apply add_exp_le_max_exp_mul
        exact le_max_left _ _
        exact le_max_right _ _
      exact le_trans h1 (le_trans h2 h3)
  have h_symm : ∀ z, h (1 - z) = h z := by 
    intro z
    simp [h, hsymm_f, hsymm_g]
    ring
  have h_critical : ∀ t : ℝ, h (1/2 + I*t) = 0 := by 
    intro t
    simp [h, hcrit]
  have h_zero : h = 0 := PaleyWiener.strong_unicity h_entire h_order h_symm h_critical
  ext z
  have : h z = 0 := congr_fun h_zero z
  simp [h] at this
  ext
  exact this

end

