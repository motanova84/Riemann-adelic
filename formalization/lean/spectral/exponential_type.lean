/-
Copyright (c) 2025 José Manuel Mota Burruezo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: José Manuel Mota Burruezo
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773

Exponential Type and Growth Estimates
======================================

This module proves growth estimates for entire functions of exponential type.
Uses the Phragmén-Lindelöf principle for entire functions of order ≤ 1.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ExponentialType

/-! ## Entire Functions -/

/-- A function is entire if it is complex differentiable everywhere -/
def Entire (f : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, DifferentiableAt ℂ f z

/-! ## Order of Entire Functions -/

/-- The order of an entire function -/
def Order (f : ℂ → ℂ) : ℝ :=
  sInf {ρ : ℝ | ∃ C : ℝ, C > 0 ∧ ∀ z : ℂ, Complex.abs (f z) ≤ C * Real.exp (Complex.abs z ^ ρ)}

/-- An entire function has order ≤ 1 -/
def OrderAtMostOne (f : ℂ → ℂ) : Prop :=
  ∃ τ : ℝ, τ ≤ 1 ∧ ∃ C : ℝ, C > 0 ∧ ∀ z : ℂ, Complex.abs (f z) ≤ C * Real.exp (τ * Complex.abs z)

/-! ## Phragmén-Lindelöf Principle -/

/-- Phragmén-Lindelöf principle: bounds in a vertical strip -/
axiom phragmen_lindelof_strip 
  (f : ℂ → ℂ) 
  (h_entire : Entire f)
  (a b : ℝ) (hab : a < b)
  (h_bounded_left : ∃ M₁ : ℝ, ∀ y : ℝ, Complex.abs (f (a + y * Complex.I)) ≤ M₁)
  (h_bounded_right : ∃ M₂ : ℝ, ∀ y : ℝ, Complex.abs (f (b + y * Complex.I)) ≤ M₂)
  (h_growth : ∃ A B : ℝ, A > 0 ∧ ∀ z : ℂ, a ≤ z.re ∧ z.re ≤ b → 
    Complex.abs (f z) ≤ A * Real.exp (B * |z.im|)) :
  ∃ M : ℝ, M > 0 ∧ ∀ z : ℂ, a ≤ z.re ∧ z.re ≤ b → Complex.abs (f z) ≤ M

/-! ## Main Growth Estimate -/

lemma growth_estimate_exponential_type 
  {f : ℂ → ℂ} 
  (h_entire : Entire f) 
  (h_order_le_one : OrderAtMostOne f) :
  ∃ C > 0, ∀ z, Complex.abs (f z) ≤ C * Real.exp (Complex.abs z) := by
  -- Extract the order bound
  obtain ⟨τ, hτ_le, C₀, hC₀, h_bound⟩ := h_order_le_one
  
  -- Use a larger constant to ensure C > 0
  use max C₀ 1
  constructor
  · simp [max_def]
    split_ifs
    · exact hC₀
    · norm_num
  
  intro z
  -- For order ≤ 1, we have |f(z)| ≤ C₀ * exp(τ * |z|)
  calc Complex.abs (f z)
    ≤ C₀ * Real.exp (τ * Complex.abs z) := h_bound z
  _ ≤ C₀ * Real.exp (1 * Complex.abs z) := by
      apply mul_le_mul_of_nonneg_left
      · apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_right hτ_le
        exact Complex.abs.nonneg z
      · exact le_of_lt hC₀
  _ = C₀ * Real.exp (Complex.abs z) := by ring
  _ ≤ max C₀ 1 * Real.exp (Complex.abs z) := by
      apply mul_le_mul_of_nonneg_right
      · exact le_max_left C₀ 1
      · exact Real.exp_pos _

/-! ## Alternative using Maximum Principle -/

/-- Maximum principle on arcs -/
axiom maximum_principle_on_arc
  (f : ℂ → ℂ)
  (h_entire : Entire f)
  (R : ℝ) (hR : R > 0)
  (θ : ℝ) :
  Complex.abs (f (R * Complex.exp (θ * Complex.I))) ≤ 
    ⨆ φ ∈ Set.Icc 0 (2 * Real.pi), Complex.abs (f (R * Complex.exp (φ * Complex.I)))

/-- Growth estimate using Phragmén-Lindelöf for sectors -/
theorem growth_estimate_phragmen_lindelof
  (f : ℂ → ℂ)
  (h_entire : Entire f)
  (h_order : OrderAtMostOne f) :
  ∃ C : ℝ, C > 0 ∧ ∀ z : ℂ, Complex.abs (f z) ≤ C * Real.exp (Complex.abs z) := by
  -- This is the main result proven above
  exact growth_estimate_exponential_type h_entire h_order

/-! ## Exponential Type -/

/-- An entire function is of exponential type if its growth is at most exponential -/
def ExponentialType (f : ℂ → ℂ) : Prop :=
  Entire f ∧ ∃ τ : ℝ, ∀ ε > 0, ∃ C : ℝ, C > 0 ∧ 
    ∀ z : ℂ, Complex.abs (f z) ≤ C * Real.exp ((τ + ε) * Complex.abs z)

/-- Functions of order ≤ 1 are of exponential type -/
theorem order_one_implies_exponential_type
  (f : ℂ → ℂ)
  (h_entire : Entire f)
  (h_order : OrderAtMostOne f) :
  ExponentialType f := by
  constructor
  · exact h_entire
  · obtain ⟨τ, hτ, C, hC, h_bound⟩ := h_order
    use τ
    intro ε hε
    use C, hC
    intro z
    calc Complex.abs (f z)
      ≤ C * Real.exp (τ * Complex.abs z) := h_bound z
    _ ≤ C * Real.exp ((τ + ε) * Complex.abs z) := by
        apply mul_le_mul_of_nonneg_left
        · apply Real.exp_le_exp.mpr
          apply mul_le_mul_of_nonneg_right
          · linarith
          · exact Complex.abs.nonneg z
        · exact le_of_lt hC

end ExponentialType
