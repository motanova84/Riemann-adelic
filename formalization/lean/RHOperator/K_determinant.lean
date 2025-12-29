import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.MeasureTheory.Integral.SetIntegral

/-
  K_determinant.lean
  -----------------------------------------------------
  Auxiliary module for K operator and determinant definitions
  Provides necessary definitions for HPsi_selfadjoint.lean
  -----------------------------------------------------
  José Manuel Mota Burruezo Ψ ∞³ — Instituto Conciencia Cuántica
-/

noncomputable section
open Complex Set

namespace RHOperator

/-- K operator acting on functions as an integral kernel -/
def K_op (s : ℂ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y in Ioi 0, (y : ℂ) ^ (s - 1/2) * f y / y

/-- Eigenfunction property for operators on function spaces -/
def Eigenfunction (T : (ℝ → ℂ) → (ℝ → ℂ)) (Φ : ℝ → ℂ) : Prop :=
  ∃ λ : ℂ, ∀ x, T Φ x = λ * Φ x

end RHOperator

end -- noncomputable section
