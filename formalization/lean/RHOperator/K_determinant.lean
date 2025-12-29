import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-
  K_determinant.lean
  -----------------------------------------------------
  Auxiliary module for K operator and determinant definitions
  Provides necessary definitions for HPsi_selfadjoint.lean
  -----------------------------------------------------
  José Manuel Mota Burruezo Ψ ∞³ — Instituto Conciencia Cuántica
-/

noncomputable section
open Complex

namespace RHOperator

/-- K operator acting on functions -/
def K_op (s : ℂ) (f : ℂ → ℂ) : ℂ → ℂ :=
  fun z ↦ f z * exp (-(s - 1/2)^2)

/-- Eigenfunction property for operators -/
def Eigenfunction (T : (ℂ → ℂ) → (ℂ → ℂ)) (Φ : ℂ → ℂ) : Prop :=
  ∃ λ : ℂ, ∀ z, T Φ z = λ * Φ z

end RHOperator

end -- noncomputable section
