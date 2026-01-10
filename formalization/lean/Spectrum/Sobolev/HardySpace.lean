/-
  HardySpace.lean
  -----------------------------------------------------
  Sobolev-Hardy space foundations for spectral theory
  Provides function spaces for operator H_Ψ domain
  -----------------------------------------------------
  José Manuel Mota Burruezo Ψ ∞³ — Instituto Conciencia Cuántica
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Calculus.ContDiff.Defs

noncomputable section
open Real MeasureTheory

namespace Spectrum.Sobolev

/-- Smooth functions with compact support on ℝ —/
def Cc∞ (α : Type*) [TopologicalSpace α] : Type* :=
  Subtype (fun f : α → ℂ => HasCompactSupport f ∧ ContDiff ℂ ⊤ f)

/-- Instance for embedding into function type —/
instance {α : Type*} [TopologicalSpace α] : CoeFun (Cc∞ α) (fun _ => α → ℂ) where
  coe f := f.val

end Spectrum.Sobolev
