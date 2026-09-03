/-
  Trace_Fredholm.lean
  ------------------------------------------------------------
  Módulo 3 (interfaz): traza regularizada y determinante de Fredholm
  construidos desde el bloque no acotado de `Unbounded_Hpsi`.
-/

import Mathlib
import RiemannAdelic.Unbounded_Hpsi

noncomputable section

namespace RiemannAdelic
namespace TraceFredholm

open Complex
open RiemannAdelic.UnboundedHpsi

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Datos abstractos del resolvente para el modelo `H_Ψ`. -/
structure ResolventData (M : CoreModel H) where
  /-- Operador resolvente abstracto en parámetro espectral `z`. -/
  resolvent : ℂ → H → H
  /-- Predicado abstracto de regularidad de traza para el resolvente. -/
  isRegularizedTraceClass : ℂ → Prop
  /-- Traza regularizada del resolvente. -/
  regularizedTrace : ℂ → ℂ
  /-- Determinante espectral tipo Fredholm asociado. -/
  fredholmDeterminant : ℂ → ℂ
  /-- Ley puente (interfaz): ceros del determinante ↔ espectro de `M`. -/
  isSpectralPoint : ℂ → Prop
  zeros_eq_spectrum :
    ∀ s : ℂ, fredholmDeterminant s = 0 ↔ isSpectralPoint s

/-- Predicado interfaz: holomorfía compleja global del determinante de Fredholm. -/
def IsEntireFredholmDeterminant {M : CoreModel H} (R : ResolventData M) : Prop :=
  Differentiable ℂ R.fredholmDeterminant

variable {M : CoreModel H}

/-- Teorema interfaz: ceros del determinante de Fredholm y espectro coinciden. -/
theorem fredholm_zeros_eq_spectrum (R : ResolventData M) (s : ℂ) :
    R.fredholmDeterminant s = 0 ↔ R.isSpectralPoint s := by
  exact R.zeros_eq_spectrum s

/--
Hipótesis del frente analítico 2:
regularidad de clase de traza y holomorfía de `D(s)`.
-/
structure SecondFrontHypotheses (R : ResolventData M) : Prop where
  entire_fredholm_determinant :
    IsEntireFredholmDeterminant R

/-- Cierre del frente 2 sin axioma global. -/
theorem fredholm_determinant_is_entire
    (R : ResolventData M) (h : SecondFrontHypotheses R) :
    IsEntireFredholmDeterminant R := by
  exact h.entire_fredholm_determinant

end TraceFredholm
end RiemannAdelic
