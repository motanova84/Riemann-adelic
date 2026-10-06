/-
  Hadamard_Uniqueness.lean
  ------------------------------------------------------------
  Rigidez analítica (cerrador):
  igualdad de derivadas logarítmicas + normalización
  ⇒ identificación global de funciones enteras.
-/

import Mathlib
import RiemannAdelic.Spectral_Mechanics
import RiemannAdelic.Trace_Fredholm

noncomputable section

namespace RiemannAdelic
namespace HadamardUniqueness

open Complex
open RiemannAdelic.TraceFredholm
open RiemannAdelic.SpectralMechanics

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {M : RiemannAdelic.UnboundedHpsi.CoreModel H}

/-- Hipótesis de rigidez Hadamard–Borel para integrar la igualdad log-derivada. -/
structure HadamardBorelRigidity (f g : ℂ → ℂ) : Prop where
  conclude :
    (∀ s : ℂ, deriv f s / f s = deriv g s / g s) →
    f 0 = g 0 →
    ∀ s : ℂ, f s = g s

/-- Teorema fundamental de rigidez: cierre global a partir de igualdad log-derivada. -/
theorem entire_eq_of_log_deriv_eq_and_eq_at_point
    (f g : ℂ → ℂ)
    (hRig : HadamardBorelRigidity f g)
    (h_log_deriv : ∀ s : ℂ, deriv f s / f s = deriv g s / g s)
    (h_norm : f 0 = g 0) :
    ∀ s : ℂ, f s = g s :=
  hRig.conclude h_log_deriv h_norm

/-- Cierre final: `D(s) ≡ Ξ(1/2 + i s)` desde mecanismo espectral + rigidez. -/
theorem spectral_determinant_identically_equals_xi
    (R : ResolventData M)
    (A : AdelicTraceData M)
    (MP : MellinPrimeData)
    (S : SpectralLogDerivData R A MP)
    (hRig : HadamardBorelRigidity
      R.fredholmDeterminant
      (fun w => S.xi ((1 / 2 : ℂ) + Complex.I * w)))
    (h_norm : R.fredholmDeterminant 0 = S.xi (1 / 2 : ℂ)) :
    ∀ s : ℂ, R.fredholmDeterminant s = S.xi ((1 / 2 : ℂ) + Complex.I * s) := by
  exact
    entire_eq_of_log_deriv_eq_and_eq_at_point
      R.fredholmDeterminant
      (fun w => S.xi ((1 / 2 : ℂ) + Complex.I * w))
      hRig
      (trace_match_derived R A MP S)
      h_norm

end HadamardUniqueness
end RiemannAdelic

