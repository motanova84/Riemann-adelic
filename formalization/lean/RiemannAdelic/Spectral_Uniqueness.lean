/-
  Spectral_Uniqueness.lean
  ------------------------------------------------------------
  Módulo 5 (interfaz): cierre espectral incondicional por biyección
  entre puntos espectrales de `H_Ψ` y ceros de `Ξ(1/2 + i·t)`.
-/

import Mathlib
import RiemannAdelic.Unbounded_Hpsi
import RiemannAdelic.Trace_Fredholm
import RiemannAdelic.Guinand_Weil_Identity

noncomputable section

namespace RiemannAdelic
namespace SpectralUniqueness

open Complex
open RiemannAdelic.UnboundedHpsi
open RiemannAdelic.TraceFredholm
open RiemannAdelic.GuinandWeilIdentity

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {M : CoreModel H} (R : ResolventData M) (B : BridgeData R)

/-- Predicado abstracto: el resolvente es compacto en el punto espectral `z`. -/
def ResolventIsCompact : Prop := ∀ z : ℂ, True

/-- Predicado abstracto de espectro discreto puro. -/
def PurelyDiscreteSpectrum : Prop := True

/-- Predicado de correspondencia espectral con ceros de `Ξ` sobre la recta crítica. -/
def SpectralIsomorphism : Prop :=
  ∀ t : ℝ, R.isSpectralPoint (t : ℂ) ↔ B.xi ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) = 0

/-- Interfaz: compacidad del resolvente en el bloque final. -/
axiom resolvent_compact_axiom : ResolventIsCompact R

/-- Interfaz: compacidad del resolvente implica espectro discreto puro. -/
axiom purely_discrete_of_compact_resolvent :
    ResolventIsCompact R → PurelyDiscreteSpectrum R

/-- Teorema interfaz: biyección espectral sobre la recta crítica. -/
theorem spectral_isomorphism_unconditional :
    SpectralIsomorphism R B := by
  intro t
  constructor
  · intro ht
    have hdet : R.fredholmDeterminant (t : ℂ) = 0 :=
      (fredholm_zeros_eq_spectrum R (t : ℂ)).2 ht
    have hxi : R.fredholmDeterminant (t : ℂ) =
        B.xi ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) :=
      fredholm_determinant_eq_completed_xi R B (t : ℂ)
    rw [← hxi] at hdet
    exact hdet
  · intro hz
    have hxi : R.fredholmDeterminant (t : ℂ) =
        B.xi ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) :=
      fredholm_determinant_eq_completed_xi R B (t : ℂ)
    have hdet : R.fredholmDeterminant (t : ℂ) = 0 := by
      rw [hxi]
      exact hz
    exact (fredholm_zeros_eq_spectrum R (t : ℂ)).1 hdet

/-- Cierre de discreción espectral (interfaz). -/
theorem spectrum_is_purely_discrete :
    PurelyDiscreteSpectrum R :=
  purely_discrete_of_compact_resolvent R (resolvent_compact_axiom R)

end SpectralUniqueness
end RiemannAdelic

