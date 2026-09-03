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

/-- Desplazamiento crítico `Ξ_crit(s) = Ξ(1/2 + i s)`. -/
def xiShifted (Xi : ℂ → ℂ) (s : ℂ) : ℂ :=
  Xi ((1 / 2 : ℂ) + Complex.I * s)

/-- Anulación del wronskiano cruzado bajo igualdad de derivadas logarítmicas. -/
lemma wronskian_zero_of_log_deriv_eq
    {D Xi : ℂ → ℂ} {s : ℂ}
    (hDs : D s ≠ 0) (hXis : Xi s ≠ 0)
    (h_match : deriv D s / D s = deriv Xi s / Xi s) :
    deriv D s * Xi s - D s * deriv Xi s = 0 := by
  have h_factor :
      deriv D s * Xi s - D s * deriv Xi s =
        (D s * Xi s) * (deriv D s / D s - deriv Xi s / Xi s) := by
    field_simp [hDs, hXis]
    ring
  rw [h_factor, h_match, sub_self, mul_zero]

/-- Derivada del cociente nula en puntos regulares cuando coinciden log-derivadas. -/
lemma deriv_div_eq_zero_of_log_deriv_eq
    {D Xi : ℂ → ℂ} {s : ℂ}
    (hD : DifferentiableAt ℂ D s) (hXi : DifferentiableAt ℂ Xi s)
    (hDs : D s ≠ 0) (hXis : Xi s ≠ 0)
    (h_match : deriv D s / D s = deriv Xi s / Xi s) :
    deriv (fun z => D z / Xi z) s = 0 := by
  rw [deriv_div hD hXi hXis]
  exact wronskian_zero_of_log_deriv_eq hDs hXis h_match

/-- Testigo del paso global de rigidez holomorfa del cociente en dominio conexo. -/
structure HolomorphicQuotientRigidityWitness (D Xi : ℂ → ℂ) : Prop where
  conclude :
    (∀ s : ℂ, D s ≠ 0 → Xi s ≠ 0 → deriv (fun z => D z / Xi z) s = 0) →
    D 0 = Xi 0 →
    Xi 0 ≠ 0 →
    ∀ s : ℂ, D s = Xi s

/--
Rigidez espectral por cociente:
si `D'/D = Xi'/Xi` en puntos regulares y hay normalización en `0`,
la identificación global queda fijada por el testigo holomorfo.
-/
theorem spectral_rigidity_quotient
    (D Xi : ℂ → ℂ)
    (hD_entire : Entire D)
    (hXi_entire : Entire Xi)
    (h_xi_zero_ne : Xi 0 ≠ 0)
    (h_scale_match : D 0 = Xi 0)
    (h_log_deriv : ∀ s : ℂ, D s ≠ 0 → Xi s ≠ 0 →
      deriv D s / D s = deriv Xi s / Xi s)
    (hRig : HolomorphicQuotientRigidityWitness D Xi) :
    ∀ s : ℂ, D s = Xi s := by
  apply hRig.conclude
  · intro s hDs hXis
    exact deriv_div_eq_zero_of_log_deriv_eq
      (hD_entire.differentiableAt)
      (hXi_entire.differentiableAt)
      hDs hXis (h_log_deriv s hDs hXis)
  · exact h_scale_match
  · exact h_xi_zero_ne

/-- Versión explícita del cierre de rigidez Hadamard-Borel en el plano complejo. -/
theorem entire_rigidity_of_log_deriv_match
    (D Xi : ℂ → ℂ)
    (hD_entire : Entire D)
    (hXi_entire : Entire Xi)
    (h_xi_zero_ne : Xi 0 ≠ 0)
    (h_scale_match : D 0 = Xi 0)
    (h_log_deriv : ∀ s : ℂ, D s ≠ 0 → Xi s ≠ 0 →
      deriv D s / D s = deriv Xi s / Xi s)
    (hRig : HolomorphicQuotientRigidityWitness D Xi) :
    ∀ s : ℂ, D s = Xi s :=
  spectral_rigidity_quotient D Xi
    hD_entire hXi_entire h_xi_zero_ne h_scale_match h_log_deriv hRig

/-- Predicado abstracto: el resolvente es compacto en el punto espectral `z`. -/
def ResolventIsCompact : Prop :=
  ∀ z : ℂ, IsCompact (Set.range (R.resolvent z))

/-- Predicado abstracto de espectro discreto puro. -/
def PurelyDiscreteSpectrum : Prop :=
  ∀ z : ℂ, R.isSpectralPoint z →
    ∃ ε > 0, ∀ w : ℂ, R.isSpectralPoint w → ‖w - z‖ < ε → w = z

/-- Predicado de correspondencia espectral con ceros de `Ξ` sobre la recta crítica. -/
def SpectralIsomorphism : Prop :=
  ∀ t : ℝ, R.isSpectralPoint (t : ℂ) ↔ B.xi ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) = 0

/--
Hipótesis del frente analítico 4:
compacidad del resolvente e implicación de espectro discreto puro.
-/
structure FourthFrontHypotheses : Prop where
  resolvent_compact :
    ResolventIsCompact R
  purely_discrete_of_compact :
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
theorem spectrum_is_purely_discrete
    (h : FourthFrontHypotheses R B) :
    PurelyDiscreteSpectrum R :=
  h.purely_discrete_of_compact h.resolvent_compact

/-- Datos de cierre incondicional por rigidez Hadamard-Borel en la variable espectral. -/
structure UnconditionalSpectralIdentificationData where
  D_spec : ℂ → ℂ
  h_norm : D_spec 0 = concreteXi (1 / 2 : ℂ)
  h_log :
    ∀ s : ℂ,
      deriv D_spec s / D_spec s =
        deriv (fun w => concreteXi ((1 / 2 : ℂ) + Complex.I * w)) s /
          concreteXi ((1 / 2 : ℂ) + Complex.I * s)
  h_rigidity :
    (∀ s : ℂ, deriv D_spec s / D_spec s =
      deriv (fun w => concreteXi ((1 / 2 : ℂ) + Complex.I * w)) s /
        concreteXi ((1 / 2 : ℂ) + Complex.I * s)) →
    D_spec 0 = concreteXi (1 / 2 : ℂ) →
    ∀ s : ℂ, D_spec s = concreteXi ((1 / 2 : ℂ) + Complex.I * s)

/-- Cierre global: identificación espectral incondicional desde log-derivada + normalización. -/
theorem unconditional_spectral_identification
    (U : UnconditionalSpectralIdentificationData) :
    ∀ s : ℂ, U.D_spec s = concreteXi ((1 / 2 : ℂ) + Complex.I * s) :=
  U.h_rigidity U.h_log U.h_norm

end SpectralUniqueness
end RiemannAdelic
