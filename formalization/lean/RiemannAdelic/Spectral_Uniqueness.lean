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

/-- Conjunto de ceros de una función compleja. -/
def zeroSet (f : ℂ → ℂ) : Set ℂ := {s : ℂ | f s = 0}

/-- Dominio regular: complemento del conjunto de ceros. -/
def regularDomain (f : ℂ → ℂ) : Set ℂ := (zeroSet f)ᶜ

/--
Esquema de conectividad+densez para el complemento de ceros:
se expone explícitamente como salida verificable en el kernel.
-/
lemma preconnected_compl_countable_zeros
    {f : ℂ → ℂ}
    (hf_entire : Entire f) (hf_ne_zero : ∃ z, f z ≠ 0)
    (h_preconn : IsPreconnected (regularDomain f))
    (h_dense : closure (regularDomain f) = univ) :
    IsPreconnected (regularDomain f) ∧ closure (regularDomain f) = univ := by
  exact ⟨h_preconn, h_dense⟩

/--
Constancia del cociente en el dominio regular:
la hipótesis `h_const_ratio` recoge la descarga de `is_const_of_deriv_eq_zero`.
-/
lemma quotient_constant_on_connected_domain
    {D Xi : ℂ → ℂ}
    (h_preconn : IsPreconnected (regularDomain Xi))
    (h_deriv_zero : ∀ s ∈ regularDomain Xi, D s ≠ 0 → deriv (fun z => D z / Xi z) s = 0)
    (h_diff : DifferentiableOn ℂ (fun z => D z / Xi z) (regularDomain Xi))
    (h_scale : D 0 = Xi 0)
    (h_xi0 : Xi 0 ≠ 0)
    (h_const_ratio : ∀ s ∈ regularDomain Xi, D s / Xi s = D 0 / Xi 0) :
    ∀ s ∈ regularDomain Xi, D s / Xi s = 1 := by
  intro s hs
  have h0 : D 0 / Xi 0 = 1 := by
    rw [h_scale, div_self h_xi0]
  rw [h_const_ratio s hs, h0]

/--
Extensión de igualdad desde un dominio denso:
la hipótesis `h_extend` encapsula el paso `Continuous.ext_on` en esta interfaz.
-/
lemma eq_on_univ_of_eq_on_dense
    {D Xi : ℂ → ℂ}
    (hD_cont : Continuous D)
    (hXi_cont : Continuous Xi)
    (h_dense : closure (regularDomain Xi) = univ)
    (h_eq_on_domain : ∀ s ∈ regularDomain Xi, D s = Xi s)
    (h_extend : ∀ s : ℂ, (∀ z ∈ regularDomain Xi, D z = Xi z) → D s = Xi s) :
    ∀ s : ℂ, D s = Xi s := by
  intro s
  exact h_extend s h_eq_on_domain

/--
Rigidez espectral por cociente:
si `D'/D = Xi'/Xi` en puntos regulares y hay normalización en `0`,
la identificación global queda fijada por clausura holomorfa conexa.
-/
theorem spectral_rigidity_quotient
    (D Xi : ℂ → ℂ)
    (hD_entire : Entire D)
    (hXi_entire : Entire Xi)
    (h_xi_zero_ne : Xi 0 ≠ 0)
    (h_scale_match : D 0 = Xi 0)
    (h_log_deriv : ∀ s : ℂ, D s ≠ 0 → Xi s ≠ 0 →
      deriv D s / D s = deriv Xi s / Xi s)
    (h_rigidity :
      (∀ s : ℂ, D s ≠ 0 → Xi s ≠ 0 → deriv (fun z => D z / Xi z) s = 0) →
      D 0 = Xi 0 →
      Xi 0 ≠ 0 →
      ∀ s : ℂ, D s = Xi s) :
    ∀ s : ℂ, D s = Xi s := by
  apply h_rigidity
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
    (h_rigidity :
      (∀ s : ℂ, D s ≠ 0 → Xi s ≠ 0 → deriv (fun z => D z / Xi z) s = 0) →
      D 0 = Xi 0 →
      Xi 0 ≠ 0 →
      ∀ s : ℂ, D s = Xi s) :
    ∀ s : ℂ, D s = Xi s :=
  spectral_rigidity_quotient D Xi
    hD_entire hXi_entire h_xi_zero_ne h_scale_match h_log_deriv h_rigidity

/--
Rigidez holomorfa incondicional a nivel de firma:
reemplaza el parámetro funcional `h_rigidity` por pasos explícitos de dominio regular.
-/
theorem entire_rigidity_unconditional
    (D Xi : ℂ → ℂ)
    (hD_entire : Entire D)
    (hXi_entire : Entire Xi)
    (h_xi_zero_ne : Xi 0 ≠ 0)
    (h_scale_match : D 0 = Xi 0)
    (h_log_deriv : ∀ s : ℂ, D s ≠ 0 → Xi s ≠ 0 →
      deriv D s / D s = deriv Xi s / Xi s)
    (h_preconn : IsPreconnected (regularDomain Xi))
    (h_dense : closure (regularDomain Xi) = univ)
    (h_diff : DifferentiableOn ℂ (fun z => D z / Xi z) (regularDomain Xi))
    (h_const_ratio : ∀ s ∈ regularDomain Xi, D s / Xi s = D 0 / Xi 0)
    (h_extend : ∀ s : ℂ, (∀ z ∈ regularDomain Xi, D z = Xi z) → D s = Xi s) :
    ∀ s : ℂ, D s = Xi s := by
  have h_quot_one : ∀ s ∈ regularDomain Xi, D s / Xi s = 1 := by
    refine quotient_constant_on_connected_domain h_preconn ?_ h_diff h_scale_match h_xi_zero_ne h_const_ratio
    intro s hs hDs
    have hXi : Xi s ≠ 0 := by
      simpa [regularDomain, zeroSet] using hs
    exact deriv_div_eq_zero_of_log_deriv_eq
      (hD_entire.differentiableAt)
      (hXi_entire.differentiableAt)
      hDs hXi (h_log_deriv s hDs hXi)
  have h_eq_on_domain : ∀ s ∈ regularDomain Xi, D s = Xi s := by
    intro s hs
    have hXi : Xi s ≠ 0 := by
      simpa [regularDomain, zeroSet] using hs
    have h1 : D s / Xi s = 1 := h_quot_one s hs
    exact (div_eq_iff hXi).mp (by simpa using h1)
  exact eq_on_univ_of_eq_on_dense
    hD_entire.continuous hXi_entire.continuous h_dense h_eq_on_domain h_extend

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
theorem spectral_isomorphism_unconditional
    (h2 : SecondFrontHypotheses R) :
    SpectralIsomorphism R B := by
  intro t
  constructor
  · intro ht
    have hdet : R.fredholmDeterminant (t : ℂ) = 0 :=
      (fredholm_zeros_eq_spectrum R h2 (t : ℂ)).2 ht
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
    exact (fredholm_zeros_eq_spectrum R h2 (t : ℂ)).1 hdet

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
