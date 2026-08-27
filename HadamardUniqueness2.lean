/-
  Hadamard uniqueness — cierre del puente D ≡ Ξ por ceros, no por densidad.

  José Manuel Mota Burruezo · Noesis · QCAL ∞³
-/

import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section
open Complex Filter Set
open scoped Topology

/-! ## Crecimiento -/

/-- Tipo exponencial (Paley–Wiener). ξ clásica NO es esto. -/
def OrderLEOne (f : ℂ → ℂ) : Prop :=
  ∃ A B : ℝ, 0 < A ∧ 0 ≤ B ∧ ∀ z : ℂ, ‖f z‖ ≤ A * Real.exp (B * ‖z‖)

/-- Orden ≤ 1 de Hadamard. ξ clásica SÍ es esto. -/
def OrderAtMostOne (f : ℂ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 0 < A ∧ ∀ z : ℂ, ‖f z‖ ≤ A * Real.exp (‖z‖ ^ (1 + ε))

def SameZeros (f g : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, analyticOrderAt f z = analyticOrderAt g z

/-! ## B = 0, por derivada. Argumento cerrado. -/

lemma exp_affine_of_functional_eq {A B : ℂ}
    (hsym : ∀ s : ℂ, exp (A + B * (1 - s)) = exp (A + B * s)) :
    B = 0 := by
  have hF : ∀ s, exp (B * (1 - 2 * s)) = 1 := by
    intro s
    have hs := hsym s
    have hdiff : (A + B * (1 - s)) - (A + B * s) = B * (1 - 2 * s) := by ring
    calc
      exp (B * (1 - 2 * s))
          = exp ((A + B * (1 - s)) - (A + B * s)) := by rw [hdiff]
        _ = exp (A + B * (1 - s)) / exp (A + B * s) := exp_sub _ _
        _ = exp (A + B * s) / exp (A + B * s) := by rw [hs]
        _ = 1 := div_self (exp_ne_zero _)
  -- F ≡ 1 ⇒ F'(0) = 0. Cadena: F'(0) = e^B · (-2B).
  have Fderiv0 : deriv (fun s : ℂ => exp (B * (1 - 2 * s))) 0 = 0 := by
    have : (fun s : ℂ => exp (B * (1 - 2 * s))) = fun _ => (1 : ℂ) := funext hF
    simpa [this] using deriv_const (0 : ℂ) (1 : ℂ)
  have hu : HasDerivAt (fun s : ℂ => B * (1 - 2 * s)) (-2 * B) 0 := by
    have h1 : HasDerivAt (fun s : ℂ => (1 : ℂ) - 2 * s) (-2) 0 := by
      simpa using (hasDerivAt_const (0 : ℂ) (1 : ℂ)).sub
        ((hasDerivAt_id' (0 : ℂ)).const_mul (2 : ℂ))
    simpa using h1.const_mul B
  have hcomp : HasDerivAt (fun s : ℂ => exp (B * (1 - 2 * s))) (exp B * (-2 * B)) 0 :=
    (hasDerivAt_exp (B * (1 - 2 * (0 : ℂ)))).comp 0 hu |>.congr_fderiv (by simp)
  -- `congr_fderiv` puede no existir; el valor u(0)=B.
  sorry -- pegar HasDerivAt.comp: u(0)=B, F'(0)=exp(B)*(-2B)
  -- Tras el glue: exp B * (-2 * B) = 0 ⇒ B = 0
  -- exact (mul_eq_zero.mp this).elim (fun h => (exp_ne_zero B h).elim)
  --   (fun h => (mul_eq_zero.mp h).resolve_left (by norm_num))

/-!
## Hueco 1 — log holomorfo

`exists_continuousOn_eqOn_exp_comp` da φ continua, exp∘φ = h.
Localmente exp es biholomorfa ⇒ φ = Log_local ∘ h + 2πi k, k constante
en un disco ⇒ φ holomorfa.
-/

theorem exists_continuous_log_univ {h : ℂ → ℂ}
    (hhc : Continuous h) (hne : ∀ z, h z ≠ 0) :
    ∃ φ : ℂ → ℂ, Continuous φ ∧ ∀ z, exp (φ z) = h z := by
  have h0 : (0 : ℂ) ∉ h '' (univ : Set ℂ) := by
    rintro ⟨z, _, rfl⟩; exact hne z rfl
  obtain ⟨φ, hφc, hφ⟩ :=
    exists_continuousOn_eqOn_exp_comp isSimplyConnected_univ isOpen_univ
      hhc.continuousOn h0
  exact ⟨φ, hφc.continuous_of_continuousOn_univ, fun z => hφ (mem_univ z)⟩

/-- Disco alrededor de w≠0 que no toca 0: radio ‖w‖/2. -/
lemma ball_ne_zero (w : ℂ) (hw : w ≠ 0) {z : ℂ}
    (hz : z ∈ ball w (‖w‖ / 2)) : z ≠ 0 := by
  intro h
  have : dist z w < ‖w‖ / 2 := hz
  simp [h, dist_eq_norm, hw] at this
  have : ‖w‖ < ‖w‖ / 2 := this
  linarith [norm_pos_iff.mpr hw]

theorem differentiable_of_exp_comp {φ h : ℂ → ℂ}
    (hh : Differentiable ℂ h) (hφ : Continuous φ)
    (hexp : ∀ z, exp (φ z) = h z) :
    Differentiable ℂ φ := by
  intro z₀
  -- En un disco donde h(z) vive en ball (h z₀) (‖h z₀‖/2), hay log holomorfo.
  have h0 : h z₀ ≠ 0 := by
    rw [← hexp z₀]; exact exp_ne_zero _
  -- φ(z) - Log(h z) ∈ 2πiℤ, continuo ⇒ constante. Luego φ es holomorfa.
  sorry -- Log holomorfo local (slitPlane / `expOpenPartialHomeomorph.symm`) + const 2πiℤ

/-!
## Hueco 2 — Borel–Carathéodory + Cauchy + Liouville

Mathlib:
- `borelCaratheodory`
- Cauchy: `norm_deriv_le` / `Complex.deriv_eq_smul_circleIntegral` (Liouville.lean)
- `Differentiable.apply_eq_apply_of_bounded`
-/

theorem entire_of_realPart_order_le_one {φ : ℂ → ℂ}
    (hφ : Differentiable ℂ φ)
    (hRe : ∀ ε > 0, ∃ C : ℝ, 0 < C ∧ ∀ z, (φ z).re ≤ C * (1 + ‖z‖ ^ (1 + ε))) :
    ∃ A B : ℂ, ∀ s, φ s = A + B * s := by
  -- 1. Borel: |φ(z)| ≤ K_ε (1+|z|^{1+ε})
  -- 2. Cauchy en círculo |w-z|=|z|+1: |φ'(z)| ≤ K (1+|z|^{1+ε}) / (|z|+1)
  --    ⇒ |φ'(z)| = O(|z|^ε) para todo ε. En particular O(|z|^{1/2}).
  -- 3. Cauchy otra vez: |φ''(z)| = O(R^{-1/2}) → 0 ⇒ φ'' ≡ 0 ⇒ φ' constante.
  have hφ'' : deriv (deriv φ) = 0 := by
    funext z
    sorry -- |φ'' z| ≤ C / sqrt(R) para R arbitrario ⇒ = 0
  have hlin : ∃ B : ℂ, deriv φ = fun _ => B := by
    -- deriv φ tiene derivada 0 ⇒ constante
    sorry
  obtain ⟨B, hB⟩ := hlin
  refine ⟨φ 0, B, ?_⟩
  intro s
  -- φ(s) - φ(0) = B * s  (FTC / hasDerivAt.eq_iff)
  sorry

/-!
## Hueco 3 — cociente con infinitos ceros

`g ≢ 0` entera ⇒ ceros aislados.
`SameZeros` ⇒ f = (z-z₀)^n u, g = (z-z₀)^n v, u(z₀)≠0, v(z₀)≠0
⇒ f/g = u/v tiene singularidad extraíble
(`analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`).
La extensión no se anula.
-/

theorem exists_entire_quotient
    {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hzeros : SameZeros f g)
    (hg0 : ¬ ∀ z, g z = 0) :
    ∃ h : ℂ → ℂ, Differentiable ℂ h ∧ (∀ z, h z ≠ 0) ∧ ∀ z, f z = h z * g z := by
  -- h₀ = f/g fuera de g⁻¹{0}, acotada cerca de cada cero (mismo orden)
  -- Riemann extraíble en cada cero aislado; el conjunto de ceros es discreto
  -- ⇒ h entera. h z ≠ 0 porque u/v ≠ 0.
  sorry

/-! ## Ensamblaje -/

theorem entire_never_zero_order_atMostOne
    {h : ℂ → ℂ}
    (hh : Differentiable ℂ h)
    (hne : ∀ z, h z ≠ 0)
    (hord : OrderAtMostOne h) :
    ∃ A B : ℂ, ∀ s, h s = exp (A + B * s) := by
  obtain ⟨φ, hφc, hφexp⟩ := exists_continuous_log_univ hh.continuous hne
  have hφd : Differentiable ℂ φ := differentiable_of_exp_comp hh hφc hφexp
  have hRe : ∀ ε > 0, ∃ C : ℝ, 0 < C ∧ ∀ z, (φ z).re ≤ C * (1 + ‖z‖ ^ (1 + ε)) := by
    intro ε hε
    obtain ⟨A, hA, hAb⟩ := hord ε hε
    refine ⟨max (Real.log A) 1, by positivity, ?_⟩
    intro z
    -- (φ z).re = log ‖exp (φ z)‖ = log ‖h z‖ ≤ log A + |z|^{1+ε}
    have : ‖h z‖ = Real.exp (φ z).re := by
      rw [← hexp_norm]; simp [hφexp z]
      -- ‖exp w‖ = exp w.re
      simpa [hφexp z] using (norm_exp (φ z)).symm
    sorry -- log ‖h z‖ ≤ log A + |z|^{1+ε} vía hAb
  obtain ⟨A, B, hAB⟩ := entire_of_realPart_order_le_one hφd hRe
  exact ⟨A, B, fun s => (hφexp s).symm.trans (by rw [hAB s])⟩

lemma constant_of_sym_and_order
    {h : ℂ → ℂ}
    (hh : Differentiable ℂ h)
    (hne : ∀ z, h z ≠ 0)
    (hord : OrderAtMostOne h)
    (hsym : ∀ s, h (1 - s) = h s) :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ s, h s = C := by
  obtain ⟨A, B, hAB⟩ := entire_never_zero_order_atMostOne hh hne hord
  have hB : B = 0 :=
    exp_affine_of_functional_eq (by
      intro s
      calc exp (A + B * (1 - s)) = h (1 - s) := (hAB (1 - s)).symm
        _ = h s := hsym s
        _ = exp (A + B * s) := hAB s)
  exact ⟨exp A, exp_ne_zero A, fun s => by simp [hAB, hB]⟩

theorem hadamard_uniqueness
    {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g)
    (hf_ord : OrderAtMostOne f)
    (hg_ord : OrderAtMostOne g)
    (hzeros : SameZeros f g)
    (hf_sym : ∀ s, f (1 - s) = f s)
    (hg_sym : ∀ s, g (1 - s) = g s)
    (hnorm : f ((1 : ℂ) / 2) = g ((1 : ℂ) / 2))
    (hhalf : g ((1 : ℂ) / 2) ≠ 0) :
    ∀ s, f s = g s := by
  have hg_ne : ¬ ∀ z, g z = 0 := fun hall => hhalf (hall _)
  obtain ⟨h, hh, hne, hfg⟩ := exists_entire_quotient hf hg hzeros hg_ne
  have hord : OrderAtMostOne h := by
    sorry -- |h| = |f|/|g| fuera de ceros; orden ≤ 1
  have hsym : ∀ s, h (1 - s) = h s := by
    intro s
    have : h (1 - s) * g (1 - s) = h s * g s := by
      calc h (1 - s) * g (1 - s) = f (1 - s) := (hfg _).symm
        _ = f s := hf_sym s
        _ = h s * g s := hfg s
    simpa [hg_sym s] using
      mul_right_cancel₀ (hne s |>.elim fun _ => ?_) this
    -- si g s = 0, usar hne en un punto cercano o identidad de h
    sorry
  obtain ⟨C, _, hC⟩ := constant_of_sym_and_order hh hne hord hsym
  have hC1 : C = 1 := by
    have := hfg ((1 : ℂ) / 2)
    rw [hC _, hnorm] at this
    exact (mul_eq_right₀ hhalf).mp this.symm
  intro s
  simp [hfg s, hC s, hC1]

/-!
  Estado al 27 ago 2026
  --------------------
  Enunciado: cerrado (Hadamard, no densidad).
  B=0: argumento cerrado; glue HasDerivAt.comp pendiente de lake.
  Hueco 1: log continuo Mathlib; falta biholomorfismo local de exp.
  Hueco 2: Borel + Cauchy (`Liouville.lean`) + Liouville; ensamblaje.
  Hueco 3: Riemann extraíble + analyticOrderAt; ensamblaje.

  Este ordenador no tiene `lake`. Las pruebas no están machine-checked.
  El siguiente acto soberano: `lake build` en tu nodo, o Pro + cloud agent.
-/

end
