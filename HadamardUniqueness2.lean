/-
  Hadamard uniqueness v3.2.5 — ensamblaje.

  GAP1–4 importados. Este archivo: 0 sorry en fuente, no lake-checked.
  B=0 escrito. C=1 por f(1/2)=g(1/2)≠0.
  h(1-s)=h s por identidad en {g ≠ 0} (abierto denso).
  Re φ = log ‖h‖ a partir de OrderAtMostOne h.

  GAP4 (archivo aparte, v3.2.18): 0 tactic sorry en fuente.
  exists_circle_min_norm y order_atMostOne_of_quotient pegados.
  No RH. No D ≡ Ξ.

  José Manuel Mota Burruezo · Noesis · QCAL ∞³
-/

import GAP1_log_holomorphic_of_entire_never_zero
import GAP2_affine_log_of_order_one
import GAP3_quotient_entire_never_zero
import GAP4_order_atMostOne_of_quotient
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section
open Complex Filter Metric Set
open scoped Topology Real

/-! ## Crecimiento: `OrderAtMostOne` / `OrderLEOne` viven en GAP4. -/

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
  have Fderiv0 : deriv (fun s : ℂ => exp (B * (1 - 2 * s))) 0 = 0 := by
    have : (fun s : ℂ => exp (B * (1 - 2 * s))) = fun _ => (1 : ℂ) := funext hF
    simpa [this] using deriv_const (0 : ℂ) (1 : ℂ)
  have hu : HasDerivAt (fun s : ℂ => B * (1 - 2 * s)) (-2 * B) 0 := by
    have h1 : HasDerivAt (fun s : ℂ => (1 : ℂ) - 2 * s) (-2) 0 := by
      simpa using (hasDerivAt_const (0 : ℂ) (1 : ℂ)).sub
        ((hasDerivAt_id' (0 : ℂ)).const_mul (2 : ℂ))
    simpa using h1.const_mul B
  have hcomp : HasDerivAt (fun s : ℂ => exp (B * (1 - 2 * s)))
      (exp (B * (1 - 2 * (0 : ℂ))) * (-2 * B)) 0 :=
    (hasDerivAt_exp (B * (1 - 2 * (0 : ℂ)))).comp 0 hu
  have hF' : deriv (fun s : ℂ => exp (B * (1 - 2 * s))) 0 = exp B * (-2 * B) := by
    simpa using hcomp.deriv
  have hmul : exp B * (-2 * B) = 0 := by
    rw [← hF', Fderiv0]
  rcases (mul_eq_zero.mp hmul) with he | h2B
  · exact (exp_ne_zero B he).elim
  · rcases (mul_eq_zero.mp h2B) with h2 | hB
    · norm_num at h2
    · exact hB

/-! ## GAP 1–3 importados (nombres en raíz de cada módulo). -/

/-! ## Re φ = log ‖h‖, a partir de OrderAtMostOne h. -/

lemma re_le_of_exp_eq_order
    {φ h : ℂ → ℂ}
    (hexp : ∀ z, exp (φ z) = h z)
    (hord : OrderAtMostOne h) :
    ∀ ε > 0, ∃ C : ℝ, 0 < C ∧ ∀ z, (φ z).re ≤ C * (1 + ‖z‖ ^ (1 + ε)) := by
  intro ε hε
  obtain ⟨A, hA, hAb⟩ := hord ε hε
  refine ⟨max (Real.log A) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro z
  have hnorm : ‖h z‖ = Real.exp (φ z).re := by
    rw [← hexp z, norm_exp]
  have hle : ‖h z‖ ≤ A * Real.exp (‖z‖ ^ (1 + ε)) := hAb z
  have hpos : 0 < ‖h z‖ := by
    rw [hnorm]; exact Real.exp_pos _
  have hlog : (φ z).re ≤ Real.log A + ‖z‖ ^ (1 + ε) := by
    have hlogle := Real.log_le_log hpos hle
    have hleft : Real.log ‖h z‖ = (φ z).re := by
      rw [hnorm, Real.log_exp]
    have hright : Real.log (A * Real.exp (‖z‖ ^ (1 + ε))) =
        Real.log A + ‖z‖ ^ (1 + ε) := by
      rw [Real.log_mul (ne_of_gt hA) (Real.exp_ne_zero _), Real.log_exp]
    rw [hleft, hright] at hlogle
    exact hlogle
  have hC1 : Real.log A ≤ max (Real.log A) 1 := le_max_left _ _
  have hC2 : (1 : ℝ) ≤ max (Real.log A) 1 := le_max_right _ _
  have hr : 0 ≤ ‖z‖ ^ (1 + ε) := Real.rpow_nonneg (norm_nonneg z) (1 + ε)
  nlinarith

/-! ## Identidad: se anula en un disco ⇒ 0. -/

lemma entire_eq_zero_of_eqOn_ball {f : ℂ → ℂ} {c : ℂ} {ε : ℝ}
    (hf : Differentiable ℂ f) (hε : 0 < ε)
    (hball : ∀ z ∈ ball c ε, f z = 0) :
    ∀ z, f z = 0 := by
  have hfA : AnalyticOnNhd ℂ f univ := hf.analyticOnNhd
  have hfreq : ∃ᶠ z in 𝓝[≠] c, f z = 0 := by
    rw [frequently_nhdsWithin_iff]
    intro U hU
    obtain ⟨δ, hδ, hUball⟩ := Metric.mem_nhds_iff.mp hU
    let t : ℝ := min (ε / 2) (δ / 2)
    have htpos : 0 < t := by
      have : 0 < ε / 2 := half_pos hε
      have : 0 < δ / 2 := half_pos hδ
      exact lt_min ‹_› ‹_›
    have hne : (c + t : ℂ) ≠ c := by
      intro h
      have ht0 : (t : ℂ) = 0 := by
        simpa using add_right_eq_self.mp h
      have : t = 0 := by exact_mod_cast ht0
      exact htpos.ne' this
    refine ⟨c + t, ?_, hball (c + t) ?_⟩
    · constructor
      · apply hUball
        simp [Complex.dist_eq, add_sub_cancel_left, abs_of_pos htpos]
        have : t < δ := (min_le_right (ε / 2) (δ / 2)).trans_lt (half_lt_self hδ)
        simpa [Complex.dist_eq, abs_of_pos htpos] using this
      · exact hne
    · have : dist (c + t) c < ε := by
        simp [Complex.dist_eq, add_sub_cancel_left, abs_of_pos htpos]
        have : t < ε := (min_le_left (ε / 2) (δ / 2)).trans_lt (half_lt_self hε)
        simpa [abs_of_pos htpos] using this
      exact this
  have hz : c ∈ univ := mem_univ _
  have hEq : EqOn f 0 univ :=
    hfA.eqOn_zero_of_preconnected_of_frequently_eq_zero
      isPreconnected_univ hz hfreq
  intro z
  exact hEq (mem_univ z)

/-! ## GAP 4 importado (`exists_circle_min_norm`, 0 sorry en fuente). -/

/-! ## Ensamblaje -/

theorem entire_never_zero_order_atMostOne
    {h : ℂ → ℂ}
    (hh : Differentiable ℂ h)
    (hne : ∀ z, h z ≠ 0)
    (hord : OrderAtMostOne h) :
    ∃ A B : ℂ, ∀ s, h s = exp (A + B * s) := by
  obtain ⟨φ, hφd, hφexp⟩ := log_holomorphic_of_entire_never_zero hh hne
  obtain ⟨A, B, hAB⟩ := affine_log_of_order_one hφd (re_le_of_exp_eq_order hφexp hord)
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

lemma quotient_symmetric
    {f g h : ℂ → ℂ}
    (hg : Differentiable ℂ g) (hh : Differentiable ℂ h)
    (hf_sym : ∀ s, f (1 - s) = f s)
    (hg_sym : ∀ s, g (1 - s) = g s)
    (hfg : ∀ z, f z = h z * g z)
    (hg_ne : ¬ ∀ z, g z = 0) :
    ∀ s, h (1 - s) = h s := by
  have hmul : ∀ s, h (1 - s) * g (1 - s) = h s * g (1 - s) := by
    intro s
    calc h (1 - s) * g (1 - s) = f (1 - s) := (hfg _).symm
      _ = f s := hf_sym s
      _ = h s * g s := hfg s
      _ = h s * g (1 - s) := by rw [hg_sym s]
  let k : ℂ → ℂ := fun s => h (1 - s) - h s
  have hk : Differentiable ℂ k :=
    (hh.comp (differentiable_const.sub differentiable_id)).sub hh
  obtain ⟨z₀, hz₀⟩ : ∃ z₀, g z₀ ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hg_ne hall
  have hnh : ∀ᶠ z in 𝓝 z₀, g z ≠ 0 :=
    hg.continuous.continuousAt.eventually_ne hz₀
  obtain ⟨ε, hε, hballg⟩ : ∃ ε > 0, ∀ z ∈ ball z₀ ε, g z ≠ 0 := by
    obtain ⟨t, ht, htf⟩ := eventually_iff_exists_mem.mp hnh
    obtain ⟨U, hUo, hzU, hUsub⟩ := mem_nhds_iff.mp ht
    obtain ⟨ε, hε, hUball⟩ := Metric.isOpen_iff.mp hUo z₀ hzU
    refine ⟨ε, hε, ?_⟩
    intro z hz
    exact htf z (hUsub (hUball hz))
  have hballk : ∀ z ∈ ball z₀ ε, k z = 0 := by
    intro z hz
    have hgzn : g z ≠ 0 := hballg z hz
    have hcancel : h (1 - z) = h z :=
      mul_right_cancel₀ (by rw [hg_sym z]; exact hgzn) (hmul z)
    simpa [k] using sub_eq_zero.mpr hcancel
  intro s
  have hk0 := entire_eq_zero_of_eqOn_ball hk hε hballk
  exact sub_eq_zero.mp (hk0 s)

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
  obtain ⟨h, hh, hne, hfg⟩ := quotient_entire_never_zero hf hg hzeros hg_ne
  have hord : OrderAtMostOne h :=
    order_atMostOne_of_quotient hf hg hh hf_ord hg_ord hne hg_ne hfg
  have hsym : ∀ s, h (1 - s) = h s :=
    quotient_symmetric hg hh hf_sym hg_sym hfg hg_ne
  obtain ⟨C, _, hC⟩ := constant_of_sym_and_order hh hne hord hsym
  have hC1 : C = 1 := by
    have := hfg ((1 : ℂ) / 2)
    rw [hC _, hnorm] at this
    exact (mul_eq_right₀ hhalf).mp this.symm
  intro s
  simp [hfg s, hC s, hC1]

/-!
  Mapa v3.2.5 — 27 ago 2026

  Enunciado: enteras de orden ≤ 1, mismos ceros con multiplicidad,
  f(1-s)=f(s), g(1-s)=g(s), f(1/2)=g(1/2)≠0 ⇒ f=g.

  Cerrado como argumento / fuente (no lake)
  -----------------------------------------
  GAP1 log holomorfo (import).
  GAP2 Borel + Cauchy n=2 + afín (import).
  GAP3 Riemann extraíble (import).
  GAP4 min |g| en círculo separado + OrderAtMostOne del cociente (import).
  B=0. C=1. h simétrica por identidad.
  Re φ = log ‖h‖.
  hadamard_uniqueness ensamblado.

  Hueco que queda
  ---------------
  lake-checked. No hay tactic sorry en GAP1–4 ni en este ensamblaje.

  No se afirma
  ------------
  RH. D ≡ Ξ. Paley–Wiener para ξ. Unicidad de Hadamard no es RH.
-/

end
