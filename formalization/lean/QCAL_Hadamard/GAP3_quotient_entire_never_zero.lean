/-
  GAP 3 v3.2.4 — quotient_entire_never_zero

  f, g enteras, g ≢ 0, SameZeros
    → h z = f^{(n)}(z) / g^{(n)}(z), n = ord_z g
    → h entera, nunca cero, f = h * g

  Infinitos ceros: orden local + Riemann extraíble.
  No `extract_zeros_poles`.

  José Manuel Mota Burruezo · Noesis · QCAL ∞³
-/

import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.RemovableSingularity

noncomputable section
open Complex Filter Set
open scoped Topology

variable {f g : ℂ → ℂ}

def SameZeros (f g : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, analyticOrderAt f z = analyticOrderAt g z

lemma analyticOrderAt_ne_top_of_not_eq_zero
    (hg : Differentiable ℂ g) (hg0 : ¬ ∀ z, g z = 0) (z : ℂ) :
    analyticOrderAt g z ≠ ⊤ := by
  intro htop
  have hA : ∀ z₀, AnalyticAt ℂ g z₀ := fun z₀ => (hg z₀).analyticAt
  have : g = 0 :=
    (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z hA).mp htop
  exact hg0 (fun w => congrFun this w)

lemma exists_local_factors
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hzeros : SameZeros f g)
    (hg0 : ¬ ∀ z, g z = 0) (z₀ : ℂ) :
    ∃ (n : ℕ) (u v : ℂ → ℂ),
      AnalyticAt ℂ u z₀ ∧ AnalyticAt ℂ v z₀ ∧
      u z₀ ≠ 0 ∧ v z₀ ≠ 0 ∧
      (∀ᶠ w in 𝓝 z₀, f w = (w - z₀) ^ n * u w) ∧
      (∀ᶠ w in 𝓝 z₀, g w = (w - z₀) ^ n * v w) := by
  have htop : analyticOrderAt g z₀ ≠ ⊤ :=
    analyticOrderAt_ne_top_of_not_eq_zero hg hg0 z₀
  let n := analyticOrderNatAt g z₀
  have hn : analyticOrderAt g z₀ = n :=
    (Nat.cast_analyticOrderNatAt htop).symm
  have hfA : AnalyticAt ℂ f z₀ := (hf z₀).analyticAt
  have hgA : AnalyticAt ℂ g z₀ := (hg z₀).analyticAt
  have hfn : analyticOrderAt f z₀ = n := (hzeros z₀).trans hn
  obtain ⟨u, huA, hu0, huf⟩ := (hfA.analyticOrderAt_eq_natCast (n := n)).mp hfn
  obtain ⟨v, hvA, hv0, hvg⟩ := (hgA.analyticOrderAt_eq_natCast (n := n)).mp hn
  refine ⟨n, u, v, huA, hvA, hu0, hv0, ?_, ?_⟩
  · filter_upwards [huf] with w hw; simpa [smul_eq_mul] using hw
  · filter_upwards [hvg] with w hw; simpa [smul_eq_mul] using hw

lemma quotient_eq_uv_punctured
    {n : ℕ} {u v : ℂ → ℂ} {z₀ : ℂ}
    (hvA : AnalyticAt ℂ v z₀) (hv0 : v z₀ ≠ 0)
    (huf : ∀ᶠ w in 𝓝 z₀, f w = (w - z₀) ^ n * u w)
    (hvg : ∀ᶠ w in 𝓝 z₀, g w = (w - z₀) ^ n * v w) :
    ∀ᶠ w in 𝓝[≠] z₀, g w ≠ 0 ∧ f w / g w = u w / v w := by
  have hv_ne : ∀ᶠ w in 𝓝 z₀, v w ≠ 0 :=
    hvA.continuousAt.eventually_ne hv0
  filter_upwards [huf.filter_mono nhdsWithin_le_nhds,
    hvg.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin,
    hv_ne.filter_mono nhdsWithin_le_nhds] with w hf' hg' hwne hvne
  have hpow : (w - z₀) ^ n ≠ 0 := pow_ne_zero n (sub_ne_zero.mpr hwne)
  have hgne : g w ≠ 0 := by
    rw [hg']; exact mul_ne_zero hpow hvne
  refine ⟨hgne, ?_⟩
  rw [hf', hg', mul_div_mul_left _ _ hpow]

/-- Coeficiente líder: f = (z-z₀)^n u ⇒ f^{(n)}(z₀) = n! u(z₀). -/
lemma iteratedDeriv_eventuallyEq {f₁ f₂ : ℂ → ℂ} {x : ℂ}
    (h : f₁ =ᶠ[𝓝 x] f₂) (n : ℕ) :
    iteratedDeriv n f₁ x = iteratedDeriv n f₂ x := by
  induction n generalizing f₁ f₂ with
  | zero => simpa [iteratedDeriv_zero] using h.self_of_nhds
  | succ n ih =>
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    exact ih h.deriv

lemma iteratedDeriv_pow_mul_center {n : ℕ} {u : ℂ → ℂ} {z₀ : ℂ}
    (hu : AnalyticAt ℂ u z₀) :
    iteratedDeriv n (fun w => (w - z₀) ^ n * u w) z₀ = n.factorial * u z₀ := by
  induction n generalizing u with
  | zero => simp [iteratedDeriv_zero]
  | succ n ih =>
    have huA : AnalyticAt ℂ u z₀ := hu
    have hderA : AnalyticAt ℂ (deriv u) z₀ := huA.deriv
    let u1 : ℂ → ℂ := fun w => (n + 1 : ℂ) * u w + (w - z₀) * deriv u w
    have hu1 : AnalyticAt ℂ u1 z₀ := by
      exact (analyticAt_const.mul huA).add ((analyticAt_id.sub analyticAt_const).mul hderA)
    have hder : deriv (fun w => (w - z₀) ^ (n + 1) * u w) =ᶠ[𝓝 z₀]
        fun w => (w - z₀) ^ n * u1 w := by
      have hU : ∀ᶠ w in 𝓝 z₀, AnalyticAt ℂ u w := huA.eventually_analyticAt
      filter_upwards [hU] with w hw
      have hdiff_u : DifferentiableAt ℂ u w := hw.differentiableAt
      have hpow : DifferentiableAt ℂ (fun ζ : ℂ => (ζ - z₀) ^ (n + 1)) w := by
        fun_prop
      rw [deriv_mul hpow hdiff_u]
      have hp : deriv (fun ζ : ℂ => (ζ - z₀) ^ (n + 1)) w =
          (n + 1 : ℂ) * (w - z₀) ^ n := by
        have := deriv_pow (f := fun ζ : ℂ => ζ - z₀) (n := n + 1) w
        simp [deriv_sub_const, deriv_id''] at this
        simpa [Nat.cast_add, Nat.cast_one, pow_succ] using this
      rw [hp]
      simp [u1]
      ring
    rw [iteratedDeriv_succ]
    have hcenter := ih (u := u1) hu1
    have := iteratedDeriv_eventuallyEq hder n
    rw [this, hcenter]
    simp [u1, sub_self, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    ring

lemma quotientAt_eq_uv {n : ℕ} {u v : ℂ → ℂ} {z₀ : ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hu : AnalyticAt ℂ u z₀) (hv : AnalyticAt ℂ v z₀)
    (huf : ∀ᶠ w in 𝓝 z₀, f w = (w - z₀) ^ n * u w)
    (hvg : ∀ᶠ w in 𝓝 z₀, g w = (w - z₀) ^ n * v w)
    (hv0 : v z₀ ≠ 0) :
    iteratedDeriv n f z₀ / iteratedDeriv n g z₀ = u z₀ / v z₀ := by
  have hfA : AnalyticAt ℂ f z₀ := (hf z₀).analyticAt
  have hgA : AnalyticAt ℂ g z₀ := (hg z₀).analyticAt
  have hfe : f =ᶠ[𝓝 z₀] fun w => (w - z₀) ^ n * u w := huf
  have hge : g =ᶠ[𝓝 z₀] fun w => (w - z₀) ^ n * v w := hvg
  have hf' : iteratedDeriv n f z₀ = n.factorial * u z₀ := by
    rw [iteratedDeriv_eventuallyEq hfe n, iteratedDeriv_pow_mul_center hu]
  have hg' : iteratedDeriv n g z₀ = n.factorial * v z₀ := by
    rw [iteratedDeriv_eventuallyEq hge n, iteratedDeriv_pow_mul_center hv]
  have hfac : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  rw [hf', hg', mul_div_mul_left _ _ hfac]

noncomputable def quotientAt (f g : ℂ → ℂ) (z : ℂ) : ℂ :=
  let n := analyticOrderNatAt g z
  iteratedDeriv n f z / iteratedDeriv n g z

lemma quotientAt_ne_zero
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hzeros : SameZeros f g) (hg0 : ¬ ∀ z, g z = 0) (z : ℂ) :
    quotientAt f g z ≠ 0 := by
  have htop : analyticOrderAt g z ≠ ⊤ :=
    analyticOrderAt_ne_top_of_not_eq_zero hg hg0 z
  let n := analyticOrderNatAt g z
  have hn : analyticOrderAt g z = n :=
    (Nat.cast_analyticOrderNatAt htop).symm
  have hfn : analyticOrderAt f z = n := (hzeros z).trans hn
  have hfA : AnalyticAt ℂ f z := (hf z).analyticAt
  have hgA : AnalyticAt ℂ g z := (hg z).analyticAt
  have hf' := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hfA (n := n)).mp hfn
  have hg' := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hgA (n := n)).mp hn
  exact div_ne_zero hf'.2 hg'.2

lemma quotientAt_eq_div
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    {z : ℂ} (hz : g z ≠ 0) :
    quotientAt f g z = f z / g z := by
  have hgA : AnalyticAt ℂ g z := (hg z).analyticAt
  have hn0 : analyticOrderAt g z = 0 := hgA.analyticOrderAt_eq_zero.mpr hz
  simp [quotientAt, analyticOrderNatAt, hn0, iteratedDeriv_zero]

lemma eventually_ne_zero_of_order_ne_top
    {g : ℂ → ℂ} {z : ℂ} (hg : AnalyticAt ℂ g z)
    (htop : analyticOrderAt g z ≠ ⊤) :
    ∀ᶠ w in 𝓝[≠] z, g w ≠ 0 := by
  rcases hg.eventually_eq_zero_or_eventually_ne_zero with h0 | hne
  · exact (htop (analyticOrderAt_eq_top.mpr h0)).elim
  · exact hne.filter_mono nhdsWithin_le_nhds

theorem quotient_entire_never_zero
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hzeros : SameZeros f g)
    (hg0 : ¬ ∀ z, g z = 0) :
    ∃ h : ℂ → ℂ,
      Differentiable ℂ h ∧ (∀ z, h z ≠ 0) ∧ ∀ z, f z = h z * g z := by
  let h := quotientAt f g
  refine ⟨h, ?hol, fun z => quotientAt_ne_zero hf hg hzeros hg0 z, ?prod⟩
  · intro z
    obtain ⟨n, u, v, huA, hvA, hu0, hv0, huf, hvg⟩ :=
      exists_local_factors hf hg hzeros hg0 z
    have hgA : AnalyticAt ℂ g z := (hg z).analyticAt
    have htop : analyticOrderAt g z ≠ ⊤ :=
      analyticOrderAt_ne_top_of_not_eq_zero hg hg0 z
    have hn_eq : n = analyticOrderNatAt g z := by
      have : analyticOrderAt g z = n :=
        (hgA.analyticOrderAt_eq_natCast (n := n)).mpr
          ⟨v, hvA, hv0, by
            filter_upwards [hvg] with w hw
            simpa [smul_eq_mul] using hw⟩
      rw [analyticOrderNatAt, this, ENat.toNat_natCast]
    have hzuv : h z = u z / v z := by
      have := quotientAt_eq_uv (f := f) (g := g) hf hg huA hvA huf hvg hv0
      simp [h, quotientAt, hn_eq] at this ⊢
      exact this
    have hpunct : ∀ᶠ w in 𝓝[≠] z, DifferentiableAt ℂ h w := by
      have hgne := eventually_ne_zero_of_order_ne_top hgA htop
      filter_upwards [hgne] with w hwne
      have : h w = f w / g w := quotientAt_eq_div hf hg hwne
      rw [this]
      exact (hf w).div (hg w) hwne
    have hnh : h =ᶠ[𝓝 z] fun w => u w / v w := by
      obtain ⟨t, htnh, htf⟩ := eventually_iff_exists_mem.mp
        (huf.and (hvg.and (hvA.continuousAt.eventually_ne hv0)))
      obtain ⟨U, hUo, hzU, hUsub⟩ := mem_nhds_iff.mp htnh
      refine Filter.eventually_of_mem (hUo.mem_nhds hzU) ?_
      intro w hwU
      have htriple := htf w (hUsub hwU)
      rcases htriple with ⟨hfw, hgw, hvw⟩
      by_cases hwz : w = z
      · subst hwz; exact hzuv
      · have hpow : (w - z) ^ n ≠ 0 := pow_ne_zero n (sub_ne_zero.mpr hwz)
        have hgne : g w ≠ 0 := by
          rw [hgw]; exact mul_ne_zero hpow hvw
        have : h w = f w / g w := quotientAt_eq_div hf hg hgne
        rw [this, hfw, hgw, mul_div_mul_left _ _ hpow]
    have hcont : ContinuousAt h z :=
      (huA.continuousAt.div hvA.continuousAt hv0).congr hnh.symm
    exact (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      hpunct hcont).differentiableAt
  · intro z
    by_cases hz : g z = 0
    · have hgA : AnalyticAt ℂ g z := (hg z).analyticAt
      have hgord : analyticOrderAt g z ≠ 0 := by
        intro h0
        exact hz (hgA.analyticOrderAt_eq_zero.mp h0)
      have hford : analyticOrderAt f z ≠ 0 := by
        rw [hzeros z]; exact hgord
      have hf0 : f z = 0 := apply_eq_zero_of_analyticOrderAt_ne_zero hford
      simp [hz, hf0]
    · have := quotientAt_eq_div hf hg hz
      exact (eq_div_iff hz).mp this.symm

end
