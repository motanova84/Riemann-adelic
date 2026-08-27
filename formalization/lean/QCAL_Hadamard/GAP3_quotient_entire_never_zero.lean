/-
  GAP 3 v3.2.3 — quotient_entire_never_zero

  f, g enteras, g ≢ 0, SameZeros
    → h z = f^{(n)}(z) / g^{(n)}(z), n = ord_z g
    → h entera, nunca cero, f = h * g

  Infinitos ceros: orden local, no `extract_zeros_poles`.

  José Manuel Mota Burruezo · Noesis · QCAL ∞³
-/

import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.RemovableSingularity

noncomputable section
open Complex Filter Set
open scoped Topology

variable {f g : ℂ → ℂ}

def SameZeros (f g : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, analyticOrderAt f z = analyticOrderAt g z

/-- g ≢ 0 entera ⇒ orden finito. Mathlib nombra el iff. -/
lemma analyticOrderAt_ne_top_of_not_eq_zero
    (hg : Differentiable ℂ g) (hg0 : ¬ ∀ z, g z = 0) (z : ℂ) :
    analyticOrderAt g z ≠ ⊤ := by
  intro htop
  have hA : ∀ z₀, AnalyticAt ℂ g z₀ := fun z₀ => (hg z₀).analyticAt
  have : g = 0 :=
    (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z hA).mp htop
  exact hg0 (fun w => congrFun this w)

/-- Factorización local, mismo n. -/
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

/-- En el agujero, f/g = u/v. -/
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
  rw [hf', hg', mul_div_mul_comm, div_self hpow, one_mul]
  -- `mul_div_mul_comm` / `mul_div_mul_left`: glue de anillo
  sorry

/-- Definición canónica: n-ésimas derivadas. Sin Classical.choose. -/
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
  -- n = 0 ⇒ iteratedDeriv 0 = id
  simp [quotientAt, analyticOrderNatAt, hn0, iteratedDeriv_zero]

/-- GAP 3. -/
theorem quotient_entire_never_zero
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hzeros : SameZeros f g)
    (hg0 : ¬ ∀ z, g z = 0) :
    ∃ h : ℂ → ℂ,
      Differentiable ℂ h ∧ (∀ z, h z ≠ 0) ∧ ∀ z, f z = h z * g z := by
  let h := quotientAt f g
  refine ⟨h, ?hol, fun z => quotientAt_ne_zero hf hg hzeros hg0 z, ?prod⟩
  · -- {g ≠ 0}: h = f/g, cociente holomorfo
    -- ceros: Riemann `analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`
    --   porque f/g → u(z)/v(z) = h(z)
    sorry
  · intro z
    by_cases hz : g z = 0
    · -- n > 0 (o n=0 contradice hz vía SameZeros + eq_zero)
      -- ambos lados 0: f z = 0 por mismo orden
      sorry
    · have := quotientAt_eq_div hf hg hz
      exact (eq_div_iff hz).mp this.symm

/-
  Cerrado como argumento:
  - orden ≠ ⊤  (`analyticOrderAt_eq_top_iff_eq_zero`)
  - factores locales (`analyticOrderAt_eq_natCast`)
  - h canónica por iteratedDeriv (sin choose)
  - h ≠ 0 (`analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero`)
  - h = f/g fuera de ceros (`analyticOrderAt_eq_zero`)

  Glue de lake:
  - `DifferentiableAt.analyticAt` (ℂ)
  - anillo: `mul_div_mul_left` en el agujero
  - Riemann extraíble + continuidad de h en el cero
  - f = h g en el cero (ambos 0)

  No densidad. No extract_zeros_poles.
-/

end
