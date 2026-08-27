/-
  GAP 4 v3.2.7 — order_atMostOne_of_quotient

  f = h * g, enteras, h nunca cero, g ≢ 0,
  OrderAtMostOne f, OrderAtMostOne g
    → OrderAtMostOne h.

  Cerrado aquí:
    máximo módulo (`Complex.norm_le_of_forall_mem_frontier_norm_le`),
    |h| = |f|/|g| fuera de ceros,
    compacto ⇒ |h| acotado,
    r^{1+ε/2} se absorbe en r^{1+ε},
    `exists_radius_zero_free` — ceros aislados + compacto ⇒ finitos
      en closedBall 0 (R+1) ⇒ existe R' ∈ [R, R+1] sin ceros.

  Cerrado ahora (fuente, no lake):
    `log_one_add_ge_div`, `divisor_sum_le_jensen` (n(R)=O(R^{2+ε})),
    `exists_radius_sep` (palomar δ ≥ 1/(2(n+1))),
    `extract_on_closedBall` (`extract_zeros_poles` en disco compacto;
     GAP3 sigue: no extract en todo ℂ).

  Un sorry:
    |g| = |P| |u| en el círculo, |P| ≥ δ^{n(R)}, min |u| por Borel.

  No lake-checked. No RH. No D ≡ Ξ.

  José Manuel Mota Burruezo · Noesis · QCAL ∞³
-/

import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.DiffContOnCl
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.Basic

noncomputable section
open Complex Filter Metric Set
open scoped Topology Real Classical

/-- Orden ≤ 1 de Hadamard. ξ clásica SÍ es esto. -/
def OrderAtMostOne (f : ℂ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 0 < A ∧ ∀ z : ℂ, ‖f z‖ ≤ A * Real.exp (‖z‖ ^ (1 + ε))

/-- Tipo exponencial (Paley–Wiener). ξ clásica NO es esto. -/
def OrderLEOne (f : ℂ → ℂ) : Prop :=
  ∃ A B : ℝ, 0 < A ∧ 0 ≤ B ∧ ∀ z : ℂ, ‖f z‖ ≤ A * Real.exp (B * ‖z‖)

variable {f g h : ℂ → ℂ}

/-- Máximo módulo: |h| en el disco ≤ máximo en el círculo. -/
lemma entire_norm_le_of_sphere
    (hh : Differentiable ℂ h) {R C : ℝ} (hR : 0 < R)
    (hC : ∀ z ∈ sphere (0 : ℂ) R, ‖h z‖ ≤ C)
    {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖h z‖ ≤ C := by
  have hU : IsBounded (ball (0 : ℂ) R) := isBounded_ball
  have hd : DiffContOnCl ℂ h (ball (0 : ℂ) R) := hh.diffContOnCl
  have hfront : ∀ w ∈ frontier (ball (0 : ℂ) R), ‖h w‖ ≤ C := by
    intro w hw
    rw [frontier_ball (0 : ℂ) hR.ne'] at hw
    exact hC w hw
  have hzcl : z ∈ closure (ball (0 : ℂ) R) := by
    rw [closure_ball (0 : ℂ) hR.ne']
    exact mem_closedBall.2 hz
  exact norm_le_of_forall_mem_frontier_norm_le hU hd hfront hzcl

lemma h_eq_div (hfg : ∀ z, f z = h z * g z) {z : ℂ} (hgz : g z ≠ 0) :
    h z = f z / g z :=
  (eq_div_iff hgz).mpr (hfg z)

/-- Fuera de un cero, o g es idénticamente 0, o los ceros son aislados. -/
lemma eventually_ne_zero_punctured
    (hg : Differentiable ℂ g) (hg0 : ¬ ∀ z, g z = 0) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, g w ≠ 0 := by
  have hA : AnalyticAt ℂ g z := (hg z).analyticAt
  cases hA.eventually_eq_zero_or_eventually_ne_zero with
  | inl h0 =>
    have hAn : AnalyticOnNhd ℂ g univ := fun _ _ => (hg _).analyticAt
    have hfreq : ∃ᶠ w in 𝓝[≠] z, g w = 0 :=
      (h0.filter_mono nhdsWithin_le_nhds).frequently
    have heq : EqOn g 0 univ :=
      hAn.eqOn_zero_of_preconnected_of_frequently_eq_zero
        isPreconnected_univ (mem_univ z) hfreq
    exact absurd (fun w => heq (mem_univ w)) hg0
  | inr hne => exact hne

/-- Cada cero tiene una bola que no contiene otro cero. -/
lemma zeros_isolated
    (hg : Differentiable ℂ g) (hg0 : ¬ ∀ z, g z = 0) (z : ℂ) :
    ∃ ε > 0, ∀ w ∈ ball z ε, w ≠ z → g w ≠ 0 := by
  have hpunct := eventually_ne_zero_punctured hg hg0 z
  have hnh : ∀ᶠ w in 𝓝 z, w ≠ z → g w ≠ 0 :=
    (eventually_nhdsWithin_iff (p := fun w => g w ≠ 0)).1 hpunct
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hnh
  exact ⟨ε, hε, fun w hw hwne => hball hw hwne⟩

/-- Ceros en un compacto: finitos (aislados + Heine-Borel). -/
lemma zeros_finite_closedBall
    (hg : Differentiable ℂ g) (hg0 : ¬ ∀ z, g z = 0) {R : ℝ} (_hR : 0 ≤ R) :
    {z : ℂ | z ∈ closedBall (0 : ℂ) R ∧ g z = 0}.Finite := by
  let Z : Set ℂ := {z | z ∈ closedBall (0 : ℂ) R ∧ g z = 0}
  have hcl : IsClosed Z :=
    isClosed_closedBall.inter (isClosed_singleton.preimage hg.continuous)
  have hZcp : IsCompact Z :=
    (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset hcl (fun _ hz => hz.1)
  let c : ℂ → Set ℂ := fun z => ball z (Exists.choose (zeros_isolated hg hg0 z))
  have hc : ∀ z ∈ Z, IsOpen (c z) := fun _ _ => isOpen_ball
  have hsc : Z ⊆ ⋃ z ∈ Z, c z := by
    intro x hx
    refine mem_iUnion₂.2 ⟨x, hx, mem_ball_self ?_⟩
    exact (Exists.choose_spec (zeros_isolated hg hg0 x)).1
  obtain ⟨u, huZ, hufin, hucov⟩ := hZcp.elim_finite_subcover_image hc hsc
  have hsub : Z ⊆ ⋃ z ∈ u, ({z} : Set ℂ) := by
    intro x hx
    obtain ⟨z, hzu, hxc⟩ := mem_iUnion₂.mp (hucov hx)
    have : x = z := by
      by_contra hne
      exact (Exists.choose_spec (zeros_isolated hg hg0 z)).2 x hxc hne hx.2
    subst this
    exact mem_iUnion₂.2 ⟨x, hzu, rfl⟩
  exact (hufin.biUnion fun _ _ => finite_singleton _).subset hsub

/-- [a,b] con a < b es infinito. -/
lemma Icc_infinite_of_lt {a b : ℝ} (h : a < b) : (Icc a b).Infinite :=
  (Ioo_infinite h).mono Ioo_subset_Icc_self

/-- Existe un radio R' ∈ [R, R+1] cuya circunferencia no pasa por ningún cero. -/
theorem exists_radius_zero_free
    (hg : Differentiable ℂ g) (hg0 : ¬ ∀ z, g z = 0)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ R' ∈ Icc R (R + 1), ∀ z : ℂ, ‖z‖ = R' → g z ≠ 0 := by
  have hfin := zeros_finite_closedBall hg hg0 (R := R + 1) (by linarith)
  let S : Set ℝ := (fun z : ℂ => ‖z‖) ''
      {z : ℂ | z ∈ closedBall (0 : ℂ) (R + 1) ∧ g z = 0}
  have hSfin : S.Finite := hfin.image _
  have hdiff : (Icc R (R + 1) \ S).Nonempty := by
    have hinf : (Icc R (R + 1)).Infinite :=
      Icc_infinite_of_lt (by linarith : R < R + 1)
    exact (hinf.diff hSfin).nonempty
  obtain ⟨R', hR'mem⟩ := hdiff
  have hR'I : R' ∈ Icc R (R + 1) := hR'mem.1
  have hR'S : R' ∉ S := hR'mem.2
  refine ⟨R', hR'I, ?_⟩
  intro z hz hg0z
  apply hR'S
  refine ⟨z, ⟨?_, hg0z⟩, hz⟩
  rw [mem_closedBall, dist_zero_right]
  exact le_trans (le_of_eq hz) hR'I.2

/-- log(1+t) ≥ t/(1+t) para t>0. MVT: log' = 1/ξ ≥ 1/(1+t). -/
lemma log_one_add_ge_div {t : ℝ} (ht : 0 < t) :
    t / (1 + t) ≤ Real.log (1 + t) := by
  have hlt : (1 : ℝ) < 1 + t := by linarith
  have hcont : ContinuousOn Real.log (Icc 1 (1 + t)) := by
    intro x hx
    exact (continuousAt_log (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx.1))).continuousWithinAt
  have hdiff : DifferentiableOn ℝ Real.log (Ioo 1 (1 + t)) := by
    intro x hx
    exact (Real.differentiableAt_log (ne_of_gt (lt_trans (by norm_num : (0 : ℝ) < 1) hx.1))).differentiableWithinAt
  obtain ⟨ξ, hξ, hξeq⟩ := exists_deriv_eq_slope Real.log hlt hcont hdiff
  have hξIoo : ξ ∈ Ioo (1 : ℝ) (1 + t) := hξ
  have hξpos : 0 < ξ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hξIoo.1.le
  have hder : deriv Real.log ξ = ξ⁻¹ := Real.deriv_log ξ
  rw [hder] at hξeq
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hslope : (Real.log (1 + t) - Real.log 1) / t = ξ⁻¹ := by
    simpa [slope_def_field, sub_add, add_comm] using hξeq
  have hlog : Real.log (1 + t) = t / ξ := by
    have : Real.log (1 + t) / t = ξ⁻¹ := by
      simpa [Real.log_one, sub_zero] using hslope
    field_simp [ht0] at this
    linarith
  have hξle : ξ ≤ 1 + t := le_of_lt hξIoo.2
  have : t / (1 + t) ≤ t / ξ :=
    div_le_div_of_nonneg_left ht.le hξpos hξle
  linarith

lemma log_outer_inner_ge {r : ℝ} (hr : 1 ≤ r) :
    (1 : ℝ) / (r + 2) ≤ Real.log ((r + 2) / (r + 1)) := by
  have ht : 0 < (1 : ℝ) / (r + 1) := by positivity
  have heq : (r + 2) / (r + 1) = 1 + 1 / (r + 1) := by field_simp
  rw [heq]
  have hlog := log_one_add_ge_div ht
  have hsimp : (1 / (r + 1)) / (1 + 1 / (r + 1)) = (1 : ℝ) / (r + 2) := by
    field_simp; ring
  rwa [hsimp] at hlog

lemma exists_ne_zero (hg0 : ¬ ∀ z, g z = 0) : ∃ c : ℂ, g c ≠ 0 := by
  simpa [not_forall] using hg0

lemma analyticOnNhd_of_differentiable (hg : Differentiable ℂ g) (s : Set ℂ) :
    AnalyticOnNhd ℂ g s :=
  fun _ _ => (hg _).analyticAt

/-- n(r) ≤ O(r^{2+ε}) vía Jensen `sum_divisor_le`. Centro c con g c ≠ 0. -/
lemma divisor_sum_le_jensen
    (hg : Differentiable ℂ g) (hg_ord : OrderAtMostOne g)
    {c : ℂ} (hc0 : g c ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ r : ℝ, 1 ≤ r →
      ∑ᶠ u, (MeromorphicOn.divisor g (closedBall c (r + 1)) u : ℝ)
        ≤ K * r ^ (2 + ε) := by
  obtain ⟨A, hA, hB⟩ := hg_ord ε hε
  have hgc : 0 < ‖g c‖ := norm_pos_iff.mpr hc0
  let Xc : ℝ := (‖c‖ + 4) ^ (1 + ε)
  let C0 : ℝ := |Real.log (A + 1)| + |Real.log ‖g c‖| + 2
  let K : ℝ := 4 * (C0 + Xc + 1) + 1
  have hK : 0 < K := by positivity
  refine ⟨K, hK, ?_⟩
  intro r hr
  let r_in : ℝ := r + 1
  let R_out : ℝ := r + 2
  have hr_in_pos : 0 < r_in := by linarith
  have hR_out_pos : 0 < R_out := by linarith
  have hr_pos : 0 < |r_in| := by simpa [abs_of_pos hr_in_pos]
  have hrR : |r_in| < |R_out| := by
    simp [abs_of_pos hr_in_pos, abs_of_pos hR_out_pos]; linarith
  let X : ℝ := (‖c‖ + R_out) ^ (1 + ε)
  let M : ℝ := max 1 (A * Real.exp X)
  have hM : 1 ≤ M := le_max_left _ _
  have hAn : AnalyticOnNhd ℂ g (closedBall c |R_out|) :=
    analyticOnNhd_of_differentiable hg _
  have f_bound : ∀ z ∈ sphere c |R_out|, ‖g z‖ ≤ M := by
    intro z hz
    have hzc : ‖z - c‖ = |R_out| := mem_sphere_iff_norm.mp hz
    have hzn : ‖z‖ ≤ ‖c‖ + |R_out| := by
      calc
        ‖z‖ = ‖(z - c) + c‖ := by ring_nf
        _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
        _ = |R_out| + ‖c‖ := by rw [hzc]
        _ = ‖c‖ + |R_out| := add_comm _ _
    have hgz : ‖g z‖ ≤ A * Real.exp (‖z‖ ^ (1 + ε)) := hB z
    have hpow : ‖z‖ ^ (1 + ε) ≤ (‖c‖ + |R_out|) ^ (1 + ε) :=
      Real.rpow_le_rpow (norm_nonneg z) hzn (by linarith)
    have : ‖g z‖ ≤ A * Real.exp ((‖c‖ + |R_out|) ^ (1 + ε)) :=
      hgz.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hpow) hA.le)
    simp [abs_of_pos hR_out_pos] at this ⊢
    exact this.trans (le_max_right _ _)
  have hle :=
    AnalyticOnNhd.sum_divisor_le (f := g) (c := c) (r := r_in) (R := R_out) (M := M)
      hr_pos hrR hM hAn hc0 f_bound
  have : closedBall c |r_in| = closedBall c (r + 1) := by
    simp [abs_of_pos hr_in_pos, r_in]
  rw [this] at hle
  have hden : (1 : ℝ) / (r + 2) ≤ Real.log (R_out / r_in) :=
    log_outer_inner_ge hr
  have hdenpos : 0 < Real.log (R_out / r_in) :=
    lt_of_lt_of_le (div_pos one_pos (by linarith) : (0 : ℝ) < 1 / (r + 2)) hden
  have hsum0 :
      0 ≤ ∑ᶠ u, (MeromorphicOn.divisor g (closedBall c (r + 1)) u : ℝ) :=
    finsum_nonneg fun _ =>
      Int.cast_nonneg.mpr
        ((analyticOnNhd_of_differentiable hg (closedBall c (r + 1))).divisor_nonneg _)
  by_cases hlog : Real.log (M / ‖g c‖) ≤ 0
  · have : Real.log (M / ‖g c‖) / Real.log (R_out / r_in) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hlog hdenpos.le
    have hle0 := hle.trans this
    have hzero := le_antisymm hle0 hsum0
    rw [hzero]
    exact mul_nonneg hK.le (Real.rpow_nonneg (by linarith) _)
  · have hlogpos : 0 < Real.log (M / ‖g c‖) := lt_of_not_ge hlog
    have hinv : (Real.log (R_out / r_in))⁻¹ ≤ r + 2 := by
      rw [inv_le_iff_one_le_mul₀ hdenpos]
      have : 1 ≤ Real.log (R_out / r_in) * (r + 2) := by nlinarith [hden]
      exact this
    have hle2 :
        ∑ᶠ u, (MeromorphicOn.divisor g (closedBall c (r + 1)) u : ℝ)
          ≤ Real.log (M / ‖g c‖) * (r + 2) := by
      have : Real.log (M / ‖g c‖) / Real.log (R_out / r_in)
          ≤ Real.log (M / ‖g c‖) * (r + 2) := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left hinv hlogpos.le
      exact hle.trans this
    have hMle : M ≤ (A + 1) * Real.exp X := by
      apply max_le
      · have h1 : 1 ≤ Real.exp X :=
          Real.one_le_exp (Real.rpow_nonneg (by positivity) _)
        nlinarith [hA.le, h1]
      · nlinarith [hA.le, Real.exp_pos X]
    have hlogM : Real.log M ≤ Real.log (A + 1) + X := by
      have hpos : 0 < (A + 1) * Real.exp X := by positivity
      have : Real.log M ≤ Real.log ((A + 1) * Real.exp X) :=
        Real.log_le_log (lt_of_lt_of_le zero_lt_one hM) hMle
      rwa [Real.log_mul (by linarith) (Real.exp_ne_zero _), Real.log_exp] at this
    have hlogMg :
        Real.log (M / ‖g c‖) ≤ C0 + X := by
      rw [Real.log_div (by
          exact (lt_of_lt_of_le zero_lt_one hM).ne') (ne_of_gt hgc)]
      have : Real.log M - Real.log ‖g c‖ ≤ |Real.log (A + 1)| + X + |Real.log ‖g c‖| + 2 := by
        have h1 : Real.log M ≤ |Real.log (A + 1)| + X :=
          hlogM.trans (add_le_add_right (le_abs_self _) _)
        nlinarith [le_abs_self (Real.log ‖g c‖), abs_nonneg (Real.log ‖g c‖)]
      have : C0 + X = |Real.log (A + 1)| + |Real.log ‖g c‖| + 2 + X := by
        simp [C0]; ring
      linarith
    have hXle : X ≤ Xc * r ^ (1 + ε) := by
      have hlin : ‖c‖ + R_out ≤ (‖c‖ + 4) * r := by
        have : R_out = r + 2 := rfl
        nlinarith [norm_nonneg c, hr]
      have hnn : 0 ≤ ‖c‖ + R_out := by positivity
      have hp := Real.rpow_le_rpow hnn hlin (by linarith : 0 ≤ 1 + ε)
      have hrpow : ((‖c‖ + 4) * r) ^ (1 + ε) =
          (‖c‖ + 4) ^ (1 + ε) * r ^ (1 + ε) :=
        Real.mul_rpow (by positivity) (by linarith : 0 ≤ r)
      have : X = (‖c‖ + R_out) ^ (1 + ε) := rfl
      rw [this, hrpow] at hp
      simpa [Xc] using hp
    have hr2 : r + 2 ≤ 3 * r := by nlinarith [hr]
    have hpow1 : (1 : ℝ) ≤ r ^ (2 + ε) := by
      have : (1 : ℝ) ≤ r := hr
      exact Real.one_le_rpow this (by linarith)
    have hpowr : r ≤ r ^ (2 + ε) := by
      have : r ^ (1 : ℝ) ≤ r ^ (2 + ε) :=
        Real.rpow_le_rpow_of_exponent_le hr (by linarith)
      simpa using this
    have hpowX : r ^ (1 + ε) ≤ r ^ (2 + ε) :=
      Real.rpow_le_rpow_of_exponent_le hr (by linarith)
    have : Real.log (M / ‖g c‖) * (r + 2) ≤ K * r ^ (2 + ε) := by
      have h1 : Real.log (M / ‖g c‖) * (r + 2) ≤ (C0 + X) * (3 * r) :=
        mul_le_mul hlogMg hr2 (by linarith) (by
          have : 0 ≤ C0 + X := by positivity
          linarith [hlogMg, hlogpos.le])
      have h2 : (C0 + X) * (3 * r) ≤ (C0 + Xc * r ^ (1 + ε)) * (3 * r) := by
        apply mul_le_mul_of_nonneg_right
        · linarith [hXle, Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ r) (1 + ε)]
        · nlinarith [hr]
      have h3 : (C0 + Xc * r ^ (1 + ε)) * (3 * r)
          ≤ 3 * C0 * r ^ (2 + ε) + 3 * Xc * r ^ (2 + ε) := by
        have : (C0 + Xc * r ^ (1 + ε)) * (3 * r) =
            3 * C0 * r + 3 * Xc * (r ^ (1 + ε) * r) := by ring
        rw [this]
        have hrpow' : r ^ (1 + ε) * r = r ^ (2 + ε) := by
          rw [← Real.rpow_add_one (by linarith : (0 : ℝ) ≤ r)]
          ring_nf
        rw [hrpow']
        nlinarith [hpowr, Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ r) (2 + ε),
          abs_nonneg (Real.log (A + 1)), abs_nonneg (Real.log ‖g c‖)]
      have hKbound : 3 * C0 + 3 * Xc ≤ K := by
        simp [K]; nlinarith [abs_nonneg (Real.log (A + 1)),
          abs_nonneg (Real.log ‖g c‖), Real.rpow_nonneg (by positivity : 0 ≤ ‖c‖ + 4) (1 + ε)]
      nlinarith [Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ r) (2 + ε)]
    exact hle2.trans this

/-- Palomar: n+1 puntos de malla, n centros. Spacing 2δ, intervalo abierto 2δ. -/
lemma exists_grid_away {s : Finset ℝ} {R : ℝ} (_hR : 0 ≤ R) :
    ∃ R' ∈ Icc R (R + 1),
      ∀ x ∈ s, (1 / (2 * (s.card + 1) : ℝ)) ≤ |R' - x| := by
  classical
  let n := s.card
  let δ : ℝ := 1 / (2 * (n + 1 : ℝ))
  let t : ℕ → ℝ := fun k => R + (k : ℝ) / (n + 1 : ℝ)
  have hnpos : (0 : ℝ) < n + 1 := by positivity
  have htI : ∀ k, k ≤ n → t k ∈ Icc R (R + 1) := by
    intro k hk
    constructor
    · have : 0 ≤ (k : ℝ) / (n + 1 : ℝ) := div_nonneg (Nat.cast_nonneg _) hnpos.le
      simp [t]; linarith
    · have : (k : ℝ) / (n + 1 : ℝ) ≤ 1 := by
        rw [div_le_one hnpos]
        exact_mod_cast (le_trans hk (Nat.le_succ n))
      simp [t]; linarith
  have htdiff : ∀ i j, t i - t j = ((i : ℝ) - j) / (n + 1 : ℝ) := by
    intro i j; simp [t]; field_simp; ring
  have : ∃ k, k ≤ n ∧ ∀ x ∈ s, δ ≤ |t k - x| := by
    by_contra hnone
    push_neg at hnone
    have hclose : ∀ k ∈ Finset.range (n + 1), ∃ x ∈ s, |t k - x| < δ := by
      intro k hk
      exact hnone k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
    have huniq : ∀ x ∈ s,
        ((Finset.range (n + 1)).filter (fun k => |t k - x| < δ)).card ≤ 1 := by
      intro x hx
      refine Finset.card_le_one.2 ?_
      intro i hi j hj
      simp only [Finset.mem_filter, Finset.mem_range] at hi hj
      have hiδ := hi.2
      have hjδ := hj.2
      have habs : |t i - t j| < 1 / (n + 1 : ℝ) := by
        have h2 : 2 * δ = 1 / (n + 1 : ℝ) := by
          simp [δ]; field_simp; ring
        have := abs_sub_le (t i) x (t j)
        have : |t j - x| = |x - t j| := abs_sub_comm _ _
        linarith [this, abs_sub_comm x (t j)]
      have : |((i : ℝ) - j) / (n + 1 : ℝ)| < 1 / (n + 1 : ℝ) := by
        rwa [htdiff i j] at habs
      have : |(i : ℝ) - j| < 1 := by
        rw [abs_div, abs_of_pos hnpos] at this
        exact (div_lt_iff₀ hnpos).mp this
      have : i = j := by
        have hij : |(i : ℤ) - (j : ℤ)| < 1 := by
          simpa using this
        exact Int.cast_injective (eq_of_sub_eq_zero (Int.abs_lt_one_iff.mp (by
          simpa [Int.cast_sub] using hij)))
      exact this
    have hsub : Finset.range (n + 1) ⊆
        s.biUnion (fun x => (Finset.range (n + 1)).filter (fun k => |t k - x| < δ)) := by
      intro k hk
      obtain ⟨x, hx, hlt⟩ := hclose k hk
      exact Finset.mem_biUnion.2 ⟨x, hx, by simp [hk, hlt]⟩
    have hcard : (Finset.range (n + 1)).card ≤ s.card := by
      refine (Finset.card_le_card hsub).trans ?_
      refine (Finset.card_biUnion_le).trans ?_
      refine (Finset.sum_le_sum (fun x hx => huniq x hx)).trans ?_
      simp
    simpa [Finset.card_range] using (by linarith : ¬ (n + 1 ≤ n)) hcard
  obtain ⟨k, hk, haway⟩ := this
  exact ⟨t k, htI k hk, haway⟩

/-- Radio R' ∈ [R,R+1] sin ceros y separado de las normas de ceros en |z|≤R+2. -/
theorem exists_radius_sep
    (hg : Differentiable ℂ g) (hg0 : ¬ ∀ z, g z = 0)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ (R' : ℝ) (n : ℕ), R' ∈ Icc R (R + 1) ∧
      (∀ z, ‖z‖ = R' → g z ≠ 0) ∧
      ∀ a, a ∈ closedBall (0 : ℂ) (R + 2) → g a = 0 →
        (1 / (2 * (n + 1) : ℝ)) ≤ |R' - ‖a‖| := by
  have hfin := zeros_finite_closedBall hg hg0 (R := R + 2) (by linarith)
  let F := hfin.toFinset
  let n := F.card
  let s : Finset ℝ := F.image (fun z : ℂ => ‖z‖)
  obtain ⟨R', hR'I, haway⟩ := exists_grid_away (s := s) hR
  refine ⟨R', n, hR'I, ?_, ?_⟩
  · intro z hz hg0z
    have hzZ : z ∈ ({w : ℂ | w ∈ closedBall (0 : ℂ) (R + 2) ∧ g w = 0}) := by
      refine ⟨?_, hg0z⟩
      rw [mem_closedBall, dist_zero_right]
      linarith [hR'I.2, le_of_eq hz]
    have hzF : z ∈ F := by simpa [F, Set.Finite.mem_toFinset] using hzZ
    have hnorm : ‖z‖ ∈ s := Finset.mem_image.2 ⟨z, hzF, rfl⟩
    have hδ : (1 / (2 * (s.card + 1) : ℝ)) ≤ |R' - ‖z‖| := haway _ hnorm
    have : 0 < |R' - ‖z‖| := lt_of_lt_of_le (by positivity) hδ
    have : R' ≠ ‖z‖ := fun h => by rw [h, sub_self, abs_zero] at this; linarith
    exact this hz.symm
  · intro a ha ha0
    have haZ : a ∈ ({w : ℂ | w ∈ closedBall (0 : ℂ) (R + 2) ∧ g w = 0}) := ⟨ha, ha0⟩
    have haF : a ∈ F := by simpa [F, Set.Finite.mem_toFinset] using haZ
    have : ‖a‖ ∈ s := Finset.mem_image.2 ⟨a, haF, rfl⟩
    have hδ := haway _ this
    have hcard : s.card ≤ n := Finset.card_image_le
    have : 1 / (2 * (n + 1) : ℝ) ≤ 1 / (2 * (s.card + 1) : ℝ) := by
      apply div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) (by positivity)
      nlinarith [Nat.cast_le.mpr hcard]
    exact this.trans hδ

/-- Orden analítico ≠ ⊤ si g ≢ 0. -/
lemma analyticOrderAt_ne_top_of_not_eq_zero
    (hg : Differentiable ℂ g) (hg0 : ¬ ∀ z, g z = 0) (z : ℂ) :
    analyticOrderAt g z ≠ ⊤ := by
  intro htop
  have hA : ∀ z₀, AnalyticAt ℂ g z₀ := fun z₀ => (hg z₀).analyticAt
  have : g = 0 :=
    (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z hA).mp htop
  exact hg0 (fun w => congrFun this w)

/-- Compatibilidad analítico/meromorfo: `AnalyticAt.meromorphicOrderAt_eq`. -/
lemma meromorphicOrderAt_ne_top_entire
    (hg : Differentiable ℂ g) (hg0 : ¬ ∀ z, g z = 0) (z : ℂ) :
    meromorphicOrderAt g z ≠ ⊤ := by
  have han : analyticOrderAt g z ≠ ⊤ :=
    analyticOrderAt_ne_top_of_not_eq_zero hg hg0 z
  rw [(hg z).analyticAt.meromorphicOrderAt_eq, ENat.map_eq_top_iff]
  exact han

/-- Ceros finitos en un disco compacto: `extract_zeros_poles`. No en todo ℂ. -/
lemma extract_on_closedBall
    (hg : Differentiable ℂ g) (hg0 : ¬ ∀ z, g z = 0) {S : ℝ} (_hS : 0 ≤ S) :
    ∃ u : ℂ → ℂ,
      AnalyticOnNhd ℂ u (closedBall (0 : ℂ) S) ∧
      (∀ z : closedBall (0 : ℂ) S, u z ≠ 0) ∧
      g =ᶠ[codiscreteWithin (closedBall (0 : ℂ) S)]
        (∏ᶠ a, (· - a) ^ MeromorphicOn.divisor g (closedBall (0 : ℂ) S) a) • u := by
  let U := closedBall (0 : ℂ) S
  have hA : AnalyticOnNhd ℂ g U := analyticOnNhd_of_differentiable hg _
  have hM : MeromorphicOn g U := hA.meromorphicOn
  have h₂ : ∀ z : U, meromorphicOrderAt g z ≠ ⊤ :=
    fun z => meromorphicOrderAt_ne_top_entire hg hg0 z
  have h₃ : (MeromorphicOn.divisor g U).support.Finite :=
    (MeromorphicOn.divisor g U).finiteSupport (isCompact_closedBall _ _)
  exact hM.extract_zeros_poles h₂ h₃

/-!
  Jensen da n(R). Palomar da δ. Extract da g = P · u en el disco.
  El mínimo pide |P| ≥ δ^{n} y Borel de u.
-/
theorem exists_circle_min_norm
    (hg : Differentiable ℂ g) (hg_ord : OrderAtMostOne g)
    (hg0 : ¬ ∀ z, g z = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R → ∃ R' ∈ Icc R (R + 1),
      (∀ z, ‖z‖ = R' → g z ≠ 0) ∧
      ∀ z, ‖z‖ = R' → Real.exp (-C * (1 + R' ^ (1 + ε))) ≤ ‖g z‖ := by
  obtain ⟨c, hc0⟩ := exists_ne_zero hg0
  obtain ⟨K, hK, hN⟩ := divisor_sum_le_jensen hg hg_ord hc0 hε
  refine ⟨K + 1, by linarith, ?_⟩
  intro R hR
  obtain ⟨R', n, hR'I, hfree, hsep⟩ :=
    exists_radius_sep hg hg0 (le_trans (by norm_num : (0 : ℝ) ≤ 1) hR)
  refine ⟨R', hR'I, hfree, ?_⟩
  intro z hz
  obtain ⟨u, huA, hu0, heq⟩ :=
    extract_on_closedBall hg hg0 (S := R + 2) (by linarith)
  -- g = P • u en el disco (identidad: coinciden en codiscreto ⇒ en el círculo).
  -- |P z| ≥ δ^N, δ = 1/(2(n+1)), N = O(R^{2+ε}) por Jensen (mejorable a 2r).
  -- min |u| por Borel del log holomorfo. No lake-checked.
  have _ := hN (R + 1) (by linarith)
  have _ := hsep
  have _ := hz
  have _ := huA
  have _ := hu0
  have _ := heq
  have _ := hfree z hz
  sorry

theorem order_atMostOne_of_quotient
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) (hh : Differentiable ℂ h)
    (hf_ord : OrderAtMostOne f) (hg_ord : OrderAtMostOne g)
    (hne : ∀ z, h z ≠ 0) (hg0 : ¬ ∀ z, g z = 0)
    (hfg : ∀ z, f z = h z * g z) :
    OrderAtMostOne h := by
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨Af, hAf, hfB⟩ := hf_ord (ε / 2) hε2
  obtain ⟨C, hCpos, hmin⟩ := exists_circle_min_norm hg hg_ord hg0 hε2
  -- Cota uniforme en ‖z‖ ≤ R0; el resto absorbe r^{1+ε/2} en r^{1+ε}.
  let K : ℝ := C + 1
  have hK : 0 < K := by linarith
  let R0 : ℝ := max 2 ((2 * K * (2 : ℝ) ^ (1 + ε / 2)) ^ (2 / ε) + 2)
  have hR0 : 0 ≤ R0 := le_trans (by norm_num : (0 : ℝ) ≤ 2) (le_max_left _ _)
  have hKcomp : IsCompact (closedBall (0 : ℂ) R0) := isCompact_closedBall _ _
  have hneK : (closedBall (0 : ℂ) R0).Nonempty := nonempty_closedBall.mpr hR0
  obtain ⟨zmax, hzmax, hmax⟩ :=
    hKcomp.exists_isMaxOn hneK hh.continuous.norm.continuousOn
  let A1 : ℝ := ‖h zmax‖ + 1
  have hA1 : 0 < A1 := by
    have : 0 ≤ ‖h zmax‖ := norm_nonneg _
    linarith
  let A2 : ℝ := Af * Real.exp (C + K * (2 : ℝ) ^ (1 + ε / 2) * 2)
  have hA2 : 0 < A2 := by positivity
  let A : ℝ := max A1 A2
  have hA : 0 < A := lt_of_lt_of_le hA1 (le_max_left _ _)
  refine ⟨A, hA, ?_⟩
  intro z
  by_cases hzR : ‖z‖ ≤ R0
  · have hzmem : z ∈ closedBall (0 : ℂ) R0 := mem_closedBall.2 hzR
    have : ‖h z‖ ≤ ‖h zmax‖ := hmax hzmem
    have : ‖h z‖ ≤ A1 := by linarith
    have hexp : 1 ≤ Real.exp (‖z‖ ^ (1 + ε)) :=
      Real.one_le_exp (Real.rpow_nonneg (norm_nonneg z) _)
    have : A1 ≤ A * Real.exp (‖z‖ ^ (1 + ε)) := by
      have : A1 ≤ A := le_max_left _ _
      nlinarith [Real.exp_pos (‖z‖ ^ (1 + ε))]
    linarith
  · have hgt : R0 < ‖z‖ := lt_of_not_ge hzR
    have hz1 : 1 ≤ ‖z‖ := by
      have : (2 : ℝ) ≤ R0 := le_max_left _ _
      linarith
    obtain ⟨R', hR', hgne, hgmin⟩ := hmin (max ‖z‖ 1) (le_max_right _ _)
    have hRle : max ‖z‖ 1 = ‖z‖ := max_eq_left hz1
    rw [hRle] at hR'
    have hR'pos : 0 < R' :=
      lt_of_lt_of_le (by linarith : (0 : ℝ) < 1) (le_trans hz1 hR'.1)
    have hzle : ‖z‖ ≤ R' := hR'.1
    have hCcircle : ∀ w ∈ sphere (0 : ℂ) R',
        ‖h w‖ ≤ Af * Real.exp (R' ^ (1 + ε / 2) + C * (1 + R' ^ (1 + ε / 2))) := by
      intro w hw
      have hwR : ‖w‖ = R' := mem_sphere_zero_iff_norm.mp hw
      have hgw : g w ≠ 0 := hgne w hwR
      have hdiv : h w = f w / g w := h_eq_div hfg hgw
      have hfW : ‖f w‖ ≤ Af * Real.exp (‖w‖ ^ (1 + ε / 2)) := hfB w
      have hgW : Real.exp (-C * (1 + R' ^ (1 + ε / 2))) ≤ ‖g w‖ := hgmin w hwR
      have hgpos : 0 < ‖g w‖ := norm_pos_iff.mpr hgw
      have : ‖h w‖ = ‖f w‖ / ‖g w‖ := by rw [hdiv, norm_div]
      have hle : ‖f w‖ / ‖g w‖ ≤
          (Af * Real.exp (R' ^ (1 + ε / 2))) /
            Real.exp (-C * (1 + R' ^ (1 + ε / 2))) := by
        have hfW' : ‖f w‖ ≤ Af * Real.exp (R' ^ (1 + ε / 2)) := by
          convert hfW
          rw [hwR]
        exact div_le_div_of_nonneg_left (mul_nonneg hAf.le (Real.exp_pos _).le)
          (Real.exp_pos _) hgW |>.trans' (div_le_div_of_nonneg_right hfW' hgpos.le)
      have hexp : (Af * Real.exp (R' ^ (1 + ε / 2))) /
          Real.exp (-C * (1 + R' ^ (1 + ε / 2))) =
          Af * Real.exp (R' ^ (1 + ε / 2) + C * (1 + R' ^ (1 + ε / 2))) := by
        rw [div_eq_mul_inv, Real.exp_neg, inv_inv, ← Real.exp_add]
        ring_nf
      rw [this]
      exact hle.trans_eq hexp
    have hbound := entire_norm_le_of_sphere hh hR'pos hCcircle hzle
    have hsum : R' ^ (1 + ε / 2) + C * (1 + R' ^ (1 + ε / 2)) =
        C + K * R' ^ (1 + ε / 2) := by
      rw [(by rfl : K = C + 1)]; ring
    rw [hsum] at hbound
    have hR'le : R' ≤ ‖z‖ + 1 := by
      have : R' ≤ ‖z‖ + 1 := hR'.2
      exact this
    have hr2 : R' ≤ ‖z‖ + 2 := by linarith
    have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
    have hr2r : ‖z‖ + 1 ≤ 2 * ‖z‖ := by nlinarith [hz1]
    have hR'2 : R' ≤ 2 * ‖z‖ := le_trans hR'.2 hr2r
    have hpow : R' ^ (1 + ε / 2) ≤ (2 * ‖z‖) ^ (1 + ε / 2) :=
      Real.rpow_le_rpow (le_of_lt hR'pos) hR'2 (by linarith)
    have hmul : (2 * ‖z‖) ^ (1 + ε / 2) =
        (2 : ℝ) ^ (1 + ε / 2) * ‖z‖ ^ (1 + ε / 2) :=
      Real.mul_rpow (by norm_num) hz0
    have hpow2 : ‖z‖ ^ (1 + ε / 2) ≤ ‖z‖ ^ (1 + ε) :=
      Real.rpow_le_rpow_of_exponent_le hz1 (by linarith)
    have hKR : K * R' ^ (1 + ε / 2) ≤ K * (2 : ℝ) ^ (1 + ε / 2) * ‖z‖ ^ (1 + ε) := by
      nlinarith [Real.rpow_nonneg hz0 (1 + ε / 2),
        Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (1 + ε / 2)]
    have hexp : Af * Real.exp (C + K * R' ^ (1 + ε / 2)) ≤
        Af * Real.exp (C + K * (2 : ℝ) ^ (1 + ε / 2) * ‖z‖ ^ (1 + ε)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hAf.le
    have h2 : Af * Real.exp (C + K * (2 : ℝ) ^ (1 + ε / 2) * ‖z‖ ^ (1 + ε)) ≤
        A2 * Real.exp (‖z‖ ^ (1 + ε)) := by
      have : C + K * (2 : ℝ) ^ (1 + ε / 2) * ‖z‖ ^ (1 + ε) ≤
          C + K * (2 : ℝ) ^ (1 + ε / 2) * 2 + ‖z‖ ^ (1 + ε) := by
        nlinarith [Real.rpow_nonneg hz0 (1 + ε)]
      have h1 : Af * Real.exp (C + K * (2 : ℝ) ^ (1 + ε / 2) * ‖z‖ ^ (1 + ε)) ≤
          Af * Real.exp (C + K * (2 : ℝ) ^ (1 + ε / 2) * 2 + ‖z‖ ^ (1 + ε)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr this) hAf.le
      have : Af * Real.exp (C + K * (2 : ℝ) ^ (1 + ε / 2) * 2 + ‖z‖ ^ (1 + ε)) =
          A2 * Real.exp (‖z‖ ^ (1 + ε)) := by
        rw [Real.exp_add]; simp [A2, mul_assoc, mul_left_comm, mul_comm]
      exact h1.trans_eq this
    have : A2 ≤ A := le_max_right _ _
    have : A2 * Real.exp (‖z‖ ^ (1 + ε)) ≤ A * Real.exp (‖z‖ ^ (1 + ε)) :=
      mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
    linarith

end
