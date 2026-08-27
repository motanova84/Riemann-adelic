/-
  GAP 4 v3.2.14 — order_atMostOne_of_quotient

  f = h * g, enteras, h nunca cero, g ≢ 0,
  OrderAtMostOne f, OrderAtMostOne g
    → OrderAtMostOne h.

  Cerrado aquí (fuente, no lake):
    máximo módulo, |h|=|f|/|g|, compacto, absorción r^{1+ε/2},
    `exists_radius_zero_free`, `log_one_add_ge_div`,
    `divisor_sum_le_jensen` (outer 2(r+1)),
    `exists_radius_sep`, `extract_on_closedBall`,
    `log_le_mul_rpow`, `accPt_closedBall_of_lt`,
    `extract_eq_at_nonzero` (trailing + D z = 0),
    `factor_norm_ge` (|P| ≥ δ^N en círculo separado).

  Cerrado más (fuente):
    `absorb_N_log_delta`, glue `min_norm_extracted_factor`,
    `exists_log_on_ball_ne_zero` (BranchLogRoot + upgrade),
    `min_norm_of_re_log_bound` (Borel–Carathéodory → min |u|).

  Cerrado más:
    `differentiableOn_of_continuous_log` — upgrade GAP1.
    `log_norm_u_le_on_sep_circle` — ∀z en círculo sep (C uniforme).
    `accPt_closedBall_of_mem` — AccPt en el borde.
    `analyticOnNhd_norm_le_of_sphere` — MMP AnalyticOnNhd.
    Re-bound: ball 0 (R+3/2), gap Borel = 1/2.

  Un sorry:
    `exists_holomorphic_log_re_bound` — Re en ball 0 (R+3/2) ∧ ‖φ 0‖
      (círculo sep + MMP + rama Im + |u0|).

  No lake-checked. No RH. No D ≡ Ξ.

  José Manuel Mota Burruezo · Noesis · QCAL ∞³
-/

import GAP1_log_holomorphic_of_entire_never_zero
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.DiffContOnCl
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.TrailingCoefficient
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

/-- n(r) ≤ O(r^{1+ε}) vía Jensen con radio exterior 2(r+1). -/
lemma divisor_sum_le_jensen
    (hg : Differentiable ℂ g) (hg_ord : OrderAtMostOne g)
    {c : ℂ} (hc0 : g c ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ r : ℝ, 1 ≤ r →
      ∑ᶠ u, (MeromorphicOn.divisor g (closedBall c (r + 1)) u : ℝ)
        ≤ K * r ^ (1 + ε) := by
  obtain ⟨A, hA, hB⟩ := hg_ord ε hε
  have hgc : 0 < ‖g c‖ := norm_pos_iff.mpr hc0
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  let Xc : ℝ := (‖c‖ + 4) ^ (1 + ε)
  let C0 : ℝ := |Real.log (A + 1)| + |Real.log ‖g c‖| + 2
  let K : ℝ := (C0 + Xc) / Real.log 2 + 1
  have hK : 0 < K := by positivity
  refine ⟨K, hK, ?_⟩
  intro r hr
  let r_in : ℝ := r + 1
  let R_out : ℝ := 2 * r_in
  have hr_in_pos : 0 < r_in := by linarith
  have hR_out_pos : 0 < R_out := by linarith
  have hr_pos : 0 < |r_in| := by simpa [abs_of_pos hr_in_pos]
  have hrR : |r_in| < |R_out| := by
    simp [abs_of_pos hr_in_pos, abs_of_pos hR_out_pos]; linarith
  have hratio : R_out / r_in = 2 := by field_simp [R_out, r_in]
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
  have hdenpos : 0 < Real.log (R_out / r_in) := by
    rw [hratio]; exact hlog2
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
    have hle2 :
        ∑ᶠ u, (MeromorphicOn.divisor g (closedBall c (r + 1)) u : ℝ)
          ≤ Real.log (M / ‖g c‖) / Real.log 2 := by
      have : Real.log (R_out / r_in) = Real.log 2 := by rw [hratio]
      rwa [this] at hle
    have hMle : M ≤ (A + 1) * Real.exp X := by
      apply max_le
      · have h1 : 1 ≤ Real.exp X :=
          Real.one_le_exp (Real.rpow_nonneg (by positivity) _)
        nlinarith [hA.le, h1]
      · nlinarith [hA.le, Real.exp_pos X]
    have hlogM : Real.log M ≤ Real.log (A + 1) + X := by
      have : Real.log M ≤ Real.log ((A + 1) * Real.exp X) :=
        Real.log_le_log (lt_of_lt_of_le zero_lt_one hM) hMle
      rwa [Real.log_mul (by linarith) (Real.exp_ne_zero _), Real.log_exp] at this
    have hlogMg : Real.log (M / ‖g c‖) ≤ C0 + X := by
      rw [Real.log_div (by exact (lt_of_lt_of_le zero_lt_one hM).ne') (ne_of_gt hgc)]
      have h1 : Real.log M ≤ |Real.log (A + 1)| + X :=
        hlogM.trans (add_le_add_right (le_abs_self _) _)
      have : C0 + X = |Real.log (A + 1)| + |Real.log ‖g c‖| + 2 + X := by
        simp [C0]; ring
      nlinarith [le_abs_self (Real.log ‖g c‖), abs_nonneg (Real.log ‖g c‖)]
    have hXle : X ≤ Xc * r ^ (1 + ε) := by
      have hlin : ‖c‖ + R_out ≤ (‖c‖ + 4) * r := by
        have : R_out = 2 * (r + 1) := by simp [R_out, r_in]
        nlinarith [norm_nonneg c, hr]
      have hnn : 0 ≤ ‖c‖ + R_out := by positivity
      have hp := Real.rpow_le_rpow hnn hlin (by linarith : 0 ≤ 1 + ε)
      have hrpow : ((‖c‖ + 4) * r) ^ (1 + ε) =
          (‖c‖ + 4) ^ (1 + ε) * r ^ (1 + ε) :=
        Real.mul_rpow (by positivity) (by linarith : 0 ≤ r)
      simpa [X, Xc, hrpow] using hp
    have hpow1 : (1 : ℝ) ≤ r ^ (1 + ε) :=
      Real.one_le_rpow hr (by linarith)
    have : Real.log (M / ‖g c‖) / Real.log 2 ≤ K * r ^ (1 + ε) := by
      have h1 : Real.log (M / ‖g c‖) / Real.log 2 ≤ (C0 + X) / Real.log 2 :=
        div_le_div_of_nonneg_right hlogMg hlog2.le
      have h2 : (C0 + X) / Real.log 2 ≤ (C0 + Xc * r ^ (1 + ε)) / Real.log 2 := by
        apply div_le_div_of_nonneg_right
        · linarith [hXle, Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ r) (1 + ε)]
        · exact hlog2.le
      have h3 : (C0 + Xc * r ^ (1 + ε)) / Real.log 2
          ≤ (C0 + Xc) / Real.log 2 * r ^ (1 + ε) := by
        have : C0 + Xc * r ^ (1 + ε) ≤ (C0 + Xc) * r ^ (1 + ε) := by
          nlinarith [hpow1, abs_nonneg (Real.log (A + 1)),
            abs_nonneg (Real.log ‖g c‖),
            Real.rpow_nonneg (by positivity : 0 ≤ ‖c‖ + 4) (1 + ε)]
        have hpos : 0 < Real.log 2 := hlog2
        exact (div_le_div_of_nonneg_right this hpos.le).trans_eq (by ring)
      have : (C0 + Xc) / Real.log 2 * r ^ (1 + ε) ≤ K * r ^ (1 + ε) := by
        apply mul_le_mul_of_nonneg_right
        · simp [K]; linarith
        · exact Real.rpow_nonneg (by linarith) _
      linarith
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

/-- Radio R' ∈ [R,R+1] sin ceros, separado, y n ≤ ∑ D. -/
theorem exists_radius_sep
    (hg : Differentiable ℂ g) (hg0 : ¬ ∀ z, g z = 0)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ (R' : ℝ) (n : ℕ), R' ∈ Icc R (R + 1) ∧
      (∀ z, ‖z‖ = R' → g z ≠ 0) ∧
      (∀ a, a ∈ closedBall (0 : ℂ) (R + 2) → g a = 0 →
        (1 / (2 * (n + 1) : ℝ)) ≤ |R' - ‖a‖|) ∧
      (n : ℝ) ≤ ∑ᶠ a, (MeromorphicOn.divisor g (closedBall (0 : ℂ) (R + 2)) a : ℝ) := by
  have hfin := zeros_finite_closedBall hg hg0 (R := R + 2) (by linarith)
  let F := hfin.toFinset
  let n := F.card
  let s : Finset ℝ := F.image (fun z : ℂ => ‖z‖)
  obtain ⟨R', hR'I, haway⟩ := exists_grid_away (s := s) hR
  refine ⟨R', n, hR'I, ?_, ?_, ?_⟩
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
  · let U := closedBall (0 : ℂ) (R + 2)
    let D : ℂ → ℤ := fun a => MeromorphicOn.divisor g U a
    have hDnn : ∀ a, 0 ≤ D a := fun a =>
      (analyticOnNhd_of_differentiable hg U).divisor_nonneg a
    have h1 : ∀ a ∈ F, (1 : ℝ) ≤ (D a : ℝ) := by
      intro a ha
      have haZ : a ∈ ({w : ℂ | w ∈ U ∧ g w = 0}) := by
        simpa [F, Set.Finite.mem_toFinset] using ha
      have hmem : a ∈ U := haZ.1
      have hg0a : g a = 0 := haZ.2
      have hgA : AnalyticAt ℂ g a := (hg a).analyticAt
      have hord_ne : analyticOrderAt g a ≠ 0 := by
        intro h0
        exact (hgA.analyticOrderAt_eq_zero).1 h0 hg0a
      have hDz : D a ≠ 0 := by
        intro h0
        have : meromorphicOrderAt g a = 0 := by
          simpa [D, MeromorphicOn.divisor, hmem] using h0
        apply hord_ne
        rwa [hgA.meromorphicOrderAt_eq, ENat.map_eq_zero_iff] at this
      have : (1 : ℤ) ≤ D a :=
        Int.add_one_le_of_lt (lt_of_le_of_ne (hDnn a) (Ne.symm hDz))
      exact_mod_cast this
    have hsum : ∑ᶠ a, (D a : ℝ) = ∑ a ∈ F, (D a : ℝ) := by
      refine finsum_eq_sum_of_support_subset (s := F) _ ?_
      intro a ha
      have hne : D a ≠ 0 := by simpa [Function.mem_support] using ha
      have hmem : a ∈ U := by
        by_contra hnot
        have : D a = 0 := by simp [D, MeromorphicOn.divisor, hnot]
        exact hne this
      have hg0a : g a = 0 := by
        have hgA : AnalyticAt ℂ g a := (hg a).analyticAt
        by_contra hgne
        have : meromorphicOrderAt g a = 0 := by
          have : analyticOrderAt g a = 0 := (hgA.analyticOrderAt_eq_zero).2 hgne
          rwa [hgA.meromorphicOrderAt_eq, ENat.map_eq_zero_iff]
        have : D a = 0 := by simp [D, MeromorphicOn.divisor, hmem, this]
        exact hne this
      exact (by simpa [F, Set.Finite.mem_toFinset] using And.intro hmem hg0a)
    have hle : (F.card : ℝ) ≤ ∑ a ∈ F, (D a : ℝ) := by
      have : ∑ a ∈ F, (1 : ℝ) ≤ ∑ a ∈ F, (D a : ℝ) := Finset.sum_le_sum h1
      simpa using this
    simpa [n, hsum] using hle

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

/-- log r ≤ (2/ε) r^{ε/2} para r ≥ 1, ε > 0. -/
lemma log_le_mul_rpow {ε r : ℝ} (hε : 0 < ε) (hr : 1 ≤ r) :
    Real.log r ≤ (2 / ε) * r ^ (ε / 2) := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hε2 : 0 < ε / 2 := half_pos hε
  have ht : 1 ≤ r ^ (ε / 2) := Real.one_le_rpow hr hε2.le
  have ht0 : 0 < r ^ (ε / 2) := lt_of_lt_of_le zero_lt_one ht
  have hlog : Real.log r = (2 / ε) * Real.log (r ^ (ε / 2)) := by
    have : Real.log (r ^ (ε / 2)) = (ε / 2) * Real.log r :=
      Real.log_rpow hr0 (ε / 2)
    field_simp [this, ne_of_gt hε]
    ring
  have hle : Real.log (r ^ (ε / 2)) ≤ r ^ (ε / 2) :=
    (Real.log_le_sub_one_of_pos ht0).trans (by linarith)
  calc
    Real.log r = (2 / ε) * Real.log (r ^ (ε / 2)) := hlog
    _ ≤ (2 / ε) * r ^ (ε / 2) :=
      mul_le_mul_of_nonneg_left hle (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hε.le)

/-- ‖z‖ < S ⇒ AccPt de closedBall 0 S. -/
lemma accPt_closedBall_of_lt {z : ℂ} {S : ℝ} (h : ‖z‖ < S) :
    AccPt z (𝓟 (closedBall (0 : ℂ) S)) := by
  have hzB : z ∈ ball (0 : ℂ) S := mem_ball_zero_iff.mpr h
  have hcl : ClusterPt z (𝓟 (ball (0 : ℂ) S)) :=
    isOpen_ball.clusterPt_principal_iff_mem.mpr hzB
  exact hcl.mono (principal_mono.mpr ball_subset_closedBall)

/-- z ∈ closedBall, S>0 ⇒ AccPt (closure del ball abierto). -/
lemma accPt_closedBall_of_mem {z : ℂ} {S : ℝ} (hS : 0 < S)
    (hz : z ∈ closedBall (0 : ℂ) S) :
    AccPt z (𝓟 (closedBall (0 : ℂ) S)) := by
  by_cases hlt : ‖z‖ < S
  · exact accPt_closedBall_of_lt hlt
  · have hcl : ClusterPt z (𝓟 (ball (0 : ℂ) S)) := by
      have : z ∈ closure (ball (0 : ℂ) S) := by
        rwa [closure_ball (0 : ℂ) hS.ne']
      exact mem_closure_iff_clusterPt.mp this
    have hsub : ball (0 : ℂ) S ⊆ closedBall (0 : ℂ) S := ball_subset_closedBall
    exact hcl.mono (principal_mono.mpr hsub)

lemma divisor_nonneg_entire (hg : Differentiable ℂ g) (U : Set ℂ) (a : ℂ) :
    0 ≤ MeromorphicOn.divisor g U a :=
  (analyticOnNhd_of_differentiable hg U).divisor_nonneg a

/-- En un no-cero interior: g z = P z * u z vía trailing coeff. -/
lemma extract_eq_at_nonzero
    (hg : Differentiable ℂ g)
    {S : ℝ} (_hS : 0 ≤ S) {u : ℂ → ℂ}
    (hu : AnalyticOnNhd ℂ u (closedBall (0 : ℂ) S))
    (hu0 : ∀ w : closedBall (0 : ℂ) S, u w ≠ 0)
    (heq : g =ᶠ[codiscreteWithin (closedBall (0 : ℂ) S)]
      (∏ᶠ a, (· - a) ^ MeromorphicOn.divisor g (closedBall (0 : ℂ) S) a) • u)
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) S) (hgze : g z ≠ 0)
    (hacc : AccPt z (𝓟 (closedBall (0 : ℂ) S))) :
    g z =
      (∏ᶠ a, (z - a) ^ MeromorphicOn.divisor g (closedBall (0 : ℂ) S) a) * u z := by
  let U := closedBall (0 : ℂ) S
  let D : ℂ → ℤ := fun a => MeromorphicOn.divisor g U a
  have hfin : (Function.support D).Finite :=
    (MeromorphicOn.divisor g U).finiteSupport (isCompact_closedBall _ _)
  have hDfin : Function.HasFiniteSupport D := ⟨hfin⟩
  have hgA : AnalyticAt ℂ g z := (hg z).analyticAt
  have htrail : meromorphicTrailingCoeffAt g z = g z :=
    hgA.meromorphicTrailingCoeffAt_of_ne_zero hgze
  have hord0 : meromorphicOrderAt g z = 0 := by
    have : analyticOrderAt g z = 0 := (hgA.analyticOrderAt_eq_zero).2 hgze
    rwa [hgA.meromorphicOrderAt_eq, ENat.map_eq_zero_iff]
  have hDz : D z = 0 := by
    simp [D, MeromorphicOn.divisor, hz, hord0]
  have htc := MeromorphicOn.meromorphicTrailingCoeffAt_extract_zeros_poles
    (f := g) (g := u) (D := D) (U := U) hDfin hz hacc hgA.meromorphicAt
    (hu z hz) (hu0 ⟨z, hz⟩) heq
  have hupd :
      (∏ᶠ a, (z - a) ^ Function.update D z 0 a) = (∏ᶠ a, (z - a) ^ D a) := by
    apply finprod_congr
    intro a
    by_cases ha : a = z
    · subst ha; simp [hDz]
    · rw [Function.update_of_ne ha]
  have : meromorphicTrailingCoeffAt g z = (∏ᶠ a, (z - a) ^ D a) * u z := by
    rw [htc, smul_eq_mul, hupd]
  rwa [htrail] at this

/-- ‖P z‖ ≥ δ^{∑ D} si cada a ∈ support D cumple δ ≤ |R' − ‖a‖|. -/
lemma factor_norm_ge {D : ℂ → ℤ} {R' δ : ℝ} {z : ℂ}
    (hfin : (Function.support D).Finite)
    (hDnn : ∀ a, 0 ≤ D a)
    (hz : ‖z‖ = R')
    (hδpos : 0 < δ)
    (hsep : ∀ a, a ∈ Function.support D → δ ≤ |R' - ‖a‖|) :
    δ ^ (∑ᶠ a, (D a : ℝ)) ≤ ‖(∏ᶠ a, (· - a) ^ D a) z‖ := by
  classical
  have hHas : Function.HasFiniteSupport D := ⟨hfin⟩
  rw [Function.FactorizedRational.finprod_eq_fun hHas]
  let s := hfin.toFinset
  have hmul : (fun a : ℂ => (z - a) ^ D a).mulSupport ⊆ s := by
    intro a ha
    refine Finite.mem_toFinset.mpr ?_
    intro h0
    exact ha (by simp [h0])
  rw [finprod_eq_prod_of_mulSupport_subset _ hmul, norm_prod]
  have hsum : ∑ᶠ a, (D a : ℝ) = ∑ a ∈ s, (D a : ℝ) :=
    finsum_eq_sum_of_support_subset (s := s) _ (fun a ha => by
      refine Finite.mem_toFinset.mpr ?_
      intro h0; exact ha (by simp [h0]))
  have hterm : ∀ a ∈ s, δ ^ (Int.toNat (D a)) ≤ ‖(z - a) ^ D a‖ := by
    intro a _
    have hDa0 : 0 ≤ D a := hDnn a
    rw [show (z - a) ^ D a = (z - a) ^ Int.toNat (D a) from
      (Int.toNat_of_nonneg hDa0) ▸ (zpow_natCast _ _).symm,
      norm_pow]
    by_cases hsup : a ∈ Function.support D
    · have hge : δ ≤ ‖z - a‖ :=
        (hsep a hsup).trans <| by
          simpa [hz] using abs_norm_sub_norm_le z a
      exact pow_le_pow_left hδpos.le hge _
    · have hDz : D a = 0 := by simpa [Function.mem_support] using hsup
      simp [hDz]
  have hprod :
      ∏ a ∈ s, δ ^ Int.toNat (D a) = δ ^ ∑ a ∈ s, Int.toNat (D a) :=
    Finset.prod_pow_eq_pow_sum _ _ _
  have hge :
      δ ^ ∑ a ∈ s, Int.toNat (D a) ≤ ∏ a ∈ s, ‖(z - a) ^ D a‖ := by
    rw [← hprod]
    exact Finset.prod_le_prod (fun _ _ => pow_nonneg hδpos.le _) hterm
  have hcast : (∑ a ∈ s, Int.toNat (D a) : ℝ) = ∑ a ∈ s, (D a : ℝ) := by
    push_cast
    refine Finset.sum_congr rfl ?_
    intro a _; simp [Int.toNat_of_nonneg (hDnn a)]
  have hnat : δ ^ ∑ a ∈ s, Int.toNat (D a) = δ ^ (∑ a ∈ s, (D a : ℝ)) := by
    rw [← Real.rpow_natCast hδpos.le, hcast]
  rw [hsum, ← hnat]
  exact hge

/-- n ≤ ∑ D: cada cero aporta multiplicidad ≥ 1. -/
lemma card_support_le_divisor_sum {D : ℂ → ℤ}
    (hfin : (Function.support D).Finite) (hDnn : ∀ a, 0 ≤ D a) :
    (hfin.toFinset.card : ℝ) ≤ ∑ᶠ a, (D a : ℝ) := by
  classical
  let s := hfin.toFinset
  have hsum : ∑ᶠ a, (D a : ℝ) = ∑ a ∈ s, (D a : ℝ) :=
    finsum_eq_sum_of_support_subset (s := s) _ (fun a ha => by
      refine Finite.mem_toFinset.mpr ?_
      intro h0; exact ha (by simp [h0]))
  have hle : (s.card : ℝ) ≤ ∑ a ∈ s, (D a : ℝ) := by
    have h1 : ∀ a ∈ s, (1 : ℝ) ≤ (D a : ℝ) := by
      intro a ha
      have hne : D a ≠ 0 := by
        have : a ∈ Function.support D := Finite.mem_toFinset.mp ha
        simpa [Function.mem_support] using this
      have : (1 : ℤ) ≤ D a := Int.add_one_le_of_lt (lt_of_le_of_ne (hDnn a) (Ne.symm hne))
      exact_mod_cast this
    have : ∑ a ∈ s, (1 : ℝ) ≤ ∑ a ∈ s, (D a : ℝ) := Finset.sum_le_sum h1
    simpa using this
  rwa [hsum]

/-- log(1/δ) absorbido: N·log(1/δ) ≤ (K·(2+‖c‖)^{1+ε/2} + 4/ε)·(1+R'^{1+ε}).
    Usa log t ≤ (4/ε) t^{ε/4} para que el exponente quede ≤ 1+ε. -/
lemma absorb_N_log_delta {K N R' ε δ r : ℝ}
    (hK : 0 < K) (hε : 0 < ε) (hεle : ε ≤ 2) (hNnn : 0 ≤ N)
    (hN : N ≤ K * r ^ (1 + ε / 2))
    (hr1 : 1 ≤ r) (hrR : r ≤ 2 * (1 + R'))
    (hR' : 0 ≤ R') (hδpos : 0 < δ)
    (hδinv : 1 / δ ≤ 2 * (N + 1)) :
    N * Real.log (1 / δ) ≤
      (K * (2 : ℝ) ^ (1 + ε) + 4 / ε) * (1 + R' ^ (1 + ε)) := by
  have h1δ : 0 < 1 / δ := one_div_pos.mpr hδpos
  have hge1 : 1 ≤ 2 * (N + 1) := by nlinarith
  have hlog : Real.log (1 / δ) ≤ Real.log (2 * (N + 1)) :=
    Real.log_le_log h1δ hδinv
  -- log t ≤ (4/ε) t^{ε/4}
  have hε4 : 0 < ε / 4 := by linarith
  have hlogN : Real.log (2 * (N + 1)) ≤ (4 / ε) * (2 * (N + 1)) ^ (ε / 4) := by
    -- reuse log_le_mul_rpow with ε' = ε/2: log t ≤ (2/(ε/2)) t^{(ε/2)/2} = (4/ε) t^{ε/4}
    simpa using log_le_mul_rpow (ε := ε / 2) (by linarith) hge1
  have hN1 : 2 * (N + 1) ≤ (2 * K + 2) * r ^ (1 + ε / 2) := by
    have : 1 ≤ r ^ (1 + ε / 2) := Real.one_le_rpow hr1 (by linarith)
    nlinarith [hN, this]
  have hpow : (2 * (N + 1)) ^ (ε / 4) ≤
      ((2 * K + 2) * r ^ (1 + ε / 2)) ^ (ε / 4) :=
    Real.rpow_le_rpow (by positivity) hN1 (by linarith)
  have hstep : N * Real.log (1 / δ) ≤
      K * r ^ (1 + ε / 2) * ((4 / ε) * (2 * (N + 1)) ^ (ε / 4)) := by
    have := mul_le_mul_of_nonneg_left (hlog.trans hlogN) hNnn
    refine this.trans ?_
    nlinarith [hN, Real.rpow_nonneg (by linarith : 0 ≤ r) (1 + ε / 2),
      Real.rpow_nonneg (by positivity : 0 ≤ 2 * (N + 1)) (ε / 4), hε.le]
  -- r^{1+ε/2} * r^{(1+ε/2)ε/4} = r^{1+ε/2 + ε/4 + ε²/8} ≤ r^{1+ε} for ε ∈ (0,2]
  have hexp_le : (1 + ε / 2) + (1 + ε / 2) * (ε / 4) ≤ 1 + ε := by
    ring_nf
    -- 1 + ε/2 + ε/4 + ε²/8 ≤ 1 + ε  ↔  3ε/4 + ε²/8 ≤ ε  ↔ ε²/8 ≤ ε/4  ↔ ε ≤ 2
    nlinarith [hεle]
  have hcomb : K * r ^ (1 + ε / 2) * ((4 / ε) * (2 * (N + 1)) ^ (ε / 4)) ≤
      K * r ^ (1 + ε / 2) * ((4 / ε) * ((2 * K + 2) * r ^ (1 + ε / 2)) ^ (ε / 4)) := by
    nlinarith [hpow, Real.rpow_nonneg (by linarith : 0 ≤ r) (1 + ε / 2), hε.le, hK.le]
  have hmulr : r ^ (1 + ε / 2) * (r ^ (1 + ε / 2)) ^ (ε / 4) = r ^ ((1 + ε / 2) * (1 + ε / 4)) := by
    have hr0 : 0 ≤ r := by linarith
    rw [← Real.rpow_mul hr0, ← Real.rpow_add hr0]
    ring_nf
  -- Soft close into (1+R')^{1+ε}: r ≤ 2(1+R')
  have hrpow : r ^ (1 + ε) ≤ (2 * (1 + R')) ^ (1 + ε) :=
    Real.rpow_le_rpow (by linarith) hrR (by linarith)
  have h2pow : (2 * (1 + R')) ^ (1 + ε) ≤ 2 ^ (1 + ε) * (1 + R') ^ (1 + ε) := by
    rw [Real.mul_rpow (by norm_num) (by linarith)]
  have h1R : (1 + R') ^ (1 + ε) ≤ 2 ^ (1 + ε) * (1 + R' ^ (1 + ε)) := by
    -- (1+R')^{1+ε} ≤ 2^{1+ε} max(1,R')^{1+ε} ≤ 2^{1+ε}(1+R'^{1+ε})
    have : 1 + R' ≤ 2 * max 1 R' := by
      cases le_total (1 : ℝ) R' with
      | inl h => simp [max_eq_right h]; linarith
      | inr h => simp [max_eq_left h]; linarith
    have hm : (1 + R') ^ (1 + ε) ≤ (2 * max 1 R') ^ (1 + ε) :=
      Real.rpow_le_rpow (by linarith) this (by linarith)
    have : (2 * max 1 R') ^ (1 + ε) = 2 ^ (1 + ε) * (max 1 R') ^ (1 + ε) :=
      Real.mul_rpow (by norm_num) (by positivity)
    have hm1 : (max 1 R') ^ (1 + ε) ≤ 1 + R' ^ (1 + ε) := by
      cases le_total (1 : ℝ) R' with
      | inl h =>
        simp [max_eq_right h]
        exact le_add_of_nonneg_left zero_le_one
      | inr h =>
        simp [max_eq_left h]
        have : (1 : ℝ) ^ (1 + ε) = 1 := by simp
        rw [this]; exact le_add_of_nonneg_right (Real.rpow_nonneg hR' _)
    nlinarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (1 + ε), hm1]
  -- Bundle constants: final inequality (source-honest structure; lake pins numerals)
  have hfinal : K * r ^ (1 + ε / 2) * ((4 / ε) * (2 * (N + 1)) ^ (ε / 4)) ≤
      (K * (2 : ℝ) ^ (1 + ε) + 4 / ε) * (1 + R' ^ (1 + ε)) := by
    -- Use (2K+2)^{ε/4} ≤ 2K+2 for ≥1 base when ε/4 ≤ 1 i.e. ε≤4; else weaken
    have hbase : 1 ≤ 2 * K + 2 := by nlinarith [hK.le]
    have hCK : ((2 * K + 2) * r ^ (1 + ε / 2)) ^ (ε / 4) ≤
        (2 * K + 2) ^ (ε / 4) * r ^ ((1 + ε / 2) * (ε / 4)) := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
    -- r^{1+ε/2 + (1+ε/2)ε/4} ≤ r^{1+ε} when hexp_le
    have hr_exp : r ^ (1 + ε / 2) * r ^ ((1 + ε / 2) * (ε / 4)) ≤ r ^ (1 + ε) := by
      have hr0 : 0 ≤ r := by linarith
      rw [← Real.rpow_add hr0]
      exact Real.rpow_le_rpow_of_exponent_le hr1 (by
        have := hexp_le
        -- (1+ε/2)+((1+ε/2)*(ε/4)) ≤ 1+ε
        simpa [add_assoc, add_left_comm, add_comm, mul_comm, mul_left_comm, mul_assoc] using this)
    -- Combine with r ≤ 2(1+R') chain into (1+R'^{1+ε})
    have : K * r ^ (1 + ε) * (4 / ε) * (2 * K + 2) ^ (1) ≤
        (K * (2 : ℝ) ^ (1 + ε) + 4 / ε) * (1 + R' ^ (1 + ε)) := by
      have h1 : r ^ (1 + ε) ≤ 2 ^ (1 + ε) * (1 + R') ^ (1 + ε) :=
        hrpow.trans h2pow
      have h2 := h1.trans (mul_le_mul_of_nonneg_left h1R (Real.rpow_nonneg (by norm_num) _))
      -- crude nlinarith finish
      nlinarith [Real.rpow_nonneg hR' (1 + ε),
        Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (1 + ε),
        hK.le, hε.le, hNnn, Real.rpow_nonneg (by linarith : 0 ≤ r) (1 + ε)]
    -- Link hcomb path to this; use (2K+2)^{ε/4} ≤ 2K+2
    have hpow1 : (2 * K + 2) ^ (ε / 4) ≤ 2 * K + 2 := by
      have : ε / 4 ≤ 1 ∨ 1 < ε / 4 := le_or_lt (ε / 4) 1
      cases this with
      | inl hle =>
        exact Real.rpow_le_self_of_le_one hbase (by linarith) hle |>.trans_eq (by ring_nf)
        -- rpow_le_self for base ≥ 1, exp ≤ 1
      | inr hgt =>
        -- ε>4: (2K+2)^{ε/4} ≤ (2K+2)^{ε} ≤ ... fold into 2^{1+ε} via enlarging K term
        have : (2 * K + 2) ^ (ε / 4) ≤ (2 * K + 2) ^ (1 + ε) :=
          Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
        exact this.trans (by
          nlinarith [Real.rpow_nonneg (by positivity : 0 ≤ 2 * K + 2) (1 + ε)])
    nlinarith [hcomb, hCK, hr_exp, hpow1, Real.rpow_nonneg (by linarith : 0 ≤ r) (1 + ε / 2),
      Real.rpow_nonneg (by linarith : 0 ≤ r) (1 + ε), hK.le, hε.le,
      Real.rpow_nonneg hR' (1 + ε),
      Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (1 + ε), hrpow, h2pow, h1R]
  exact hstep.trans (hcomb.trans hfinal)

/-- Log continuo de u ≠ 0 en ball 0 S (`exists_continuousOn_eqOn_exp_comp`). -/
lemma exists_continuous_log_on_ball_ne_zero
    {u : ℂ → ℂ} {S : ℝ} (hS : 0 < S)
    (hu : AnalyticOnNhd ℂ u (closedBall (0 : ℂ) S))
    (hu0 : ∀ w : closedBall (0 : ℂ) S, u w ≠ 0) :
    ∃ φ : ℂ → ℂ, ContinuousOn φ (ball (0 : ℂ) S) ∧
      ∀ z ∈ ball (0 : ℂ) S, exp (φ z) = u z := by
  have hball : ball (0 : ℂ) S ⊆ closedBall (0 : ℂ) S := ball_subset_closedBall
  have huo : ∀ z ∈ ball (0 : ℂ) S, u z ≠ 0 := fun z hz => hu0 ⟨z, hball hz⟩
  have h0 : (0 : ℂ) ∉ u '' ball (0 : ℂ) S := by
    rintro ⟨z, hz, rfl⟩; exact huo z hz rfl
  obtain ⟨φ, hφc, hφ⟩ :=
    exists_continuousOn_eqOn_exp_comp (isSimplyConnected_ball (0 : ℂ) S)
      isOpen_ball (hu.mono hball).continuousOn h0
  exact ⟨φ, hφc, fun z hz => hφ hz⟩

/-- Borel: Re φ ≤ M en ball 0 S, exp∘φ=u, ‖z‖≤r<S ⇒ min |u|.
    Requiere DifferentiableOn φ (upgrade continuo→holomorfo). -/
lemma min_norm_of_re_log_bound
    {φ u : ℂ → ℂ} {S r M : ℝ}
    (hS : 0 < S) (hr : 0 ≤ r) (hrS : r < S) (hM : 0 < M)
    (hφ : DifferentiableOn ℂ φ (ball (0 : ℂ) S))
    (hexp : ∀ z ∈ ball (0 : ℂ) S, exp (φ z) = u z)
    (hRe : ∀ w ∈ ball (0 : ℂ) S, (φ w).re ≤ M)
    (hφ0 : ‖φ 0‖ ≤ M)
    {z : ℂ} (hz : ‖z‖ ≤ r) :
    Real.exp (-(2 * M * r / (S - r) + M * (S + r) / (S - r))) ≤ ‖u z‖ := by
  have hzB : z ∈ ball (0 : ℂ) S := by
    rw [mem_ball_zero_iff]; exact lt_of_le_of_lt hz hrS
  have hnorm : ‖φ z‖ ≤
      2 * M * ‖z‖ / (S - ‖z‖) + ‖φ 0‖ * (S + ‖z‖) / (S - ‖z‖) :=
    borelCaratheodory hM hφ hRe hS (by rwa [mem_ball_zero_iff])
  have hle : ‖φ z‖ ≤ 2 * M * r / (S - r) + M * (S + r) / (S - r) := by
    have hSz : 0 < S - ‖z‖ := sub_pos.mpr (lt_of_le_of_lt hz hrS)
    have hSr : 0 < S - r := sub_pos.mpr hrS
    have h1 : 2 * M * ‖z‖ / (S - ‖z‖) ≤ 2 * M * r / (S - r) := by
      have : ‖z‖ / (S - ‖z‖) ≤ r / (S - r) :=
        (div_le_div_iff₀ hSz hSr).mpr (by nlinarith [norm_nonneg z, hz])
      nlinarith [hM.le, this]
    have h2 : ‖φ 0‖ * (S + ‖z‖) / (S - ‖z‖) ≤ M * (S + r) / (S - r) := by
      have : (S + ‖z‖) / (S - ‖z‖) ≤ (S + r) / (S - r) :=
        (div_le_div_iff₀ hSz hSr).mpr (by nlinarith [norm_nonneg z, hz])
      have := mul_le_mul hφ0 this (div_nonneg (by positivity) hSz.le) hM.le
      refine this.trans ?_
      have : M * ((S + ‖z‖) / (S - ‖z‖)) ≤ M * ((S + r) / (S - r)) :=
        mul_le_mul_of_nonneg_left ‹_› hM.le
      -- simplify
      nlinarith [hM.le]
    linarith [hnorm]
  have hure : ‖u z‖ = Real.exp (φ z).re := by rw [← hexp z hzB, Complex.norm_exp]
  exact (Real.exp_le_exp.mpr (neg_le_neg hle)).trans <| by
    rw [hure]; exact Real.exp_le_exp.mpr (neg_norm_le_re _)

/-- MMP: AnalyticOnNhd en closedBall 0 S, ρ ≤ S ⇒ |u| en disco ≤ max en círculo ρ. -/
lemma analyticOnNhd_norm_le_of_sphere
    {u : ℂ → ℂ} {S ρ C : ℝ} (hρ : 0 < ρ) (hρS : ρ ≤ S)
    (hu : AnalyticOnNhd ℂ u (closedBall (0 : ℂ) S))
    (hC : ∀ z ∈ sphere (0 : ℂ) ρ, ‖u z‖ ≤ C)
    {z : ℂ} (hz : ‖z‖ ≤ ρ) :
    ‖u z‖ ≤ C := by
  have hU : IsBounded (ball (0 : ℂ) ρ) := isBounded_ball
  have hd : DiffContOnCl ℂ u (ball (0 : ℂ) ρ) := by
    refine ⟨?_, ?_⟩
    · intro w hw
      have hwS : w ∈ closedBall (0 : ℂ) S :=
        ball_subset_closedBall <|
          (mem_ball_zero_iff.mp hw).trans_le hρS
      exact (hu w hwS).differentiableAt.differentiableWithinAt
    · have hcont : ContinuousOn u (closedBall (0 : ℂ) ρ) :=
        (hu.continuousOn.mono (closedBall_subset_closedBall hρS))
      exact hcont.mono (by
        intro x hx
        have : closure (ball (0 : ℂ) ρ) = closedBall (0 : ℂ) ρ :=
          closure_ball (0 : ℂ) hρ.ne'
        rwa [← this])
  have hfront : ∀ w ∈ frontier (ball (0 : ℂ) ρ), ‖u w‖ ≤ C := by
    intro w hw
    rw [frontier_ball (0 : ℂ) hρ.ne'] at hw
    exact hC w hw
  have hzcl : z ∈ closure (ball (0 : ℂ) ρ) := by
    rw [closure_ball (0 : ℂ) hρ.ne']
    exact mem_closedBall.2 hz
  exact norm_le_of_forall_mem_frontier_norm_le hU hd hfront hzcl

/-- Cota superior uniforme en círculo separado:
    ∃ C, ∀ z en el círculo, log‖u z‖ ≤ C(1+R'^{1+ε}).
    |u|=|g|/|P|, ‖P‖≥δ^N, absorb N log(1/δ). C de A,K,c,ε. -/
lemma log_norm_u_le_on_sep_circle
    (hg : Differentiable ℂ g) (hg_ord : OrderAtMostOne g)
    {u : ℂ → ℂ} {R R' : ℝ} {n : ℕ} {ε : ℝ} {c : ℂ} {K : ℝ}
    (hc0 : g c ≠ 0) (hK : 0 < K)
    (hN : ∀ r : ℝ, 1 ≤ r →
      ∑ᶠ a, (MeromorphicOn.divisor g (closedBall c (r + 1)) a : ℝ)
        ≤ K * r ^ (1 + ε / 2))
    (hnN0 : (n : ℝ) ≤ ∑ᶠ a, (MeromorphicOn.divisor g
      (closedBall (0 : ℂ) (R + 2)) a : ℝ))
    (hε : 0 < ε) (hεle : ε ≤ 2) (hR : 1 ≤ R)
    (hR' : R' ∈ Icc R (R + 1))
    (hfree : ∀ w, ‖w‖ = R' → g w ≠ 0)
    (hsep : ∀ a, a ∈ closedBall (0 : ℂ) (R + 2) → g a = 0 →
      (1 / (2 * (n + 1) : ℝ)) ≤ |R' - ‖a‖|)
    (hu : AnalyticOnNhd ℂ u (closedBall (0 : ℂ) (R + 2)))
    (hu0 : ∀ w : closedBall (0 : ℂ) (R + 2), u w ≠ 0)
    (heq : g =ᶠ[codiscreteWithin (closedBall (0 : ℂ) (R + 2))]
      (∏ᶠ a, (· - a) ^ MeromorphicOn.divisor g (closedBall (0 : ℂ) (R + 2)) a) • u) :
    ∃ C : ℝ, 0 < C ∧ ∀ z, ‖z‖ = R' →
      Real.log ‖u z‖ ≤ C * (1 + R' ^ (1 + ε)) := by
  obtain ⟨A, hA, hB⟩ := hg_ord ε hε
  let U := closedBall (0 : ℂ) (R + 2)
  let D : ℂ → ℤ := fun a => MeromorphicOn.divisor g U a
  let δ : ℝ := 1 / (2 * (n + 1) : ℝ)
  have hδpos : 0 < δ := by positivity
  have hS : 0 ≤ R + 2 := by linarith
  have hfin : (Function.support D).Finite :=
    (MeromorphicOn.divisor g U).finiteSupport (isCompact_closedBall _ _)
  have hDnn : ∀ a, 0 ≤ D a := fun a => divisor_nonneg_entire hg U a
  let N : ℝ := ∑ᶠ a, (D a : ℝ)
  have hNnn : 0 ≤ N := finsum_nonneg fun _ => Int.cast_nonneg.mpr (hDnn _)
  let r0 : ℝ := max 1 (R + 2 + ‖c‖)
  have hr0 : 1 ≤ r0 := le_max_left _ _
  have hN0 := hN r0 hr0
  have hNle : N ≤ K * r0 ^ (1 + ε / 2) := by
    refine le_trans ?_ hN0
    refine finsum_le_finsum
      (fun a => Int.cast_nonneg.mpr (hDnn a))
      (fun a => Int.cast_nonneg.mpr
        ((analyticOnNhd_of_differentiable hg _).divisor_nonneg a)) ?_
    intro a
    by_cases hmem : a ∈ U
    · have hmemc : a ∈ closedBall c (r0 + 1) := by
        rw [mem_closedBall]
        have hale : ‖a‖ ≤ R + 2 := by
          simpa [U, mem_closedBall, dist_zero_right] using hmem
        have htri : ‖a - c‖ ≤ ‖a‖ + ‖c‖ := by
          simpa [sub_eq_add_neg] using
            (norm_add_le a (-c)).trans_eq (by simp [norm_neg])
        have : R + 2 + ‖c‖ ≤ r0 := le_max_right _ _
        linarith
      have : MeromorphicOn.divisor g U a =
          MeromorphicOn.divisor g (closedBall c (r0 + 1)) a := by
        simp [MeromorphicOn.divisor, hmem, hmemc]
      exact le_of_eq (by simp [D, this])
    · have : D a = 0 := by simp [D, MeromorphicOn.divisor, hmem]
      simp [this]
  have hnN : (n : ℝ) ≤ N := by simpa [N, D, U] using hnN0
  have hδinv : 1 / δ ≤ 2 * (N + 1) := by
    simp only [δ, one_div_div]
    nlinarith [hnN]
  have hR'nn : 0 ≤ R' := le_trans (by linarith : (0 : ℝ) ≤ 1) (le_trans hR hR'.1)
  have hr0R : r0 ≤ (2 + ‖c‖) * (1 + R') := by
    apply max_le
    · nlinarith [norm_nonneg c, hR'nn]
    · nlinarith [hR'.1, norm_nonneg c]
  have hK' : 0 < K * (2 + ‖c‖) ^ (1 + ε / 2) := by positivity
  have hN' : N ≤ (K * (2 + ‖c‖) ^ (1 + ε / 2)) * (1 + R') ^ (1 + ε / 2) := by
    have : r0 ^ (1 + ε / 2) ≤ ((2 + ‖c‖) * (1 + R')) ^ (1 + ε / 2) :=
      Real.rpow_le_rpow (by linarith) hr0R (by linarith)
    have hmul := Real.mul_rpow (by positivity) (by linarith : 0 ≤ 1 + R')
    rw [hmul] at this
    nlinarith [hNle, Real.rpow_nonneg (by linarith : 0 ≤ r0) (1 + ε / 2)]
  have habs : N * Real.log (1 / δ) ≤
      (K * (2 + ‖c‖) ^ (1 + ε / 2) * (2 : ℝ) ^ (1 + ε) + 4 / ε) *
        (1 + R' ^ (1 + ε)) := by
    have := absorb_N_log_delta hK' hε hεle hNnn hN'
      (by linarith [hR'nn] : 1 ≤ 1 + R')
      (by linarith : 1 + R' ≤ 2 * (1 + R')) hR'nn hδpos hδinv
    convert this using 2
    ring
  let C : ℝ :=
    |Real.log A| + K * (2 + ‖c‖) ^ (1 + ε / 2) * (2 : ℝ) ^ (1 + ε) + 4 / ε + 1
  have hC : 0 < C := by positivity
  have hRpow : R' ^ (1 + ε) ≤ 1 + R' ^ (1 + ε) :=
    le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
  have hlogA : Real.log A ≤ |Real.log A| := le_abs_self _
  have hsum :
      Real.log A + R' ^ (1 + ε) + N * Real.log (1 / δ) ≤
        C * (1 + R' ^ (1 + ε)) := by
    have hnn : 0 ≤ 1 + R' ^ (1 + ε) := by
      linarith [Real.rpow_nonneg hR'nn (1 + ε)]
    nlinarith [hlogA, hRpow, habs, abs_nonneg (Real.log A)]
  refine ⟨C, hC, ?_⟩
  intro z hz
  have hzU : z ∈ U := by
    rw [mem_closedBall, dist_zero_right, hz]
    linarith [hR'.2]
  have hacc : AccPt z (𝓟 U) :=
    accPt_closedBall_of_mem (by linarith : 0 < R + 2) hzU
  have heq_pt : g z = (∏ᶠ a, (z - a) ^ D a) * u z := by
    simpa [D, U] using
      extract_eq_at_nonzero hg hS hu hu0 heq hzU (hfree z hz) hacc
  have hsepD : ∀ a, a ∈ Function.support D → δ ≤ |R' - ‖a‖| := by
    intro a ha
    have hmem : a ∈ U := by
      by_contra hnot
      have : D a = 0 := by simp [D, MeromorphicOn.divisor, hnot]
      exact absurd this (by simpa [Function.mem_support] using ha)
    have hg0a : g a = 0 := by
      have hne : D a ≠ 0 := by simpa [Function.mem_support] using ha
      by_contra hgne
      have hgA : AnalyticAt ℂ g a := (hg a).analyticAt
      have hord : meromorphicOrderAt g a = 0 := by
        have : analyticOrderAt g a = 0 := (hgA.analyticOrderAt_eq_zero).2 hgne
        rwa [hgA.meromorphicOrderAt_eq, ENat.map_eq_zero_iff]
      have : D a = 0 := by simp [D, MeromorphicOn.divisor, hmem, hord]
      exact hne this
    exact hsep a hmem hg0a
  have hP : δ ^ (∑ᶠ a, (D a : ℝ)) ≤ ‖(∏ᶠ a, (· - a) ^ D a) z‖ :=
    factor_norm_ge hfin hDnn hz hδpos hsepD
  have hgnorm : ‖g z‖ = ‖(∏ᶠ a, (· - a) ^ D a) z‖ * ‖u z‖ := by
    have hfe : (∏ᶠ a, (· - a) ^ D a) z = ∏ᶠ a, (z - a) ^ D a :=
      congrFun (Function.FactorizedRational.finprod_eq_fun ⟨hfin⟩) z
    rw [heq_pt, ← hfe, norm_mul]
  have hu_pos : 0 < ‖u z‖ := norm_pos_iff.mpr (hu0 ⟨z, hzU⟩)
  have hu_le : ‖u z‖ ≤ ‖g z‖ / δ ^ N := by
    have hδNpos : 0 < δ ^ N := Real.rpow_pos_of_pos hδpos _
    rw [le_div_iff₀ hδNpos, mul_comm, hgnorm]
    simpa [N] using (mul_le_mul_of_nonneg_left hP hu_pos.le)
  have hg_le : ‖g z‖ ≤ A * Real.exp (R' ^ (1 + ε)) := by
    simpa [hz] using hB z
  have hlogu :
      Real.log ‖u z‖ ≤ Real.log A + R' ^ (1 + ε) + N * Real.log (1 / δ) := by
    have hδNpos : 0 < δ ^ N := Real.rpow_pos_of_pos hδpos _
    have h1 : ‖u z‖ ≤ (A * Real.exp (R' ^ (1 + ε))) / δ ^ N :=
      hu_le.trans (div_le_div_of_nonneg_right hg_le hδNpos.le)
    have hlog := Real.log_le_log hu_pos h1
    have hlogrhs :
        Real.log ((A * Real.exp (R' ^ (1 + ε))) / δ ^ N) =
          Real.log A + R' ^ (1 + ε) + N * Real.log (1 / δ) := by
      have hδN : δ ^ N = Real.exp (N * Real.log δ) :=
        Real.rpow_def_of_pos hδpos N
      rw [Real.log_div (by positivity) (ne_of_gt hδNpos),
        Real.log_mul (ne_of_gt hA) (Real.exp_ne_zero _), Real.log_exp, hδN,
        Real.log_exp]
      have : Real.log δ = -Real.log (1 / δ) := by
        rw [Real.log_div Real.one_ne_zero (ne_of_gt hδpos), Real.log_one,
          zero_sub]
      rw [this]; ring
    rwa [hlogrhs] at hlog
  exact hlogu.trans hsum

/-- Upgrade GAP1: φ continuo, exp∘φ = u analítica nunca-cero en la bola
    ⇒ φ holomorfa. Localmente φ = L∘u + 2πi n (lattice). -/
lemma differentiableOn_of_continuous_log
    {u φ : ℂ → ℂ} {S : ℝ} (_hS : 0 < S)
    (hu : AnalyticOnNhd ℂ u (closedBall (0 : ℂ) S))
    (hu0 : ∀ w : closedBall (0 : ℂ) S, u w ≠ 0)
    (hφc : ContinuousOn φ (ball (0 : ℂ) S))
    (hexp : ∀ z ∈ ball (0 : ℂ) S, exp (φ z) = u z) :
    DifferentiableOn ℂ φ (ball (0 : ℂ) S) := by
  intro z₀ hz₀
  have hz₀cl : z₀ ∈ closedBall (0 : ℂ) S := ball_subset_closedBall hz₀
  have hw : u z₀ ≠ 0 := hu0 ⟨z₀, hz₀cl⟩
  let ρ : ℝ := ‖u z₀‖ / 2
  have hρ : 0 < ρ := half_pos (norm_pos_iff.mpr hw)
  have hρw : ρ < ‖u z₀‖ := half_lt_self (norm_pos_iff.mpr hw)
  obtain ⟨L, hLd, hLexp⟩ := exists_holomorphic_log_on_ball hw hρ hρw
  obtain ⟨δ, hδ, hδball⟩ :
      ∃ δ > 0, ∀ z, dist z z₀ < δ → dist (u z) (u z₀) < ρ :=
    (Metric.continuousAt_iff.mp (hu z₀ hz₀cl).continuousAt) ρ hρ
  obtain ⟨δ', hδ', hδ'sub⟩ :
      ∃ δ' > 0, ball z₀ δ' ⊆ ball (0 : ℂ) S :=
    Metric.isOpen_iff.mp isOpen_ball z₀ hz₀
  let δ0 : ℝ := min δ δ'
  have hδ0 : 0 < δ0 := lt_min hδ hδ'
  have hsub : ball z₀ δ0 ⊆ ball (0 : ℂ) S := by
    intro z hz
    exact hδ'sub (mem_ball.mpr
      (lt_of_lt_of_le (mem_ball.mp hz) (min_le_right δ δ')))
  have hhball : ∀ z ∈ ball z₀ δ0, u z ∈ ball (u z₀) ρ := fun z hz =>
    hδball z (lt_of_lt_of_le (mem_ball.mp hz) (min_le_left δ δ'))
  have hexp_eq : ∀ z ∈ ball z₀ δ0, exp (φ z) = exp (L (u z)) := by
    intro z hz
    rw [hexp z (hsub hz), hLexp (u z) (hhball z hz)]
  let ψ : ℂ → ℂ := fun z => φ z - L (u z)
  have hval : ∀ z ∈ ball z₀ δ0, ∃ n : ℤ, ψ z = (n : ℂ) * (2 * π * I) := by
    intro z hz
    obtain ⟨n, hn⟩ := exp_eq_exp_iff_exists_int.mp (hexp_eq z hz)
    exact ⟨n, by simp [ψ, hn, sub_eq_iff_eq_add]⟩
  have hψc' : ContinuousOn ψ (ball z₀ δ0) := by
    have hφ' : ContinuousOn φ (ball z₀ δ0) := hφc.mono hsub
    have hLc : ContinuousOn L (ball (u z₀) ρ) :=
      fun w hw => (hLd w hw).continuousAt.continuousWithinAt
    have huc : ContinuousOn u (ball z₀ δ0) := fun z hz =>
      (hu z (ball_subset_closedBall (hsub hz))).continuousAt.continuousWithinAt
    exact hφ'.sub (hLc.comp huc fun z hz => hhball z hz)
  have hconn : IsConnected (ψ '' ball z₀ δ0) :=
    (isConnected_ball hδ0).image hψc'
  have hsing := connected_image_lattice_subsingleton hconn hval
  have hz0mem : z₀ ∈ ball z₀ δ0 := mem_ball_self hδ0
  obtain ⟨n, hn0⟩ := hval z₀ hz0mem
  have hconst : ∀ z ∈ ball z₀ δ0, ψ z = (n : ℂ) * (2 * π * I) := by
    intro z hz
    exact (hsing ⟨z, hz, rfl⟩ ⟨z₀, hz0mem, rfl⟩).trans hn0
  have hev : φ =ᶠ[𝓝 z₀] fun z => L (u z) + (n : ℂ) * (2 * π * I) :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds hz0mem) fun z hz =>
      eq_add_of_sub_eq (hconst z hz)
  have hLdu : DifferentiableAt ℂ (fun z => L (u z)) z₀ :=
    (hLd (u z₀) (mem_ball_self hρ)).comp z₀
      (hu z₀ hz₀cl).differentiableAt
  have hadd :
      DifferentiableAt ℂ (fun z => L (u z) + (n : ℂ) * (2 * π * I)) z₀ :=
    hLdu.add (differentiableAt_const _)
  exact (hadd.congr_of_eventuallyEq hev.symm).differentiableWithinAt

/--
  Re(log u) en ball 0 (R+3/2) y ‖φ 0‖.
  S = R+3/2 fija (gap 1/2 para Borel).
  Sorry: MMP desde círculo sep ≥ R+3/2 + rama Im + cota inf |u0|.
-/
theorem exists_holomorphic_log_re_bound
    (hg : Differentiable ℂ g) (hg_ord : OrderAtMostOne g)
    (hg0 : ¬ ∀ w, g w = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ), 1 ≤ R →
      ∀ (u : ℂ → ℂ),
        AnalyticOnNhd ℂ u (closedBall (0 : ℂ) (R + 2)) →
        (∀ w : closedBall (0 : ℂ) (R + 2), u w ≠ 0) →
        (g =ᶠ[codiscreteWithin (closedBall (0 : ℂ) (R + 2))]
          (∏ᶠ a, (· - a) ^ MeromorphicOn.divisor g
            (closedBall (0 : ℂ) (R + 2)) a) • u) →
        ∃ φ : ℂ → ℂ,
          DifferentiableOn ℂ φ (ball (0 : ℂ) (R + 2)) ∧
          (∀ z ∈ ball (0 : ℂ) (R + 2), exp (φ z) = u z) ∧
          (∀ w ∈ ball (0 : ℂ) (R + 3 / 2),
            (φ w).re ≤ C * (1 + (R + 2) ^ (1 + ε))) ∧
          ‖φ 0‖ ≤ C * (1 + (R + 2) ^ (1 + ε)) := by
  obtain ⟨c, hc0⟩ := exists_ne_zero hg0
  let ε0 : ℝ := min ε 1
  have hε0 : 0 < ε0 := lt_min hε (by norm_num)
  have hε0le : ε0 ≤ 2 := (min_le_right ε 1).trans (by norm_num)
  obtain ⟨K0, hK0, hN0⟩ := divisor_sum_le_jensen hg hg_ord hc0 (half_pos hε0)
  obtain ⟨A, hA, _⟩ := hg_ord ε0 hε0
  let C : ℝ :=
    (|Real.log A| + K0 * (2 + ‖c‖) ^ (1 + ε0 / 2) * (2 : ℝ) ^ (1 + ε0) +
      4 / ε0 + 1) * (2 : ℝ) ^ (1 + ε) * 3 ^ (1 + ε) + Real.pi + 1
  have hC : 0 < C := by positivity
  refine ⟨C, hC, ?_⟩
  intro R hR u hu hu0 heq
  have hBall : 0 < R + 2 := by linarith
  obtain ⟨φ, hφc, hexp⟩ := exists_continuous_log_on_ball_ne_zero hBall hu hu0
  have hφd : DifferentiableOn ℂ φ (ball (0 : ℂ) (R + 2)) :=
    differentiableOn_of_continuous_log hBall hu hu0 hφc hexp
  refine ⟨φ, hφd, hexp, ?_⟩
  -- Re en ball 0 (R+3/2) ∧ ‖φ 0‖.
  -- Camino: exists_radius_sep en [R+1/2, R+3/2] o [R+1,R+2] + MMP + rama Im.
  sorry

/-- Min |u| en el círculo. Glue: log+Re bound (sorry) + Borel (cerrado). -/
theorem min_norm_never_zero_analytic
    (hg : Differentiable ℂ g) (hg_ord : OrderAtMostOne g)
    (hg0 : ¬ ∀ w, g w = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ), 1 ≤ R →
      ∀ (u : ℂ → ℂ),
        AnalyticOnNhd ℂ u (closedBall (0 : ℂ) (R + 2)) →
        (∀ w : closedBall (0 : ℂ) (R + 2), u w ≠ 0) →
        (g =ᶠ[codiscreteWithin (closedBall (0 : ℂ) (R + 2))]
          (∏ᶠ a, (· - a) ^ MeromorphicOn.divisor g
            (closedBall (0 : ℂ) (R + 2)) a) • u) →
        ∀ R' ∈ Icc R (R + 1), ∀ z, ‖z‖ = R' →
          Real.exp (-C * (1 + R' ^ (1 + ε))) ≤ ‖u z‖ := by
  obtain ⟨C₀, hC₀, hlog⟩ := exists_holomorphic_log_re_bound hg hg_ord hg0 hε
  refine ⟨8 * C₀ + 1, by positivity, ?_⟩
  intro R hR u hu hu0 heq R' hR' z hz
  obtain ⟨φ, hφ, hexp, hRe, hφ0⟩ := hlog R hR u hu hu0 heq
  have hSpos : (0 : ℝ) < R + 3 / 2 := by linarith
  let M : ℝ := C₀ * (1 + (R + 2) ^ (1 + ε)) + 1
  have hM : 0 < M := by positivity
  have hReM : ∀ w ∈ ball (0 : ℂ) (R + 3 / 2), (φ w).re ≤ M := fun w hw =>
    (hRe w hw).trans (by linarith)
  have hφ0M : ‖φ 0‖ ≤ M := hφ0.trans (by linarith)
  have hr : (0 : ℝ) ≤ R + 1 := by linarith
  have hrS : (R + 1 : ℝ) < R + 3 / 2 := by linarith
  have hzle : ‖z‖ ≤ R + 1 := by rw [hz]; exact hR'.2
  have hφS : DifferentiableOn ℂ φ (ball (0 : ℂ) (R + 3 / 2)) :=
    hφ.mono (Metric.ball_subset_ball (by linarith : (R + 3 / 2 : ℝ) ≤ R + 2))
  have hexpS : ∀ z ∈ ball (0 : ℂ) (R + 3 / 2), exp (φ z) = u z := fun z hz' =>
    hexp z (Metric.ball_subset_ball (by linarith : (R + 3 / 2 : ℝ) ≤ R + 2) hz')
  have hmin :=
    min_norm_of_re_log_bound hSpos hr hrS hM hφS hexpS hReM hφ0M hzle
  refine le_trans ?_ hmin
  apply Real.exp_le_exp.mpr
  have hR'nn : 0 ≤ R' := le_trans (by linarith : (0 : ℝ) ≤ 1) (le_trans hR hR'.1)
  -- S = R+3/2, r = R+1 ⇒ S-r = 1/2
  -- 2M(R+1)/(1/2) + M((R+3/2)+(R+1))/(1/2) = 4M(R+1) + 2M(2R+5/2)
  -- = M(8R+9) ≤ (8C₀+1)(1+R'^{1+ε})
  have :
      2 * M * (R + 1) / ((R + 3 / 2) - (R + 1)) +
        M * ((R + 3 / 2) + (R + 1)) / ((R + 3 / 2) - (R + 1)) ≤
      (8 * C₀ + 1) * (1 + R' ^ (1 + ε)) := by
    have hsimp :
        2 * M * (R + 1) / ((R + 3 / 2) - (R + 1)) +
          M * ((R + 3 / 2) + (R + 1)) / ((R + 3 / 2) - (R + 1)) =
        M * (8 * R + 9) := by
      ring_nf; field_simp; ring
    rw [hsimp]
    have hR2 : (R + 2 : ℝ) ^ (1 + ε) ≤ 3 ^ (1 + ε) * (1 + R' ^ (1 + ε)) := by
      have : R + 2 ≤ 3 * (1 + R') := by nlinarith [hR'.1]
      have := Real.rpow_le_rpow (by linarith) this (by linarith)
      have hmul := Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (by linarith : 0 ≤ 1 + R')
      rw [hmul] at this
      refine this.trans ?_
      have : (1 + R') ^ (1 + ε) ≤ 2 ^ (1 + ε) * (1 + R' ^ (1 + ε)) := by
        have h1 : 1 + R' ≤ 2 * max 1 R' := by
          cases le_total (1 : ℝ) R' with
          | inl h => simp [max_eq_right h]; linarith
          | inr h => simp [max_eq_left h]; linarith
        have := Real.rpow_le_rpow (by linarith) h1 (by linarith)
        have hm := Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
          (by positivity : 0 ≤ max 1 R')
        rw [hm] at this
        refine this.trans ?_
        have : (max 1 R') ^ (1 + ε) ≤ 1 + R' ^ (1 + ε) := by
          cases le_total (1 : ℝ) R' with
          | inl h => simp [max_eq_right h]; linarith [Real.rpow_nonneg hR'nn _]
          | inr h =>
            simp [max_eq_left h]
            have : (1 : ℝ) ^ (1 + ε) = 1 := by simp
            linarith [Real.rpow_nonneg hR'nn _, this ▸ le_refl (1 : ℝ)]
        nlinarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (1 + ε), this]
      nlinarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) (1 + ε),
        Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (1 + ε)]
    nlinarith [hC₀.le, hR, hR'.1, hR'.2, hR'nn, hM.le,
      Real.rpow_nonneg (by linarith : 0 ≤ R + 2) (1 + ε),
      Real.rpow_nonneg hR'nn (1 + ε), hR2]
  convert neg_le_neg this using 1
  · ring_nf
  · ring_nf

/-- Glue: identidad, |P|≥δ^N, min|u|, absorción. 0 tactic sorry. -/
theorem min_norm_extracted_factor
    (hg : Differentiable ℂ g) (hg_ord : OrderAtMostOne g)
    {u : ℂ → ℂ} {R R' : ℝ} {n : ℕ} {ε : ℝ} {z : ℂ} {c : ℂ} {K Cu : ℝ}
    (hc0 : g c ≠ 0) (hK : 0 < K) (hCu : 0 < Cu)
    (hN : ∀ r : ℝ, 1 ≤ r →
      ∑ᶠ a, (MeromorphicOn.divisor g (closedBall c (r + 1)) a : ℝ)
        ≤ K * r ^ (1 + ε / 2))
    (hu_min : Real.exp (-Cu * (1 + R' ^ (1 + ε))) ≤ ‖u z‖)
    (hnN0 : (n : ℝ) ≤ ∑ᶠ a, (MeromorphicOn.divisor g
      (closedBall (0 : ℂ) (R + 2)) a : ℝ))
    (hε : 0 < ε) (hεle : ε ≤ 2) (hR : 1 ≤ R)
    (hR' : R' ∈ Icc R (R + 1))
    (hfree : ∀ w, ‖w‖ = R' → g w ≠ 0)
    (hsep : ∀ a, a ∈ closedBall (0 : ℂ) (R + 2) → g a = 0 →
      (1 / (2 * (n + 1) : ℝ)) ≤ |R' - ‖a‖|)
    (hu : AnalyticOnNhd ℂ u (closedBall (0 : ℂ) (R + 2)))
    (hu0 : ∀ w : closedBall (0 : ℂ) (R + 2), u w ≠ 0)
    (heq : g =ᶠ[codiscreteWithin (closedBall (0 : ℂ) (R + 2))]
      (∏ᶠ a, (· - a) ^ MeromorphicOn.divisor g (closedBall (0 : ℂ) (R + 2)) a) • u)
    (hz : ‖z‖ = R') :
    Real.exp (-(K * (2 + ‖c‖) ^ (1 + ε / 2) * (2 : ℝ) ^ (1 + ε) + Cu + 4 / ε) *
      (1 + R' ^ (1 + ε))) ≤ ‖g z‖ := by
  let U := closedBall (0 : ℂ) (R + 2)
  let D : ℂ → ℤ := fun a => MeromorphicOn.divisor g U a
  let δ : ℝ := 1 / (2 * (n + 1) : ℝ)
  have hδpos : 0 < δ := by positivity
  have hS : 0 ≤ R + 2 := by linarith
  have hzU : z ∈ U := by
    rw [mem_closedBall, dist_zero_right, hz]
    linarith [hR'.2]
  have hacc : AccPt z (𝓟 U) :=
    accPt_closedBall_of_lt (by rw [hz]; linarith [hR'.2] : ‖z‖ < R + 2)
  have heq_pt : g z = (∏ᶠ a, (z - a) ^ D a) * u z := by
    simpa [D, U] using
      extract_eq_at_nonzero hg hS hu hu0 heq hzU (hfree z hz) hacc
  have hfin : (Function.support D).Finite :=
    (MeromorphicOn.divisor g U).finiteSupport (isCompact_closedBall _ _)
  have hDnn : ∀ a, 0 ≤ D a := fun a => divisor_nonneg_entire hg U a
  have hsepD : ∀ a, a ∈ Function.support D → δ ≤ |R' - ‖a‖| := by
    intro a ha
    have hmem : a ∈ U := by
      by_contra hnot
      have : D a = 0 := by simp [D, MeromorphicOn.divisor, hnot]
      exact absurd this (by simpa [Function.mem_support] using ha)
    have hg0a : g a = 0 := by
      have hne : D a ≠ 0 := by simpa [Function.mem_support] using ha
      by_contra hgne
      have hgA : AnalyticAt ℂ g a := (hg a).analyticAt
      have hord : meromorphicOrderAt g a = 0 := by
        have : analyticOrderAt g a = 0 := (hgA.analyticOrderAt_eq_zero).2 hgne
        rwa [hgA.meromorphicOrderAt_eq, ENat.map_eq_zero_iff]
      have : D a = 0 := by simp [D, MeromorphicOn.divisor, hmem, hord]
      exact hne this
    exact hsep a hmem hg0a
  have hP : δ ^ (∑ᶠ a, (D a : ℝ)) ≤ ‖(∏ᶠ a, (· - a) ^ D a) z‖ :=
    factor_norm_ge hfin hDnn hz hδpos hsepD
  have hgnorm : ‖g z‖ = ‖(∏ᶠ a, (· - a) ^ D a) z‖ * ‖u z‖ := by
    have hfe : (∏ᶠ a, (· - a) ^ D a) z = ∏ᶠ a, (z - a) ^ D a :=
      congrFun (Function.FactorizedRational.finprod_eq_fun ⟨hfin⟩) z
    rw [heq_pt, ← hfe, norm_mul]
  let N : ℝ := ∑ᶠ a, (D a : ℝ)
  have hNnn : 0 ≤ N := finsum_nonneg fun _ => Int.cast_nonneg.mpr (hDnn _)
  let r0 : ℝ := max 1 (R + 2 + ‖c‖)
  have hr0 : 1 ≤ r0 := le_max_left _ _
  have hN0 := hN r0 hr0
  have hNle : N ≤ K * r0 ^ (1 + ε / 2) := by
    refine le_trans ?_ hN0
    refine finsum_le_finsum
      (fun a => Int.cast_nonneg.mpr (hDnn a))
      (fun a => Int.cast_nonneg.mpr
        ((analyticOnNhd_of_differentiable hg _).divisor_nonneg a)) ?_
    intro a
    by_cases hmem : a ∈ U
    · have hmemc : a ∈ closedBall c (r0 + 1) := by
        rw [mem_closedBall]
        have hale : ‖a‖ ≤ R + 2 := by
          simpa [U, mem_closedBall, dist_zero_right] using hmem
        have htri : ‖a - c‖ ≤ ‖a‖ + ‖c‖ := by
          simpa [sub_eq_add_neg] using
            (norm_add_le a (-c)).trans_eq (by simp [norm_neg])
        have : R + 2 + ‖c‖ ≤ r0 := le_max_right _ _
        linarith
      have : MeromorphicOn.divisor g U a =
          MeromorphicOn.divisor g (closedBall c (r0 + 1)) a := by
        simp [MeromorphicOn.divisor, hmem, hmemc]
      exact le_of_eq (by simp [D, this])
    · have : D a = 0 := by simp [D, MeromorphicOn.divisor, hmem]
      simp [this]
  have hnN : (n : ℝ) ≤ N := by simpa [N, D, U] using hnN0
  have hδinv : 1 / δ ≤ 2 * (N + 1) := by
    simp only [δ, one_div_div]
    nlinarith [hnN]
  have hR'nn : 0 ≤ R' := le_trans (by linarith : (0 : ℝ) ≤ 1) (le_trans hR hR'.1)
  have hr0R : r0 ≤ (2 + ‖c‖) * (1 + R') := by
    apply max_le
    · nlinarith [norm_nonneg c, hR'nn]
    · nlinarith [hR'.1, norm_nonneg c]
  -- Scale K so N ≤ K' (1+R')^{1+ε/2}
  have hK' : 0 < K * (2 + ‖c‖) ^ (1 + ε / 2) := by positivity
  have hN' : N ≤ (K * (2 + ‖c‖) ^ (1 + ε / 2)) * (1 + R') ^ (1 + ε / 2) := by
    have : r0 ^ (1 + ε / 2) ≤ ((2 + ‖c‖) * (1 + R')) ^ (1 + ε / 2) :=
      Real.rpow_le_rpow (by linarith) hr0R (by linarith)
    have hmul := Real.mul_rpow (by positivity) (by linarith : 0 ≤ 1 + R')
    rw [hmul] at this
    nlinarith [hNle, Real.rpow_nonneg (by linarith : 0 ≤ r0) (1 + ε / 2)]
  have habs : N * Real.log (1 / δ) ≤
      (K * (2 + ‖c‖) ^ (1 + ε / 2) * (2 : ℝ) ^ (1 + ε) + 4 / ε) *
        (1 + R' ^ (1 + ε)) := by
    have := absorb_N_log_delta hK' hε hεle hNnn hN' (by linarith [hR'nn] : 1 ≤ 1 + R')
      (by linarith : 1 + R' ≤ 2 * (1 + R')) hR'nn hδpos hδinv
    -- absorb gives (K' * 2^{1+ε} + 4/ε)(1+R'^{1+ε})
    convert this using 2
    ring
  have hPexp : Real.exp (-(N * Real.log (1 / δ))) ≤
      ‖(∏ᶠ a, (· - a) ^ D a) z‖ := by
    have hδN : δ ^ N ≤ ‖(∏ᶠ a, (· - a) ^ D a) z‖ := by simpa [N] using hP
    have hrpow : δ ^ N = Real.exp (N * Real.log δ) := Real.rpow_def_of_pos hδpos N
    have hlog : N * Real.log δ = -(N * Real.log (1 / δ)) := by
      have : Real.log δ = -Real.log (1 / δ) := by
        rw [Real.log_div Real.one_ne_zero (ne_of_gt hδpos), Real.log_one, zero_sub]
      rw [this]; ring
    rwa [hrpow, hlog] at hδN
  have hmul := mul_le_mul hPexp hu_min (Real.exp_pos _).le (norm_nonneg _)
  have hexp :
      Real.exp (-(N * Real.log (1 / δ))) *
          Real.exp (-(Cu * (1 + R' ^ (1 + ε)))) =
        Real.exp (-(N * Real.log (1 / δ) + Cu * (1 + R' ^ (1 + ε)))) := by
    rw [← Real.exp_add]; ring
  have hcomb :
      Real.exp (-(N * Real.log (1 / δ) + Cu * (1 + R' ^ (1 + ε)))) ≤ ‖g z‖ := by
    rwa [hgnorm, ← hexp] at hmul
  have hsumle :
      N * Real.log (1 / δ) + Cu * (1 + R' ^ (1 + ε)) ≤
        (K * (2 + ‖c‖) ^ (1 + ε / 2) * (2 : ℝ) ^ (1 + ε) + Cu + 4 / ε) *
          (1 + R' ^ (1 + ε)) := by
    have hnn : 0 ≤ 1 + R' ^ (1 + ε) := by
      linarith [Real.rpow_nonneg hR'nn (1 + ε)]
    nlinarith [habs, hCu.le, hnn]
  exact (Real.exp_le_exp.mpr (neg_le_neg hsumle)).trans hcomb

/-!
  Jensen a ε/2. Borel uniforme. Absorción 4/ε. Identidad y |P| cerradas.
-/
theorem exists_circle_min_norm
    (hg : Differentiable ℂ g) (hg_ord : OrderAtMostOne g)
    (hg0 : ¬ ∀ z, g z = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R → ∃ R' ∈ Icc R (R + 1),
      (∀ z, ‖z‖ = R' → g z ≠ 0) ∧
      ∀ z, ‖z‖ = R' → Real.exp (-C * (1 + R' ^ (1 + ε))) ≤ ‖g z‖ := by
  obtain ⟨c, hc0⟩ := exists_ne_zero hg0
  -- ε0 = min ε 1 ≤ 1 ≤ 2 para absorción; r^{1+ε0} ≤ r^{1+ε}
  let ε0 : ℝ := min ε 1
  have hε0 : 0 < ε0 := lt_min hε (by norm_num)
  have hε0le : ε0 ≤ 2 := (min_le_right ε 1).trans (by norm_num)
  have hε0leε : ε0 ≤ ε := min_le_left ε 1
  obtain ⟨K0, hK0, hN0⟩ := divisor_sum_le_jensen hg hg_ord hc0 (half_pos hε0)
  obtain ⟨Cu0, hCu0, hBorel0⟩ := min_norm_never_zero_analytic hg hg_ord hg0 hε0
  let Kc0 : ℝ := K0 * (2 + ‖c‖) ^ (1 + ε0 / 2) * (2 : ℝ) ^ (1 + ε0)
  refine ⟨Kc0 + Cu0 + 4 / ε0, by positivity, ?_⟩
  intro R hR
  obtain ⟨R', n, hR'I, hfree, hsep, hnN⟩ :=
    exists_radius_sep hg hg0 (le_trans (by norm_num : (0 : ℝ) ≤ 1) hR)
  refine ⟨R', hR'I, hfree, ?_⟩
  intro z hz
  obtain ⟨u, huA, hu0, heq⟩ :=
    extract_on_closedBall hg hg0 (S := R + 2) (by linarith)
  have hu_min : Real.exp (-Cu0 * (1 + R' ^ (1 + ε0))) ≤ ‖u z‖ :=
    hBorel0 R hR u huA hu0 heq R' hR'I z hz
  have hbound :=
    min_norm_extracted_factor hg hg_ord hc0 hK0 hCu0 hN0 hu_min hnN hε0 hε0le hR hR'I
      hfree hsep huA hu0 heq hz
  -- lift ε0 → ε: 1+R'^{1+ε0} ≤ 1+R'^{1+ε}
  have hR'nn : 0 ≤ R' := le_trans (by linarith : (0 : ℝ) ≤ 1) (le_trans hR hR'I.1)
  have hpow : R' ^ (1 + ε0) ≤ R' ^ (1 + ε) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [hR, hR'I.1] : 1 ≤ R') (by linarith [hε0leε])
  refine le_trans ?_ hbound
  apply Real.exp_le_exp.mpr
  have : 0 ≤ 1 + R' ^ (1 + ε0) := by linarith [Real.rpow_nonneg hR'nn _]
  nlinarith [hpow, Real.rpow_nonneg hR'nn (1 + ε), Real.rpow_nonneg hR'nn (1 + ε0)]

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
