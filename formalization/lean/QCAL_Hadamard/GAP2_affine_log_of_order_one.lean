/-
  GAP 2 v3.2.4 — affine_log_of_order_one

  Re φ = O(|z|^{1+ε}) ∀ε>0, φ entera
    → Borel–Carathéodory: |φ| = O(|z|^{1+ε})
    → Cauchy n=2: |φ''(c)| ≤ 2 C_R / R^2 = O(R^{ε-1}) → 0 (ε=1/2)
    → φ'' ≡ 0 → φ' constante → φ(s) = A + B s

  Mathlib:
    Complex.borelCaratheodory
    Differentiable.diffContOnCl
    Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    is_const_of_deriv_eq_zero

  José Manuel Mota Burruezo · Noesis · QCAL ∞³
-/

import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Analysis.Calculus.DiffContOnCl
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Basic

noncomputable section
open Complex Metric Set Filter
open scoped Topology Real

variable {φ : ℂ → ℂ}

lemma differentiable_diffContOnCl_ball (hφ : Differentiable ℂ φ)
    (c : ℂ) {R : ℝ} (_hR : 0 < R) :
    DiffContOnCl ℂ φ (ball c R) :=
  hφ.diffContOnCl

lemma differentiable_deriv_complex {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ (deriv f) :=
  fun z => (hf z).analyticAt.deriv.differentiableAt

lemma norm_le_of_re_bound (hφ : Differentiable ℂ φ) {S M : ℝ} {z : ℂ}
    (hS : 0 < S) (hM : 0 < M)
    (hRe : ∀ w ∈ ball 0 S, (φ w).re ≤ M)
    (hz : z ∈ ball 0 S) :
    ‖φ z‖ ≤ 2 * M * ‖z‖ / (S - ‖z‖) + ‖φ 0‖ * (S + ‖z‖) / (S - ‖z‖) :=
  borelCaratheodory hM hφ.differentiableOn (fun w hw => hRe w hw) hS hz

/--
  Un solo K, independiente de c y R.
  Esfera ⊂ ball 0 S con S = 2(‖c‖+R)+1; Borel da |φ| = O(R^{1+ε}).
-/
lemma exists_norm_bound_sphere (hφ : Differentiable ℂ φ)
    (hRe : ∀ ε > 0, ∃ C : ℝ, 0 < C ∧ ∀ z, (φ z).re ≤ C * (1 + ‖z‖ ^ (1 + ε)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (c : ℂ) {R : ℝ}, 0 < R →
      ∀ z ∈ sphere c R, ‖φ z‖ ≤ K * (1 + (‖c‖ + R) ^ (1 + ε)) := by
  obtain ⟨C, hC, hCre⟩ := hRe ε hε
  let K : ℝ := 2 * C * (1 + (3 : ℝ) ^ (1 + ε) * (2 : ℝ) ^ (1 + ε)) +
    4 * (‖φ 0‖ + 1) + 1
  have hK : 0 < K := by positivity
  refine ⟨K, hK, ?_⟩
  intro c R hR z hz
  let r : ℝ := ‖c‖ + R
  have hr : 0 < r := by positivity
  let S : ℝ := 2 * r + 1
  have hS : 0 < S := by positivity
  have hS_gt : r < S := by nlinarith
  have hsphere_subset : sphere c R ⊆ ball (0 : ℂ) S := by
    intro w hw
    have hwc : ‖w - c‖ = R := mem_sphere_iff_norm.mp hw
    have hwn : ‖w‖ ≤ r := by
      calc
        ‖w‖ = ‖(w - c) + c‖ := by ring_nf
        _ ≤ ‖w - c‖ + ‖c‖ := norm_add_le _ _
        _ = R + ‖c‖ := by rw [hwc]
        _ = r := add_comm _ _
    exact mem_ball_zero_iff.mpr (hwn.trans_lt hS_gt)
  have hε1 : 0 ≤ 1 + ε := by linarith
  let M : ℝ := C * (1 + S ^ (1 + ε))
  have hM : 0 < M := mul_pos hC (by positivity)
  have hReS : ∀ w ∈ ball (0 : ℂ) S, (φ w).re ≤ M := by
    intro w hw
    have hwS : ‖w‖ < S := mem_ball_zero_iff.mp hw
    exact (hCre w).trans (by
      gcongr
      exact Real.rpow_le_rpow (norm_nonneg _) hwS.le hε1)
  have hzS : z ∈ ball (0 : ℂ) S := hsphere_subset hz
  have hzn : ‖z‖ ≤ r := by
    have hzc : ‖z - c‖ = R := mem_sphere_iff_norm.mp hz
    calc
      ‖z‖ = ‖(z - c) + c‖ := by ring_nf
      _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
      _ = R + ‖c‖ := by rw [hzc]
      _ = r := add_comm _ _
  have hden : 1 ≤ S - ‖z‖ := by nlinarith
  have hborel := norm_le_of_re_bound hφ hS hM hReS hzS
  have hposd : 0 < S - ‖z‖ := lt_of_lt_of_le zero_lt_one hden
  have hfrac1 : ‖z‖ / (S - ‖z‖) ≤ 1 :=
    (div_le_one hposd).mpr (by nlinarith)
  have hfrac2 : (S + ‖z‖) / (S - ‖z‖) ≤ 4 :=
    (div_le_iff₀ hposd).mpr (by nlinarith)
  have hb' : ‖φ z‖ ≤ 2 * M * (‖z‖ / (S - ‖z‖)) +
      ‖φ 0‖ * ((S + ‖z‖) / (S - ‖z‖)) := by
    convert hborel using 2 <;> ring
  have hle1 : ‖φ z‖ ≤ 2 * M + ‖φ 0‖ * 4 := by
    nlinarith [hfrac1, hfrac2, mul_nonneg (by positivity : 0 ≤ (2 : ℝ) * M) (div_nonneg (norm_nonneg z) hposd.le),
      mul_nonneg (norm_nonneg (φ 0)) (div_nonneg (by positivity : 0 ≤ S + ‖z‖) hposd.le)]
  have hSle : S ≤ 3 * (r + 1) := by nlinarith
  have hr1 : 0 ≤ r + 1 := by positivity
  have hSpow : S ^ (1 + ε) ≤ (3 * (r + 1)) ^ (1 + ε) :=
    Real.rpow_le_rpow (le_of_lt hS) hSle hε1
  have h3r : (3 * (r + 1)) ^ (1 + ε) = (3 : ℝ) ^ (1 + ε) * (r + 1) ^ (1 + ε) :=
    Real.mul_rpow (by positivity) hr1
  have hrpow : (r + 1) ^ (1 + ε) ≤ (2 : ℝ) ^ (1 + ε) * (1 + r ^ (1 + ε)) := by
    by_cases hrle : 1 ≤ r
    · have : r + 1 ≤ 2 * r := by nlinarith
      have hle : (r + 1) ^ (1 + ε) ≤ (2 * r) ^ (1 + ε) :=
        Real.rpow_le_rpow (by positivity) this hε1
      have hmul : (2 * r) ^ (1 + ε) = (2 : ℝ) ^ (1 + ε) * r ^ (1 + ε) :=
        Real.mul_rpow (by positivity) (by positivity)
      nlinarith [Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ r) (1 + ε),
        Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ)) (1 + ε)]
    · have : r + 1 ≤ 2 := by nlinarith
      have hle : (r + 1) ^ (1 + ε) ≤ (2 : ℝ) ^ (1 + ε) :=
        Real.rpow_le_rpow (by positivity) this hε1
      nlinarith [Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ r) (1 + ε),
        Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ)) (1 + ε)]
  nlinarith [Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ r) (1 + ε),
    Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (3 : ℝ)) (1 + ε),
    Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ)) (1 + ε),
    norm_nonneg (φ 0)]

lemma cauchy_two (hφ : Differentiable ℂ φ) (c : ℂ) {R C : ℝ}
    (hR : 0 < R) (hC : ∀ z ∈ sphere c R, ‖φ z‖ ≤ C) :
    ‖iteratedDeriv 2 φ c‖ ≤ (2 : ℝ) * C / R ^ 2 := by
  have hdc : DiffContOnCl ℂ φ (ball c R) := hφ.diffContOnCl
  have := norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (F := ℂ) 2 hR hdc hC
  simpa [Nat.factorial] using this

lemma tendsto_bound_cauchy (c : ℂ) (K : ℝ) :
    Tendsto (fun R : ℝ => (2 : ℝ) * K * (1 + (‖c‖ + R) ^ ((3 : ℝ) / 2)) / R ^ 2)
      atTop (𝓝 0) := by
  have hRneg : Tendsto (fun R : ℝ => R ^ (-(1 : ℝ) / 2)) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  have hratio : Tendsto (fun R : ℝ => (‖c‖ + R) / R) atTop (𝓝 1) := by
    have h1 : Tendsto (fun R : ℝ => ‖c‖ / R) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := ‖c‖)).mul tendsto_inv_atTop_zero
    have : (fun R : ℝ => (‖c‖ + R) / R) = fun R => ‖c‖ / R + 1 := by
      funext R; field_simp
    simpa [this] using h1.add tendsto_const_nhds
  have hpow : Tendsto (fun R : ℝ => ((‖c‖ + R) / R) ^ ((3 : ℝ) / 2)) atTop (𝓝 1) := by
    simpa [Real.one_rpow] using hratio.rpow tendsto_const_nhds (by norm_num)
  have hprod := hpow.mul hRneg
  have h1R2 : Tendsto (fun R : ℝ => (1 : ℝ) / R ^ 2) atTop (𝓝 0) := by
    simpa [pow_two] using tendsto_inv_atTop_zero.comp (tendsto_pow_atTop two_ne_zero)
  have heq : (fun R : ℝ => (1 + (‖c‖ + R) ^ ((3 : ℝ) / 2)) / R ^ 2) =ᶠ[atTop]
      fun R => (1 / R ^ 2) +
        ((‖c‖ + R) / R) ^ ((3 : ℝ) / 2) * R ^ (-(1 : ℝ) / 2) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have hRnn : 0 ≤ R := hR.le
    have hr0 : 0 ≤ ‖c‖ + R := by positivity
    have hR2 : (R : ℝ) ^ (2 : ℝ) = R ^ 2 := by norm_cast
    have : (‖c‖ + R) ^ ((3 : ℝ) / 2) / R ^ (2 : ℝ) =
        ((‖c‖ + R) / R) ^ ((3 : ℝ) / 2) * R ^ (-(1 : ℝ) / 2) := by
      have hdiv := Real.div_rpow hr0 hRnn ((3 : ℝ) / 2)
      have : R ^ ((3 : ℝ) / 2 - 2) = R ^ (-(1 : ℝ) / 2) := by ring_nf
      calc
        (‖c‖ + R) ^ ((3 : ℝ) / 2) / R ^ (2 : ℝ) =
            (‖c‖ + R) ^ ((3 : ℝ) / 2) * R ^ (-(2 : ℝ)) := by
          rw [div_eq_mul_inv, Real.rpow_neg hRnn]
        _ = ((‖c‖ + R) ^ ((3 : ℝ) / 2) / R ^ ((3 : ℝ) / 2)) * R ^ ((3 : ℝ) / 2 - 2) := by
          rw [Real.rpow_sub hR]
          ring
        _ = ((‖c‖ + R) / R) ^ ((3 : ℝ) / 2) * R ^ (-(1 : ℝ) / 2) := by
          rw [hdiv, this]
    field_simp [this]
  have hsum := h1R2.add hprod
  have hmain : Tendsto (fun R : ℝ => (1 + (‖c‖ + R) ^ ((3 : ℝ) / 2)) / R ^ 2)
      atTop (𝓝 0) := (tendsto_congr' heq).mp (by simpa using hsum)
  simpa [mul_div_assoc] using hmain.const_mul (2 * K)

theorem iteratedDeriv_two_eq_zero (hφ : Differentiable ℂ φ)
    (hRe : ∀ ε > 0, ∃ C : ℝ, 0 < C ∧ ∀ z, (φ z).re ≤ C * (1 + ‖z‖ ^ (1 + ε))) :
    iteratedDeriv 2 φ = 0 := by
  funext c
  have hε : (0 : ℝ) < 1 / 2 := by norm_num
  obtain ⟨K, hK, hbd⟩ := exists_norm_bound_sphere hφ hRe hε
  have hle : ∀ R > 0, ‖iteratedDeriv 2 φ c‖ ≤
      (2 : ℝ) * K * (1 + (‖c‖ + R) ^ ((3 : ℝ) / 2)) / R ^ 2 := by
    intro R hR
    have hC : ∀ z ∈ sphere c R,
        ‖φ z‖ ≤ K * (1 + (‖c‖ + R) ^ ((3 : ℝ) / 2)) := by
      intro z hz
      convert hbd c hR z hz using 2
      ring_nf
      norm_num
    have := cauchy_two hφ c hR hC
    convert this using 1
    ring
  have hlim := tendsto_bound_cauchy c K
  have : ‖iteratedDeriv 2 φ c‖ ≤ 0 :=
    ge_of_tendsto hlim <|
      (eventually_gt_atTop (0 : ℝ)).mono fun R hR => hle R hR
  exact norm_le_zero_iff.mp this

/-- φ'' ≡ 0 ⇒ φ' constante. -/
theorem deriv_const_of_iteratedDeriv_two_zero (hφ : Differentiable ℂ φ)
    (hφ'' : iteratedDeriv 2 φ = 0) :
    ∃ B : ℂ, deriv φ = fun _ => B := by
  refine ⟨deriv φ 0, ?_⟩
  funext z
  have hder : Differentiable ℂ (deriv φ) := differentiable_deriv_complex hφ
  have hder0 : deriv (deriv φ) = 0 := by
    funext w
    simpa [iteratedDeriv_succ, iteratedDeriv_one] using congrFun hφ'' w
  exact is_const_of_deriv_eq_zero hder (fun w => by simp [hder0]) z 0

theorem affine_log_of_order_one (hφ : Differentiable ℂ φ)
    (hRe : ∀ ε > 0, ∃ C : ℝ, 0 < C ∧ ∀ z, (φ z).re ≤ C * (1 + ‖z‖ ^ (1 + ε))) :
    ∃ A B : ℂ, ∀ s, φ s = A + B * s := by
  have hφ'' := iteratedDeriv_two_eq_zero hφ hRe
  obtain ⟨B, hB⟩ := deriv_const_of_iteratedDeriv_two_zero hφ hφ''
  refine ⟨φ 0, B, ?_⟩
  intro s
  let ψ : ℂ → ℂ := fun z => φ z - B * z
  have hψ : Differentiable ℂ ψ :=
    hφ.sub ((differentiable_id (𝕜 := ℂ)).const_mul B)
  have hψ' : deriv ψ = 0 := by
    funext z
    have hmul : DifferentiableAt ℂ (fun w : ℂ => B * w) z :=
      (differentiable_id.const_mul B) z
    rw [deriv_sub (hφ z) hmul, hB]
    have : deriv (fun w : ℂ => B * w) z = B := by
      simpa using deriv_const_mul B (differentiableAt_id : DifferentiableAt ℂ id z)
    rw [this, sub_self]
  have hconst : ψ s = ψ 0 := is_const_of_deriv_eq_zero hψ (fun _ => by simp [hψ']) s 0
  have : φ s - B * s = φ 0 := by
    simpa [ψ] using hconst
  linarith

end
