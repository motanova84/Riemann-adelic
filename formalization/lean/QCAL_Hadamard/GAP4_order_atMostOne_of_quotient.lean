/-
  GAP 4 v3.2.5 — order_atMostOne_of_quotient

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

  Un sorry:
    cota inferior min |g| ≥ exp(-C (1+R'^{1+ε})) en ese círculo.
    Plan (Mathlib v4.32.1, no Cartan global):
      1. `AnalyticOnNhd.sum_divisor_le` ⇒ n(R) = O(R^{1+ε})
         (si g(0)=0, factor z^n vía `analyticOrderNatAt`).
      2. palomar: δ ≥ 1/(2(n+1)) entre R' y el cero más cercano.
      3. `MeromorphicOn.extract_zeros_poles` en closedBall 0 (R+2)
         (finito; NO en todo ℂ — GAP3 sigue en pie).
      4. g = P · u, u analítica nunca-cero en el disco.
      5. log holomorfo de u + `borelCaratheodory`
         ⇒ min |u| ≥ exp(-O(R^{1+ε} log R)).
      6. |P| ≥ δ^{n(R)} absorbe log R en cualquier ε' > ε.

  No lake-checked. No RH. No D ≡ Ξ.

  José Manuel Mota Burruezo · Noesis · QCAL ∞³
-/

import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.DiffContOnCl
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.JensenFormula
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

/-!
  Jensen da la media de log |g|. El mínimo en el círculo sin ceros
  pide Borel del factor nunca-cero tras extraer ceros finitos en el disco.
-/
theorem exists_circle_min_norm
    (hg : Differentiable ℂ g) (_hg_ord : OrderAtMostOne g)
    (hg0 : ¬ ∀ z, g z = 0) {ε : ℝ} (_hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R → ∃ R' ∈ Icc R (R + 1),
      (∀ z, ‖z‖ = R' → g z ≠ 0) ∧
      ∀ z, ‖z‖ = R' → Real.exp (-C * (1 + R' ^ (1 + ε))) ≤ ‖g z‖ := by
  refine ⟨1, by norm_num, ?_⟩
  intro R hR
  obtain ⟨R', hR'I, hfree⟩ := exists_radius_zero_free hg hg0 (le_trans (by norm_num : (0 : ℝ) ≤ 1) hR)
  refine ⟨R', hR'I, hfree, ?_⟩
  -- min |g| ≥ exp(-C (1+R'^{1+ε})): Cartan / Borel del factor u.
  -- `sum_divisor_le` + `extract_zeros_poles` (disco compacto) + Borel.
  intro z hz
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
