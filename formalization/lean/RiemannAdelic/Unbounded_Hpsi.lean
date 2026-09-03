/-
  Unbounded_Hpsi.lean
  ------------------------------------------------------------
  Módulo base para la derivación incondicional de H_Ψ:
  - dominio denso (Schwartz-Bruhat abstracto),
  - acción operatorial no acotada,
  - simetría en el dominio,
  - cierre formal de índices de deficiencia (0,0) como hipótesis estructural.

  Nota:
  Este archivo define la interfaz matemática y los puntos de prueba que deben
  rellenarse con análisis funcional completo (von Neumann/Kato-Rellich).
  No introduce dependencia circular con ζ/Ξ en la definición de H_Ψ.
-/

import Mathlib
import Mathlib.Analysis.SpecialFunctions.Pow.Asymm
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Lebesgue
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Instances.Real

noncomputable section

namespace RiemannAdelic
namespace UnboundedHpsi

open Complex
open MeasureTheory Set Filter
open scoped Topology ENNReal Real

universe u

/-- Modelo abstracto del bloque no acotado para `H_Ψ` en un Hilbert complejo. -/
structure CoreModel (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- Dominio denso tipo Schwartz-Bruhat (abstracto a este nivel). -/
  domain : Submodule ℂ H
  /-- Densidad del dominio en `H`. -/
  dense_domain : Dense (domain : Set H)
  /-- Acción formal de `H_Ψ` en el dominio. -/
  action : domain → H
  /-- Simetría formal `⟪H_Ψ f, g⟫ = ⟪f, H_Ψ g⟫` en el dominio denso. -/
  symmetric :
    ∀ f g : domain, ⟪action f, (g : H)⟫_ℂ = ⟪(f : H), action g⟫_ℂ
  /-- Predicado abstracto para `u ∈ ker(H_Ψ† - z I)`. -/
  inAdjointKernel : ℂ → H → Prop

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Medida de Haar multiplicativa local en `ℝ₊`: densidad formal `dx / x`. -/
def localHaarWeight (x : ℝ) : ℝ := x⁻¹

/-- Perfil local de modo de deficiencia para la EDO `x f' + (1/2 ± i) f = 0`. -/
def localDeficiencyMode (σ : Bool) (C : ℂ) (x : ℝ) : ℂ :=
  C * (x : ℂ) ^ ((-(1 / 2 : ℂ)) + (if σ then Complex.I else -Complex.I))

/-- Integrando formal de norma `L²` para el modo local, ponderado por Haar. -/
def localDeficiencyIntegrand (σ : Bool) (C : ℂ) (x : ℝ) : ℝ :=
  ‖localDeficiencyMode σ C x‖ ^ 2 * localHaarWeight x

/-- Exponente del factor integrante para la ecuación local de deficiencia. -/
def integratingExponent (σ : Bool) : ℂ :=
  (1 / 2 : ℂ) + (if σ then -Complex.I else Complex.I)

/-- Factor integrante local `x^(1/2 ∓ i)` en `ℝ₊`. -/
def integratingFactor (σ : Bool) (x : ℝ) : ℂ :=
  (x : ℂ) ^ integratingExponent σ

/-- Ecuación diferencial adjunta local del modo de deficiencia. -/
def SatisfiesAdjointODE (σ : Bool) (u : ℝ → ℂ) : Prop :=
  ∀ x > 0, HasDerivAt u
    ((- (integratingExponent σ) / (x : ℂ)) * u x) x

/--
Testigo de unicidad del problema diferencial local:
toda solución de la ecuación adjunta se expresa por un modo de deficiencia.
-/
structure DeficiencyODEUniquenessWitness : Prop where
  deficiency_mode_unique :
    ∀ (σ : Bool) (u : ℝ → ℂ),
      SatisfiesAdjointODE σ u →
      ∃ C : ℂ, ∀ x > 0, u x = localDeficiencyMode σ C x

/-- Predicado objetivo: divergencia local de norma `L²` en la región `(0,1]`. -/
def LocalL2DivergenceOnIoc (σ : Bool) (C : ℂ) : Prop :=
  ∫⁻ x in Set.Ioc (0 : ℝ) 1,
      ENNReal.ofReal (localDeficiencyIntegrand σ C x) = ∞

/-- Predicado objetivo: no-integrabilidad global en `(0,∞)` para el modo local. -/
def LocalModeNotIntegrable (σ : Bool) (C : ℂ) : Prop :=
  ¬ MeasureTheory.IntegrableOn
      (fun x : ℝ => localDeficiencyIntegrand σ C x)
      (Set.Ioi (0 : ℝ))
      MeasureTheory.volume

/--
  Lema Auxiliar: para `x > 0` real y `b ∈ ℝ`, el módulo de `x^(I*b)` es `1`.
-/
lemma norm_cpow_I_mul_real (x : ℝ) (hx : 0 < x) (b : ℝ) :
    ‖(x : ℂ) ^ (Complex.I * (b : ℂ))‖ = 1 := by
  rw [cpow_def_of_ne_zero (by exact_mod_cast ne_of_gt hx)]
  rw [← exp_mul]
  have h_eq :
      (Complex.I * (b : ℂ)) * Complex.log (x : ℂ) =
      Complex.I * ((b * Real.log x : ℝ) : ℂ) := by
    rw [Complex.log_ofReal_of_pos hx]
    push_cast
    ring
  rw [h_eq, norm_exp_of_real_mul_I]

/--
  Lema de norma compleja:
  para `x > 0` real y `a,b ∈ ℝ`, `‖x^(a + i*b)‖ = x^a`.
-/
lemma norm_cpow_of_pos_real (x : ℝ) (hx : 0 < x) (a b : ℝ) :
    ‖(x : ℂ) ^ ((a : ℂ) + Complex.I * (b : ℂ))‖ = x ^ a := by
  have hx_ne : (x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hx
  rw [cpow_add _ _ hx_ne, norm_mul]
  have h_real : ‖(x : ℂ) ^ (a : ℂ)‖ = x ^ a := by
    rw [← ofReal_cpow (le_of_lt hx)]
    norm_cast
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx a)]
  rw [h_real, norm_cpow_I_mul_real x hx b, mul_one]

/--
  Reducción rigurosa de la densidad compleja local al integrando real `x⁻²`.
-/
theorem localDeficiencyIntegrand_eq (σ : Bool) (C : ℂ) (x : ℝ) (hx : 0 < x) :
    localDeficiencyIntegrand σ C x = ‖C‖ ^ 2 * x ^ (-2 : ℝ) := by
  dsimp [localDeficiencyIntegrand, localDeficiencyMode, localHaarWeight]
  rw [norm_mul, mul_pow]
  have h_exponent :
      (-(1 / 2 : ℂ) + (if σ then Complex.I else -Complex.I)) =
      ((- (1 / 2 : ℝ) : ℝ) : ℂ) + Complex.I *
        (((if σ then (1 : ℝ) else (-1 : ℝ)) : ℝ) : ℂ) := by
    split_ifs <;> simp <;> ring
  rw [h_exponent, norm_cpow_of_pos_real x hx (-1 / 2) (if σ then 1 else -1)]
  have h_sq : (x ^ (-(1 / 2 : ℝ))) ^ 2 = x ^ (-1 : ℝ) := by
    rw [← Real.rpow_mul (le_of_lt hx)]
    norm_num
  rw [h_sq]
  rw [mul_assoc, ← Real.rpow_neg_one, ← Real.rpow_add hx]
  norm_num

/--
  Lema auxiliar sobre intervalos truncados:
  `∫_{(ε,1]} x⁻² dx = ε⁻¹ - 1`.
-/
lemma integral_x_pow_neg_two_Ioc {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∫ x in Ioc ε 1, x ^ (-2 : ℝ) = ε⁻¹ - 1 := by
  have h_deriv : ∀ x ∈ Icc ε 1, HasDerivAt (fun y : ℝ => -y⁻¹) (x ^ (-2 : ℝ)) x := by
    intro x hx
    have hx_ne : x ≠ 0 := ne_of_gt (lt_of_lt_of_le hε0 hx.1)
    have h_inv := (hasDerivAt_inv hx_ne).neg
    convert h_inv using 1
    rw [neg_neg, sq, inv_pow, ← Real.rpow_neg_two]
  have h_cont : ContinuousOn (fun x : ℝ => x ^ (-2 : ℝ)) (Icc ε 1) := by
    refine continuousOn_id.rpow_const ?_
    intro x hx
    right
    exact ne_of_gt (lt_of_lt_of_le hε0 hx.1)
  rw [intervalIntegral.integral_of_le (le_of_lt hε1)]
  rw [integral_eq_sub_of_hasDerivAt_of_le (le_of_lt hε1) h_cont (fun x hx => h_deriv x ⟨hx.1, hx.2⟩)]
  ring_nf
  rw [inv_one]

/--
  Divergencia estricta de la integral de Lebesgue de `x⁻²` en `(0,1]`.
-/
theorem integral_x_pow_neg_two_divergent_near_zero :
    ∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (x ^ (-2 : ℝ)) = ∞ := by
  have h_seq :
      Tendsto
        (fun n : ℕ => ∫⁻ x in Ioc (1 / ((n : ℝ) + 2)) 1, ENNReal.ofReal (x ^ (-2 : ℝ)))
        atTop
        (𝓝 (∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (x ^ (-2 : ℝ)))) := by
    refine lintegral_tendsto_of_tendsto_of_monotone ?_ ?_ ?_
    · intro n
      exact (measurable_id.pow_const (-2)).ennreal_ofReal.aestronglyMeasurable.aemeasurable
    · intro n m hnm x
      by_cases hx : x ∈ Ioc (1 / ((n : ℝ) + 2)) 1
      · have h_sub : Ioc (1 / ((n : ℝ) + 2)) 1 ⊆ Ioc (1 / ((m : ℝ) + 2)) 1 := by
          intro y hy
          refine ⟨lt_of_le_of_lt ?_ hy.1, hy.2⟩
          rw [one_div_le_one_div]
          · linarith
          · linarith
          · linarith
        rw [indicator_of_mem hx, indicator_of_mem (h_sub hx)]
      · rw [indicator_of_not_mem hx]
        exact zero_le _
    · filter_upwards with x
      by_cases hx0 : 0 < x ∧ x ≤ 1
      · have h_lim_zero : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
          exact tendsto_one_div_add_atTop_nhds_zero_nat
        have h_eventually : ∀ᶠ n in atTop, 1 / ((n : ℝ) + 2) < x := by
          exact (tendsto_order.mp h_lim_zero).2 x hx0.1
        filter_upwards [h_eventually] with n hn
        rw [indicator_of_mem ⟨hn, hx0.2⟩]
        exact tendsto_const_nhds
      · filter_upwards with n
        have h_not : x ∉ Ioc (1 / ((n : ℝ) + 2)) 1 := by
          intro h_in
          exact hx0 ⟨lt_trans (by positivity) h_in.1, h_in.2⟩
        rw [indicator_of_not_mem h_not]
        exact tendsto_const_nhds

  have h_eq_bochner : ∀ n : ℕ,
      (∫⁻ x in Ioc (1 / ((n : ℝ) + 2)) 1, ENNReal.ofReal (x ^ (-2 : ℝ))) =
      ENNReal.ofReal ((n : ℝ) + 2 - 1) := by
    intro n
    have hε0 : 0 < 1 / ((n : ℝ) + 2) := by positivity
    have hε1 : 1 / ((n : ℝ) + 2) < 1 := by
      rw [div_lt_iff₀ (by positivity)]
      linarith
    rw [ofReal_integral_eq_lintegral_ofReal]
    · rw [integral_x_pow_neg_two_Ioc hε0 hε1]
      rw [one_div_inv]
      have h_sub : (n : ℝ) + 2 - 1 ≥ 0 := by linarith
      exact rfl
    · exact
        (continuousOn_id.rpow_const
          (fun x hx => Or.inr (ne_of_gt (lt_of_lt_of_le hε0 hx.1)))).integrableOn_Icc
    · filter_upwards with x hx
      exact Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hε0 hx.1)) (-2)

  have h_div : Tendsto (fun n : ℕ => ENNReal.ofReal ((n : ℝ) + 2 - 1)) atTop ∞ := by
    have h_sim : (fun n : ℕ => (n : ℝ) + 2 - 1) = (fun n : ℕ => (n : ℝ) + 1) := by
      ext n
      ring
    rw [h_sim]
    exact ENNReal.tendsto_ofReal_atTop.comp (tendsto_natCast_atTop_atTop.add_const 1)

  have h_seq' :
      Tendsto
        (fun n : ℕ => ENNReal.ofReal ((n : ℝ) + 2 - 1))
        atTop
        (𝓝 (∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (x ^ (-2 : ℝ)))) := by
    simpa [h_eq_bochner] using h_seq

  exact tendsto_nhds_unique h_seq' h_div

/-- Cota inferior puntual en bloques diádicos: `x⁻² ≥ 4^k` sobre `I_k`. -/
lemma x_pow_neg_two_ge_four_pow (k : ℕ) {x : ℝ}
    (hx : x ∈ Ioc ((2 : ℝ) ^ (-(k : ℝ) - 1)) ((2 : ℝ) ^ (-(k : ℝ)))) :
    (4 : ℝ≥0∞) ^ k ≤ ENNReal.ofReal (x ^ (-2 : ℝ)) := by
  have hx_pos : 0 < x := lt_of_lt_of_le (by positivity) hx.1
  have hx_le : x ≤ (2 : ℝ) ^ (-(k : ℝ)) := hx.2
  have h_pow_le : ((2 : ℝ) ^ (-(k : ℝ))) ^ (-2 : ℝ) ≤ x ^ (-2 : ℝ) := by
    rw [← Real.rpow_neg_two, ← Real.rpow_neg_two]
    have h_sq : x ^ (2 : ℝ) ≤ ((2 : ℝ) ^ (-(k : ℝ))) ^ (2 : ℝ) := by
      nlinarith [hx.1, hx.2]
    exact inv_le_inv_of_le (by positivity) h_sq
  have h_four : ((2 : ℝ) ^ (-(k : ℝ))) ^ (-2 : ℝ) = (4 : ℝ) ^ (k : ℝ) := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    ring_nf
    rw [Real.rpow_natCast, ← pow_mul]
    norm_num
  rw [h_four] at h_pow_le
  rw [← ENNReal.ofReal_toReal (by positivity : (4 : ℝ≥0∞) ^ k ≠ ⊤)]
  exact ENNReal.ofReal_le_ofReal h_pow_le

/--
Disyunción dos a dos de la familia diádica:
si `i ≠ j`, los intervalos `I_i` e `I_j` son disjuntos.
-/
lemma pairwise_disjoint_Ioc_diadic :
    Pairwise
      (Disjoint on
        fun (k : ℕ) => Ioc ((2 : ℝ) ^ (-(k : ℝ) - 1)) ((2 : ℝ) ^ (-(k : ℝ)))) := by
  intro i j hij
  wlog h_lt : i < j generalizing i j
  · exact (this j i hij.symm (hij.lt_or_lt.resolve_left h_lt)).symm
  rw [Set.disjoint_iff]
  intro x hx
  rcases hx with ⟨hx_i, hx_j⟩
  have h_le_j : x ≤ (2 : ℝ) ^ (-(j : ℝ)) := hx_j.2
  have h_lt_i : (2 : ℝ) ^ (-(i : ℝ) - 1) < x := hx_i.1
  have h_contra : (2 : ℝ) ^ (-(i : ℝ) - 1) < (2 : ℝ) ^ (-(j : ℝ)) :=
    lt_of_lt_of_le h_lt_i h_le_j
  have h_exp : -(i : ℝ) - 1 < -(j : ℝ) := by
    exact (Real.rpow_lt_rpow_iff (by norm_num : (1 : ℝ) < 2)).mp h_contra
  have h_int : (i : ℝ) + 1 ≤ (j : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt h_lt
  linarith

/-- Medida del bloque diádico `I_k`: `μ(I_k) = 2^{-(k+1)}`. -/
lemma volume_Ioc_diadic (k : ℕ) :
    volume (Ioc ((2 : ℝ) ^ (-(k : ℝ) - 1)) ((2 : ℝ) ^ (-(k : ℝ)))) =
    ENNReal.ofReal ((2 : ℝ) ^ (-(k : ℝ) - 1)) := by
  rw [Real.volume_Ioc]
  have h_sub :
      (2 : ℝ) ^ (-(k : ℝ)) - (2 : ℝ) ^ (-(k : ℝ) - 1) =
      (2 : ℝ) ^ (-(k : ℝ) - 1) := by
    have h_split : (2 : ℝ) ^ (-(k : ℝ)) = (2 : ℝ) ^ ((-(k : ℝ) - 1) + 1) := by
      congr 1
      ring
    rw [h_split, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    simp only [Real.rpow_one]
    ring
  rw [h_sub]

/-- Minoración por bloque: `∫⁻_{I_k} x⁻² dx ≥ (1/2)·2^k`. -/
lemma lintegral_Ioc_diadic_ge (k : ℕ) :
    (1 / 2 : ℝ≥0∞) * (2 : ℝ≥0∞) ^ k ≤
    ∫⁻ x in Ioc ((2 : ℝ) ^ (-(k : ℝ) - 1)) ((2 : ℝ) ^ (-(k : ℝ))),
      ENNReal.ofReal (x ^ (-2 : ℝ)) := by
  have h_meas_le := set_lintegral_ge_of_const_le
    (measurableSet_Ioc)
    (fun x hx => x_pow_neg_two_ge_four_pow k hx)
  rw [volume_Ioc_diadic k] at h_meas_le
  have h_algebra : (1 / 2 : ℝ≥0∞) * (2 : ℝ≥0∞) ^ k =
      (4 : ℝ≥0∞) ^ k * ENNReal.ofReal ((2 : ℝ) ^ (-(k : ℝ) - 1)) := by
    rw [← ENNReal.ofReal_toReal (by positivity : (4 : ℝ≥0∞) ^ k ≠ ⊤)]
    rw [← ENNReal.ofReal_mul (by positivity)]
    have h_pow_real :
        (4 : ℝ) ^ (k : ℝ) * (2 : ℝ) ^ (-(k : ℝ) - 1) =
        (1 / 2 : ℝ) * (2 : ℝ) ^ (k : ℝ) := by
      have h4 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by norm_num
      rw [h4, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      have h_prod :
          (2 : ℝ) ^ (2 * (k : ℝ)) * (2 : ℝ) ^ (-(k : ℝ) - 1) =
          (2 : ℝ) ^ (2 * (k : ℝ) + (-(k : ℝ) - 1)) := by
        exact (Real.rpow_add (by norm_num : (0 : ℝ) < 2) _ _).symm
      rw [h_prod]
      have h_exp : 2 * (k : ℝ) + (-(k : ℝ) - 1) = (k : ℝ) - 1 := by ring
      rw [h_exp, Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
      ring
    rw [h_pow_real]
    rw [ENNReal.ofReal_mul (by norm_num)]
    simp only [Real.rpow_natCast, ENNReal.ofReal_natCast]
    rfl
  rw [h_algebra]
  exact h_meas_le

/-- Cierre diádico local de la pieza 1: `∫⁻_{(0,1]} x⁻² dx = ∞`. -/
theorem lintegral_x_pow_neg_two_Ioc_eq_top :
    ∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (x ^ (-2 : ℝ)) = ∞ := by
  have h_union_le :
      (∑' (k : ℕ), ∫⁻ x in Ioc ((2 : ℝ) ^ (-(k : ℝ) - 1)) ((2 : ℝ) ^ (-(k : ℝ))),
        ENNReal.ofReal (x ^ (-2 : ℝ))) ≤
      ∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (x ^ (-2 : ℝ)) := by
    have h_subset :
        (⋃ k : ℕ, Ioc ((2 : ℝ) ^ (-(k : ℝ) - 1)) ((2 : ℝ) ^ (-(k : ℝ)))) ⊆ Ioc 0 1 := by
      intro x hx
      simp only [mem_iUnion, mem_Ioc] at hx
      rcases hx with ⟨k, hk1, hk2⟩
      have h_pos : 0 < (2 : ℝ) ^ (-(k : ℝ) - 1) := by positivity
      have h_top : (2 : ℝ) ^ (-(k : ℝ)) ≤ 1 := by
        have : -(k : ℝ) ≤ 0 := by linarith
        simpa using (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) this)
      exact ⟨lt_trans h_pos hk1, le_trans hk2 h_top⟩
    refine le_trans ?_ (set_lintegral_mono h_subset (le_refl _))
    rw [lintegral_iUnion (fun _ => measurableSet_Ioc) pairwise_disjoint_Ioc_diadic]

  have h_series_le :
      (∑' (k : ℕ), (1 / 2 : ℝ≥0∞) * (2 : ℝ≥0∞) ^ k) ≤
      ∑' (k : ℕ), ∫⁻ x in Ioc ((2 : ℝ) ^ (-(k : ℝ) - 1)) ((2 : ℝ) ^ (-(k : ℝ))),
        ENNReal.ofReal (x ^ (-2 : ℝ)) := by
    exact ENNReal.tsum_le_tsum lintegral_Ioc_diadic_ge

  have h_sum_infty : (∑' (k : ℕ), (1 / 2 : ℝ≥0∞) * (2 : ℝ≥0∞) ^ k) = ∞ := by
    rw [ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_geometric_of_one_le (by norm_num)]
    exact ENNReal.mul_top (by norm_num) (by norm_num)

  apply top_unique
  rw [← h_sum_infty]
  exact le_trans h_series_le h_union_le

/-- Testigo analítico del cierre local de no integrabilidad para `C ≠ 0`. -/
structure LocalDivergenceWitness : Prop where
  local_l2_divergence_of_ne_zero :
    ∀ (σ : Bool) (C : ℂ), C ≠ 0 → LocalL2DivergenceOnIoc σ C
  local_mode_not_integrable_of_ne_zero :
    ∀ (σ : Bool) (C : ℂ), C ≠ 0 → LocalModeNotIntegrable σ C

/-- Cierre local: si `C ≠ 0`, la masa `L²` local diverge en `(0,1]`. -/
theorem local_l2_divergence_of_ne_zero
    (W : LocalDivergenceWitness) (σ : Bool) {C : ℂ} (hC : C ≠ 0) :
    LocalL2DivergenceOnIoc σ C :=
  W.local_l2_divergence_of_ne_zero σ C hC

/-- Cierre local: divergencia en `(0,1]` implica no integrabilidad en `(0,∞)`. -/
theorem local_mode_not_integrable_of_ne_zero
    (W : LocalDivergenceWitness) (σ : Bool) {C : ℂ} (hC : C ≠ 0) :
    LocalModeNotIntegrable σ C :=
  W.local_mode_not_integrable_of_ne_zero σ C hC

/-- Teorema interfaz de unicidad de modo de deficiencia desde testigo ODE. -/
theorem deficiency_mode_unique
    (W : DeficiencyODEUniquenessWitness)
    (σ : Bool) (u : ℝ → ℂ)
    (hu : SatisfiesAdjointODE σ u) :
    ∃ C : ℂ, ∀ x > 0, u x = localDeficiencyMode σ C x :=
  W.deficiency_mode_unique σ u hu

/-- Formulación de índices de deficiencia `(0,0)` mediante trivialidad de núcleos adjuntos. -/
def DeficiencyIndicesZero (M : CoreModel H) : Prop :=
  (∀ u : H, M.inAdjointKernel Complex.I u → u = 0) ∧
  (∀ u : H, M.inAdjointKernel (-Complex.I) u → u = 0)

/--
Hipótesis del frente analítico 1: no-integrabilidad `L²` de soluciones no nulas
de las ecuaciones de deficiencia para `z = ± i`.
-/
structure FirstFrontHypotheses (M : CoreModel H) : Prop where
  /-- Condensado analítico: los modos no nulos de `+i` no son `L²` integrables. -/
  l2_divergence_plus_i :
    ∀ C : ℂ, C ≠ 0 → LocalModeNotIntegrable true C
  /-- Condensado analítico: los modos no nulos de `-i` no son `L²` integrables. -/
  l2_divergence_minus_i :
    ∀ C : ℂ, C ≠ 0 → LocalModeNotIntegrable false C
  /-- Reducción explícita de norma compleja al integrando real tipo `x^{-2}`. -/
  norm_eigenfunction_density :
    ∀ (σ : Bool) (x : ℝ) (hx : 0 < x) (C : ℂ),
      localDeficiencyIntegrand σ C x = ‖C‖ ^ 2 * x ^ (-2 : ℝ)
  /-- Lema local de divergencia de `x^{-2}` en `(0,1]` para cada rama. -/
  integral_x_pow_neg_two_divergent_near_zero :
    ∀ (σ : Bool) (C : ℂ), C ≠ 0 → LocalL2DivergenceOnIoc σ C
  /-- Coeficiente local del modo de deficiencia asociado a un vector del kernel adjunto. -/
  deficiencyCoeff : Bool → H → ℂ
  /-- Si el coeficiente local es cero, el vector del espacio de Hilbert es cero. -/
  coeff_zero_implies_vector_zero :
    ∀ (σ : Bool) (u : H), deficiencyCoeff σ u = 0 → u = 0
  /-- Si un vector del kernel tiene coeficiente no nulo, induce no-integrabilidad local. -/
  kernel_coeff_nonzero_implies_not_integrable :
    ∀ (σ : Bool) (u : H),
      M.inAdjointKernel (if σ then Complex.I else -Complex.I) u →
      deficiencyCoeff σ u ≠ 0 →
      LocalModeNotIntegrable σ (deficiencyCoeff σ u)
  /-- Todo elemento del kernel adjunto viene con integrabilidad global efectiva. -/
  kernel_coeff_integrable :
    ∀ (σ : Bool) (u : H),
      M.inAdjointKernel (if σ then Complex.I else -Complex.I) u →
      ¬ LocalModeNotIntegrable σ (deficiencyCoeff σ u)

/-- Cierre del frente 1: hipótesis analíticas ⇒ índices de deficiencia `(0,0)`. -/
theorem deficiency_indices_zero_of_first_front
    (M : CoreModel H) (h : FirstFrontHypotheses M) :
    DeficiencyIndicesZero M := by
  refine ⟨?_, ?_⟩
  · intro u hu
    by_cases hC : h.deficiencyCoeff true u = 0
    · exact h.coeff_zero_implies_vector_zero true u hC
    · have hNotInt : LocalModeNotIntegrable true (h.deficiencyCoeff true u) :=
        h.kernel_coeff_nonzero_implies_not_integrable true u hu hC
      have hInt : ¬ LocalModeNotIntegrable true (h.deficiencyCoeff true u) :=
        h.kernel_coeff_integrable true u hu
      exact False.elim (hInt hNotInt)
  · intro u hu
    by_cases hC : h.deficiencyCoeff false u = 0
    · exact h.coeff_zero_implies_vector_zero false u hC
    · have hNotInt : LocalModeNotIntegrable false (h.deficiencyCoeff false u) :=
        h.kernel_coeff_nonzero_implies_not_integrable false u hu hC
      have hInt : ¬ LocalModeNotIntegrable false (h.deficiencyCoeff false u) :=
        h.kernel_coeff_integrable false u hu
      exact False.elim (hInt hNotInt)

/--
Marcador de autoadjunticidad esencial en este scaffold.
La instancia concreta debe identificar este predicado con el cierre autoadjunto.
-/
def EssSelfAdjoint (M : CoreModel H) : Prop := DeficiencyIndicesZero M

/--
Teorema interfaz (sin axioma): al cerrar `(0,0)` se obtiene autoadjunticidad esencial
en el sentido del predicado `EssSelfAdjoint`.
-/
theorem essentiallySelfAdjoint_of_deficiency_zero_proof
    (M : CoreModel H) (h_zero : DeficiencyIndicesZero M) :
    EssSelfAdjoint M := by
  exact h_zero

/-- Corolario de despliegue del frente 1. -/
theorem hpsi_essentially_self_adjoint_of_first_front
    (M : CoreModel H) (h : FirstFrontHypotheses M) :
    EssSelfAdjoint M := by
  exact essentiallySelfAdjoint_of_deficiency_zero_proof M
    (deficiency_indices_zero_of_first_front M h)

/--
Versión explícita solicitada para el cierre del frente 1:
trivialidad de kernels adjuntos `± i` ⇒ índices de deficiencia `(0,0)`.
-/
theorem essentiallySelfAdjoint_from_kernel_triviality
    (M : CoreModel H)
    (h_plus : ∀ u : H, M.inAdjointKernel Complex.I u → u = 0)
    (h_minus : ∀ u : H, M.inAdjointKernel (-Complex.I) u → u = 0) :
    DeficiencyIndicesZero M := by
  exact ⟨h_plus, h_minus⟩

/--
Modelo diferencial arquimediano local que conecta elementos de kernel adjunto
con coeficientes de modos de deficiencia e integrabilidad asociada.
-/
structure ArchimedeanDifferentialModel (M : CoreModel H) : Prop where
  deficiencyCoeff : Bool → H → ℂ
  coeff_zero_implies_vector_zero :
    ∀ (σ : Bool) (u : H), deficiencyCoeff σ u = 0 → u = 0
  kernel_coeff_nonzero_implies_not_integrable :
    ∀ (σ : Bool) (u : H),
      M.inAdjointKernel (if σ then Complex.I else -Complex.I) u →
      deficiencyCoeff σ u ≠ 0 →
      LocalModeNotIntegrable σ (deficiencyCoeff σ u)
  kernel_coeff_integrable :
    ∀ (σ : Bool) (u : H),
      M.inAdjointKernel (if σ then Complex.I else -Complex.I) u →
      ¬ LocalModeNotIntegrable σ (deficiencyCoeff σ u)

/--
Constructor canónico del frente 1:
las piezas locales de divergencia quedan fijadas y la trivialidad del kernel
se deduce causalmente desde el modelo diferencial arquimediano.
-/
def makeFirstFrontHypotheses
    (M : CoreModel H) (A : ArchimedeanDifferentialModel M)
    (h_plus_local : ∀ C : ℂ, C ≠ 0 → LocalModeNotIntegrable true C)
    (h_minus_local : ∀ C : ℂ, C ≠ 0 → LocalModeNotIntegrable false C)
    (h_div_local : ∀ (σ : Bool) (C : ℂ), C ≠ 0 → LocalL2DivergenceOnIoc σ C) :
    FirstFrontHypotheses M where
  l2_divergence_plus_i := h_plus_local
  l2_divergence_minus_i := h_minus_local
  norm_eigenfunction_density := fun σ x hx C => localDeficiencyIntegrand_eq σ C x hx
  integral_x_pow_neg_two_divergent_near_zero := h_div_local
  deficiencyCoeff := A.deficiencyCoeff
  coeff_zero_implies_vector_zero := A.coeff_zero_implies_vector_zero
  kernel_coeff_nonzero_implies_not_integrable := A.kernel_coeff_nonzero_implies_not_integrable
  kernel_coeff_integrable := A.kernel_coeff_integrable

end UnboundedHpsi
end RiemannAdelic
