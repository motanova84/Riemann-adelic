/-
  GAP 1 v3.2.3 — log_holomorphic_of_entire_never_zero

  Paso A: primitiva F de 1/z en ball w ρ (ρ < ‖w‖).
          G(z) = z exp(-F z), G' = 0 ⇒ G constante.
          L(z) = F(z) - F(w) + log w  ⇒  exp(L z) = z.
  Paso B: φ continua, exp∘φ = h. Localmente φ = L∘h + 2πi n.

  Mathlib real:
    DifferentiableOn.isExactOn_ball
    exists_continuousOn_eqOn_exp_comp
    Complex.exp_eq_exp_iff_exists_int
    Complex.exp_log

  José Manuel Mota Burruezo · Noesis · QCAL ∞³
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Connected.Basic

noncomputable section
open Complex Metric Set
open scoped Topology

/-! ### Paso A — log de id en un disco 0-libre -/

lemma zero_not_mem_ball {w : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hρw : ρ < ‖w‖) :
    (0 : ℂ) ∉ ball w ρ := by
  intro h
  have : dist 0 w < ρ := h
  simp [dist_zero_left] at this
  exact lt_asymm this hρw

lemma inv_differentiableOn_ball {w : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hρw : ρ < ‖w‖) :
    DifferentiableOn ℂ (fun z : ℂ => z⁻¹) (ball w ρ) := by
  intro z hz
  have hz0 : z ≠ 0 := fun h => (zero_not_mem_ball hρ hρw) (h ▸ hz)
  exact (differentiableAt_inv hz0).differentiableWithinAt

theorem exists_primitive_inv_on_ball {w : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hρw : ρ < ‖w‖) :
    ∃ F : ℂ → ℂ, ∀ z ∈ ball w ρ, HasDerivAt F z⁻¹ z := by
  have hEx : IsExactOn (fun z : ℂ => z⁻¹) (ball w ρ) :=
    (inv_differentiableOn_ball hρ hρw).isExactOn_ball
  exact hEx

/-- G(z) = z exp(-F z). Si F' = 1/z, G' = 0. -/
lemma hasDerivAt_z_mul_exp_neg {F : ℂ → ℂ} {z : ℂ}
    (hz : z ≠ 0) (hF : HasDerivAt F z⁻¹ z) :
    HasDerivAt (fun ζ => ζ * exp (-F ζ)) 0 z := by
  have h_id : HasDerivAt (fun ζ : ℂ => ζ) 1 z := hasDerivAt_id z
  have h_negF : HasDerivAt (fun ζ => -F ζ) (-z⁻¹) z := hF.neg
  have h_exp : HasDerivAt (fun ζ => exp (-F ζ)) (exp (-F z) * (-z⁻¹)) z :=
    (hasDerivAt_exp (-F z)).comp z h_negF
  have := h_id.mul h_exp
  convert this using 1
  field_simp [hz]
  ring

/-- Log holomorfo de `id` en `ball w ρ`. Rama: L(z) = F(z) − F(w) + log w. -/
theorem exists_holomorphic_log_on_ball {w : ℂ} {ρ : ℝ}
    (hw : w ≠ 0) (hρ : 0 < ρ) (hρw : ρ < ‖w‖) :
    ∃ L : ℂ → ℂ,
      (∀ z ∈ ball w ρ, DifferentiableAt ℂ L z) ∧
      ∀ z ∈ ball w ρ, exp (L z) = z := by
  obtain ⟨F, hF⟩ := exists_primitive_inv_on_ball hρ hρw
  let G : ℂ → ℂ := fun ζ => ζ * exp (-F ζ)
  have hG0 : ∀ z ∈ ball w ρ, HasDerivAt G 0 z := by
    intro z hz
    have hz0 : z ≠ 0 := fun h => (zero_not_mem_ball hρ hρw) (h ▸ hz)
    exact hasDerivAt_z_mul_exp_neg hz0 (hF z hz)
  have hwmem : w ∈ ball w ρ := mem_ball_self hρ
  -- disco convexo + G' = 0 ⇒ G constante = G w
  have hGconst : ∀ z ∈ ball w ρ, G z = G w := by
    intro z hz
    -- `intervalIntegral.integral_eq_sub_of_hasDerivAt` en el segmento [w,z] ⊂ ball
    -- o `Convex.is_const_of_fderiv_eq_zero`
    sorry
  let L : ℂ → ℂ := fun z => F z - F w + log w
  refine ⟨L, ?diff, ?exp⟩
  · intro z hz
    exact ((hF z hz).sub (hasDerivAt_const z (F w))).add
      (hasDerivAt_const z (log w)) |>.differentiableAt
  · intro z hz
    have hz0 : z ≠ 0 := fun h => (zero_not_mem_ball hρ hρw) (h ▸ hz)
    have hGz : z * exp (-F z) = w * exp (-F w) := hGconst z hz
    -- exp(F z − F w) = z/w
    have hratio : exp (F z - F w) = z / w := by
      have := congrArg (fun t => t * exp (F z) * exp (F w)) hGz
      -- z exp(-F z) exp(F z) exp(F w) = w exp(-F w) exp(F z) exp(F w)
      -- z exp(F w) = w exp(F z)
      sorry -- anillo + exp_neg / exp_sub
    calc
      exp (L z) = exp (F z - F w) * exp (log w) := by
        simp [L, exp_add, sub_eq_add_neg]
      _ = (z / w) * w := by rw [hratio, exp_log hw]
      _ = z := by field_simp [hw]

/-! ### Paso B — de log continuo global a holomorfo -/

theorem exists_continuous_log_univ {h : ℂ → ℂ}
    (hhc : Continuous h) (hne : ∀ z, h z ≠ 0) :
    ∃ φ : ℂ → ℂ, Continuous φ ∧ ∀ z, exp (φ z) = h z := by
  have h0 : (0 : ℂ) ∉ h '' (univ : Set ℂ) := by
    rintro ⟨z, _, rfl⟩; exact hne z rfl
  obtain ⟨φ, hφc, hφ⟩ :=
    exists_continuousOn_eqOn_exp_comp isSimplyConnected_univ isOpen_univ
      hhc.continuousOn h0
  exact ⟨φ, hφc.continuous_of_continuousOn_univ, fun z => hφ (mem_univ z)⟩

theorem log_holomorphic_of_entire_never_zero {h : ℂ → ℂ}
    (hh : Differentiable ℂ h) (hne : ∀ z, h z ≠ 0) :
    ∃ φ : ℂ → ℂ, Differentiable ℂ φ ∧ ∀ z, exp (φ z) = h z := by
  obtain ⟨φ, hφc, hexp⟩ := exists_continuous_log_univ hh.continuous hne
  refine ⟨φ, ?hol, hexp⟩
  intro z₀
  have hw : h z₀ ≠ 0 := hne z₀
  let ρ : ℝ := ‖h z₀‖ / 2
  have hρ : 0 < ρ := half_pos (norm_pos_iff.mpr hw)
  have hρw : ρ < ‖h z₀‖ := half_lt_self (norm_pos_iff.mpr hw)
  obtain ⟨L, hLd, hLexp⟩ := exists_holomorphic_log_on_ball hw hρ hρw
  -- ε-δ: h continua ⇒ h(ball z₀ δ) ⊂ ball (h z₀) ρ
  obtain ⟨δ, hδ, hδball⟩ : ∃ δ > 0, ∀ z, dist z z₀ < δ → dist (h z) (h z₀) < ρ := by
    have hcont := hh.continuous.continuousAt (x := z₀)
    exact (Metric.continuousAt_iff.mp hcont) ρ hρ
  have hδpos : 0 < δ := hδ
  -- En ball z₀ δ: exp(φ z) = exp(L (h z)) ⇒ diferencia 2πiℤ, continua ⇒ constante
  have hconst : ∃ n : ℤ, ∀ z ∈ ball z₀ δ,
      φ z = L (h z) + n * (2 * π * I) := by
    -- `exp_eq_exp_iff_exists_int` + imagen conexa ⊂ 2πiℤ discreto
    sorry
  obtain ⟨n, hn⟩ := hconst
  -- localmente φ = L ∘ h + const, holomorfa en z₀
  have : DifferentiableAt ℂ φ z₀ := by
    -- `HasDerivAt.comp` de L y h, más constante
    sorry
  exact this

/-
  Glue pendiente de lake (nombres reales):
  - G constante: FTC en el segmento, disco convexo
  - anillo exp_neg / exp_sub para z/w
  - 2πiℤ constante: exp_eq_exp_iff_exists_int
  - HasDerivAt.comp en z₀
-/

end
