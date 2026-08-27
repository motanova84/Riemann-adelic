/-
  entire_eq_zero_of_eqOn_criticalLine
  Lema de identidad: una función entera que se anula en la línea crítica es idénticamente nula.

  Sustituye el `admit` de `identity_principle_exp_line` en
  formalization/lean/identity_principle_exp_type.lean
  (motanova84/Riemann-adelic).

  Mathlib: AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero
  José Manuel Mota Burruezo · Noesis · QCAL ∞³ · f₀ = 141.7001 Hz
-/

import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Basic

open Complex Filter Set
open scoped Topology

/-- La línea crítica Re(s) = 1/2 es un conjunto con puntos de acumulación en ℂ.
    Una función entera que se anula ahí es idénticamente cero. -/
lemma entire_eq_zero_of_eqOn_criticalLine
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hline : ∀ t : ℝ, f ((1 : ℂ) / 2 + I * t) = 0) :
    ∀ s, f s = 0 := by
  have hfA : AnalyticOnNhd ℂ f univ := hf.analyticOnNhd
  intro s
  -- Testigo de acumulación: 1/2 + I/n → 1/2, todos ceros, n ≥ 1.
  have hfreq : ∃ᶠ z in 𝓝[≠] ((1 : ℂ) / 2), f z = 0 := by
    rw [frequently_nhdsWithin_iff]
    intro U hU
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
    -- t = ε/2 > 0  ⇒  ‖I*t‖ = t < ε  y  1/2 + I*t ≠ 1/2
    let t : ℝ := ε / 2
    have htpos : 0 < t := by
      have : 0 < ε := hε
      dsimp [t]
      linarith
    have hne : ((1 : ℂ) / 2 + I * t) ≠ (1 : ℂ) / 2 := by
      intro h
      have : (I : ℂ) * t = 0 := by
        linear_combination h
      have : (t : ℂ) = 0 := by
        simpa [I_ne_zero] using (mul_eq_zero.mp this).resolve_left I_ne_zero
      have : t = 0 := by exact_mod_cast this
      exact htpos.ne' this
    refine ⟨(1 : ℂ) / 2 + I * t, ?_, hline t⟩
    constructor
    · apply hball
      simp [Complex.dist_eq, norm_mul, norm_I, abs_of_pos htpos]
      have : |t| = t := abs_of_pos htpos
      -- ‖I * t‖ = |t| = t = ε/2 < ε
      have : t < ε := by
        dsimp [t]
        linarith
      simpa [Complex.dist_eq, norm_mul, norm_I, abs_of_pos htpos] using this
    · exact hne
  have hz : ((1 : ℂ) / 2) ∈ univ := mem_univ _
  have hEq : EqOn f 0 univ :=
    hfA.eqOn_zero_of_preconnected_of_frequently_eq_zero
      isPreconnected_univ hz hfreq
  exact hEq (mem_univ s)

/-- Cómo cerrar `identity_principle_exp_line` una vez tienes `hline`.
    El caso Phragmén–Lindelöf del `admit` se elimina: f es entera. -/
lemma identity_principle_exp_line_of_entire
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf_vanish : ∀ t : ℝ, f ((1 : ℂ) / 2 + I * t) = 0) :
    ∀ s, f s = 0 :=
  entire_eq_zero_of_eqOn_criticalLine hf hf_vanish
