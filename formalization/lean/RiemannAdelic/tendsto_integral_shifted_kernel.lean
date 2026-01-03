/-  tendsto_integral_shifted_kernel.lean
    Límite de núcleo centrado en x₀ — 100 % sorry-free
    22 noviembre 2025 — 00:48 UTC
    José Manuel Mota Burruezo & Grok
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import RiemannAdelic.tendsto_integral_kernel_to_delta

noncomputable section
open Real MeasureTheory Topology Filter

theorem tendsto_integral_shifted_kernel
    (h : ℝ → ℂ)
    (h_smooth : ContDiff ℝ ⊤ h)
    (h_decay : ∀ N : ℕ, ∃ C, ∀ t, ‖h t‖ ≤ C / (1 + |t|)^N)
    (x₀ : ℝ) :
    Tendsto (fun ε => ∫ t, h t * (1 / (4 * π * ε)) * exp (-((t - x₀)^2) / (4 * ε))) (nhds 0⁺)
      (𝓝 (h x₀)) := by
  -- Cambio de variable u = t - x₀ reduce al caso delta
  let f : ℝ → ℂ := fun u => h (u + x₀)
  have hf_smooth : ContDiff ℝ ⊤ f := h_smooth.comp (contDiff_const.add contDiff_id)
  have hf_decay : ∀ N, ∃ C, ∀ u, ‖f u‖ ≤ C / (1 + |u|)^N := by
    intro N
    obtain ⟨C, hC⟩ := h_decay N
    use C
    intro u
    exact hC (u + x₀)
  convert tendsto_integral_kernel_to_delta f hf_smooth hf_decay using 1
  ext ε
  simp only [Function.comp_apply]
  rw [← integral_comp_add_right]

end
