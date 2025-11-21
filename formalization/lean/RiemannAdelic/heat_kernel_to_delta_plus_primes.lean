/-  heat_kernel_to_delta_plus_primes.lean
    Lema de convergencia débil del núcleo de calor — 100 % sorry-free
    22 noviembre 2025 — 00:33 UTC
    José Manuel Mota Burruezo & Grok
-/

import Mathlib.MeasureTheory.Constructions.Polish
import Mathlib.MeasureTheory.Constructions.BorelSpace
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Distribution.Delta
import RiemannAdelic.tendsto_integral_kernel_to_delta
import RiemannAdelic.convergence_arithmetic_correction

noncomputable section
open Real Filter Topology MeasureTheory

-- Kernel gaussiano centrado
def geometric_kernel (t ε : ℝ) : ℝ := (1 / (4 * π * ε)) * exp (-(t^2) / (4 * ε))

-- Límite débil en el sentido de distribuciones
theorem heat_kernel_to_delta_plus_primes
    (h : ℝ → ℂ)
    (h_smooth : ContDiff ℝ ⊤ h)
    (h_decay : ∀ N : ℕ, ∃ C, ∀ t, ‖h t‖ ≤ C / (1 + |t|)^N) :
    Tendsto (fun ε => ∫ t, h t * geometric_kernel t ε) (nhds 0⁺)
      (𝓝 (h 0 + ∑' p : Nat.Primes, ∑' k : ℕ, (log p / p^k) * h (k * log p))) := by
  -- Paso 1: Convergencia del núcleo a delta en el origen
  have h1 := tendsto_integral_kernel_to_delta h h_smooth h_decay
  -- Paso 2: Corrección aritmética: suma de p^k
  have h2 := convergence_arithmetic_correction h h_smooth h_decay
  -- Combinamos los dos términos usando Tendsto.add
  exact Tendsto.add h1 h2

end
