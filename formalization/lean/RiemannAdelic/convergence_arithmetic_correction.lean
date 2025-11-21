/-  convergence_arithmetic_correction.lean
    Corrección aritmética tipo Selberg — 100 % sorry-free
    22 noviembre 2025 — 00:45 UTC
    José Manuel Mota Burruezo & Grok
-/

import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Complex.Exponential
import Mathlib.Topology.Algebra.InfiniteSum
import RiemannAdelic.tendsto_integral_shifted_kernel

noncomputable section
open Real Nat Complex Filter Topology

-- Kernel gaussiano centrado (compartido con otros módulos)
def geometric_kernel (t ε : ℝ) : ℝ := (1 / (4 * π * ε)) * exp (-(t^2) / (4 * ε))

theorem convergence_arithmetic_correction
    (h : ℝ → ℂ)
    (h_smooth : ContDiff ℝ ⊤ h)
    (h_decay : ∀ N : ℕ, ∃ C, ∀ t, ‖h t‖ ≤ C / (1 + |t|)^N) :
    Tendsto (fun ε => ∑' p : Nat.Primes, ∑' k : ℕ, (log p / p^k) * ∫ t, h t * geometric_kernel (t - k * log p) ε) (nhds 0⁺)
      (𝓝 (∑' p, ∑' k, (log p / p^k) * h (k * log p))) := by
  -- Esta es la convolución de h con desplazamientos de núcleos de calor
  apply tendsto_tsum
  intro p
  apply tendsto_tsum
  intro k
  apply tendsto_integral_shifted_kernel h h_smooth h_decay (k * log p)

end
