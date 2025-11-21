import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.MeasureTheory.Integral.IntervalIntegral

noncomputable section
open Real Complex Filter Topology BigOperators MeasureTheory

structure TestFunction where
  h : ℝ → ℂ
  contDiff : ContDiff ℝ ⊤ h
  rapid_decay : ∀ N : ℕ, ∃ C, ∀ t, ‖h t‖ ≤ C / (1 + |t|)^N

def spectral_side (h : TestFunction) (ε : ℝ) (N : ℕ) : ℂ :=
  ∑ n in Finset.range N, h.h (n + 1/2 + ε * Real.sin (π * n))

def geometric_kernel (t : ℝ) (ε : ℝ) : ℝ := (1/(4*π*ε)) * exp(-t^2/(4*ε))
def geometric_side (h : TestFunction) (ε : ℝ) : ℂ :=
  ∫ t, h.h t * geometric_kernel t ε

def arithmetic_side (h : TestFunction) (M : ℕ) : ℂ :=
  ∑ n in Finset.range M, if Nat.Prime (n+1) then h.h (Real.log (n+1)) else 0

theorem selberg_trace_formula_weak
    (h : TestFunction) (ε : ℝ) (N M : ℕ)
    (hε : 0 < ε) (hN : N > 1000) (hM : M > 1000) :
    ‖spectral_side h ε N - (geometric_side h ε + arithmetic_side h M)‖ < ε + 1/N + 1/M := by
  have h_spectral := sorry
  have h_geometric := sorry
  have h_arithmetic := sorry
  linarith [h_spectral, h_geometric, h_arithmetic]

end
