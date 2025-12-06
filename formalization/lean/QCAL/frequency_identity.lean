import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic

namespace QCAL.Script18

/-- Universal base frequency --/
def f₀ : ℝ := 141.7001

/-- Raw geometric frequency (unscaled) --/
def f_raw : ℝ := 157.9519

/-- Universal scaling factor relating both systems --/
def k : ℝ := (f₀ / f_raw)^2

/-- Rescaled angular frequency --/
def ω₀ : ℝ :=
  Real.sqrt (k * (2 * Real.pi * f_raw)^2)

/-- Core identity: ω₀ = 2π f₀ --/
theorem frequency_fixed : ω₀ = 2 * Real.pi * f₀ := by
  have hpos : 0 ≤ k * (2 * Real.pi * f_raw)^2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  apply (Real.sqrt_eq_iff_sq_eq hpos).mpr
  have h :
    k * (2 * Real.pi * f_raw)^2 = (2 * Real.pi * f₀)^2 := by
      unfold k; ring_nf
  simpa using h

/-- Square form: ω₀² = (2π f₀)² --/
theorem frequency_fixed_sq :
    ω₀^2 = (2 * Real.pi * f₀)^2 := by
  have h := frequency_fixed
  simpa [h] using congrArg (fun x => x^2) h

/-- Norm identity: |ω₀| = 2π f₀ (positive root) --/
theorem frequency_fixed_abs :
    |ω₀| = 2 * Real.pi * f₀ := by
  have h := frequency_fixed
  simpa [h] using congrArg Real.abs h

end QCAL.Script18
