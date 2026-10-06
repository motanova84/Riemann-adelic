import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!
# QCAL-EXP-01: cota escalar, no identificación espectral

Esta definición modela un residuo escalar normalizado. Identificarlo con una
norma de operador, una fidelidad medida o una ley física requiere pruebas
adicionales. No se importan axiomas de correspondencia con ceros de zeta.
-/

namespace QCAL.Experimental

/-- Frecuencia de modulación propuesta, en Hz; no frecuencia óptica. -/
def f0 : ℝ := 141.7001

/-- Umbral propuesto para el modelo escalar normalizado. -/
def coherenceThreshold : ℝ := 0.999999

/-- Residuo escalar con constante de escala igual a uno. -/
def discrepancy (psi : ℝ) : ℝ := Real.sqrt (1 - psi)

/-- En coherencia perfecta, el residuo definido es cero. -/
theorem discrepancy_at_one : discrepancy 1 = 0 := by
  simp [discrepancy]

/-- La raíz del residuo en el umbral es exactamente una milésima. -/
theorem sqrt_threshold_residual :
    Real.sqrt (0.000001 : ℝ) = (0.001 : ℝ) := by
  have hs : (0.001 : ℝ) ^ 2 = 0.000001 := by norm_num
  rw [← hs, Real.sqrt_sq_eq_abs]
  norm_num

/-- Cota operacional del modelo, bajo las hipótesis explícitas sobre psi. -/
theorem discrepancy_at_threshold (psi : ℝ)
    (hLower : coherenceThreshold ≤ psi) (hUpper : psi ≤ 1) :
    0 ≤ 1 - psi ∧ 0 ≤ discrepancy psi ∧ discrepancy psi ≤ 0.001 := by
  constructor
  · linarith
  · constructor
    · exact Real.sqrt_nonneg _
    · have hBound : 1 - psi ≤ (0.000001 : ℝ) := by
        unfold coherenceThreshold at hLower
        linarith
      have hRoot := Real.sqrt_le_sqrt hBound
      rw [sqrt_threshold_residual] at hRoot
      exact hRoot

end QCAL.Experimental

#print axioms QCAL.Experimental.discrepancy_at_one
#print axioms QCAL.Experimental.discrepancy_at_threshold
