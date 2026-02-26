import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Algebra.BigOperators.Basic

/-! # Hardy-Littlewood Exponential Sum Decomposition
  
  Este archivo define las sumas exponenciales de Hardy-Littlewood
  con la función de von Mangoldt y sus descomposiciones.
-/

open Complex BigOperators
open scoped Real

namespace AnalyticNumberTheory

/-- Suma exponencial de Hardy-Littlewood con la función de von Mangoldt -/
noncomputable def HLsum_vonMangoldt (N : ℕ) (α : ℝ) : ℂ :=
  ∑ n in Finset.range N, (ArithmeticFunction.vonMangoldt n : ℝ) * 
    Complex.exp (2 * Real.pi * I * α * n)

/-- El cuadrado de HLsum para la integral de Goldbach -/
noncomputable def HLsum_sq (N : ℕ) (α : ℝ) : ℂ :=
  (HLsum_vonMangoldt N α) ^ 2

/-- Kernel suave para los arcos mayores -/
noncomputable def smoothKernel (N : ℕ) (β : ℝ) : ℂ :=
  if N = 0 then 0 else N * Complex.exp (-Real.pi * N ^ 2 * β ^ 2)

end AnalyticNumberTheory
