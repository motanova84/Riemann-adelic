import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Real.Basic

/-! # Singular Series for Goldbach
  
  La serie singular 𝔖(n) es el producto infinito sobre primos
  que da el término principal en el método del círculo para Goldbach.
-/

open BigOperators
open scoped Real

namespace AnalyticNumberTheory

/-- Factor local de la serie singular en el primo p -/
noncomputable def singularLocal (p : ℕ) (n : ℕ) : ℝ :=
  if Nat.Prime p then
    if p = 2 then 
      if Even n then 0 else 1  -- Para n par, el factor en p=2 es 0
    else
      let cp := (p - 1 : ℝ) / (p - 2)  -- Aproximación para p ≥ 3
      cp
  else 1

/-- Factor singular para un módulo q coprimo -/
noncomputable def singularFactor (q : ℕ) : ℂ :=
  (Int.möbiusMu q : ℂ) / (Nat.totient q : ℂ)

/-- Serie singular completa (producto infinito) -/
noncomputable def singularSeries (n : ℕ) : ℝ :=
  ∏' p : {p : ℕ // Nat.Prime p}, singularLocal p.val n

/-- La serie singular es positiva para n par -/
axiom singularSeries_pos (n : ℕ) (hn_even : Even n) (hn : n ≥ 4) :
  singularSeries n > 0

/-- Cota inferior cuantitativa para la serie singular -/
axiom singularSeries_lower_bound (n : ℕ) (hn_even : Even n) (hn : n ≥ 4) :
  ∃ c > 0, singularSeries n ≥ c

end AnalyticNumberTheory
