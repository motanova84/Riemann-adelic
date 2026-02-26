import RiemannAdelic.core.analytic.hlsum_decompose
import Mathlib.Analysis.Complex.Basic

/-! # Minor Arcs
  
  Este archivo define los arcos menores y proporciona la cota de potencia
  que hace que su contribución sea negligible.
-/

open Complex
open scoped Real

namespace AnalyticNumberTheory

/-- Arcos menores: complemento de los arcos mayores -/
def MinorArcs (N : ℕ) : Set ℝ :=
  {α : ℝ | ∀ q ≤ ⌊Real.log N⌋, ∀ a < q, 
    Nat.gcd a q = 1 → Real.dist α (a / q) > (Real.log N)⁻¹}

/-- Contribución de arcos menores (axiom de Vaughan + Large Sieve) -/
axiom minorArc_power_saving (N : ℕ) (A : ℝ) (hA : A > 0) :
  ∃ C > 0, ∀ α ∈ MinorArcs N,
    Complex.abs (HLsum_vonMangoldt N α) ≤ C * (N : ℝ) / (Real.log N) ^ A

/-- La integral sobre arcos menores es negligible -/
axiom minorArcContribution_negligible (n N : ℕ) (hN : N ≥ n) :
  ∃ C > 0,
    Complex.abs (∫ α in MinorArcs N, (HLsum_vonMangoldt N α) ^ 2 *
      Complex.exp (-2 * Real.pi * I * α * n))
    ≤ C * (N : ℝ) ^ 2 / (Real.log N) ^ 10

end AnalyticNumberTheory
