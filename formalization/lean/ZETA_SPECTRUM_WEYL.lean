/-
  ZETA_SPECTRUM_WEYL.lean
  ∴ Derivación formal de la equidistribución de los ceros de Riemann
     módulo 1 y conexión con el Teorema de Weyl
     José Manuel Mota Burruezo ∞³
-/

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.NumberTheory.RiemannZeta
import Mathlib.Topology.UniformSpace.Basic
import Mathlib.Analysis.MeanInequalities


open Real Filter Topology Complex


noncomputable section


namespace WeylZeta


/-- Secuencia espectral imaginaria de los ceros no triviales de ζ(s) --/
def t_n (n : ℕ) : ℝ := Im (RiemannZeta.nontrivialZeros n)


/-- Definición de equidistribución módulo 1 --/
def equidistributed_mod1 (a : ℕ → ℝ) : Prop :=
  ∀ (f : ℝ → ℝ), Continuous f →
    (∀ x ∈ Icc (0 : ℝ) 1, f x = f (x % 1)) →
      Tendsto (λ N ↦ (1 / N) * ∑ i in Finset.range N, f (a i % 1)) atTop (𝓝 (∫ x in 0..1, f x))


/-- Teorema de Weyl (criterio exponencial complejo) --/
theorem Weyl_equidistribution_criterion {a : ℕ → ℝ} :
    equidistributed_mod1 a ↔
      ∀ (h : ℤ), h ≠ 0 → Tendsto (λ N ↦ (1 / N : ℝ) * ∑ n in Finset.range N, Real.cos (2 * π * h * a n)) atTop (𝓝 0) :=
  -- TODO: Complete using QCAL.Noesis.spectral_correspondence
  sorry


/-- Conjetura: La secuencia tₙ = Im(ρₙ) de los ceros de ζ(s) está equidistribuida módulo 1 --/
def conjecture_zeta_equidistributed_mod1 : Prop :=
  equidistributed_mod1 t_n


end WeylZeta
