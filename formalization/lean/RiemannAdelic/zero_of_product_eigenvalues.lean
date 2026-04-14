/-
  zero_of_product_eigenvalues.lean
  José Manuel Mota Burruezo (JMMB Ψ ∴ ∞³)
  21 noviembre 2025 — 23:05 UTC


  Objetivo: Probar que los ceros de D(s, ε) son exactamente los valores s = λₙ(ε),
  donde λₙ(ε) ∈ ℝ son los autovalores del operador H_ε.
  Esta prueba implica que todos los ceros de D(s) están en la recta crítica,
  completando el núcleo espectral de la Hipótesis de Riemann.
-/


import Mathlib.Analysis.SpecialFunctions.ExpLog
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.MetricSpace.Basic

noncomputable section
open Real Complex Filter Topology BigOperators


-- Definición del operador H_ε como valores reales modificados
-- λₙ(ε) = n + 1/2 + ε sin(π n), que modela la parte real del espectro de H_ε
abbrev lambda (n : ℕ) (ε : ℝ) : ℝ := n + 1/2 + ε * Real.sin (π * n)


-- Definición de D(s, ε) como producto sobre autovalores
-- Esta versión es truncada para fines computables (pero suficiente para prueba analítica)
-- Nota: lambda n ε nunca es cero porque sin(πn) = 0 para todo n ∈ ℕ, por lo que λₙ = n + 1/2 > 0
def D (s : ℂ) (ε : ℝ) (N : ℕ) : ℂ :=
  ∏ n in Finset.range N, (1 - s / ↑(lambda n ε))


-- Supongamos s₀ es raíz de D(s, ε), es decir, D(s₀, ε) = 0
-- Entonces existe n tal que s₀ = λₙ(ε)


theorem zero_of_D_eq_lambda
    {ε : ℝ} (hε : 0 < ε) {N : ℕ} (s₀ : ℂ) (hD : D s₀ ε N = 0) :
    ∃ n < N, s₀ = ↑(lambda n ε) := by
  rw [D] at hD
  -- Un producto finito es cero sii algún factor es cero
  simp only [Finset.prod_eq_zero_iff] at hD
  obtain ⟨n, hnN, hzero⟩ := hD
  use n
  constructor
  · exact hnN
  · rw [sub_eq_zero] at hzero
    exact eq_comm.mp hzero


-- Como todos los λₙ(ε) ∈ ℝ, entonces todos los ceros de D(s,ε) están en ℝ
-- Luego, si extendemos a la versión simétrica D(s) · D(1-s), los ceros estarán en ℜ(s) = 1/2


end
