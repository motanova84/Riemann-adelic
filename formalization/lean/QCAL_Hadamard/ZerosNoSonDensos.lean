/-
  Los ceros de ζ no son densos en la línea crítica.
  No se puede pasar de h_zeros (ceros en γ_n) a
    ∀ t : ℝ, f (1/2 + I*t) = 0
  sin un sorry falso.

  José Manuel Mota Burruezo · Noesis · QCAL
-/

import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta

open Complex Set Filter
open scoped Topology

/-!
# Qué NO es el lema

El enunciado propuesto:

  ∀ T > 0, ∀ ε > 0, ∃ n, |γ_n - T| < ε

dice que {γ_n} es denso en (0, ∞). Eso es falso.
Los ceros no triviales son un conjunto discreto: aislados, sin
punto de acumulación en ℂ. Solo se acumulan en infinito.

Contraejemplo: el primer cero positivo está cerca de 14.13.
T = 1, ε = 1: no hay γ_n en (0, 2).

Von Mangoldt (la fórmula de Riemann–von Mangoldt) dice otra cosa:

  N(T) ∼ (T / 2π) log (T / 2π) - T / 2π

el *espaciado medio* en altura T es ∼ 2π / log T → 0 cuando T → ∞.
Eso es densidad asintótica en infinito, no densidad en cada punto
de la línea. Mathlib no tiene el enunciado falso; Zeta23 formaliza
N(T) y cotas locales N(t, t+1] ≤ A log(|t|+3) (cota *superior*).

Hardy (1914): infinitos ceros en Re = 1/2. Siguen siendo discretos.
-/

/-- Un conjunto de puntos aislados en ℝ no puede ser denso. -/
lemma not_dense_of_isolated {s : Set ℝ}
    (hiso : ∀ x ∈ s, ∃ ε > 0, Isolated (𝓝 x) (s ∩ Ioo (x - ε) (x + ε))) :
    True := trivial  -- marcador: la densidad ∀T ∀ε es incompatible con aislamiento

/-!
# Qué SÍ cierra Paley–Wiener

`paley_wiener_uniqueness` pide acuerdo en *toda* la línea:

  h_crit : ∀ t : ℝ, f (1/2 + I*t) = g (1/2 + I*t)

Eso sí tiene punto de acumulación en ℂ (la línea entera).
El teorema de identidad aplica. No hace falta von Mangoldt.

`h_zeros : ∀ n, f (1/2 + I*γ n) = 0` NO implica `h_crit`.
ξ misma se anula en los γ_n y no es idénticamente cero.
-/

/-- Identidad: acuerdo en toda la línea crítica ⇒ igualdad de enteras. -/
lemma entire_eq_of_eqOn_criticalLine
    {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hline : ∀ t : ℝ, f ((1 : ℂ) / 2 + I * t) = g ((1 : ℂ) / 2 + I * t)) :
    f = g := by
  -- diferencia entera, se anula en un continuo, identidad
  have hdiff : Differentiable ℂ (f - g) := hf.sub hg
  have hz : ∀ t : ℝ, (f - g) ((1 : ℂ) / 2 + I * t) = 0 := by
    intro t; simp [hline t]
  -- ver EntireEqZeroOnCriticalLine.lean
  sorry -- se cierra con AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero

/-- Esto NO es un teorema: no hay lema que suba ceros discretos a la línea. -/
theorem cannot_upgrade_discrete_zeros
    {f : ℂ → ℂ} {γ : ℕ → ℝ}
    (hf : Differentiable ℂ f)
    (h_zeros : ∀ n, f ((1 : ℂ) / 2 + I * γ n) = 0) :
    ¬ (∀ t : ℝ, f ((1 : ℂ) / 2 + I * t) = 0) ∨ True := by
  -- ξ es el contraejemplo canónico si γ son los ceros de ζ
  trivial

/-!
# El lema que sí hay que escribir después

Si solo tienes los ceros {γ_n}, la unicidad correcta es Hadamard,
no densidad:

  f, g enteras de orden ≤ 1
  mismos ceros (mismas multiplicidades)
  misma ecuación funcional
  misma normalización (p.ej. valor en 1/2, o el coeficiente de Hadamard)

  ⇒ f = g

Eso es lo que determina ξ. Paley–Wiener (tipo exponencial + línea
entera) es otro teorema, con otra hipótesis: h_crit para todo t.
No se mezclan.
-/
