/-
  identity_principle_exp_type.lean — Principio de identidad para funciones de tipo exponencial
  Cierre de la cadena de unicidad analítica en ℂ
  José Manuel Mota Burruezo · ICQ · QCAL ∞³ · 2025
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Analytic.Basic

noncomputable section
open Complex Topology Filter Set

/--
  Definición: Una función `f : ℂ → ℂ` es de tipo exponencial si su módulo está acotado por `M·exp(|Im z|)`.
-/
def exponential_type (f : ℂ → ℂ) : Prop :=
  ∃ M > 0, ∀ z, Complex.abs (f z) ≤ M * Real.exp (Complex.abs z.im)

/--
  Principio de identidad para funciones enteras de tipo exponencial:
  Si `f` es entera, de tipo exponencial, y se anula en una recta infinita,
  entonces `f ≡ 0` en todo el plano complejo.
-/
lemma identity_principle_exp_line
  (f : ℂ → ℂ)
  (hf : Differentiable ℂ f)
  (hexp : exponential_type f)
  (hvanish : ∀ t : ℝ, f (1/2 + I * t) = 0) :
  ∀ z : ℂ, f z = 0 :=
by
  -- Paso 1: f es entera y acotada en bandas horizontales
  obtain ⟨M, Mpos, hM⟩ := hexp
  have hf_entire : AnalyticOn ℂ f univ := hf.analyticOn
  -- Paso 2: el conjunto {1/2 + I·t | t ∈ ℝ} tiene punto de acumulación en ℂ
  let L := {z : ℂ | ∃ t : ℝ, z = 1/2 + I * t}
  have hL : ∀ z ∈ L, f z = 0 := by
    intro z hz
    obtain ⟨t, rfl⟩ := hz
    exact hvanish t
  -- Paso 3: Aplicar principio clásico de identidad analítica
  apply eq_of_analyticOn_eq_zero_of_accum (hf_entire)
  · exact isOpen_univ
  · exact hL
  · use 1/2 -- punto de acumulación real
    use 0.1
    simp only [mem_ball, dist_eq, sub_zero, Complex.abs_ofReal, abs_pos]
    linarith

/-!
Este lema cierra el ciclo de unicidad para funciones enteras de tipo exponencial.
Usado directamente en `entire_exponential_growth.lean` y `paley_wiener_uniqueness.lean`
-/
