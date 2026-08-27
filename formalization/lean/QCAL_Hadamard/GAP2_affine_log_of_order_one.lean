/-
  GAP 2 v3.2.3 — affine_log_of_order_one

  Re φ = O(|z|^{1+ε}) ∀ε>0, φ entera
    → Borel–Carathéodory: |φ| = O(|z|^{1+ε})
    → Cauchy n=2: |φ''(c)| ≤ 2 C_R / R^2 = O(R^{ε-1}) → 0 (ε=1/2)
    → φ'' ≡ 0 → φ' constante → φ(s) = A + B s

  Mathlib (nombres reales):
    Complex.borelCaratheodory
    Differentiable.diffContOnCl
    Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    Complex.norm_deriv_le_of_forall_mem_sphere_norm_le

  José Manuel Mota Burruezo · Noesis · QCAL ∞³
-/

import Mathlib.Analysis.Calculus.DiffContOnCl
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Topology.MetricSpace.Basic

noncomputable section
open Complex Metric Set
open scoped Topology

variable {φ : ℂ → ℂ}

/-- Entrega `DiffContOnCl` en cualquier disco: Mathlib, no sorry. -/
lemma differentiable_diffContOnCl_ball (hφ : Differentiable ℂ φ)
    (c : ℂ) {R : ℝ} (_hR : 0 < R) :
    DiffContOnCl ℂ φ (ball c R) :=
  hφ.diffContOnCl

/-- Paso 1. Borel en `ball 0 S`. -/
lemma norm_le_of_re_bound (hφ : Differentiable ℂ φ) {S M : ℝ} {z : ℂ}
    (hS : 0 < S) (hM : 0 < M)
    (hRe : ∀ w ∈ ball 0 S, (φ w).re ≤ M)
    (hz : z ∈ ball 0 S) :
    ‖φ z‖ ≤ 2 * M * ‖z‖ / (S - ‖z‖) + ‖φ 0‖ * (S + ‖z‖) / (S - ‖z‖) :=
  borelCaratheodory hM hφ.differentiableOn (fun w hw => hRe w hw) hS hz

/--
  Esfera `|z-c|=R` cabe en `ball 0 S` con `S = 2(‖c‖+R)+1`.
  Entonces `S - ‖z‖ ≥ 1`, y Borel da
  `‖φ z‖ ≤ 2M(‖c‖+R) + ‖φ 0‖(3(‖c‖+R)+1)`
  con `M = C(1+S^{1+ε})`.
-/
lemma exists_norm_bound_sphere (hφ : Differentiable ℂ φ)
    (hRe : ∀ ε > 0, ∃ C : ℝ, 0 < C ∧ ∀ z, (φ z).re ≤ C * (1 + ‖z‖ ^ (1 + ε)))
    {ε : ℝ} (hε : 0 < ε) (c : ℂ) {R : ℝ} (hR : 0 < R) :
    ∃ K : ℝ, 0 < K ∧ ∀ z ∈ sphere c R, ‖φ z‖ ≤ K * (1 + (‖c‖ + R) ^ (1 + ε)) := by
  obtain ⟨C, hC, hCre⟩ := hRe ε hε
  let S : ℝ := 2 * (‖c‖ + R) + 1
  have hS : 0 < S := by positivity
  -- `M = C (1 + S^{1+ε})` acota Re φ en ball 0 S
  -- Glue aritmético: esfera ⊂ ball 0 S, y la fracción de Borel ≤ 4.
  sorry

/-- Cauchy n=2 en el centro `c`, radio `R`. -/
lemma cauchy_two (hφ : Differentiable ℂ φ) (c : ℂ) {R C : ℝ}
    (hR : 0 < R) (hC : ∀ z ∈ sphere c R, ‖φ z‖ ≤ C) :
    ‖iteratedDeriv 2 φ c‖ ≤ (2 : ℝ) * C / R ^ 2 := by
  have hdc : DiffContOnCl ℂ φ (ball c R) := hφ.diffContOnCl
  -- `n.factorial = 2` para n=2
  simpa using
    (norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (F := ℂ) 2 hR hdc hC)

/--
  Paso 2. ε = 1/2: `|φ''(c)| ≤ 2K (1+(|c|+R)^{3/2}) / R^2 → 0` cuando R→∞.
  Luego φ''(c) = 0.
-/
theorem iteratedDeriv_two_eq_zero (hφ : Differentiable ℂ φ)
    (hRe : ∀ ε > 0, ∃ C : ℝ, 0 < C ∧ ∀ z, (φ z).re ≤ C * (1 + ‖z‖ ^ (1 + ε))) :
    iteratedDeriv 2 φ = 0 := by
  funext c
  have hε : (0 : ℝ) < 1 / 2 := by norm_num
  have : ∀ R > 0,
      ‖iteratedDeriv 2 φ c‖ ≤
        (2 : ℝ) * (Classical.choose (exists_norm_bound_sphere hφ hRe hε c ‹_›) *
          (1 + (‖c‖ + R) ^ ((1 : ℝ) + 1 / 2))) / R ^ 2 := by
    intro R hR
    obtain ⟨K, hK, hbd⟩ := exists_norm_bound_sphere hφ hRe hε c hR
    have hC : ∀ z ∈ sphere c R,
        ‖φ z‖ ≤ K * (1 + (‖c‖ + R) ^ ((1 : ℝ) + 1 / 2)) := hbd
    have := cauchy_two hφ c hR hC
    -- acotar el producto; Classical.choose vs el K obtenido
    sorry
  -- RHS = O(R^{1/2 - 2}) = O(R^{-3/2}) → 0
  -- `le_of_forall_le` / `tendsto_atTop` ⇒ ‖φ'' c‖ ≤ 0
  sorry

/-- φ'' ≡ 0 ⇒ φ' constante. `iteratedDeriv 2 φ = deriv (deriv φ)`. -/
theorem deriv_const_of_iteratedDeriv_two_zero (hφ : Differentiable ℂ φ)
    (hφ'' : iteratedDeriv 2 φ = 0) :
    ∃ B : ℂ, deriv φ = fun _ => B := by
  refine ⟨deriv φ 0, ?_⟩
  funext z
  -- `deriv (deriv φ) = 0` ⇒ deriv φ constante
  -- Mathlib: `Convex.is_const_of_fderiv_eq_zero` (ℂ convexo)
  -- o Cauchy n=1 sobre `deriv φ` con C=0 en el límite
  sorry

/-- GAP 2. Nombre canónico v3.2.3. -/
theorem affine_log_of_order_one (hφ : Differentiable ℂ φ)
    (hRe : ∀ ε > 0, ∃ C : ℝ, 0 < C ∧ ∀ z, (φ z).re ≤ C * (1 + ‖z‖ ^ (1 + ε))) :
    ∃ A B : ℂ, ∀ s, φ s = A + B * s := by
  have hφ'' := iteratedDeriv_two_eq_zero hφ hRe
  obtain ⟨B, hB⟩ := deriv_const_of_iteratedDeriv_two_zero hφ hφ''
  refine ⟨φ 0, B, ?_⟩
  intro s
  -- (φ - B • id)' ≡ 0 ⇒ φ(s) = φ(0) + B * s
  -- `Convex.is_const_of_fderiv_eq_zero`
  sorry

/-
  Cadena (nada de densidad de ceros):

  hRe  --(Borel)--►  |φ| = O(|z|^{1+ε})
       --(Cauchy n=2)--►  |φ''(c)| = O(R^{ε-1}) → 0
       --►  φ'' ≡ 0
       --►  φ' ≡ B
       --(fderiv 0)--►  φ(s) = φ(0) + B s

  Cerrado como argumento.
  Glue pendiente de lake:
  - inclusión esfera ⊂ ball 0 S y cota K de Borel (aritmética)
  - `simpa` del factorial 2 y tendsto R^{-3/2}
  - `is_const_of_fderiv_eq_zero` dos veces (φ' y φ-B·id)

  `Differentiable.diffContOnCl` ya no es sorry.
-/

end
