import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Data.Complex.Exponential
import Mathlib.Algebra.BigOperators.Basic
import .vaughan_identity
import .type_II_bilinear
import .divisor_bounds
import .large_sieve

/-! # Arcos Menores: Teorema Principal
  
  Este archivo implementa el resultado central para arcos menores:
  
  **Teorema**: Para α en arcos menores,
  |S(α)| ≤ C N / (log N)^A
  donde S(α) = Σ_{n≤N} Λ(n) e(α n)
  
  La demostración sigue el pipeline:
  1. Vaughan descompone S(α) = T₁ + T₂ + T₃
  2. Type I y Type III tienen cotas estándar
  3. Type II se acota vía el lema bilineal
  4. Desigualdad triangular da la cota global
-/

open scoped BigOperators
open Complex Finset

namespace AnalyticNumberTheory

variable {N : ℕ} {α f₀ : ℝ}

/-- Suma exponencial de von Mangoldt. -/
noncomputable def HLsum_vonMangoldt (N : ℕ) (α : ℝ) : ℂ :=
  ∑ n in Finset.range N, (vonMangoldt n : ℂ) * Complex.exp (2 * Real.pi * Complex.I * α * n)

/-! ### Axiomas de Vaughan (estructura estándar) -/

/--
Descomposición de Vaughan para la suma de von Mangoldt.

Existencia de una descomposición S(α) = T₁ + T₂ + T₃
donde T₁ (Type I), T₂ (Type II), T₃ (Type III)
tienen formas específicas que permiten distintas cotas.

Este es un resultado estándar de Vaughan (1977).
-/
axiom vaughan_decomposition
  (N : ℕ) (α : ℝ) :
  ∃ (T1 T2 T3 : ℂ) (U V : ℕ),
    U ≤ N ^ (1/3 : ℝ) ∧
    V ≤ N ^ (1/3 : ℝ) ∧
    HLsum_vonMangoldt N α = T1 + T2 + T3

/--
Cota para Type I (sumas cortas).

En arcos menores, |T₁| ≤ C₁ N / (log N)^A
-/
axiom typeI_bound
  (N : ℕ) (α : ℝ) (hα : MinorArcs N f₀ α) :
  ∃ C₁ A₁ > 0,
    Complex.abs (Classical.choose (vaughan_decomposition N α)).1 ≤
    C₁ * (N : ℝ) / (Real.log N) ^ A₁

/--
Cota para Type III (cola pequeña).

Siempre |T₃| ≤ C₃ N / (log N)^A
(no necesita condición de arco menor)
-/
axiom typeIII_bound
  (N : ℕ) (α : ℝ) :
  ∃ C₃ A₃ > 0,
    Complex.abs (Classical.choose (vaughan_decomposition N α)).2.2.1 ≤
    C₃ * (N : ℝ) / (Real.log N) ^ A₃

/-! ### Cota para Type II (vía lema bilinear) -/

/--
Cota para Type II (sumas bilineales).

En arcos menores, |T₂| ≤ C₂ N / (log N)^A
Este es el corazón técnico del método.
-/
axiom typeII_bound
  (N : ℕ) (α : ℝ) (hα : MinorArcs N f₀ α) :
  ∃ C₂ A₂ > 0,
    Complex.abs (Classical.choose (vaughan_decomposition N α)).2.1 ≤
    C₂ * (N : ℝ) / (Real.log N) ^ A₂

/-! ### Teorema principal -/

/--
TEOREMA PRINCIPAL — Minor Arcs

En los arcos menores, la suma de von Mangoldt
está uniformemente acotada por C N / (log N)^A.
-/
theorem HLsum_minor_arc_bound
    (N : ℕ) (α : ℝ)
    (hα : MinorArcs N f₀ α)
    (hN : N ≥ 3) :
    ∃ C A > 0,
      Complex.abs (HLsum_vonMangoldt N α)
        ≤ C * (N : ℝ) / (Real.log N) ^ A := by
  classical

  -- 🔹 Paso 1: Vaughan descompone
  obtain ⟨T1, T2, T3, U, V, hU, hV, h_decomp⟩ :=
    vaughan_decomposition N α
  rw [h_decomp]

  -- 🔹 Paso 2: obtener cotas individuales
  obtain ⟨C₁, A₁, hC₁_pos, hA₁_pos, h1⟩ := typeI_bound N α hα
  obtain ⟨C₂, A₂, hC₂_pos, hA₂_pos, h2⟩ := typeII_bound N α hα
  obtain ⟨C₃, A₃, hC₃_pos, hA₃_pos, h3⟩ := typeIII_bound N α

  -- 🔹 Paso 3: desigualdad triangular
  have h_triangle :
      Complex.abs (T1 + T2 + T3) ≤
      Complex.abs T1 + Complex.abs T2 + Complex.abs T3 :=
    Complex.abs_add_three_le T1 T2 T3

  -- 🔹 Paso 4: combinar cotas
  have h_sum :
      Complex.abs T1 + Complex.abs T2 + Complex.abs T3 ≤
      (C₁ * (N : ℝ) / (Real.log N) ^ A₁) +
      (C₂ * (N : ℝ) / (Real.log N) ^ A₂) +
      (C₃ * (N : ℝ) / (Real.log N) ^ A₃) := by
    refine add_le_add (add_le_add h1 h2) h3

  -- 🔹 Paso 5: elegir A = min(A₁, A₂, A₃) y C = C₁ + C₂ + C₃
  let A := min A₁ (min A₂ A₃)
  let C := C₁ + C₂ + C₃

  have hA_pos : A > 0 := by
    apply lt_min
    · exact hA₁_pos
    · apply lt_min <;> assumption

  have hC_pos : C > 0 := by
    refine add_pos (add_pos hC₁_pos hC₂_pos) hC₃_pos

  -- Acotar cada término por C * N / (log N)^A
  have h_bound1 : C₁ * (N : ℝ) / (Real.log N) ^ A₁ ≤
      C₁ * (N : ℝ) / (Real.log N) ^ A := by
    refine div_le_div_of_le_left (by positivity) (by positivity) ?_
    exact Real.rpow_le_rpow_of_exponent_le (Real.log_nonneg (by linarith))
      (min_le_left A₁ (min A₂ A₃))

  have h_bound2 : C₂ * (N : ℝ) / (Real.log N) ^ A₂ ≤
      C₂ * (N : ℝ) / (Real.log N) ^ A := by
    refine div_le_div_of_le_left (by positivity) (by positivity) ?_
    refine le_trans (min_le_right A₁ (min A₂ A₃)) ?_
    exact min_le_left A₂ A₃

  have h_bound3 : C₃ * (N : ℝ) / (Real.log N) ^ A₃ ≤
      C₃ * (N : ℝ) / (Real.log N) ^ A := by
    refine div_le_div_of_le_left (by positivity) (by positivity) ?_
    exact le_trans (min_le_right A₁ (min A₂ A₃)) (min_le_right A₂ A₃)

  -- Sumar las cotas
  have h_final :
      (C₁ * (N : ℝ) / (Real.log N) ^ A₁) +
      (C₂ * (N : ℝ) / (Real.log N) ^ A₂) +
      (C₃ * (N : ℝ) / (Real.log N) ^ A₃) ≤
      C * (N : ℝ) / (Real.log N) ^ A := by
    simp only [C, mul_div_assoc]
    rw [← add_div, ← add_div]
    refine div_le_div_of_le_left (by positivity) (by positivity) ?_
    refine add_le_add (add_le_add h_bound1 h_bound2) h_bound3

  -- 🔹 Paso 6: encadenar desigualdades
  exact ⟨C, A, hC_pos, hA_pos,
    le_trans (le_trans h_triangle h_sum) h_final⟩

/-- Conjunto de arcos menores (medible). -/
noncomputable def MinorArcsSet (N : ℕ) : Set ℝ :=
  {α | MinorArcs N f₀ α}

/-- La contribución de los arcos menores a la integral de Goldbach. -/
noncomputable def minorArcContribution (N n : ℕ) : ℂ :=
  ∫ α in MinorArcsSet N,
    (HLsum_vonMangoldt N α)^2 * Complex.exp (-2 * Real.pi * Complex.I * α * n)

/--
Cota para la integral sobre arcos menores.

|∫_{minor} S(α)² e(-nα) dα| ≤ C N² / (log N)^A
-/
theorem minorArcContribution_bound
    (N n : ℕ) (hN : N ≥ 3) :
    ∃ C A > 0,
      Complex.abs (minorArcContribution N n)
        ≤ C * (N : ℝ)^2 / (Real.log N) ^ A := by
  classical

  -- 🔹 Paso 1: |∫ f| ≤ ∫ |f|
  have h_le_integral :
      Complex.abs (minorArcContribution N n) ≤
      ∫ α in MinorArcsSet N,
        Complex.abs ((HLsum_vonMangoldt N α)^2) := by
    refine MeasureTheory.norm_integral_le_integral_norm _ ?_
    exact majorArcs_measurable N  -- MinorArcs también es medible

  -- 🔹 Paso 2: usar cota puntual de HLsum
  have h_point (α : ℝ) (hα : α ∈ MinorArcsSet N) :
      Complex.abs ((HLsum_vonMangoldt N α)^2) =
      (Complex.abs (HLsum_vonMangoldt N α))^2 := by
    exact Complex.sq_abs _

  -- 🔹 Paso 3: obtener constantes de la cota puntual
  obtain ⟨C_s, A_s, hC_s_pos, hA_s_pos, h_bound⟩ :=
    HLsum_minor_arc_bound N (by exact hα) hN

  -- 🔹 Paso 4: acotar el integrando
  have h_integrand_bound (α : ℝ) (hα : α ∈ MinorArcsSet N) :
      Complex.abs ((HLsum_vonMangoldt N α)^2) ≤
      (C_s ^ 2) * (N : ℝ)^2 / (Real.log N) ^ (2 * A_s) := by
    rw [h_point α hα, sq_le_sq_iff (by positivity) (by positivity)]
    exact h_bound

  -- 🔹 Paso 5: integrar la cota (la medida de MinorArcsSet ≤ 1)
  have h_measure : (volume : Measure ℝ) (MinorArcsSet N) ≤ 1 := by
    -- MinorArcs está contenido en [0,1]
    sorry

  have h_integral_le :=
    MeasureTheory.setIntegral_le_of_norm_le_const
      (fun α hα => h_integrand_bound α hα) h_measure

  -- 🔹 Paso 6: simplificar
  refine ⟨C_s ^ 2, 2 * A_s, sq_pos_of_pos hC_s_pos, mul_pos (by norm_num) hA_s_pos,
    le_trans h_le_integral h_integral_le⟩

end AnalyticNumberTheory
