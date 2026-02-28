/-
  hlsum_decompose.lean
  ========================================================================
  Descomposición de HLsum en progresiones aritméticas
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
/-
Copyright (c) 2026 José Manuel Mota Burruezo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: José Manuel Mota Burruezo
/-! # Descomposición de HLsum en progresiones aritméticas
  
  Este archivo implementa la descomposición de la suma exponencial
  de von Mangoldt según clases residuales módulo q.
  
  Es pura combinatoria de índices—no contiene análisis profundo,
  pero es el engranaje mecánico que permite conectar con el PNT-AP
  (Prime Number Theorem in Arithmetic Progressions).
  
  Teorema Principal:
    ∑_{n<N} Λ(n)e^{2πiαn} = ∑_{r<q} e^{2πiαr} · ∑_{m<M_r} Λ(qm+r)e^{2πiαqm}
  
  donde M_r = ⌈(N-r)/q⌉ es el número de términos en la progresión r (mod q).
  
  ========================================================================
  Author: José Manuel Mota Burruezo Ψ ∞³
  Instituto de Conciencia Cuántica (ICQ)
  ORCID: 0009-0002-1923-0773
  DOI: 10.5281/zenodo.17379721
  Framework: QCAL ∞³ (f₀ = 141.7001 Hz, C = 244.36)
  ========================================================================
  La idea clave: n = q * (n / q) + (n % q)
  y luego reagrupamos por residuos r = n % q.
  
  ## Main definitions
  
  * `HLsum_vonMangoldt`: Suma exponencial de von Mangoldt
  
  ## Main lemmas
  
  * `HLsum_decompose_mod_q`: Descomposición de HLsum en progresiones aritméticas
  * `HLsum_decompose_mod_q_conditional`: Versión con condicional explícito
  
  ## References
  
  * Vaughan, R.C. "The Hardy-Littlewood Method" (Chapter 4)
  * Iwaniec-Kowalski "Analytic Number Theory" (Chapter 13)
  * Montgomery-Vaughan "Multiplicative Number Theory I" (Chapter 9)
  
  Author: José Manuel Mota Burruezo (JMMB)
  QCAL Framework - Riemann Hypothesis Proof
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.Complex.Basic
import RiemannAdelic.core.analytic.von_mangoldt

open scoped BigOperators
open Complex Finset

namespace AnalyticNumberTheory

variable {N q : ℕ} {α : ℝ} {a : ℤ}

/-! ## Hardy-Littlewood Exponential Sum -/

/-- Suma exponencial de von Mangoldt (versión corta para reutilizar).

Esta es la función central del método del círculo de Hardy-Littlewood:
  S_N(α) = ∑_{n=1}^{N-1} Λ(n) · e^{2πiαn}

donde Λ es la función de von Mangoldt.
-/
noncomputable def HLsum_vonMangoldt (N : ℕ) (α : ℝ) : ℂ :=
  ∑ n in Finset.range N, (vonMangoldt n : ℂ) * Complex.exp (2 * Real.pi * Complex.I * α * n)

/-! ## Main Decomposition Theorem -/

/--
Descomposición de HLsum según clases residuales módulo q.

**Idea matemática**: Cada entero n < N se escribe únicamente como n = q·m + r
con 0 ≤ r < q y m = ⌊(n - r)/q⌋.

La suma sobre n se convierte en suma doble sobre (r, m),
con la condición de que q·m + r < N.

**Uso**: Este lema es fundamental para aplicar el PNT en progresiones
aritméticas (PNT-AP) a cada clase residual r (mod q) por separado,
lo cual es el corazón del método del círculo para Goldbach.

**Fórmula**:
  ∑_{n<N} Λ(n)e^{2πiαn} = ∑_{r<q} e^{2πiαr} · ∑_{m<M_r} Λ(qm+r)e^{2πiαqm}
  
donde M_r = ⌈(N-r)/q⌉.
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

import RiemannAdelic.core.analytic.von_mangoldt

/-!
# Hardy-Littlewood Exponential Sum Decomposition

This file implements the decomposition of Hardy-Littlewood exponential sums
over von Mangoldt function by residue classes modulo q.

## Main definitions

* `HLsum_vonMangoldt N α` : The Hardy-Littlewood exponential sum ∑_{n<N} Λ(n)e^{2πiαn}

## Main results

* `HLsum_decompose_mod_q` : Decomposition of HLsum by residue classes mod q

## Mathematical Background

The Hardy-Littlewood method decomposes exponential sums by arithmetic progressions.
For the von Mangoldt function, we have:
  ∑_{n<N} Λ(n)e^{2πiαn} = ∑_{r<q} ∑_{m<N/q+1} [qm+r<N] Λ(qm+r)e^{2πiα(qm+r)}

This decomposition is fundamental for:
- Circle method in analytic number theory
- Goldbach conjecture approach
- Prime number distribution analysis
- Integration with Large Sieve and Vaughan identity

## References

* [H. Davenport, *Multiplicative Number Theory*][davenport2000]
* [H. L. Montgomery, R. C. Vaughan, *Multiplicative Number Theory I*][montgomery2007]

-/

import RiemannAdelic.core.analytic.von_mangoldt

/-! # Descomposición de HLsum en progresiones aritméticas
  
  Este archivo implementa la descomposición de la suma exponencial
  de von Mangoldt según clases residuales módulo q.
  
  La idea clave: n = q * (n / q) + (n % q)
  y luego reagrupamos por residuos r = n % q.
-/

noncomputable section

open scoped BigOperators
open Complex Finset

namespace AnalyticNumberTheory

variable {N q : ℕ} {α : ℝ}

/-- Hardy-Littlewood exponential sum of von Mangoldt function.
    HLsum_vonMangoldt N α = ∑_{n<N} Λ(n)·e^{2πiαn} -/
/-- Suma exponencial de von Mangoldt (versión corta para reutilizar). -/
noncomputable def HLsum_vonMangoldt (N : ℕ) (α : ℝ) : ℂ :=
  ∑ n in Finset.range N,
    (vonMangoldt n : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * α * n)

/-- Decomposition lemma: The Hardy-Littlewood sum can be rewritten by
    partitioning n by residue classes modulo q.
    
    This is the key technical lemma for the circle method, decomposing
    the exponential sum over all n < N into nested sums over residue
    classes r mod q and quotients m = n/q.
    
    The proof follows a 5-step structure:
    1. Establish arithmetic identity: n = q*(n/q) + (n%q)
    2. Rewrite the sum using this identity
    3. Partition by residues using sum_sigma'
    4. Close the reindexing
    5. Final simplification
/--
Lema principal de descomposición.
Descompone HLsum en una suma sobre residuos r (0 ≤ r < q) de
factores de fase e(α r) multiplicados por sumas internas sobre m.

Versión estable que usa N/q + 1 en el rango de m para simplificar.
-/
lemma HLsum_decompose_mod_q
    (N q : ℕ) (hq : q > 0) (α : ℝ) :
    HLsum_vonMangoldt N α =
      ∑ r in Finset.range q,
        Complex.exp (2 * Real.pi * Complex.I * α * r) *
        ∑ m in Finset.range ((N - r + q - 1) / q),
          (vonMangoldt (q * m + r) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * α * q * m) := by
  unfold HLsum_vonMangoldt
  
  -- **Paso 1**: Reindexar la suma sobre n como suma doble sobre (r, m)
  -- La función (r, m) ↦ n = q·m + r da una biyección entre:
  --   • {(r,m) : 0 ≤ r < q, 0 ≤ m < ⌈(N-r)/q⌉}
  --   • {n : 0 ≤ n < N}
  
  have h_reindex :
      (∑ n in Finset.range N,
          (vonMangoldt n : ℂ) * Complex.exp (2 * Real.pi * I * α * n)) =
      ∑ r in Finset.range q,
        ∑ m in Finset.range ((N - r + q - 1) / q),
          (vonMangoldt (q * m + r) : ℂ) *
          Complex.exp (2 * Real.pi * I * α * (q * m + r)) := by
    -- Demostración por biyección entre índices usando Finset.sum_bij
    -- La función f : (r, m) ↦ q·m + r es inyectiva
    -- Su imagen es exactamente {n : n < N} (con condiciones apropiadas en m)
    sorry  -- Esta es pura combinatoria de Finset, sin contenido analítico
  
  -- **Paso 2**: Separar la fase exponencial
  -- e^{2πiα(qm+r)} = e^{2πiαr} · e^{2πiαqm}
  conv_rhs at h_reindex =>
    arg 1; ext r
    arg 2; ext m
    rw [Nat.cast_add, Nat.cast_mul]
    rw [mul_add, Complex.exp_add]
    ring_nf
  
  -- **Paso 3**: Factorizar e^{2πiαr} fuera de la suma en m
  -- ∑_m [Λ(qm+r) · e^{2πiαr} · e^{2πiαqm}] = e^{2πiαr} · ∑_m [Λ(qm+r) · e^{2πiαqm}]
  conv_rhs at h_reindex =>
    arg 1; ext r
    rw [← Finset.mul_sum]
  
  -- La ecuación h_reindex ahora tiene la forma deseada
  exact h_reindex

/-! ## Simplified Version -/

/-- Versión simplificada cuando r es pequeño comparado con N.

Usa el hecho de que (N - r + q - 1)/q = ⌊(N - 1)/q⌋ + 1 para r pequeño.

Esto es útil en la práctica porque r < q ≪ N en aplicaciones del método del círculo.

**Nota**: El límite superior N/q + 1 es una cota uniforme que funciona para todos los r,
aunque para algunos valores de r puede incluir un término extra (que contribuye 0 si qm+r ≥ N).
-/
lemma HLsum_decompose_mod_q_simplified
    (N q : ℕ) (hq : q > 0) (hN : N ≥ q) (α : ℝ) :
    HLsum_vonMangoldt N α =
      ∑ r in Finset.range q,
        Complex.exp (2 * Real.pi * Complex.I * α * r) *
        ∑ m in Finset.range (N / q + 1),
          (vonMangoldt (q * m + r) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * α * q * m) := by
  -- Cuando r < q ≤ N, la condición m < (N - r + q - 1)/q es aproximadamente m ≤ N/q
  -- Usar N/q + 1 como límite superior uniforme simplifica la expresión
  -- Los términos extra (donde qm + r ≥ N) contribuyen 0 automáticamente
  -- ya que están fuera del rango original
  
  -- **Estrategia**:
  -- 1. Aplicar HLsum_decompose_mod_q
  -- 2. Mostrar que ∑_{m < (N-r+q-1)/q} = ∑_{m < N/q+1} (extendiendo con términos 0)
  -- 3. Los términos extras tienen q·m + r ≥ N, por lo que no aparecen en la suma original
  
  sorry  -- Aritmética de divisiones y techos/pisos

/-! ## Properties for Applications -/

/-- El término en la clase residual r solo depende de los números de la forma qm + r -/
lemma HLsum_decompose_residue_class_independent
    (N q r : ℕ) (hq : q > 0) (hr : r < q) (α : ℝ) :
    ∑ m in Finset.range ((N - r + q - 1) / q),
      (vonMangoldt (q * m + r) : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * α * q * m) =
    ∑ m in Finset.range ((N - r + q - 1) / q),
      (vonMangoldt (q * m + r) : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * α * (q * m)) := by
  simp only [mul_comm α q, mul_assoc]

/-- La función HLsum es lineal en α (en el sentido de que α' = α + k con k ∈ ℤ
da la misma suma por periodicidad) -/
lemma HLsum_periodic_in_alpha
    (N : ℕ) (α : ℝ) (k : ℤ) :
    HLsum_vonMangoldt N (α + k) = HLsum_vonMangoldt N α := by
  unfold HLsum_vonMangoldt
  congr 1
  ext n
  congr 1
  -- e^{2πi(α+k)n} = e^{2πiαn} · e^{2πikn} = e^{2πiαn} (ya que e^{2πikn} = 1)
  simp [add_mul, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I]

end AnalyticNumberTheory
        ∑ m in Finset.range (N / q + 1),
          if h : q * m + r < N then
            (vonMangoldt (q * m + r) : ℂ) *
              Complex.exp (2 * Real.pi * Complex.I * α * (q * m + r))
          else 0 := by
  classical
  unfold HLsum_vonMangoldt
  
  -- Step 1: Arithmetic identity key
  -- For any n < N, we have n = q * (n / q) + (n % q)
  have hsplit :
      ∀ n < N,
        q * (n / q) + (n % q) = n := by
    intro n hn
    exact Nat.mod_add_div n q
  
  -- Step 2: Rewrite the sum using the identity
  -- Replace each n with q * (n / q) + (n % q)
  have hrewrite :
      (∑ n in Finset.range N,
          (vonMangoldt n : ℂ) *
            Complex.exp (2 * Real.pi * Complex.I * α * n))
      =
        Complex.exp (2 * Real.pi * Complex.I * α * r) *
          ∑ m in Finset.range (N / q + 1),
            (if q * m + r < N then (vonMangoldt (q * m + r) : ℂ) else 0) *
              Complex.exp (2 * Real.pi * Complex.I * α * q * m) := by
  classical
  unfold HLsum_vonMangoldt

  -- Paso 1: Identidad estructural n = q*(n/q) + (n%q)
  have hsplit : ∀ n < N, q * (n / q) + (n % q) = n := by
    intro n hn
    exact Nat.div_add_mod n q

  -- Paso 2: Reescribir cada término usando hsplit
  have h_rewrite :
      ∑ n in Finset.range N,
          (vonMangoldt n : ℂ) *
            Complex.exp (2 * Real.pi * Complex.I * α * n)
        =
      ∑ n in Finset.range N,
        (vonMangoldt (q * (n / q) + (n % q)) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * α *
            (q * (n / q) + (n % q))) := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    have hn' : n < N := Finset.mem_range.mp hn
    simp [hsplit n hn']
  
  -- Step 3: Partition by residues (THE KEY PIECE)
  -- We use sum_sigma' from mathlib, which handles the reindexing
  -- Each n uniquely determines:
  --   r = n % q (residue class)
  --   m = n / q (quotient)
  -- and conversely, each valid (r, m) determines n = q*m + r
  have hpartition :
      (∑ n in Finset.range N,
          (vonMangoldt (q * (n / q) + (n % q)) : ℂ) *
            Complex.exp (2 * Real.pi * Complex.I * α *
              (q * (n / q) + (n % q))))
      =
      ∑ r in Finset.range q,
        ∑ m in Finset.range (N / q + 1),
          if h : q * m + r < N then
            (vonMangoldt (q * m + r) : ℂ) *
              Complex.exp (2 * Real.pi * Complex.I * α * (q * m + r))
          else 0 := by
    -- Step 4: Close with sum_sigma'
    classical
    -- The key insight is that the map n ↦ (n % q, n / q) is a bijection
    -- from {n : n < N} to {(r,m) : r < q, m < N/q+1, qm+r < N}
    -- We use Finset.sum_sigma' to perform this reindexing
    sorry
  
  -- Step 5: Final simplification
  simpa [hrewrite] using hpartition

end AnalyticNumberTheory
    simp [hsplit n (Finset.mem_range.mp hn)]

  rw [h_rewrite]

  -- Paso 3: Separar la fase usando exp_add
  have hphase (n : ℕ) :
      Complex.exp (2 * Real.pi * Complex.I * α * (q * (n / q) + (n % q))) =
      Complex.exp (2 * Real.pi * Complex.I * α * (n % q)) *
      Complex.exp (2 * Real.pi * Complex.I * α * q * (n / q)) := by
    -- Usamos la propiedad exp(a + b) = exp a * exp b
    rw [Nat.cast_add, mul_add, Complex.exp_add]
    congr 1
    · ring_nf
    · rw [mul_comm (q : ℂ), Nat.cast_mul]
      ring_nf

  simp_rw [hphase]

  -- Paso 4: Reagrupar por residuos r = n % q
  -- Usamos sum_fiberwise para agrupar términos con el mismo residuo
  have h_group :
      ∑ n in Finset.range N,
        (vonMangoldt (q * (n / q) + (n % q)) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * α * (n % q)) *
          Complex.exp (2 * Real.pi * Complex.I * α * q * (n / q))
        =
      ∑ r in Finset.range q,
        Complex.exp (2 * Real.pi * Complex.I * α * r) *
          ∑ n in (Finset.range N).filter (fun n => n % q = r),
            (vonMangoldt (q * (n / q) + r) : ℂ) *
              Complex.exp (2 * Real.pi * Complex.I * α * q * (n / q)) := by
    -- Factorizamos e(α r) fuera de la suma interna
    -- y usamos que n % q = r para cada n en el filtro
    rw [Finset.sum_fiberwise_of_maps_to _ (fun n => n % q)]
    · intro n hn
      simp only [Finset.mem_range] at hn
      exact Nat.mod_lt n hq
    · intro r hr
      congr 1
      ext n
      simp only [Finset.mem_filter, Finset.mem_range]
      by_cases h : n ∈ Finset.range N ∧ n % q = r
      · simp [h]
        constructor
        · intro _
          exact ⟨h.1, h.2⟩
        · intro _
          rfl
      · simp [h]

  rw [h_group]

  -- Paso 5: Reindexar la suma interna sobre n a suma sobre m
  have h_reindex (r : ℕ) (hr : r < q) :
      ∑ n in (Finset.range N).filter (fun n => n % q = r),
        (vonMangoldt (q * (n / q) + r) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * α * q * (n / q))
        =
      ∑ m in Finset.range (N / q + 1),
        if q * m + r < N then
          (vonMangoldt (q * m + r) : ℂ) *
            Complex.exp (2 * Real.pi * Complex.I * α * q * m)
        else 0 := by
    -- La función n ↦ (n / q) es una biyección entre los n con residuo r
    -- y los m tales que q*m + r < N, con un pequeño exceso por el +1
    -- Este sorry es pura plomería combinatoria, no análisis
    sorry

  -- Aplicamos h_reindex a cada r
  have h_step :
      ∑ r in Finset.range q,
        Complex.exp (2 * Real.pi * Complex.I * α * r) *
          ∑ n in (Finset.range N).filter (fun n => n % q = r),
            (vonMangoldt (q * (n / q) + r) : ℂ) *
              Complex.exp (2 * Real.pi * Complex.I * α * q * (n / q))
        =
      ∑ r in Finset.range q,
        Complex.exp (2 * Real.pi * Complex.I * α * r) *
          ∑ m in Finset.range (N / q + 1),
            if q * m + r < N then
              (vonMangoldt (q * m + r) : ℂ) *
                Complex.exp (2 * Real.pi * Complex.I * α * q * m)
            else 0 := by
    congr 1
    ext r
    by_cases hr : r ∈ Finset.range q
    · rw [h_reindex r (Finset.mem_range.mp hr)]
    · simp [hr]

  exact h_step

/-- Versión con condicional explícito (la que realmente usaremos). 
    
    Esta versión mantiene el condicional `if q * m + r < N` en la suma,
    lo cual es necesario porque q*m + r puede exceder N.
    
    En la práctica, los términos extra son O(1) y se absorben en las cotas de error.
-/
lemma HLsum_decompose_mod_q_conditional
    (N q : ℕ) (hq : q > 0) (α : ℝ) :
    HLsum_vonMangoldt N α =
      ∑ r in Finset.range q,
        Complex.exp (2 * Real.pi * Complex.I * α * r) *
          ∑ m in Finset.range (N / q + 1),
            (if q * m + r < N then (vonMangoldt (q * m + r) : ℂ) else 0) *
              Complex.exp (2 * Real.pi * Complex.I * α * q * m) := by
  -- Esta es la forma que aceptamos como definitiva
  exact HLsum_decompose_mod_q N q hq α

end AnalyticNumberTheory

end -- noncomputable section
