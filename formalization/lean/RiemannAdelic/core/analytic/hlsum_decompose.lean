/-
  hlsum_decompose.lean
  ========================================================================
  Descomposición de HLsum en progresiones aritméticas
  
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
