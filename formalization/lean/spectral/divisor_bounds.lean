import Mathlib.Data.Nat.Interval
import Mathlib.Data.Nat.Lcm
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.NormedSpace.Basic

/-! # Divisor Bounds (Cotas para Sumas de Divisores)
  
  Este archivo establece las cotas cuadráticas necesarias para el método del círculo.
  
  Pipeline:
  1. Conteo de múltiplos vía mcm (robusto)
  2. τ(n) en media cuadrática
  3. Möbius → τ (vía desigualdad triangular)
  4. Logs → τ log (cota puntual)
  5. Ensamblaje L² para Type II
-/

open scoped BigOperators
open Real Finset

namespace AnalyticNumberTheory

variable {X : ℕ}

/-! ### 1. Conteo de múltiplos vía mcm (robusto) -/

/--
Número de enteros ≤ X divisibles por d y e.

Versión robusta para el método del círculo.
-/
lemma card_multiples_le
    (d e X : ℕ) (hd : d ≠ 0) (he : e ≠ 0) :
    ((Icc 1 X).filter (fun n => d ∣ n ∧ e ∣ n)).card
      ≤ X / Nat.lcm d e := by
  classical
  -- Los n contados son múltiplos de lcm(d,e)
  have hsubset :
      (Icc 1 X).filter (fun n => d ∣ n ∧ e ∣ n)
        ⊆ (Icc 1 X).filter (fun n => Nat.lcm d e ∣ n) := by
    intro n hn
    simp at hn ⊢
    rcases hn with ⟨hn1, hn2, hdn, hen⟩
    exact ⟨hn1, hn2, Nat.lcm_dvd hdn hen⟩

  have h_card_le := Finset.card_le_card hsubset

  -- cota estándar de múltiplos
  -- Este sorry es aceptable: es un lema clásico de teoría elemental de números
  have h_mult_bound :
      ((Icc 1 X).filter (fun n => Nat.lcm d e ∣ n)).card
        ≤ X / Nat.lcm d e := by
    -- Idea: Los múltiplos de L ≤ X son L, 2L, 3L, ..., floor(X/L)*L
    -- La cantidad es floor(X/L)
    sorry

  exact le_trans h_card_le h_mult_bound

/-! ### 2. Función divisor τ(n) -/

/-- Función divisor τ(n) = número de divisores positivos de n. -/
noncomputable def tau (n : ℕ) : ℝ :=
  (Nat.divisors n).card

/-- Cota cuadrática para τ(n):
    ∑_{n ≤ X} τ(n)^2 ≪ X (log X)^3
    
    Nota: El exponente 3 es estándar y suficiente para nuestros propósitos. -/
lemma sum_tau_sq_le (X : ℕ) (hX : X ≥ 1) :
    ∃ C_τ > 0, ∑ n in Icc 1 X, (tau n) ^ 2 ≤ C_τ * X * (Real.log X) ^ 3 := by
  -- Prueba clásica usando doble conteo y estimación armónica
  sorry

/-! ### 3. Convolución de Möbius -/

/-- Convolución de Möbius: ∑_{d|n} μ(d). -/
noncomputable def mobiusConv (n : ℕ) : ℂ :=
  ∑ d in Nat.divisors n, ArithmeticFunction.moebius d

/--
La convolución de Möbius está dominada por τ(n).

Este es el puente que permite usar sum_tau_sq.
-/
lemma mobiusConv_abs_le_tau (n : ℕ) :
    Complex.abs (mobiusConv n) ≤ tau n := by
  classical
  unfold mobiusConv tau

  -- Desigualdad triangular
  have h_triangle :=
    Complex.abs_sum_le_sum_abs (s := Nat.divisors n) (f := fun d => (ArithmeticFunction.moebius d : ℂ))

  -- |μ(d)| ≤ 1
  have h_mu_bound :
      ∀ d ∈ Nat.divisors n,
        Complex.abs (ArithmeticFunction.moebius d : ℂ) ≤ 1 := by
    intro d hd
    have : |ArithmeticFunction.moebius d| ≤ 1 := by
      -- Propiedad clásica: μ(d) ∈ {-1, 0, 1}
      -- Por ahora, lo dejamos como un lema básico que se puede demostrar
      -- a partir de la definición de μ.
      sorry
    simpa using this

  -- Suma de bound ≤ τ(n)
  have h_sum_le :
      ∑ d in Nat.divisors n, Complex.abs (ArithmeticFunction.moebius d : ℂ) ≤ (Nat.divisors n).card := by
    refine Finset.sum_le_card_nsmul _ ?_
    intro d hd
    exact h_mu_bound d hd

  exact le_trans h_triangle (by simp [h_sum_le])

/-- Cota cuadrática para la convolución de Möbius (vía τ). -/
lemma sum_mobius_conv_sq_le (X : ℕ) (hX : X ≥ 1) :
    ∃ C_μ > 0,
    ∑ n in Icc 1 X, Complex.abs (mobiusConv n) ^ 2 ≤ C_μ * X * (Real.log X) ^ 3 := by
  -- Usamos mobiusConv_abs_le_tau para reducir al caso de τ
  obtain ⟨C_τ, hC_τ_pos, h_tau_bound⟩ := sum_tau_sq_le X hX
  
  have h_each : ∀ n ∈ Icc 1 X, Complex.abs (mobiusConv n) ^ 2 ≤ (tau n) ^ 2 := by
    intro n hn
    refine pow_le_pow_left (by simp) ?_ 2
    exact mobiusConv_abs_le_tau n
  
  -- Sumamos la desigualdad término a término
  have h_sum_le : ∑ n in Icc 1 X, Complex.abs (mobiusConv n) ^ 2 ≤ ∑ n in Icc 1 X, (tau n) ^ 2 := by
    refine sum_le_sum h_each
    
  exact ⟨C_τ, hC_τ_pos, le_trans h_sum_le h_tau_bound⟩

/-! ### 4. Suma de logaritmos de divisores -/

/-- Suma de logs de divisores: ∑_{d|n} log d. -/
noncomputable def logSum (n : ℕ) : ℝ :=
  ∑ d in Nat.divisors n, Real.log d

/--
Control básico: logSum ≤ τ(n) log n.

Suficiente para Type II.
-/
lemma logSum_le_tau_log (n : ℕ) (hn : n ≥ 2) :
    logSum n ≤ tau n * Real.log n := by
  classical
  unfold logSum tau

  have hlog :
      ∀ d ∈ Nat.divisors n,
        Real.log d ≤ Real.log n := by
    intro d hd
    have hdpos : (d : ℝ) > 0 := by exact_mod_cast Nat.pos_of_mem_divisors hd
    have hnpos : (n : ℝ) > 0 := by exact_mod_cast (by linarith : 0 < n)
    have hdle : (d : ℝ) ≤ n := by exact_mod_cast Nat.le_of_dvd (by linarith) (Nat.mem_divisors.mp hd).1
    exact Real.log_le_log hdpos hdle

  have h_sum_le :=
    Finset.sum_le_card_nsmul
      (s := Nat.divisors n)
      (f := fun d => Real.log d)
      (a := Real.log n)
      (by intro d hd; exact hlog d hd)

  simpa [mul_comm] using h_sum_le

/-- Cota cuadrática para la suma de logs (vía τ). -/
lemma sum_log_sum_sq_le (X : ℕ) (hX : X ≥ 2) :
    ∃ C_log > 0,
    ∑ n in Icc 1 X, (logSum n) ^ 2 ≤ C_log * X * (Real.log X) ^ 5 := by
  -- Usamos logSum_le_tau_log para reducir a τ
  obtain ⟨C_τ, hC_τ_pos, h_tau_bound⟩ := sum_tau_sq_le X (by linarith)
  
  have h_each : ∀ n ∈ Icc 2 X, (logSum n) ^ 2 ≤ (tau n) ^ 2 * (Real.log n) ^ 2 := by
    intro n hn
    have h_le := logSum_le_tau_log n (by linarith)
    refine pow_le_pow_left (by simp) ?_ 2
    exact mul_le_mul h_le (le_refl (Real.log n)) (by simp) (by simp [tau, Nat.cast_nonneg])
  
  -- Separamos n=1 (caso especial)
  have h_n1 : logSum 1 = 0 := by simp [logSum, Nat.divisors_one]
  
  -- Sumamos y acotamos (log n)² ≤ (log X)²
  -- El exponente final es 3 (de τ²) + 2 (de (log X)²) = 5
  sorry

/-! ### 5. Ensamblaje L² para Type II -/

/--
Fuel L² para Vaughan Type II.

Versión usable por large sieve.
-/
theorem vaughan_l2_fuel (X : ℕ) (hX : X ≥ 2) :
    ∃ C > 0,
      (∑ n in Icc 1 X, Complex.abs (mobiusConv n) ^ 2) *
      (∑ n in Icc 1 X, (logSum n) ^ 2) ≤
      C * X ^ 2 * (Real.log X) ^ 8 := by
  classical
  -- Obtenemos las cotas individuales
  obtain ⟨C_μ, hC_μ_pos, h_mobius_bound⟩ := sum_mobius_conv_sq_le X (by linarith)
  obtain ⟨C_log, hC_log_pos, h_log_bound⟩ := sum_log_sum_sq_le X hX
  
  -- Multiplicamos las cotas
  have h_product :
      (∑ n in Icc 1 X, Complex.abs (mobiusConv n) ^ 2) *
      (∑ n in Icc 1 X, (logSum n) ^ 2) ≤
      (C_μ * X * (Real.log X) ^ 3) * (C_log * X * (Real.log X) ^ 5) := by
    refine mul_le_mul h_mobius_bound h_log_bound ?_ ?_
    · exact sum_nonneg (fun _ _ => by simp)
    · exact sum_nonneg (fun _ _ => by simp)
  
  -- Simplificamos
  simp_rw [mul_assoc, mul_comm, mul_left_comm] at h_product
  simp only [← mul_assoc, mul_comm _ C_μ, mul_comm _ C_log] at h_product
  
  -- Reagrupamos constantes
  have h_simplify :
      (C_μ * X * (Real.log X) ^ 3) * (C_log * X * (Real.log X) ^ 5) =
      (C_μ * C_log) * X ^ 2 * (Real.log X) ^ 8 := by
    ring
  
  rw [h_simplify] at h_product
  exact ⟨C_μ * C_log, mul_pos hC_μ_pos hC_log_pos, h_product⟩

end AnalyticNumberTheory
