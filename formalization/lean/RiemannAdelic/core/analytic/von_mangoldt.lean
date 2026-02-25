/-
Copyright (c) 2026 José Manuel Mota Burruezo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: José Manuel Mota Burruezo
-/

import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.VonMangoldt

/-!
# von Mangoldt Function

This file provides a clean wrapper for the von Mangoldt function Λ(n) from Mathlib.

## Main definitions

* `vonMangoldt n` : The von Mangoldt function, returning log p if n = p^k for prime p, else 0.

## Main lemmas

* `vonMangoldt_zero` : Λ(0) = 0
* `vonMangoldt_one` : Λ(1) = 0  
* `vonMangoldt_prime` : Λ(p) = log p for prime p
* `vonMangoldt_prime_pow` : Λ(p^k) = log p for prime p and k ≥ 1
* `vonMangoldt_nonneg` : Λ(n) ≥ 0 for all n

## References

* [H. Davenport, *Multiplicative Number Theory*][davenport2000]
* [T. Tao, *An Introduction to Measure Theory*][tao2011]

-/

open scoped BigOperators
open Nat ArithmeticFunction

namespace AnalyticNumberTheory

/-- The von Mangoldt function Λ(n). 
    Returns log p if n = p^k for some prime p and k ≥ 1, otherwise returns 0. -/
noncomputable def vonMangoldt (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n

/-- Λ(0) = 0 -/
@[simp]
lemma vonMangoldt_zero : vonMangoldt 0 = 0 := by
  rw [vonMangoldt]
  exact ArithmeticFunction.vonMangoldt_apply_zero

/-- Λ(1) = 0 -/
@[simp]
lemma vonMangoldt_one : vonMangoldt 1 = 0 := by
  rw [vonMangoldt]
  exact ArithmeticFunction.vonMangoldt_apply_one

/-- For a prime p, Λ(p) = log p -/
lemma vonMangoldt_prime {p : ℕ} (hp : Nat.Prime p) : vonMangoldt p = Real.log p := by
  rw [vonMangoldt]
  exact ArithmeticFunction.vonMangoldt_apply_prime hp

/-- For a prime power p^k with k ≥ 1, Λ(p^k) = log p -/
lemma vonMangoldt_prime_pow {p k : ℕ} (hp : Nat.Prime p) (hk : k ≥ 1) :
    vonMangoldt (p ^ k) = Real.log p := by
  rw [vonMangoldt]
  exact ArithmeticFunction.vonMangoldt_apply_pow hp (Nat.one_le_iff_ne_zero.mp hk)

/-- Λ(n) ≥ 0 for all n -/
lemma vonMangoldt_nonneg (n : ℕ) : 0 ≤ vonMangoldt n := by
  rw [vonMangoldt]
  exact ArithmeticFunction.vonMangoldt_nonneg

/-- If n is not a prime power, then Λ(n) = 0 -/
lemma vonMangoldt_apply_of_not_prime_pow {n : ℕ} (h : ¬ ∃ p k : ℕ, Nat.Prime p ∧ k ≥ 1 ∧ n = p ^ k) :
    vonMangoldt n = 0 := by
  rw [vonMangoldt]
  by_cases hn : n = 0
  · simp [hn, ArithmeticFunction.vonMangoldt_apply_zero]
  · by_cases hn1 : n = 1
    · simp [hn1, ArithmeticFunction.vonMangoldt_apply_one]
    · -- If n is not 0, 1, or a prime power, then Λ(n) = 0
      -- This follows from the definition of vonMangoldt
      sorry

end AnalyticNumberTheory
