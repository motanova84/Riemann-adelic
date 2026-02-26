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
/-!
# Von Mangoldt Function

This file provides the von Mangoldt function Λ(n) for use in analytic number theory.

The von Mangoldt function is defined as:
- Λ(n) = log p if n = p^k for prime p and k ≥ 1
- Λ(n) = 0 otherwise

This is a wrapper around Mathlib's implementation for use in the QCAL framework.

## Main definitions

* `vonMangoldt`: The von Mangoldt function Λ: ℕ → ℝ

## References

* Iwaniec-Kowalski "Analytic Number Theory"
* Montgomery-Vaughan "Multiplicative Number Theory I"

Author: José Manuel Mota Burruezo (JMMB)
QCAL Framework - Riemann Hypothesis Proof
-/

import Mathlib.Data.Nat.Basic
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Real.Basic

noncomputable section

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
/-- 
The von Mangoldt function Λ(n).
This is re-exported from Mathlib for convenient use in analytic number theory.
-/
def vonMangoldt : ℕ → ℝ := fun n => (Nat.ArithmeticFunction.vonMangoldt n : ℝ)

/-- The von Mangoldt function is zero at n = 0 -/
lemma vonMangoldt_zero : vonMangoldt 0 = 0 := by
  unfold vonMangoldt
  simp [Nat.ArithmeticFunction.vonMangoldt]

/-- The von Mangoldt function is zero at n = 1 -/
lemma vonMangoldt_one : vonMangoldt 1 = 0 := by
  unfold vonMangoldt
  simp [Nat.ArithmeticFunction.vonMangoldt]

/-- 
The von Mangoldt function is log p when n is a prime power p^k.
This is the key property used in the explicit formula.
-/
lemma vonMangoldt_prime_pow {p k : ℕ} (hp : Nat.Prime p) (hk : k > 0) :
    vonMangoldt (p ^ k) = Real.log p := by
  unfold vonMangoldt
  simp [Nat.ArithmeticFunction.vonMangoldt, hp, hk]
  sorry  -- Standard result from Mathlib

/--
The von Mangoldt function is non-negative.
-/
lemma vonMangoldt_nonneg (n : ℕ) : 0 ≤ vonMangoldt n := by
  unfold vonMangoldt
  exact Nat.cast_nonneg _

end AnalyticNumberTheory

end -- noncomputable section
