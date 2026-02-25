/-
Copyright (c) 2026 José Manuel Mota Burruezo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: José Manuel Mota Burruezo

! This file defines the von Mangoldt function Λ(n) for analytic number theory.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.NumberTheory.ArithmeticFunction

/-!
# von Mangoldt Function

This file defines the von Mangoldt function Λ(n), which is fundamental in 
analytic number theory and the explicit formula for the prime counting function.

## Main Definitions

* `vonMangoldt n`: The von Mangoldt function Λ(n) defined as:
  - log p if n = p^k for some prime p and k ≥ 1
  - 0 otherwise

## Implementation Notes

The von Mangoldt function is used extensively in:
- Hardy-Littlewood exponential sums
- Vaughan's identity decomposition
- Circle method for additive problems (e.g., Goldbach conjecture)
- Explicit formulas connecting primes and zeta zeros

## References

* [Hardy & Littlewood, "Some problems of 'Partitio Numerorum'"]
* [Vaughan, "The Hardy-Littlewood Method"]
* [Davenport, "Multiplicative Number Theory"]
-/

namespace AnalyticNumberTheory

open Nat

/--
The von Mangoldt function Λ(n).

Returns log p if n = p^k for some prime p and k ≥ 1, and 0 otherwise.
This is a key arithmetic function in analytic number theory.
-/
noncomputable def vonMangoldt (n : ℕ) : ℝ :=
  if h : n > 0 then
    -- Find if n is a prime power
    if ∃ (p k : ℕ), Nat.Prime p ∧ k > 0 ∧ n = p ^ k then
      -- Extract the prime and return its logarithm
      Real.log (Nat.minFac n)
    else
      0
  else
    0

/--
Λ(1) = 0 (1 is not a prime power with k ≥ 1).
-/
lemma vonMangoldt_one : vonMangoldt 1 = 0 := by
  unfold vonMangoldt
  simp only [gt_iff_lt, zero_lt_one, ↓reduceDIte]
  -- 1 cannot be written as p^k with k ≥ 1 for prime p
  simp only [not_exists, not_and, ite_eq_right_iff]
  intro p k hp hk h
  -- If 1 = p^k with k > 0, then p^k = 1, so p = 1 (contradiction with primality)
  have : p ^ k = 1 := h
  have : p = 1 := by
    cases k with
    | zero => contradiction
    | succ k' =>
      simp only [pow_succ] at this
      have : p * p^k' = 1 := this
      omega
  -- But p is prime, so p ≠ 1
  have : ¬Nat.Prime 1 := Nat.not_prime_one
  contradiction

/--
Λ(0) = 0 by convention.
-/
lemma vonMangoldt_zero : vonMangoldt 0 = 0 := by
  unfold vonMangoldt
  simp

/--
For a prime p, Λ(p) = log p.
-/
lemma vonMangoldt_prime (p : ℕ) (hp : Nat.Prime p) : vonMangoldt p = Real.log p := by
  unfold vonMangoldt
  simp only [hp.pos, ↓reduceDIte]
  -- p = p^1, so the existential is satisfied
  have hex : ∃ (q k : ℕ), Nat.Prime q ∧ k > 0 ∧ p = q ^ k := by
    use p, 1
    exact ⟨hp, Nat.zero_lt_one, (pow_one p).symm⟩
  simp only [hex, ↓reduceIte]
  -- minFac p = p for prime p
  have : Nat.minFac p = p := Nat.Prime.minFac_eq hp
  rw [this]

/--
The von Mangoldt function is non-negative.
-/
lemma vonMangoldt_nonneg (n : ℕ) : 0 ≤ vonMangoldt n := by
  unfold vonMangoldt
  split_ifs with h hex
  · -- n > 0 and n is a prime power
    apply Real.log_nonneg
    -- minFac n ≥ 2 for n > 1 (and for n = 1 handled separately)
    by_cases hn1 : n = 1
    · -- n = 1 case handled by vonMangoldt_one
      rw [hn1]
      simp at hex
    · -- n > 1, so minFac n ≥ 2
      have : n ≥ 2 := by omega
      have : Nat.minFac n ≥ 2 := Nat.minFac_prime this |>.two_le
      norm_cast
      omega
  · rfl
  · rfl

end AnalyticNumberTheory
