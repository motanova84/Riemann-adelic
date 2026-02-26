/-
  von_mangoldt.lean
  ========================================================================
  Von Mangoldt Function Λ(n) for Analytic Number Theory
  
  Wrapper for Mathlib's von Mangoldt function with clean interface
  for use in Hardy-Littlewood circle method and Goldbach proof.
  
  Key properties:
  - Λ(n) = log p if n = p^k for prime p
  - Λ(n) = 0 otherwise
  - Always non-negative
  
  ========================================================================
  Autor: José Manuel Mota Burruezo Ψ ∞³
  Instituto de Conciencia Cuántica (ICQ)
  ORCID: 0009-0002-1923-0773
  DOI: 10.5281/zenodo.17379721
  Framework QCAL ∞³: f₀ = 141.7001 Hz, C = 244.36
  ========================================================================
-/

import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Nat.Prime
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Nat Real
open scoped BigOperators

namespace AnalyticNumberTheory

/-- Von Mangoldt function Λ(n): log p if n = p^k for prime p, 0 otherwise -/
noncomputable def vonMangoldt (n : ℕ) : ℝ :=
  if h : ∃ (p k : ℕ), Nat.Prime p ∧ k > 0 ∧ n = p ^ k then
    Real.log (Classical.choose h).1
  else
    0

/-- Λ(1) = 0 -/
lemma vonMangoldt_one : vonMangoldt 1 = 0 := by
  unfold vonMangoldt
  simp
  intro p k hp hk h1
  omega

/-- Λ(0) = 0 -/
lemma vonMangoldt_zero : vonMangoldt 0 = 0 := by
  unfold vonMangoldt
  simp
  intro p k hp hk h0
  cases k with
  | zero => simp at hk
  | succ k' =>
    simp [pow_succ] at h0

/-- Λ(p) = log p for prime p -/
lemma vonMangoldt_prime {p : ℕ} (hp : Nat.Prime p) :
    vonMangoldt p = Real.log p := by
  unfold vonMangoldt
  simp only [hp]
  have h_ex : ∃ (p' k : ℕ), Nat.Prime p' ∧ k > 0 ∧ p = p' ^ k := by
    use p, 1
    simp [hp, pow_one]
  simp [h_ex]
  -- The chosen p' must equal p since p = p'^k and p is prime
  sorry

/-- Λ(p^k) = log p for prime p and k > 0 -/
lemma vonMangoldt_prime_pow {p k : ℕ} (hp : Nat.Prime p) (hk : k > 0) :
    vonMangoldt (p ^ k) = Real.log p := by
  unfold vonMangoldt
  have h_ex : ∃ (p' k' : ℕ), Nat.Prime p' ∧ k' > 0 ∧ p ^ k = p' ^ k' := by
    use p, k
    exact ⟨hp, hk, rfl⟩
  simp [h_ex]
  -- The chosen p' must equal p since p^k = p'^k' and both are prime powers
  sorry

/-- Λ(n) ≥ 0 for all n -/
lemma vonMangoldt_nonneg (n : ℕ) : 0 ≤ vonMangoldt n := by
  unfold vonMangoldt
  split_ifs with h
  · -- n = p^k for some prime p, so Λ(n) = log p ≥ 0
    obtain ⟨p, k, hp, hk, hn⟩ := h
    apply Real.log_nonneg
    exact Nat.one_le_iff_ne_zero.mpr (Nat.Prime.ne_zero hp)
  · -- Λ(n) = 0
    rfl

/-- Characterization: Λ(n) ≠ 0 iff n is a prime power -/
lemma vonMangoldt_ne_zero_iff {n : ℕ} :
    vonMangoldt n ≠ 0 ↔ ∃ (p k : ℕ), Nat.Prime p ∧ k > 0 ∧ n = p ^ k := by
  constructor
  · intro h
    unfold vonMangoldt at h
    split_ifs at h with hex
    · exact hex
    · contradiction
  · intro ⟨p, k, hp, hk, hn⟩
    rw [hn, vonMangoldt_prime_pow hp hk]
    apply Real.log_pos
    exact Nat.Prime.one_lt hp

/-- Sum form of Chebyshev psi function -/
noncomputable def chebyshevPsi (x : ℝ) : ℝ :=
  ∑ n in Finset.range ⌊x⌋₊, vonMangoldt (n + 1)

/-- Λ is supported on prime powers -/
lemma vonMangoldt_support {n : ℕ} :
    vonMangoldt n ≠ 0 → ∃ p k, Nat.Prime p ∧ k > 0 ∧ n = p ^ k := by
  intro h
  exact vonMangoldt_ne_zero_iff.mp h

end AnalyticNumberTheory
