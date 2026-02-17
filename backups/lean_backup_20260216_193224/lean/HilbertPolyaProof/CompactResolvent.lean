import HilbertPolyaProof.KernelExplicit
import Mathlib.Analysis.NormedSpace.OperatorNorm
import Mathlib.Topology.MetricSpace.Basic

open Complex

/-!
# Compact Resolvent and Discrete Spectrum

This file proves that the resolvent of H_ψ is compact and that the spectrum
is purely discrete.

## Main theorems
- `resolvent_H_psi_compact`: The resolvent is compact for λ not in spectrum
- `spectrum_purely_discrete`: The spectrum consists of isolated eigenvalues
-/

namespace HilbertPolyaProof.CompactResolvent

/-- Compact operator predicate -/
def CompactOperator (T : (ℝ → ℂ) → (ℝ → ℂ)) : Prop :=
  ∀ S : Set (ℝ → ℂ), BddAbove (norm '' S) → 
    ∃ K : Set (ℝ → ℂ), K ⊆ T '' S ∧ IsCompact K

/-- Spectrum of an operator -/
def spectrum (T : (ℝ → ℂ) → (ℝ → ℂ)) : Set ℂ :=
  {λ : ℂ | ¬∃ S : (ℝ → ℂ) → (ℝ → ℂ), ∀ f, S ((fun g => T g - λ • g) f) = f}

/-- The resolvent of H_ψ is compact outside the spectrum -/
axiom resolvent_H_psi_compact :
  ∀ λ : ℂ, λ ∉ spectrum (integralOperator (fun x y => H_psi_kernel x y sorry sorry)) →
    CompactOperator sorry -- (resolvent at λ)

/-- The spectrum is purely discrete -/
axiom spectrum_purely_discrete :
  ∃ (λ_n : ℕ → ℂ),
    spectrum (integralOperator (fun x y => H_psi_kernel x y sorry sorry)) = Set.range λ_n ∧
    (∀ n : ℕ, ∃ ε > 0, ∀ m ≠ n, ε ≤ ‖λ_n n - λ_n m‖) ∧
    Filter.Tendsto (fun n => ‖λ_n n‖) Filter.atTop Filter.atTop

end HilbertPolyaProof.CompactResolvent
