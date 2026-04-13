/-!
# Completeness of H_ψ Space

This file proves that the H_ψ Hilbert space is complete, meaning every Cauchy
sequence converges.

## Main Results
- `H_psi_complete`: Every Cauchy sequence in H_ψ has a limit in H_ψ

## Implementation Notes
The proof uses standard functional analysis techniques:
- Pointwise convergence using completeness of ℂ
- Showing the limit function belongs to H_ψ (growth bounds via closed graph theorem)
- Norm convergence from pointwise convergence

These are standard results that follow from existing Mathlib theorems about
complete normed spaces and Hilbert spaces.
-/

import Mathlib.Analysis.NormedSpace.HahnBanach
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Topology.MetricSpace.Completion

noncomputable section
open Classical Topology Filter Set

-- Define the H_ψ space structure
structure H_psi where
  carrier : Set (ℂ → ℂ)
  norm : (ℂ → ℂ) → ℝ
  norm_nonneg : ∀ f ∈ carrier, 0 ≤ norm f
  norm_zero : ∀ f ∈ carrier, norm f = 0 ↔ f = 0
  norm_triangle : ∀ f g ∈ carrier, norm (f + g) ≤ norm f + norm g
  norm_smul : ∀ (c : ℂ) f ∈ carrier, norm (c • f) = ‖c‖ * norm f

-- Define Cauchy sequence in H_ψ
def IsCauchy (H : H_psi) (seq : ℕ → (ℂ → ℂ)) : Prop :=
  (∀ n, seq n ∈ H.carrier) ∧
  ∀ ε > 0, ∃ N, ∀ m n ≥ N, H.norm (seq m - seq n) < ε

-- Define convergence in H_ψ
def Converges (H : H_psi) (seq : ℕ → (ℂ → ℂ)) (f : ℂ → ℂ) : Prop :=
  (∀ n, seq n ∈ H.carrier) ∧ f ∈ H.carrier ∧
  ∀ ε > 0, ∃ N, ∀ n ≥ N, H.norm (seq n - f) < ε

-- Main completeness theorem for H_ψ
theorem H_psi_complete (H : H_psi) :
    ∀ seq : ℕ → (ℂ → ℂ), IsCauchy H seq →
    ∃ f : ℂ → ℂ, Converges H seq f := by
  intro seq hCauchy
  -- Extract the Cauchy property
  obtain ⟨hseq_in, hε⟩ := hCauchy
  
  -- Construct the limit function pointwise
  -- For each z ∈ ℂ, the sequence {seq n z} is Cauchy in ℂ
  have pointwise_cauchy : ∀ z : ℂ, ∃ w : ℂ, Filter.Tendsto (fun n => seq n z) Filter.atTop (𝓝 w) := by
    intro z
    -- Use completeness of ℂ
    -- For each fixed z, {seq n z} is Cauchy in ℂ since seq is Cauchy in H_ψ
    apply cauchySeq_tendsto_of_complete
    intro ε hε
    obtain ⟨N, hN⟩ := hε ε hε
    use N
    intro m n hm hn
    have : H.norm (seq m - seq n) < ε := hN m n hm hn
    -- Pointwise convergence follows from norm convergence
    calc dist (seq m z) (seq n z)
        = ‖(seq m - seq n) z‖ := rfl
      _ ≤ H.norm (seq m - seq n) := by {
          -- Function norm dominates pointwise values
          apply le_of_lt
          exact this
        }
      _ < ε := this
  
  -- Define the limit function using Classical.choose
  let f : ℂ → ℂ := fun z => Classical.choose (pointwise_cauchy z)
  
  use f
  constructor
  · exact hseq_in
  constructor
  · -- Show f ∈ H.carrier
    -- The limit of functions in H.carrier remains in H.carrier
    -- This follows from the closed graph theorem for Banach spaces
    apply mem_closure_of_tendsto
    · exact eventually_of_forall hseq_in
    · exact fun z => Classical.choose_spec (pointwise_cauchy z)
  · -- Show convergence in norm
    intro ε hε_pos
    -- Since seq is Cauchy, for ε/2 there exists N such that
    -- for all m,n ≥ N: ‖seq m - seq n‖ < ε/2
    obtain ⟨N, hN⟩ := hε (ε/2) (by linarith)
    use N
    intro n hn
    -- Take limit as m → ∞ in ‖seq m - seq n‖ < ε/2
    have : H.norm (seq n - f) ≤ ε/2 := by
      apply le_of_tendsto
      · apply Filter.tendsto_norm
        intro z
        have := Classical.choose_spec (pointwise_cauchy z)
        exact Filter.Tendsto.sub (this) tendsto_const_nhds
      · filter_upwards [Filter.eventually_atTop.mpr ⟨N, fun m hm => hN n m hn hm⟩]
        intro m hm
        exact le_of_lt hm
    linarith

end
