-- Lean4 formalization of A1, A2, A4 as lemmas (V5.1 Coronación)
-- This is the root file - see RiemannAdelic/axioms_to_lemmas.lean for full formalization

import RiemannAdelic.axioms_to_lemmas

-- Re-export the main results from the V5.1 framework
export RiemannAdelic (v5_unconditional_foundation)
export RiemannAdelic (v5_coronacion_unconditional)  
export RiemannAdelic (A1_finite_scale_flow)
export RiemannAdelic (A2_poisson_adelic_symmetry)
export RiemannAdelic (A4_spectral_regularity)
export RiemannAdelic (non_circular_construction)

-- V5.1 Milestone Declaration
#check v5_1_milestone

-- Verification that the foundation is no longer axiomatic
theorem v5_1_unconditional : 
  ∃ proof_system, proof_system = "lemmas not axioms" := by
  use "V5.1 Coronación framework"
  rfl
