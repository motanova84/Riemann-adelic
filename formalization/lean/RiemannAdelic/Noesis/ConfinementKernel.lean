/-!
# NOĒSIS — confined adelic kernel

This file records the mathematically safe part of the proposed confinement
construction. A pure translation kernel is distributional and is not
Hilbert–Schmidt on L²(R). We therefore use an honest L² kernel with a
Schwartz/Gaussian envelope.

Important: Hilbert–Schmidt does NOT by itself imply trace class, and a compact
perturbation of a non-compact-resolvent operator does NOT create compact
resolvent. Those are separate obligations.
-/

import Mathlib

namespace Noesis

/-- A positive confinement scale. -/
structure ConfinementParameter where
  beta : ℝ
  beta_pos : 0 < beta

/-- A finite family of prime-side coefficients. The analytic completion is
    deliberately separated from the finite construction. -/
structure ConfinedKernelData where
  coefficient : ℕ → ℝ
  shift : ℕ → ℝ
  parameter : ConfinementParameter

/-- The Gaussian envelope used in the proposed kernel. -/
def gaussian (β t u : ℝ) : ℝ := Real.exp (-β * (t^2 + u^2))

/-- Finite confined kernel. The sum is an honest function, unlike a sum of
    delta distributions supported on translated diagonals. -/
def confinedKernel (D : ConfinedKernelData) (N : ℕ) (t u : ℝ) : ℝ :=
  gaussian D.parameter.beta t u *
    ∑ n in Finset.range N, D.coefficient n *
      Real.exp (-D.parameter.beta * (u - t - D.shift n)^2)

/-- The analytic statement needed for Hilbert–Schmidt membership. -/
def IsHilbertSchmidtKernel
    (K : ℝ → ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∫⁻ t : ℝ, ∫⁻ u : ℝ, ENNReal.ofReal (K t u)^2 ≤ ENNReal.ofReal C

/-- The trace-class statement is kept separate: it requires an additional
    summability/factorisation argument beyond Hilbert–Schmidt membership. -/
def IsTraceClassKernel (K : ℝ → ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∫⁻ t : ℝ, ∫⁻ u : ℝ, ENNReal.ofReal |K t u| ≤ ENNReal.ofReal C

/-- A confined kernel is not itself a proof of compact resolvent. This marker
    keeps the resolvent theorem as an independent obligation. -/
structure CompactResolventProofObligation where
  freeOperator : Prop
  domain : Prop
  selfAdjoint : Prop
  coerciveConfinement : Prop
  compactEmbedding : Prop

/-- Spectral reality follows from self-adjointness, but the zero correspondence
    remains a separate proposition. -/
structure SpectralCorrespondenceObligation where
  selfAdjoint : Prop
  realSpectrum : Prop
  zeroCorrespondence : Prop

end Noesis
