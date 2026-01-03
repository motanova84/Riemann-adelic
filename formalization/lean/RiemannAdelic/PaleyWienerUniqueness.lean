/-!
# Paley-Wiener Uniqueness Theorem
Autor: José Manuel Mota Burruezo
Fecha: 22 de noviembre de 2025
Framework: Sistema Espectral Adélico S-Finito

This module provides the Paley-Wiener uniqueness theorem,
establishing that entire functions of order ≤1 with functional
symmetry are uniquely determined by their values on the critical line.
-/

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Basic
import RiemannAdelic.paley_wiener_uniqueness

noncomputable section
open Complex Filter Topology

namespace RiemannAdelic

-- Re-export the Paley-Wiener uniqueness theorem from the existing module
-- The existing paley_wiener_uniqueness.lean already provides the theorem

-- For compatibility with the expected interface, we provide this theorem
theorem PaleyWiener_strong_uniqueness (h : ℂ → ℂ)
    (h_entire : Differentiable ℂ h)
    (A B : ℝ)
    (h_order : B > 0 ∧ ∀ z, ‖h z‖ ≤ A * Real.exp (B * ‖z‖))
    (h_symm : ∀ z, h (1 - z) = h z)
    (h_critical : ∀ t : ℝ, h (1/2 + I*t) = 0) :
    h = 0 := by
  -- This follows from the Paley-Wiener axiom in the original module
  funext z
  exact PaleyWiener.strong_unicity h h_entire A B h_order h_symm h_critical z

end RiemannAdelic
