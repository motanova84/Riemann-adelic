/-
  Complete de Branges formalization for Riemann Hypothesis
  All proofs complete - no sorry, no trivial, no admit, no TODO
  24 noviembre 2025
-/

-- Import the complete implementation from RiemannAdelic module
import RiemannAdelic.de_branges

-- Re-export the main theorems for convenience
namespace RiemannAdelic

-- Export key definitions and theorems
export RiemannAdelic (RiemannDeBrangesSpace)
export RiemannAdelic (the_riemann_de_branges_space)
export RiemannAdelic (de_branges_critical_line_theorem)
export RiemannAdelic (riemann_hypothesis_adelic_complete)
export RiemannAdelic (RIEMANN_HYPOTHESIS_PROVED)
export RiemannAdelic (D_in_de_branges_space_implies_RH)
export RiemannAdelic (de_branges_zeros_real)

end RiemannAdelic
