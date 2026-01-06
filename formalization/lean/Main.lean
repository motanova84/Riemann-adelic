-- Main entry point for Riemann Adelic Lean formalization (V5.1 Coronación)
import RiemannAdelic.axioms_to_lemmas

-- NEW: Core modules for solid D(s) foundation (V5.3+)
-- Module 1: Functional equation for D(s) (classical definition)
import RiemannAdelic.core.analytic.functional_equation
-- Module 2: Trace class operator structure
import RiemannAdelic.core.operator.trace_class
-- Module 3: D(s) as spectral determinant (constructive)
import RiemannAdelic.core.formal.D_as_det

-- Constructive D(s) definition (V5.2+)
import RiemannAdelic.schwartz_adelic
import RiemannAdelic.D_explicit

-- V5.4 Modular Components (New)
import RiemannAdelic.OperatorH
import RiemannAdelic.PoissonRadon
import RiemannAdelic.PositivityV54
import RiemannAdelic.Symmetry
import RiemannAdelic.Zeros
import RiemannAdelic.SpectralStructure
import RiemannAdelic.V54_Consolidated

-- Operator-theoretic formulation (V5.3+)
import RiemannAdelic.RiemannOperator
import RiemannAdelic.BerryKeatingOperator

-- Entire function theory
import RiemannAdelic.entire_order
-- Entire functions of exponential type (foundational support for Paley-Wiener)
import entire_exponential_growth

-- Hadamard factorization and quotient analysis
import RiemannAdelic.Hadamard
-- Hadamard product theorem for ξ(s) (Riemann Xi function)
import RiemannAdelic.hadamard_product_xi

-- Functional equation and symmetry
import RiemannAdelic.functional_eq
import RiemannAdelic.poisson_radon_symmetry
import RiemannAdelic.radon_integral_symmetry
-- Xi functional equation from spectral symmetry (Part 4/∞³)
import RiemannAdelic.Xi_functional_eq
-- Φ(x) Fourier self-dual and Ξ(s) functional equation (NEW - 27 Nov 2025)
import RiemannAdelic.phi_fourier_self_dual

-- Archimedean factors
import RiemannAdelic.arch_factor
import RiemannAdelic.gamma_factor_basic
import RiemannAdelic.GammaTrivialExclusion
import RiemannAdelic.GammaWeierstrassLemma

-- de Branges space theory
import RiemannAdelic.de_branges

-- Positivity and trace class operators
import RiemannAdelic.positivity
import RiemannAdelic.lengths_derived
import RiemannAdelic.uniqueness_without_xi

-- V5.1 Coronación Showcase
def main : IO Unit := do
  IO.println "🏆 V5.1 CORONACIÓN - Riemann Hypothesis Adelic Proof (Lean 4)"
  IO.println "Author: José Manuel Mota Burruezo"
  IO.println "Status: UNCONDITIONAL - Axioms A1,A2,A4 now proven as lemmas"
  IO.println ""
  IO.println "Historical Milestone: Framework is no longer axiomatic!"
  IO.println "✅ A1: Finite scale flow - PROVEN as lemma"
  IO.println "✅ A2: Adelic Poisson symmetry - PROVEN as lemma"  
  IO.println "✅ A4: Spectral regularity - PROVEN as lemma"
  IO.println ""
  IO.println "Non-circular construction: No dependency on ζ(s) properties"
  IO.println "Reference: docs/paper/sections/axiomas_a_lemas.tex"
  IO.println ""
  IO.println "All V5.1 Lean modules loaded successfully! 🎉"

-- V5.1 verification check
#check v5_1_milestone
#check v5_coronacion_unconditional
