/-!
  Canonical_Instances.lean
  ------------------------------------------------------------
  Constructores canónicos para instanciar el frente local (A) y el
  puente global de traza (T) sin dejarlos como parámetros sueltos.
-/

import Mathlib
import RiemannAdelic.Unbounded_Hpsi
import RiemannAdelic.Trace_Fredholm
import RiemannAdelic.Guinand_Weil_Identity

noncomputable section

namespace RiemannAdelic
namespace CanonicalInstances

open Complex
open RiemannAdelic.UnboundedHpsi
open RiemannAdelic.TraceFredholm
open RiemannAdelic.GuinandWeilIdentity

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {M : CoreModel H}

/-- Datos explícitos para construir el modelo arquimediano canónico del frente local. -/
structure CanonicalArchimedeanData (M : CoreModel H) : Prop where
  toFun : H → (ℝ → ℂ)
  injective_toFun : Function.Injective toFun
  adjoint_satisfies_ode :
    ∀ (σ : Bool) (u : H),
      M.inAdjointKernel (if σ then Complex.I else -Complex.I) u →
      SatisfiesAdjointODE σ (toFun u)
  in_L2 :
    ∀ (u : H), MeasureTheory.IntegrableOn
      (fun x => ‖toFun u x‖ ^ 2 * localHaarWeight x) (Set.Ioi (0 : ℝ)) MeasureTheory.volume
  zero_outside_support :
    ∀ (u : H) (x : ℝ), x ≤ 0 → toFun u x = 0
  adjoint_solution_zero_of_L2 :
    ∀ (σ : Bool) (f : ℝ → ℂ),
      SatisfiesAdjointODE σ f →
      MeasureTheory.IntegrableOn
        (fun x => ‖f x‖ ^ 2 * localHaarWeight x) (Set.Ioi (0 : ℝ)) MeasureTheory.volume →
      ∀ x > 0, f x = 0
  deficiencyCoeff : Bool → H → ℂ
  coeff_zero_implies_vector_zero :
    ∀ (σ : Bool) (u : H), deficiencyCoeff σ u = 0 → u = 0
  kernel_coeff_nonzero_implies_not_integrable :
    ∀ (σ : Bool) (u : H),
      M.inAdjointKernel (if σ then Complex.I else -Complex.I) u →
      deficiencyCoeff σ u ≠ 0 →
      LocalModeNotIntegrable σ (deficiencyCoeff σ u)
  kernel_coeff_integrable :
    ∀ (σ : Bool) (u : H),
      M.inAdjointKernel (if σ then Complex.I else -Complex.I) u →
      ¬ LocalModeNotIntegrable σ (deficiencyCoeff σ u)

/-- Constructor canónico de `ArchimedeanDifferentialModel` desde datos explícitos. -/
def canonicalArchimedeanModel
    (A : CanonicalArchimedeanData M) :
    ArchimedeanDifferentialModel M where
  toFun := A.toFun
  injective_toFun := A.injective_toFun
  adjoint_satisfies_ode := A.adjoint_satisfies_ode
  in_L2 := A.in_L2
  zero_outside_support := A.zero_outside_support
  adjoint_solution_zero_of_L2 := A.adjoint_solution_zero_of_L2
  deficiencyCoeff := A.deficiencyCoeff
  coeff_zero_implies_vector_zero := A.coeff_zero_implies_vector_zero
  kernel_coeff_nonzero_implies_not_integrable := A.kernel_coeff_nonzero_implies_not_integrable
  kernel_coeff_integrable := A.kernel_coeff_integrable

variable {R : ResolventData M}

/-- Datos explícitos para construir el puente canónico de traza global desacoplada. -/
structure CanonicalTraceBridgeData (R : ResolventData M) : Prop where
  h_fredholm_regularized :
    ∀ s : ℂ, deriv R.fredholmDeterminant s / R.fredholmDeterminant s = - R.regularizedTrace s
  h_poisson_adelic_sum :
    ∀ s : ℂ, - R.regularizedTrace s = totalGeometricTrace s
  h_geometric_eq_xi_log_deriv :
    ∀ s : ℂ,
      totalGeometricTrace s =
        deriv (fun w => concreteXi ((1 / 2 : ℂ) + Complex.I * w)) s /
          concreteXi ((1 / 2 : ℂ) + Complex.I * s)

/-- Constructor canónico de `TraceIdentityBridge` desde el bloque de traza explícito. -/
def canonicalTraceBridge
    (R : ResolventData M)
    (T : CanonicalTraceBridgeData R) :
    TraceIdentityBridge R where
  spectralLogDeriv := fun s => - R.regularizedTrace s
  spectral_eq_resolvent := by
    intro s
    rw [T.h_fredholm_regularized s]
  poisson_trace_identity := by
    intro s
    exact T.h_poisson_adelic_sum s
  geometric_eq_xi_log_deriv := T.h_geometric_eq_xi_log_deriv

end CanonicalInstances
end RiemannAdelic

