/-
  Poisson_Mellin.lean
  ------------------------------------------------------------
  Módulo tripartito: interfaz Poisson–Mellin para el puente
  analítico entre traza regularizada y `Ξ(1/2 + i·s)`.
-/

import Mathlib
import RiemannAdelic.Trace_Fredholm

noncomputable section

namespace RiemannAdelic
namespace PoissonMellin

open Complex
open RiemannAdelic.TraceFredholm

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {M : RiemannAdelic.UnboundedHpsi.CoreModel H} (R : ResolventData M)

/-- Testigo explícito del frente Poisson–Mellin para un resolvente dado. -/
structure PoissonMellinData where
  /-- Xi completada concreta en el frente analítico. -/
  xi : ℂ → ℂ
  /-- Flujo de traza usado como cantidad intermedia. -/
  traceFlow : ℂ → ℂ
  /-- Identificación de la traza regularizada con el flujo de Poisson–Mellin. -/
  trace_regularized_eq_flow :
    ∀ s : ℂ, R.regularizedTrace s = traceFlow s
  /-- Lado Fredholm como derivada logarítmica del flujo. -/
  flow_eq_logDeriv_det :
    ∀ s : ℂ,
      traceFlow s =
        deriv (fun w => Complex.log (R.fredholmDeterminant w)) s
  /-- Lado Xi como derivada logarítmica del flujo. -/
  flow_eq_logDeriv_xi :
    ∀ s : ℂ,
      traceFlow s =
        deriv (fun w => Complex.log (xi ((1 / 2 : ℂ) + Complex.I * w))) s
  /-- Normalización de origen para el cierre de unicidad. -/
  normalization_at_zero :
    R.fredholmDeterminant 0 = xi (1 / 2 : ℂ)

/-- Igualdad de derivadas logarítmicas obtenida del testigo Poisson–Mellin. -/
theorem trace_formula_poisson_mellin_identity
    (P : PoissonMellinData R) :
    ∀ s : ℂ,
      deriv (fun w => Complex.log (R.fredholmDeterminant w)) s =
      deriv (fun w => Complex.log (P.xi ((1 / 2 : ℂ) + Complex.I * w))) s := by
  intro s
  calc
    deriv (fun w => Complex.log (R.fredholmDeterminant w)) s
        = P.traceFlow s := by
            symm
            exact P.flow_eq_logDeriv_det s
    _ = deriv (fun w => Complex.log (P.xi ((1 / 2 : ℂ) + Complex.I * w))) s :=
          P.flow_eq_logDeriv_xi s

/-- Hipótesis de unicidad tipo Hadamard para cerrar `D ≡ Ξ`. -/
structure HadamardUniquenessHypothesis (P : PoissonMellinData R) : Prop where
  conclude :
    (∀ s : ℂ,
      deriv (fun w => Complex.log (R.fredholmDeterminant w)) s =
      deriv (fun w => Complex.log (P.xi ((1 / 2 : ℂ) + Complex.I * w))) s) →
    R.fredholmDeterminant 0 = P.xi (1 / 2 : ℂ) →
    ∀ s : ℂ, R.fredholmDeterminant s = P.xi ((1 / 2 : ℂ) + Complex.I * s)

/-- Cierre interfaz del puente `D(s) ≡ Ξ(1/2 + i s)` sin axioma global suelto. -/
theorem fredholm_det_identically_equals_xi
    (P : PoissonMellinData R)
    (hH : HadamardUniquenessHypothesis R P) :
    ∀ s : ℂ, R.fredholmDeterminant s = P.xi ((1 / 2 : ℂ) + Complex.I * s) := by
  exact hH.conclude (trace_formula_poisson_mellin_identity R P) P.normalization_at_zero

end PoissonMellin
end RiemannAdelic

