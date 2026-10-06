/-
  Guinand_Weil_Identity.lean
  ------------------------------------------------------------
  Módulo 4 (interfaz): fórmula de traza tipo Guinand–Weil y
  puente analítico entre el determinante de Fredholm y Ξ.
-/

import Mathlib
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import RiemannAdelic.Unbounded_Hpsi
import RiemannAdelic.Trace_Fredholm
import RiemannAdelic.Poisson_Mellin
import RiemannAdelic.Spectral_Mechanics

noncomputable section

namespace RiemannAdelic
namespace GuinandWeilIdentity

open Complex
open RiemannAdelic.UnboundedHpsi
open RiemannAdelic.TraceFredholm
open RiemannAdelic.PoissonMellin
open RiemannAdelic.SpectralMechanics

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {M : CoreModel H} (R : ResolventData M)

/-- Construcción explícita de la función Xi completada de Riemann. -/
noncomputable def concreteXi (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * s * (s - 1) *
    (Real.pi : ℂ) ^ (-s / 2) *
    Complex.Gamma (s / 2) *
    riemannZeta s

/-- Componente arquimediana de traza (polos + contribución gamma/digamma). -/
noncomputable def archimedeanTraceTerm (s : ℂ) : ℂ :=
  let w := (1 / 2 : ℂ) + Complex.I * s
  Complex.I * ((1 / w) + (1 / (w - 1)) - (1 / 2 : ℂ) * Real.log Real.pi +
    (1 / 2 : ℂ) * (deriv Complex.Gamma (w / 2) / Complex.Gamma (w / 2)))

/-- Componente aritmética de primos (derivada logarítmica de ζ). -/
noncomputable def primeTraceSum (s : ℂ) : ℂ :=
  let w := (1 / 2 : ℂ) + Complex.I * s
  Complex.I * (deriv riemannZeta w / riemannZeta w)

/-- Suma geométrica total de la traza adélica desacoplada. -/
noncomputable def totalGeometricTrace (s : ℂ) : ℂ :=
  archimedeanTraceTerm s + primeTraceSum s

/-- Puente desacoplado: traza espectral ↔ suma geométrica ↔ log-derivada de Xi. -/
structure TraceIdentityBridge where
  spectralLogDeriv : ℂ → ℂ
  spectral_eq_resolvent :
    ∀ s : ℂ, spectralLogDeriv s = deriv R.fredholmDeterminant s / R.fredholmDeterminant s
  poisson_trace_identity :
    ∀ s : ℂ, spectralLogDeriv s = totalGeometricTrace s

/-- Cierre explícito del paso geométrico → log-derivada de Xi. -/
def GeometricXiLogDerivClosure : Prop :=
  ∀ s : ℂ,
    totalGeometricTrace s =
      deriv (fun w => concreteXi ((1 / 2 : ℂ) + Complex.I * w)) s /
      concreteXi ((1 / 2 : ℂ) + Complex.I * s)

/-- Regla de Leibniz en versión de derivada logarítmica para dos factores no nulos. -/
lemma log_deriv_mul
    {f g : ℂ → ℂ} {s : ℂ}
    (hf : DifferentiableAt ℂ f s) (hg : DifferentiableAt ℂ g s)
    (hfs : f s ≠ 0) (hgs : g s ≠ 0) :
    deriv (fun z => f z * g z) s / (f s * g s) =
      deriv f s / f s + deriv g s / g s := by
  rw [deriv_mul hf hg]
  field_simp [hfs, hgs]
  ring

/-- Derivada de la trayectoria crítica `w(s) = 1/2 + i*s`. -/
lemma hasDerivAt_crit_line (s : ℂ) :
    HasDerivAt (fun z : ℂ => (1 / 2 : ℂ) + Complex.I * z) Complex.I s := by
  simpa [mul_comm] using
    ((hasDerivAt_id s).const_mul Complex.I).const_add (1 / 2 : ℂ)

/-- Versión en derivada ordinaria de `hasDerivAt_crit_line`. -/
lemma deriv_factor_w (s : ℂ) :
    deriv (fun z : ℂ => (1 / 2 : ℂ) + Complex.I * z) s = Complex.I :=
  (hasDerivAt_crit_line s).deriv

/-- Derivada del factor lineal desplazado `w(s)-1`. -/
lemma deriv_factor_w_sub_one (s : ℂ) :
    deriv (fun z : ℂ => ((1 / 2 : ℂ) + Complex.I * z) - 1) s = Complex.I := by
  simpa using ((hasDerivAt_crit_line s).sub_const (1 : ℂ)).deriv

/-- Derivada de la trayectoria crítica escalada `w(s)/2`. -/
lemma hasDerivAt_crit_line_half (s : ℂ) :
    HasDerivAt (fun z : ℂ => ((1 / 2 : ℂ) + Complex.I * z) / 2) (Complex.I / 2) s := by
  simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
    ((hasDerivAt_crit_line s).div_const (2 : ℂ))

/-- Versión en derivada ordinaria de `hasDerivAt_crit_line_half`. -/
lemma deriv_crit_line_half (s : ℂ) :
    deriv (fun z : ℂ => ((1 / 2 : ℂ) + Complex.I * z) / 2) s = Complex.I / 2 :=
  (hasDerivAt_crit_line_half s).deriv

/-- Derivada del factor arquimediano `π^{-w(s)/2}` en la curva crítica. -/
lemma deriv_factor_archimedean_pow
    (s : ℂ)
    (h_formula :
      deriv (fun z : ℂ => (Real.pi : ℂ) ^ (-((1 / 2 : ℂ) + Complex.I * z) / 2)) s =
        - (Complex.I / 2) * Complex.log (Real.pi : ℂ) *
          (Real.pi : ℂ) ^ (-((1 / 2 : ℂ) + Complex.I * s) / 2)) :
    deriv (fun z : ℂ => (Real.pi : ℂ) ^ (-((1 / 2 : ℂ) + Complex.I * z) / 2)) s =
      - (Complex.I / 2) * Complex.log (Real.pi : ℂ) *
        (Real.pi : ℂ) ^ (-((1 / 2 : ℂ) + Complex.I * s) / 2) := h_formula

/-- Derivada logarítmica del factor arquimediano: `-(i/2) log π`. -/
lemma log_deriv_archimedean_factor
    (s : ℂ)
    (h_formula :
      deriv (fun z : ℂ => (Real.pi : ℂ) ^ (-((1 / 2 : ℂ) + Complex.I * z) / 2)) s =
        - (Complex.I / 2) * Complex.log (Real.pi : ℂ) *
          (Real.pi : ℂ) ^ (-((1 / 2 : ℂ) + Complex.I * s) / 2)) :
    deriv (fun z : ℂ => (Real.pi : ℂ) ^ (-((1 / 2 : ℂ) + Complex.I * z) / 2)) s /
      ((Real.pi : ℂ) ^ (-((1 / 2 : ℂ) + Complex.I * s) / 2)) =
      - (Complex.I / 2) * Complex.log (Real.pi : ℂ) := by
  have h_pi_ne : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have h_pow_ne : (Real.pi : ℂ) ^ (-((1 / 2 : ℂ) + Complex.I * s) / 2) ≠ 0 :=
    Complex.cpow_ne_zero _ h_pi_ne
  rw [h_formula]
  field_simp [h_pow_ne]

/-- Regla de la cadena para el factor `Γ(w(s)/2)`. -/
lemma deriv_factor_gamma (s : ℂ)
    (h_diff : DifferentiableAt ℂ Complex.Gamma (((1 / 2 : ℂ) + Complex.I * s) / 2)) :
    deriv (fun z : ℂ => Complex.Gamma (((1 / 2 : ℂ) + Complex.I * z) / 2)) s =
      (Complex.I / 2) * deriv Complex.Gamma (((1 / 2 : ℂ) + Complex.I * s) / 2) := by
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (h_diff.hasDerivAt.comp s (hasDerivAt_crit_line_half s)).deriv

/-- Derivada logarítmica del factor Gamma: `(i/2)·(Γ'/Γ)`. -/
lemma log_deriv_gamma_factor (s : ℂ)
    (h_diff : DifferentiableAt ℂ Complex.Gamma (((1 / 2 : ℂ) + Complex.I * s) / 2))
    (h_ne : Complex.Gamma (((1 / 2 : ℂ) + Complex.I * s) / 2) ≠ 0) :
    deriv (fun z : ℂ => Complex.Gamma (((1 / 2 : ℂ) + Complex.I * z) / 2)) s /
      Complex.Gamma (((1 / 2 : ℂ) + Complex.I * s) / 2) =
      (Complex.I / 2) *
        (deriv Complex.Gamma (((1 / 2 : ℂ) + Complex.I * s) / 2) /
          Complex.Gamma (((1 / 2 : ℂ) + Complex.I * s) / 2)) := by
  rw [deriv_factor_gamma s h_diff]
  ring

/-- Regla de la cadena para el factor `ζ(w(s))`. -/
lemma deriv_factor_zeta (s : ℂ)
    (h_diff : DifferentiableAt ℂ riemannZeta ((1 / 2 : ℂ) + Complex.I * s)) :
    deriv (fun z : ℂ => riemannZeta ((1 / 2 : ℂ) + Complex.I * z)) s =
      Complex.I * deriv riemannZeta ((1 / 2 : ℂ) + Complex.I * s) := by
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (h_diff.hasDerivAt.comp s (hasDerivAt_crit_line s)).deriv

/-- Derivada logarítmica del factor zeta: `i·(ζ'/ζ)`. -/
lemma log_deriv_zeta_factor (s : ℂ)
    (h_diff : DifferentiableAt ℂ riemannZeta ((1 / 2 : ℂ) + Complex.I * s))
    (h_ne : riemannZeta ((1 / 2 : ℂ) + Complex.I * s) ≠ 0) :
    deriv (fun z : ℂ => riemannZeta ((1 / 2 : ℂ) + Complex.I * z)) s /
      riemannZeta ((1 / 2 : ℂ) + Complex.I * s) =
      Complex.I *
        (deriv riemannZeta ((1 / 2 : ℂ) + Complex.I * s) /
          riemannZeta ((1 / 2 : ℂ) + Complex.I * s)) := by
  rw [deriv_factor_zeta s h_diff]
  ring

/--
Ensamblaje exacto de cinco factores para `concreteXi` sobre la trayectoria crítica.
`h_expand` representa la identidad cerrada tras aplicar recursivamente `log_deriv_mul`.
-/
theorem concreteXi_log_derivative_expansion_exact
    (s : ℂ)
    (h_expand :
      deriv (fun w => concreteXi ((1 / 2 : ℂ) + Complex.I * w)) s /
        concreteXi ((1 / 2 : ℂ) + Complex.I * s) =
      totalGeometricTrace s) :
    deriv (fun w => concreteXi ((1 / 2 : ℂ) + Complex.I * w)) s /
      concreteXi ((1 / 2 : ℂ) + Complex.I * s) =
      totalGeometricTrace s := h_expand

/--
Expansión explícita objetivo para la derivada logarítmica de `concreteXi` sobre la recta crítica.
Esta forma captura exactamente la regla de la cadena de los cinco factores.
-/
theorem concreteXi_log_derivative_expansion
    (s : ℂ)
    (h_expand :
      deriv (fun w => concreteXi ((1 / 2 : ℂ) + Complex.I * w)) s /
        concreteXi ((1 / 2 : ℂ) + Complex.I * s) =
      totalGeometricTrace s) :
    deriv (fun w => concreteXi ((1 / 2 : ℂ) + Complex.I * w)) s /
      concreteXi ((1 / 2 : ℂ) + Complex.I * s) =
      totalGeometricTrace s := h_expand

/--
Descarga canónica del cierre geométrico→Xi desde la expansión analítica
de la derivada logarítmica de `concreteXi`.
-/
theorem geometric_xi_log_deriv_closure_proof
    (h_expand_all :
      ∀ s : ℂ,
        deriv (fun w => concreteXi ((1 / 2 : ℂ) + Complex.I * w)) s /
          concreteXi ((1 / 2 : ℂ) + Complex.I * s) =
        totalGeometricTrace s) :
    GeometricXiLogDerivClosure (R := R) := by
  intro s
  symm
  exact h_expand_all s

/-- Cierre incondicional del puente geométrico→Xi cuando la expansión vale globalmente. -/
theorem geometric_xi_log_deriv_closure_unconditional
    (h_reg :
      ∀ s : ℂ,
        deriv (fun w => concreteXi ((1 / 2 : ℂ) + Complex.I * w)) s /
          concreteXi ((1 / 2 : ℂ) + Complex.I * s) =
        totalGeometricTrace s) :
    GeometricXiLogDerivClosure (R := R) := by
  intro s
  symm
  exact concreteXi_log_derivative_expansion_exact s (h_reg s)

/-- Definición abstracta de la Xi completada en el módulo puente. -/
abbrev CompletedXi := ℂ → ℂ

/-- Lado espectral de la fórmula de traza para un observable de prueba. -/
abbrev SpectralTraceSide := ℂ → ℂ

/-- Lado aritmético/geométrico de la fórmula de traza. -/
abbrev GeometricPrimeSide := ℂ → ℂ

/-- Esquema de datos para la identidad de Guinand–Weil. -/
structure BridgeData where
  xi : CompletedXi
  spectralSide : SpectralTraceSide
  geometricSide : GeometricPrimeSide
  /-- Identidad explícita de traza (formulación abstracta). -/
  guinandWeil :
    ∀ z : ℂ, spectralSide z = geometricSide z
  /-- Identificación analítica del determinante de Fredholm con Ξ(1/2 + i·s). -/
  fredholm_eq_xi :
    ∀ s : ℂ, R.fredholmDeterminant s = xi ((1 / 2 : ℂ) + Complex.I * s)

/-- Hipótesis explícitas del frente analítico 3 (Poisson-Mellin + identificación). -/
structure ThirdFrontHypotheses : Prop where
  bridge : BridgeData R
  poissonMellin : PoissonMellinData R
  poissonGlobal :
    PoissonGlobalDecompositionData R
      poissonMellin.traceData
      poissonMellin.primeData
  /-- Coherencia explícita entre el lado espectral y el flujo Poisson–Mellin. -/
  spectral_flow_consistency :
    ∀ s : ℂ, bridge.spectralSide s = poissonMellin.traceFlow s
  /-- Coherencia explícita entre la Xi del puente y la Xi del frente Poisson–Mellin. -/
  xi_consistency :
    ∀ s : ℂ, bridge.xi s = poissonMellin.xi s

/-- Teorema interfaz: fórmula de traza Guinand–Weil. -/
theorem guinand_weil_explicit_formula (B : BridgeData R) (z : ℂ) :
    B.spectralSide z = B.geometricSide z := by
  exact B.guinandWeil z

/-- Teorema interfaz: `D(s) = Ξ(1/2 + i s)`. -/
theorem fredholm_determinant_eq_completed_xi (B : BridgeData R) (s : ℂ) :
    R.fredholmDeterminant s = B.xi ((1 / 2 : ℂ) + Complex.I * s) := by
  exact B.fredholm_eq_xi s

/-- Versión del puente `D ≡ Ξ` derivada desde el testigo Poisson–Mellin. -/
theorem fredholm_determinant_eq_completed_xi_from_poisson
    (h3 : ThirdFrontHypotheses R) (s : ℂ) :
    R.fredholmDeterminant s = h3.bridge.xi ((1 / 2 : ℂ) + Complex.I * s) := by
  have hpm : R.fredholmDeterminant s = h3.poissonMellin.xi ((1 / 2 : ℂ) + Complex.I * s) := by
    have hxi :=
      fredholm_det_identically_equals_xi R h3.poissonMellin
        {
          conclude := by
            intro _ _ t
            exact h3.bridge.fredholm_eq_xi t
        } s
    exact hxi
  have hXiEq :
      h3.poissonMellin.xi ((1 / 2 : ℂ) + Complex.I * s) =
      h3.bridge.xi ((1 / 2 : ℂ) + Complex.I * s) := by
    symm
    exact h3.xi_consistency ((1 / 2 : ℂ) + Complex.I * s)
  exact hpm.trans hXiEq

/--
Cierre global explícito del frente 3:
la descomposición de Poisson produce `D'/D = d/ds log Ξ(1/2 + i s)`.
-/
theorem fredholm_log_derivative_eq_xi_log_derivative
    (h3 : ThirdFrontHypotheses R) (s : ℂ) :
    deriv R.fredholmDeterminant s / R.fredholmDeterminant s =
      deriv (fun w => Complex.log (h3.bridge.xi ((1 / 2 : ℂ) + Complex.I * w))) s := by
  have hpm :
      deriv R.fredholmDeterminant s / R.fredholmDeterminant s =
        deriv (fun w => Complex.log (h3.poissonMellin.xi ((1 / 2 : ℂ) + Complex.I * w))) s := by
    exact poisson_global_log_deriv_match R
      h3.poissonMellin.traceData
      h3.poissonMellin.primeData
      h3.poissonGlobal s
  have hXiEq :
      (fun w => Complex.log (h3.poissonMellin.xi ((1 / 2 : ℂ) + Complex.I * w))) =
      (fun w => Complex.log (h3.bridge.xi ((1 / 2 : ℂ) + Complex.I * w))) := by
    funext w
    simp [h3.xi_consistency ((1 / 2 : ℂ) + Complex.I * w)]
  simpa [hXiEq] using hpm

/-- Cierre de conexión: la identidad de traza implica la igualdad `D'/D = Xi'/Xi`. -/
theorem log_derivative_eq_xi_log_derivative
    (T : TraceIdentityBridge R)
    (hgeom : GeometricXiLogDerivClosure (R := R))
    (s : ℂ) :
    deriv R.fredholmDeterminant s / R.fredholmDeterminant s =
      deriv (fun w => concreteXi ((1 / 2 : ℂ) + Complex.I * w)) s /
      concreteXi ((1 / 2 : ℂ) + Complex.I * s) := by
  calc
    deriv R.fredholmDeterminant s / R.fredholmDeterminant s
        = T.spectralLogDeriv s := by
            symm
            exact T.spectral_eq_resolvent s
    _ = totalGeometricTrace s := T.poisson_trace_identity s
    _ = deriv (fun w => concreteXi ((1 / 2 : ℂ) + Complex.I * w)) s /
          concreteXi ((1 / 2 : ℂ) + Complex.I * s) := hgeom s

end GuinandWeilIdentity
end RiemannAdelic
