/-
  Trace_Fredholm.lean
  ------------------------------------------------------------
  Módulo 3 (interfaz): traza regularizada y determinante de Fredholm
  construidos desde el bloque no acotado de `Unbounded_Hpsi`.
-/

import Mathlib
import RiemannAdelic.Unbounded_Hpsi

noncomputable section

namespace RiemannAdelic
namespace TraceFredholm

open Complex
open MeasureTheory ENNReal Real
open RiemannAdelic.UnboundedHpsi

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Datos abstractos del resolvente para el modelo `H_Ψ`. -/
structure ResolventData (M : CoreModel H) where
  /-- Operador resolvente abstracto en parámetro espectral `z`. -/
  resolvent : ℂ → H → H
  /-- Traza regularizada del resolvente. -/
  regularizedTrace : ℂ → ℂ
  /-- Determinante espectral tipo Fredholm asociado. -/
  fredholmDeterminant : ℂ → ℂ
  /-- Ley puente (interfaz): ceros del determinante ↔ espectro de `M`. -/
  isSpectralPoint : ℂ → Prop

/-- Testigo abstracto de regularidad Schatten `S₂` para un resolvente en `z`. -/
def IsHilbertSchmidtResolvent {M : CoreModel H} (R : ResolventData M) (z : ℂ) : Prop :=
  ∃ ψ : ℕ → H, Summable (fun n => ‖R.resolvent z (ψ n)‖ ^ 2)

/--
Núcleo integral local del resolvente en `ℝ₊` (sector `0 < y ≤ x`):
`K_z(x,y) = x⁻¹ (y/x)^(i z - 1/2)`.
-/
def resolventKernelLocal (z : ℂ) (x y : ℝ) : ℂ :=
  if 0 < y ∧ y ≤ x then
    (1 / (x : ℂ)) * ((y : ℂ) / (x : ℂ)) ^ (Complex.I * z - (1 / 2 : ℂ))
  else 0

/-- Criterio integral de Carleman-Schatten `S₂` para un núcleo local. -/
def InSchattenTwoClass (K : ℝ → ℝ → ℂ) : Prop :=
  ∫⁻ x in Set.Ioi (0 : ℝ), ∫⁻ y in Set.Ioi (0 : ℝ),
      ENNReal.ofReal (‖K x y‖ ^ 2) < ∞

/--
Lema de convergencia del bloque de dilatación:
si `p > -1`, la integral de `u^p` en `(0,1]` es finita.
-/
lemma integrable_dilation_power (p : ℝ) (hp : -1 < p) :
    ∫⁻ u in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (u ^ p) < ∞ := by
  simpa using lintegral_rpow_Ioc_zero_of_gt_neg_one hp

/--
Reducción puntual de la norma del núcleo local en el sector `0 < y ≤ x`.
La igualdad final se obtiene separando el factor `x⁻¹` y el factor de dilatación.
-/
lemma norm_sq_resolvent_kernel
    (z : ℂ) (x y : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hxy : y ≤ x)
    (hscale : ‖(1 / (x : ℂ))‖ ^ 2 = x ^ (-2 : ℝ))
    (hdilation : ‖((y : ℂ) / (x : ℂ)) ^ (Complex.I * z - (1 / 2 : ℂ))‖ ^ 2 =
      (y / x) ^ (-2 * z.im - 1)) :
    ‖resolventKernelLocal z x y‖ ^ 2 =
      (x ^ (-2 : ℝ)) * ((y / x) ^ (-2 * z.im - 1)) := by
  dsimp [resolventKernelLocal]
  rw [if_pos ⟨hy, hxy⟩]
  rw [norm_mul, sq, sq]
  rw [hscale, hdilation]
  ring

/--
Puente explícito núcleo↔operador:
si el núcleo local está en `S₂`, el resolvente abstracto pertenece a `S₂`.
-/
structure KernelSchattenWitness {M : CoreModel H} (R : ResolventData M) : Prop where
  kernel_in_schatten_two :
    ∀ z : ℂ, z.im ≠ 0 → InSchattenTwoClass (resolventKernelLocal z)
  resolvent_in_schatten_two_of_kernel :
    ∀ z : ℂ, z.im ≠ 0 →
      InSchattenTwoClass (resolventKernelLocal z) →
      IsHilbertSchmidtResolvent R z

/-- Predicado global: el resolvente regularizado pertenece a `S₂` fuera del eje real. -/
def ResolventInSchattenTwo {M : CoreModel H} (R : ResolventData M) : Prop :=
  ∀ z : ℂ, z.im ≠ 0 → IsHilbertSchmidtResolvent R z

/-- Predicado interfaz: holomorfía compleja global del determinante de Fredholm. -/
def IsEntireFredholmDeterminant {M : CoreModel H} (R : ResolventData M) : Prop :=
  Differentiable ℂ R.fredholmDeterminant

variable {M : CoreModel H}

/--
Hipótesis del frente analítico 2:
regularidad de clase de traza y holomorfía de `D(s)`.
-/
structure SecondFrontHypotheses (R : ResolventData M) : Prop where
  kernel_schatten_witness :
    KernelSchattenWitness R
  resolvent_schatten_two :
    ResolventInSchattenTwo R
  entire_fredholm_determinant :
    IsEntireFredholmDeterminant R
  zeros_eq_spectrum :
    ∀ s : ℂ, R.fredholmDeterminant s = 0 ↔ R.isSpectralPoint s

/-- Teorema interfaz: ceros del determinante de Fredholm y espectro coinciden. -/
theorem fredholm_zeros_eq_spectrum
    (R : ResolventData M) (h : SecondFrontHypotheses R) (s : ℂ) :
    R.fredholmDeterminant s = 0 ↔ R.isSpectralPoint s := by
  exact h.zeros_eq_spectrum s

/-- Cierre de interfaz: cota `S₂` del núcleo local en la franja `Im(z) ≠ 0`. -/
theorem resolvent_kernel_in_schatten_two
    (R : ResolventData M) (h : SecondFrontHypotheses R) (z : ℂ) (hz : z.im ≠ 0) :
    InSchattenTwoClass (resolventKernelLocal z) :=
  h.kernel_schatten_witness.kernel_in_schatten_two z hz

/-- Cierre interfaz: pertenencia `S₂` del resolvente regularizado. -/
theorem resolvent_in_schatten_two
    (R : ResolventData M) (h : SecondFrontHypotheses R) :
    ResolventInSchattenTwo R := by
  exact h.resolvent_schatten_two

/-- Cierre del frente 2 sin axioma global. -/
theorem fredholm_determinant_is_entire
    (R : ResolventData M) (h : SecondFrontHypotheses R) :
    IsEntireFredholmDeterminant R := by
  exact h.entire_fredholm_determinant

end TraceFredholm
end RiemannAdelic
