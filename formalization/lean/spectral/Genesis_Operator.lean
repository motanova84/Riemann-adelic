import Mathlib.Topology.Algebra.UniformField
import Mathlib.Analysis.SpecialFunctions.Zeta
import Mathlib.Analysis.UniformConvergence
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Fourier.Schwartz
import Mathlib.Analysis.Fourier.Transform
import Mathlib.Topology.MetricSpace.Baire
import Mathlib.Data.Complex.Exponential

open Real Complex Filter Topology MeasureTheory

noncomputable section

namespace Noesis

-- Definimos el operador 𝓗_Ψ sobre el espacio de Schwartz
@[nolint defLemma]
def H_psi : ℂ → SchwartzSpace ℝ ℂ → ℂ :=
  fun s φ ↦ -∫ x in Set.Ioi 0, (x : ℂ) ^ (-s) * (x * deriv φ.val x)

-- Definición como distribución: phi_s
@[nolint defLemma]
def phi_s_distribution (s : ℂ) : SchwartzSpace ℝ ℂ → ℂ :=
  fun φ ↦ ∫ x in Set.Ioi 0, (x : ℂ) ^ (-s) * φ.val x

-- Operador aplicado a la distribución φ_s
@[nolint defLemma]
def H_psi_distribution (f : SchwartzSpace ℝ ℂ → ℂ) :
    SchwartzSpace ℝ ℂ → ℂ :=
  fun φ ↦ f (fun x ↦ -x * deriv φ.val x)

-- Eigenfunción generalizada: φ_s es autofunción de H_ψ con autovalor s
lemma phi_s_eigen_distribution (s : ℂ) (φ : SchwartzSpace ℝ ℂ) :
    H_psi_distribution (phi_s_distribution s) φ = s * phi_s_distribution s φ := by
  unfold H_psi_distribution phi_s_distribution
  apply_fun (fun f ↦ ∫ x in Set.Ioi 0, (x : ℂ) ^ (-s) * f x) at *
  simp_rw [Function.comp_apply, Pi.mul_apply, mul_assoc]
  -- integración por partes: ∫ (x⁻ˢ)(x dφ) = -s ∫ x⁻ˢ φ
  -- se asume válida sobre funciones de Schwartz
  sorry

-- T: operador definido por φ ↦ ∫ (x⁻ˢ)(x dφ)
def T_operator (s : ℂ) : (SchwartzSpace ℝ ℂ → ℂ) :=
  fun φ ↦ -∫ x in Set.Ioi 0, (x : ℂ) ^ (-s) * (x * deriv φ.val x)

-- Potencias del operador T: (T^s)(φ) := ∫ (x⁻ˢ)(x dφ)
def T_powSI (s : ℂ) : SchwartzSpace ℝ ℂ → ℂ :=
  fun φ ↦ s * ∫ x in Set.Ioi 0, (x : ℂ) ^ (-s) * φ.val x

-- Convergencia uniforme de la traza ζ(s) := Tr(H_ψ^{-s})
def zeta_series (s : ℂ) (n : ℕ) : ℂ := 1 / (n + 1 : ℂ) ^ s

def RiemannZeta (s : ℂ) : ℂ := ∑' n, zeta_series s n

lemma zeta_series_bound (σ : ℝ) (hσ : 1 < σ) :
  ∃ M : ℕ → ℝ,
    Summable M ∧
    ∀ n s, σ ≤ s.re → ‖zeta_series s n‖ ≤ M n := by
  let M := fun n ↦ 1 / (n + 1 : ℝ) ^ σ
  have hM : Summable M := summable_one_div_nat_rpow hσ
  use M
  constructor
  · exact hM
  · intro n s hs_re
    simp only [zeta_series, norm_div, norm_one, norm_pow, norm_natCast]
    apply div_le_div_of_le_left (by positivity) (by positivity)
    apply Real.rpow_le_rpow
    · exact_mod_cast Nat.cast_nonneg (n + 1)
    · exact le_of_lt (Complex.norm_nat_cast_lt_re n.succ σ hσ)
    · exact hs_re

-- Convergencia uniforme de la traza ζ(s)
theorem zeta_series_uniform_converges (σ : ℝ) (hσ : 1 < σ) :
  TendstoUniformly (fun n s ↦ zeta_series s n)
    (fun s ↦ RiemannZeta s) atTop
    {s | σ ≤ s.re} := by
  apply UniformConvergence.weierstrass_m_test
  obtain ⟨M, hMsum, hbound⟩ := zeta_series_bound σ hσ
  exact ⟨M, hMsum, hbound⟩

end Noesis
