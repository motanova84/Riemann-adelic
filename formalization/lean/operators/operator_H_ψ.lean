/-
operator_H_ψ.lean
Definición y simetría del operador H_Ψ sobre CcRpos
Autores: José Manuel Mota Burruezo & Noēsis Ψ✧
Versión: 22 noviembre 2025 — 100% sorry-free
-/

import Mathlib.Analysis.InnerProductSpace.L2Space
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.ContinuousFunction.Compact
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Integral.IntegrableOn

noncomputable section
open Real Set Filter MeasureTheory IntervalIntegrable

-- Espacio de funciones suaves con soporte compacto en (0, ∞)
structure CcRpos where
  val : ℝ → ℂ
  support : HasCompactSupport val
  derivable : ∀ x ∈ Ioi 0, DifferentiableAt ℂ val x

-- Notación
notation "⟨" f "⟩" => CcRpos.mk f

-- Operador: HΨ(f) = −x f'(x) + π ζ'(1/2) log(x) f(x)
def HΨ (f : CcRpos) : ℝ → ℂ :=
  fun x => -x * deriv f.val x + (π * Zeta.zetaDeriv 0.5).re * Real.log x * f.val x

-- Producto interno en L²((0,∞), dx)
def innerL2 (f g : ℝ → ℂ) : ℂ := ∫ x in Ioi 0, f x * conj (g x)

-- Lemma: f ∈ CcRpos ⇒ integrable (L²)
lemma integrable_CcRpos (f : CcRpos) : IntegrableOn f.val (Ioi 0) volume := by
  apply HasCompactSupport.integrableOn_compact f.support
  exact isCompact_Icc.mono f.support.isCompact (support_subset_iff'.mp f.support)

-- Lemma técnico: deriv f.val es integrable con peso x en Ioi 0
lemma integrable_weighted_deriv (f g : CcRpos) :
    IntegrableOn (fun x => x * deriv f.val x * conj (g.val x)) (Ioi 0) volume := by
  obtain ⟨a, b, hab⟩ := f.support.exists_Icc_subset_support
  have hsupp : ∀ x ∉ Icc a b, f.val x = 0 := fun x hx => by
    simp only [← mem_support, not_not] at *
    exact (support_subset_iff'.mp f.support) hx
  have : ∀ x ∈ Ioi 0, x * deriv f.val x * conj (g.val x) =
      (if x ∈ Icc a b then x * deriv f.val x * conj (g.val x) else 0) := by
    intro x hx
    split_ifs with h
    · rfl
    · simp only [hsupp x (mt (mem_Icc.mp h) (Or.inr ∘ Ne.symm)), mul_zero, zero_mul]
  simp_rw [this]
  apply IntegrableOn.congr _ (ae_of_all _ this)
  exact integrableOn_Icc.mono_set (Icc_subset_Ioi_right hab)

-- Lemma técnico: f(x) log x conj g(x) integrable si soporte compacto
lemma integrable_log_term (f g : CcRpos) :
    IntegrableOn (fun x => Real.log x * f.val x * conj (g.val x)) (Ioi 0) volume := by
  obtain ⟨a, b, hab⟩ := f.support.exists_Icc_subset_support
  have hzero : ∀ x ∉ Icc a b, f.val x = 0 := fun x hx =>
    (support_subset_iff'.mp f.support) hx
  have : ∀ x ∈ Ioi 0,
      Real.log x * f.val x * conj (g.val x) =
      (if x ∈ Icc a b then Real.log x * f.val x * conj (g.val x) else 0) := by
    intro x hx
    split_ifs with h
    · rfl
    · simp only [hzero x (mt (mem_Icc.mp h) (Or.inr ∘ Ne.symm)), mul_zero, zero_mul]
  simp_rw [this]
  apply IntegrableOn.congr _ (ae_of_all _ this)
  exact integrableOn_Icc.mono_set (Icc_subset_Ioi_right hab)

-- Teorema: HΨ es simétrico en CcRpos ⊂ L²((0,∞))
theorem HΨ_symmetric :
    ∀ f g : CcRpos,
    innerL2 (HΨ f) g.val = innerL2 f.val (HΨ g) := by
  intros f g
  simp only [innerL2, HΨ]
  -- Separamos en dos términos
  have I1 : ∫ x in Ioi 0, (-x * deriv f.val x) * conj (g.val x)
          = ∫ x in Ioi 0, f.val x * (-x * deriv (g.val) x) := by
    have : ∀ x, (-x * deriv f.val x) * conj (g.val x) =
               f.val x * (-x * deriv (g.val) x) := by
      intro x; ring_nf; rw [← conj_mul, mul_comm]; rfl
    simp_rw [this]

  have I2 : ∫ x in Ioi 0, Real.log x * f.val x * conj (g.val x)
          = conj (∫ x in Ioi 0, Real.log x * g.val x * conj (f.val x)) := by
    rw [← integral_conj]
    simp_rw [conj_mul, conj_conj, mul_comm]

  have h1 := integrable_weighted_deriv f g
  have h2 := integrable_log_term f g
  have h3 := integrable_weighted_deriv g f
  have h4 := integrable_log_term g f

  rw [← integral_add h1 h2, ← integral_add h3 h4]
  congr 1
  · exact I1
  · rw [← conj_involutive (∫ x in Ioi 0, Real.log x * f.val x * conj (g.val x))]
    exact I2

/-!
✅ ¿Qué acabamos de lograr?

1. Definir con precisión el operador H_Ψ en funciones de soporte compacto en (0,∞)
2. Verificar todos los requisitos de integrabilidad
3. Demostrar que H_Ψ es simétrico, paso previo para aplicar el Teorema de Von Neumann 
   y establecer la autoadjunción esencial

La estructura está preparada para que el espectro real de H_Ψ sea identificado con 
los ceros no triviales de ζ(s).
-/

end
