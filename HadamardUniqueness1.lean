/-
  Hadamard uniqueness — ladrillo D ≡ Ξ con ceros {γ_n}

  Paley–Wiener: acuerdo en TODA la línea (h_crit ∀ t). No tocar.
  Hadamard:     mismos ceros + orden ≤ 1 + simetría + f(1/2)=g(1/2).

  José Manuel Mota Burruezo · Noesis · QCAL ∞³
-/

import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Instances.Complex

noncomputable section
open Complex

/-!
## Crecimiento

`OrderLEOne` = tipo exponencial |f| ≤ A e^{B|z|}  (Paley–Wiener).
`OrderAtMostOne` = orden ≤ 1 en el sentido de Hadamard:
  |f(z)| ≤ A_ε exp(|z|^{1+ε}) para todo ε>0.

ξ clásica es `OrderAtMostOne`, no `OrderLEOne`.
El cociente sin ceros de dos funciones de orden ≤ 1 sí cae
en exp(A+Bs).
-/

def OrderLEOne (f : ℂ → ℂ) : Prop :=
  ∃ A B : ℝ, 0 < A ∧ 0 ≤ B ∧ ∀ z : ℂ, ‖f z‖ ≤ A * Real.exp (B * ‖z‖)

def OrderAtMostOne (f : ℂ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 0 < A ∧ ∀ z : ℂ, ‖f z‖ ≤ A * Real.exp (‖z‖ ^ (1 + ε))

def SameZeros (f g : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, analyticOrderAt f z = analyticOrderAt g z

lemma OrderLEOne.to_atMostOne {f : ℂ → ℂ} (h : OrderLEOne f) : OrderAtMostOne f := by
  intro ε hε
  obtain ⟨A, B, hA, hB, hf⟩ := h
  refine ⟨A * Real.exp (B + 1), by positivity, ?_⟩
  intro z
  -- e^{B|z|} ≤ e^{B} e^{|z|^{1+ε}} para |z| grande; el resto se absorbe en A
  sorry -- fontanería de crecimiento; no es el hueco de Hadamard

/-!
## Paso 1 — B = 0  (cerrado: derivada de una constante)
-/

/-- Si exp(A+B(1-s)) = exp(A+Bs) para todo s, entonces B = 0. -/
lemma exp_affine_of_functional_eq {A B : ℂ}
    (hsym : ∀ s : ℂ, exp (A + B * (1 - s)) = exp (A + B * s)) :
    B = 0 := by
  have h : ∀ s, exp (B * (1 - 2 * s)) = 1 := by
    intro s
    have hs := hsym s
    have hdiff : A + B * (1 - s) - (A + B * s) = B * (1 - 2 * s) := by ring
    calc
      exp (B * (1 - 2 * s))
          = exp (A + B * (1 - s) - (A + B * s)) := by rw [hdiff]
        _ = exp (A + B * (1 - s)) / exp (A + B * s) := exp_sub _ _
        _ = exp (A + B * s) / exp (A + B * s) := by rw [hs]
        _ = 1 := div_self (exp_ne_zero _)
  -- F(s) = exp(B(1-2s)) ≡ 1 ⇒ F'(0) = 0
  -- cadena: F'(0) = exp(B) · (-2B)
  have F_const : (fun s : ℂ => exp (B * (1 - 2 * s))) = fun _ => (1 : ℂ) := funext h
  have Fderiv0 : deriv (fun s : ℂ => exp (B * (1 - 2 * s))) 0 = 0 := by
    rw [F_const]; exact deriv_const 0 1
  have hchain : deriv (fun s : ℂ => exp (B * (1 - 2 * s))) 0 = exp B * (-2 * B) := by
    -- d/ds exp(u(s)) = exp(u) u', u(s)=B(1-2s), u(0)=B, u'=-2B
    have hu : HasDerivAt (fun s : ℂ => B * (1 - 2 * s)) (-2 * B) 0 := by
      simp [hasDerivAt_const, hasDerivAt_id']
      convert HasDerivAt.const_mul B (hasDerivAt_id' 0 |>.const_sub 1 |>.const_mul (2 : ℂ) |>.neg) using 1
      ring
    have : HasDerivAt (fun s : ℂ => exp (B * (1 - 2 * s))) (exp B * (-2 * B)) 0 :=
      (hasDerivAt_exp B).comp 0 hu
    exact this.deriv
  have : exp B * (-2 * B) = 0 := by rw [← hchain, Fderiv0]
  rcases mul_eq_zero.mp this with he | hB
  · exact (exp_ne_zero B he).elim
  · exact (mul_eq_zero.mp hB).resolve_left (by norm_num : (-2 : ℂ) ≠ 0)

/-!
## Paso 2 — logaritmo entero  (hueco Mathlib, ahora recortado)

ℂ es simplemente conexo. `exists_continuousOn_eqOn_exp_comp`
(Mathlib.Analysis.Complex.BranchLogRoot) da un log *continuo*
de una nunca-cero. Falta subir continuo → holomorfo
(exp es cubriente) y luego Borel–Carathéodory: Re φ = O(|z|^{1+ε})
⇒ φ afín.
-/

/-- Log continuo de una nunca-cero en ℂ. Pieza Mathlib. -/
theorem exists_continuous_log_univ {h : ℂ → ℂ}
    (hhc : Continuous h) (hne : ∀ z, h z ≠ 0) :
    ∃ φ : ℂ → ℂ, Continuous φ ∧ ∀ z, exp (φ z) = h z := by
  have hU : IsSimplyConnected (Set.univ : Set ℂ) := isSimplyConnected_univ
  have hUo : IsOpen (Set.univ : Set ℂ) := isOpen_univ
  have h0 : (0 : ℂ) ∉ h '' Set.univ := by
    intro ⟨z, _, hz⟩; exact hne z hz.symm
  obtain ⟨φ, hφc, hφ⟩ :=
    exists_continuousOn_eqOn_exp_comp hU hUo (hhc.continuousOn) h0
  refine ⟨φ, hφc.continuous_of_continuousOn_univ, ?_⟩
  intro z
  simpa using hφ (Set.mem_univ z)

/-- Si exp ∘ φ = h, h holomorfa, φ continua ⇒ φ holomorfa.
    Mathlib: cubriente `isCoveringMap_exp`. Hueco corto. -/
theorem differentiable_of_exp_comp {φ h : ℂ → ℂ}
    (hh : Differentiable ℂ h) (hφ : Continuous φ)
    (hexp : ∀ z, exp (φ z) = h z) :
    Differentiable ℂ φ := by
  sorry -- covering-space lift: exp local biholomorphism

/-- Re φ = O(|z|^{1+ε}) ∀ε>0 + φ entera ⇒ φ(s) = A + B s.
    Borel–Carathéodory (`borelCaratheodory`) + Cauchy + Liouville en φ'. -/
theorem entire_of_realPart_order_le_one {φ : ℂ → ℂ}
    (hφ : Differentiable ℂ φ)
    (hRe : ∀ ε > 0, ∃ C, ∀ z, (φ z).re ≤ C * (1 + ‖z‖ ^ (1 + ε))) :
    ∃ A B : ℂ, ∀ s, φ s = A + B * s := by
  sorry -- Borel–Carathéodory está en Mathlib; ensamblar Cauchy+Liouville

/-- Hueco principal, ahora en dos piezas Mathlib-nombradas. -/
theorem entire_never_zero_order_atMostOne
    {h : ℂ → ℂ}
    (hh : Differentiable ℂ h)
    (hne : ∀ z, h z ≠ 0)
    (hord : OrderAtMostOne h) :
    ∃ A B : ℂ, ∀ s, h s = exp (A + B * s) := by
  obtain ⟨φ, hφc, hφexp⟩ := exists_continuous_log_univ hh.continuous hne
  have hφd : Differentiable ℂ φ := differentiable_of_exp_comp hh hφc hφexp
  have hRe : ∀ ε > 0, ∃ C, ∀ z, (φ z).re ≤ C * (1 + ‖z‖ ^ (1 + ε)) := by
    intro ε hε
    obtain ⟨A, hA, hAord⟩ := hord ε hε
    refine ⟨Real.log A + 1, ?_⟩
    intro z
    -- (φ z).re = log ‖h z‖ ≤ log A + |z|^{1+ε}
    sorry -- `exp_re` : (exp w).re.exp = ‖exp w‖ y log ‖h z‖ = (φ z).re
  obtain ⟨A, B, hAB⟩ := entire_of_realPart_order_le_one hφd hRe
  refine ⟨A, B, ?_⟩
  intro s
  rw [← hφexp s, hAB s]

/-!
## Paso 3 — simetría ⇒ constante
-/

lemma constant_of_sym_and_order
    {h : ℂ → ℂ}
    (hh : Differentiable ℂ h)
    (hne : ∀ z, h z ≠ 0)
    (hord : OrderAtMostOne h)
    (hsym : ∀ s, h (1 - s) = h s) :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ s, h s = C := by
  obtain ⟨A, B, hAB⟩ := entire_never_zero_order_atMostOne hh hne hord
  have hB : B = 0 :=
    exp_affine_of_functional_eq (by
      intro s
      calc exp (A + B * (1 - s)) = h (1 - s) := (hAB (1 - s)).symm
        _ = h s := hsym s
        _ = exp (A + B * s) := hAB s)
  refine ⟨exp A, exp_ne_zero A, ?_⟩
  intro s
  simp [hAB, hB]

/-!
## Paso 4 — unicidad

SameZeros ⇒ existe h entera nunca-cero con f = h · g.
Simetría + orden ⇒ h constante. Normalización ⇒ esa constante es 1.
-/

theorem exists_entire_quotient
    {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hzeros : SameZeros f g)
    (hg0 : ¬ ∀ z, g z = 0) :
    ∃ h : ℂ → ℂ, Differentiable ℂ h ∧ (∀ z, h z ≠ 0) ∧ (∀ z, f z = h z * g z) := by
  sorry -- SameZeros + g ≢ 0: quitar ceros/polos; infinitos, no `extract_zeros_poles`

theorem hadamard_uniqueness
    {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g)
    (hf_ord : OrderAtMostOne f)
    (hg_ord : OrderAtMostOne g)
    (hzeros : SameZeros f g)
    (hf_sym : ∀ s, f (1 - s) = f s)
    (hg_sym : ∀ s, g (1 - s) = g s)
    (hnorm : f ((1 : ℂ) / 2) = g ((1 : ℂ) / 2))
    (hhalf : g ((1 : ℂ) / 2) ≠ 0) :
    ∀ s, f s = g s := by
  have hg_ne : ¬ ∀ z, g z = 0 := fun hall => hhalf (hall _)
  obtain ⟨h, hh, hne, hfg⟩ := exists_entire_quotient hf hg hzeros hg_ne
  have hord : OrderAtMostOne h := by
    sorry -- |h| = |f|/|g| en {g≠0}; orden del cociente ≤ 1
  have hsym : ∀ s, h (1 - s) = h s := by
    intro s
    -- f(1-s)=h(1-s)g(1-s), f(s)=h(s)g(s), simetría de f y g
    have hfsg : h (1 - s) * g (1 - s) = h s * g s := by
      calc h (1 - s) * g (1 - s) = f (1 - s) := (hfg (1 - s)).symm
        _ = f s := hf_sym s
        _ = h s * g s := hfg s
    have : h (1 - s) * g s = h s * g s := by
      simpa [hg_sym s] using hfsg
    rcases eq_or_ne (g s) 0 with hg | hg
    · -- g s = 0 ⇒ g (1-s)=0; usar hne en otro punto / identidad
      sorry
    · exact (mul_left_inj' hg).mp this
  obtain ⟨C, _, hC⟩ := constant_of_sym_and_order hh hne hord hsym
  have hC1 : C = 1 := by
    have := hfg ((1 : ℂ) / 2)
    rw [hC ((1 : ℂ) / 2), hnorm] at this
    exact (mul_eq_right₀ hhalf).mp this.symm
  intro s
  calc f s = h s * g s := hfg s
    _ = C * g s := by rw [hC s]
    _ = 1 * g s := by rw [hC1]
    _ = g s := one_mul _

/-!
## Mapa de sorries (ninguno es “ceros densos”)

1. `differentiable_of_exp_comp` — cubriente exp. Corto.
2. `entire_of_realPart_order_le_one` — Borel–Carathéodory ya está;
   falta Cauchy+Liouville en φ'.
3. `exists_entire_quotient` — mismos ceros, infinitos
   (no vale `extract_zeros_poles`).
4. Fontanería: `OrderLEOne.to_atMostOne`, orden del cociente,
   simetría de h cuando g s = 0.

El único hueco de sustancia para un PR a Mathlib es (1)+(2)
juntos: `entire_never_zero_order_atMostOne`.
-/

end
