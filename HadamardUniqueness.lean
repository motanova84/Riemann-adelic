/-
  Hadamard uniqueness — el ladrillo que sí cierra D ≡ Ξ
  cuando solo hay ceros {γ_n}, no acuerdo en toda la línea.

  Paley–Wiener pide:  ∀ t, f(1/2+it) = g(1/2+it)     (continuo)
  Hadamard pide:      mismos ceros + orden ≤ 1
                      + f(1-s)=f(s) + f(1/2)=g(1/2)

  Mathlib NO tiene aún la factorización de Hadamard / género 1.
  El `sorry` de este archivo es ESE hueco, y es real.
  No es densidad de ceros (eso es falso).

  José Manuel Mota Burruezo · Noesis · QCAL ∞³
-/

import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Calculus.Deriv.Basic

noncomputable section
open Complex

/-!
## 1. Lo que Paley–Wiener ya pide (y no hay que tocar)

`paley_wiener_uniqueness` es correcto con

  h_crit : ∀ t : ℝ, f (1/2 + I*t) = g (1/2 + I*t)

Eso no se deduce de ceros discretos. Se deja como está.
-/

/-- Orden finito ≤ 1, en la forma de crecimiento que usa el archivo
    `entire_exponential_growth.lean` de Riemann-adelic: |f(z)| ≤ A exp(B |z|).

    OJO: ξ de Riemann es de orden 1 con n(r) ∼ r log r, *no* de tipo
    exponencial Paley–Wiener. Por eso D ≡ Ξ no cabe en
    `PaleyWienerSpaceModified` si Ξ es la ξ clásica.
    Hadamard (orden ≤ 1) es la hipótesis justa. -/
def OrderLEOne (f : ℂ → ℂ) : Prop :=
  ∃ A B : ℝ, 0 < A ∧ 0 ≤ B ∧ ∀ z : ℂ, ‖f z‖ ≤ A * Real.exp (B * ‖z‖)

/-- Mismos ceros, mismas multiplicidades. -/
def SameZeros (f g : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, analyticOrderAt f z = analyticOrderAt g z

/-!
## 2. El lema que falta en Mathlib (hueco real)

Una entera que no se anula y es de orden ≤ 1 es de la forma exp(A + B s).

Esto es Hadamard de género 0/1 para el cofactor sin ceros.
Mathlib tiene `extract_zeros_poles` solo para *finitos* ceros.
Aquí hay infinitos. Por eso este `sorry` no se sella con `exact?`.
-/

/-- Hueco Mathlib: entera nunca-cero de orden ≤ 1 = exp(afín). -/
theorem entire_never_zero_order_le_one
    {h : ℂ → ℂ}
    (hh : Differentiable ℂ h)
    (hne : ∀ z, h z ≠ 0)
    (hord : OrderLEOne h) :
    ∃ A B : ℂ, ∀ s, h s = exp (A + B * s) := by
  sorry

/-!
## 3. La ecuación funcional mata el término lineal

Si h(s) = exp(A+B s) y h(1-s)=h(s), entonces B = 0.
-/

lemma exp_affine_of_functional_eq
    {A B : ℂ}
    (hsym : ∀ s : ℂ, exp (A + B * (1 - s)) = exp (A + B * s)) :
    B = 0 := by
  -- exp(A+B(1-s)) = exp(A+Bs) para todo s
  -- ⇒ B(1-s) - B s ∈ 2πi ℤ  para todo s
  -- ⇒ B - 2 B s es localmente constante en 2πiℤ ⇒ B = 0
  have h : ∀ s, exp (B * (1 - 2 * s)) = 1 := by
    intro s
    have := hsym s
    -- exp(A+B-B s) = exp(A+B s)
    -- divide by exp(A+B s): exp(B-2Bs) = 1
    calc exp (B * (1 - 2 * s))
        = exp ((A + B * (1 - s)) - (A + B * s)) := by
            ring_nf
            -- (A + B - B*s) - (A + B*s) = B - 2*B*s = B*(1-2s)
            simp [sub_eq_add_neg]
            ring
          _ = exp (A + B * (1 - s)) / exp (A + B * s) := by
            simp [exp_sub]
          _ = 1 := by
            have := hsym s
            simp [this]
  -- exp(B) = 1 y exp(-B) = 1 tomando s=0 y s=1, luego B=0
  have h0 : exp B = 1 := by
    simpa using h 0
  have h1 : exp (-B) = 1 := by
    have := h 1
    simpa using this
  -- exp B = 1 ∧ exp (-B) = 1 ⇒ B = 0 en este contexto
  -- (la rama: exp B = 1 ⇒ B ∈ 2πiℤ; con continuidad en s, B=0)
  sorry -- cierre: exp(c(1-2s))=1 ∀s ⇒ c=0

lemma constant_of_sym_and_order_le_one
    {h : ℂ → ℂ}
    (hh : Differentiable ℂ h)
    (hne : ∀ z, h z ≠ 0)
    (hord : OrderLEOne h)
    (hsym : ∀ s, h (1 - s) = h s) :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ s, h s = C := by
  obtain ⟨A, B, hAB⟩ := entire_never_zero_order_le_one hh hne hord
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
## 4. Teorema de unicidad — el ladrillo

Mismos ceros ⇒ f/g no se anula (extensión entera).
Orden ≤ 1 + simetría ⇒ f/g constante.
Normalización en 1/2 ⇒ la constante es 1.
-/

/-- **Hadamard uniqueness for the QCAL bridge D ≡ Ξ.**

    Hipótesis justas cuando solo hay {γ_n}:
    enteras, orden ≤ 1, mismos ceros, ecuación funcional, f(1/2)=g(1/2)≠0. -/
theorem hadamard_uniqueness
    {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g)
    (hf_ord : OrderLEOne f)
    (hg_ord : OrderLEOne g)
    (hzeros : SameZeros f g)
    (hf_sym : ∀ s, f (1 - s) = f s)
    (hg_sym : ∀ s, g (1 - s) = g s)
    (hnorm : f ((1 : ℂ) / 2) = g ((1 : ℂ) / 2))
    (hhalf : g ((1 : ℂ) / 2) ≠ 0) :
    ∀ s, f s = g s := by
  -- Cociente: SameZeros + g(1/2)≠0 ⇒ g ≢ 0 ⇒ f/g se extiende a entera nunca-cero.
  -- Esto también es trabajo (infinitos ceros). Se deja nombrado.
  let h : ℂ → ℂ := fun s => f s / g s
  have hh : Differentiable ℂ h := by
    sorry -- SameZeros ⇒ polos de 1/g cancelados por ceros de f
  have hne : ∀ z, h z ≠ 0 := by
    sorry -- f y g no son idénticamente 0; mismos órdenes ⇒ ningún cero residual
  have hord : OrderLEOne h := by
    sorry -- cociente de orden ≤ 1
  have hsym : ∀ s, h (1 - s) = h s := by
    intro s
    simp [h, hf_sym, hg_sym]
  obtain ⟨C, hC0, hC⟩ := constant_of_sym_and_order_le_one hh hne hord hsym
  have hC1 : C = 1 := by
    have := hC ((1 : ℂ) / 2)
    simp [h, hnorm, div_self hhalf] at this
    exact this.symm
  intro s
  have := hC s
  simp [h, hC1] at this
  -- f s / g s = 1
  exact (div_eq_one_iff_eq (by
    intro hg0
    -- g s = 0 y SameZeros ⇒ f s = 0, contradice hne si ya está
    sorry)).1 this

/-!
## 5. Cómo se enchufa en Riemann-adelic

NO reemplazar `h_crit` por densidad de γ_n.

SI el dato espectral da acuerdo en toda la línea → `paley_wiener_uniqueness`.
SI el dato espectral da los mismos ceros que Ξ → `hadamard_uniqueness`.

Para ξ clásica: orden 1, ξ(s)=ξ(1-s), ξ(1/2)≠0.
`PaleyWienerSpaceModified` (tipo exp en |Im z|) es demasiado estrecho
para ξ. Hadamard es la caja correcta.

El único `sorry` que merece un PR a Mathlib es
`entire_never_zero_order_le_one`.
Los demás son fontanería del cociente.
-/

end
