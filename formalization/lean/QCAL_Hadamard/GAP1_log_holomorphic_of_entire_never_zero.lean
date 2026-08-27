/-
  GAP 1 v3.2.4 — log_holomorphic_of_entire_never_zero

  Paso A: primitiva F de 1/z en ball w ρ (ρ < ‖w‖).
          G(z) = z exp(-F z), G' = 0 ⇒ G constante
          (`IsOpen.is_const_of_deriv_eq_zero`).
          L(z) = F(z) - F(w) + log w  ⇒  exp(L z) = z.
  Paso B: φ continua, exp∘φ = h. Localmente φ = L∘h + 2πi n
          (imagen conexa en 2πiℤ, huecos ≥ 2π).

  José Manuel Mota Burruezo · Noesis · QCAL ∞³
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Connected.Basic

noncomputable section
open Complex Metric Set
open scoped Topology Real

/-! ### Paso A — log de id en un disco 0-libre -/

lemma zero_not_mem_ball {w : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hρw : ρ < ‖w‖) :
    (0 : ℂ) ∉ ball w ρ := by
  intro h
  have : dist 0 w < ρ := h
  simp [dist_zero_left] at this
  exact lt_asymm this hρw

lemma inv_differentiableOn_ball {w : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hρw : ρ < ‖w‖) :
    DifferentiableOn ℂ (fun z : ℂ => z⁻¹) (ball w ρ) := by
  intro z hz
  have hz0 : z ≠ 0 := fun h => (zero_not_mem_ball hρ hρw) (h ▸ hz)
  exact (differentiableAt_inv hz0).differentiableWithinAt

theorem exists_primitive_inv_on_ball {w : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hρw : ρ < ‖w‖) :
    ∃ F : ℂ → ℂ, ∀ z ∈ ball w ρ, HasDerivAt F z⁻¹ z := by
  have hEx : IsExactOn (fun z : ℂ => z⁻¹) (ball w ρ) :=
    (inv_differentiableOn_ball hρ hρw).isExactOn_ball
  exact hEx

lemma hasDerivAt_z_mul_exp_neg {F : ℂ → ℂ} {z : ℂ}
    (hz : z ≠ 0) (hF : HasDerivAt F z⁻¹ z) :
    HasDerivAt (fun ζ => ζ * exp (-F ζ)) 0 z := by
  have h_id : HasDerivAt (fun ζ : ℂ => ζ) 1 z := hasDerivAt_id z
  have h_negF : HasDerivAt (fun ζ => -F ζ) (-z⁻¹) z := hF.neg
  have h_exp : HasDerivAt (fun ζ => exp (-F ζ)) (exp (-F z) * (-z⁻¹)) z :=
    (hasDerivAt_exp (-F z)).comp z h_negF
  have := h_id.mul h_exp
  convert this using 1
  field_simp [hz]
  ring

lemma norm_two_pi_I : ‖(2 : ℂ) * π * I‖ = 2 * Real.pi := by
  rw [mul_assoc, norm_mul, norm_mul]
  simp [Complex.norm_eq_abs, Complex.abs_ofReal, Complex.abs_I,
    abs_of_nonneg Real.pi_nonneg]
  ring

lemma two_pi_le_dist_of_ne {n m : ℤ} (hne : n ≠ m) :
    2 * Real.pi ≤
      dist ((n : ℂ) * (2 * π * I)) ((m : ℂ) * (2 * π * I)) := by
  have hdist :
      dist ((n : ℂ) * (2 * π * I)) ((m : ℂ) * (2 * π * I)) =
        ‖((n - m : ℤ) : ℂ)‖ * ‖(2 : ℂ) * π * I‖ := by
    rw [dist_eq_norm, ← sub_mul, ← Int.cast_sub, norm_mul]
  rw [hdist, Complex.norm_intCast, norm_two_pi_I, Int.cast_abs]
  have : (1 : ℝ) ≤ |(n - m : ℤ)| :=
    Int.cast_le.mpr (Int.one_le_abs (sub_ne_zero.mpr hne))
  nlinarith [Real.pi_pos]

lemma dist_lattice_ne_pi (n m : ℤ) :
    dist ((n : ℂ) * (2 * π * I)) ((m : ℂ) * (2 * π * I)) ≠ Real.pi := by
  intro h
  have hdist :
      dist ((n : ℂ) * (2 * π * I)) ((m : ℂ) * (2 * π * I)) =
        ‖((n - m : ℤ) : ℂ)‖ * ‖(2 : ℂ) * π * I‖ := by
    rw [dist_eq_norm, ← sub_mul, ← Int.cast_sub, norm_mul]
  have hmul : ((n - m).natAbs : ℝ) * 2 = 1 := by
    have : |(n - m : ℤ)| * (2 * Real.pi) = Real.pi := by
      rwa [hdist, Complex.norm_intCast, norm_two_pi_I, Int.cast_abs] at h
    have : ((n - m).natAbs : ℝ) * (2 * Real.pi) = Real.pi := by
      simpa [Int.cast_natAbs] using this
    nlinarith [Real.pi_pos]
  rcases Nat.eq_zero_or_pos (n - m).natAbs with hk | hk
  · simp [hk] at hmul
  · have : (1 : ℝ) ≤ (n - m).natAbs := Nat.one_le_cast.mpr hk
    nlinarith

/-- Imagen conexa dentro de 2πiℤ: un solo punto. -/
lemma connected_image_lattice_subsingleton {s : Set ℂ} {ψ : ℂ → ℂ}
    (hconn : IsConnected (ψ '' s))
    (hval : ∀ z ∈ s, ∃ n : ℤ, ψ z = (n : ℂ) * (2 * π * I)) :
    (ψ '' s).Subsingleton := by
  intro x hx y hy
  obtain ⟨zx, hzx, rfl⟩ := hx
  obtain ⟨zy, hzy, rfl⟩ := hy
  obtain ⟨n, hn⟩ := hval zx hzx
  obtain ⟨m, hm⟩ := hval zy hzy
  by_contra hne
  have hnm : n ≠ m := by
    intro h; apply hne; rw [hn, hm, h]
  have hd : 2 * Real.pi ≤ dist (ψ zx) (ψ zy) := by
    rw [hn, hm]; exact two_pi_le_dist_of_ne hnm
  let U : Set ℂ := ball (ψ zx) Real.pi
  let V : Set ℂ := (closedBall (ψ zx) Real.pi)ᶜ
  have hcover : ψ '' s ⊆ U ∪ V := by
    intro w hw
    obtain ⟨zw, hzw, rfl⟩ := hw
    obtain ⟨k, hk⟩ := hval zw hzw
    have hπ : dist (ψ zw) (ψ zx) ≠ Real.pi := by
      rw [hk, hn]; exact dist_lattice_ne_pi k n
    by_cases hle : dist (ψ zw) (ψ zx) ≤ Real.pi
    · exact Or.inl (mem_ball.mpr (lt_of_le_of_ne hle hπ))
    · exact Or.inr (fun hcl => hle (mem_closedBall.mp hcl))
  have hUne : (ψ '' s ∩ U).Nonempty :=
    ⟨ψ zx, ⟨⟨zx, hzx, rfl⟩, mem_ball_self Real.pi_pos⟩⟩
  have hVne : (ψ '' s ∩ V).Nonempty := by
    refine ⟨ψ zy, ⟨⟨zy, hzy, rfl⟩, ?_⟩⟩
    intro hcl
    have : dist (ψ zy) (ψ zx) ≤ Real.pi := mem_closedBall.mp hcl
    linarith [Real.pi_pos]
  have hinter :=
    hconn.isPreconnected U V isOpen_ball isClosed_closedBall.isOpen_compl
      hcover hUne hVne
  obtain ⟨w, ⟨⟨hwimg, hwU⟩, hwV⟩⟩ := hinter
  exact hwV (ball_subset_closedBall hwU)

theorem exists_holomorphic_log_on_ball {w : ℂ} {ρ : ℝ}
    (hw : w ≠ 0) (hρ : 0 < ρ) (hρw : ρ < ‖w‖) :
    ∃ L : ℂ → ℂ,
      (∀ z ∈ ball w ρ, DifferentiableAt ℂ L z) ∧
      ∀ z ∈ ball w ρ, exp (L z) = z := by
  obtain ⟨F, hF⟩ := exists_primitive_inv_on_ball hρ hρw
  let G : ℂ → ℂ := fun ζ => ζ * exp (-F ζ)
  have hG0 : ∀ z ∈ ball w ρ, HasDerivAt G 0 z := by
    intro z hz
    have hz0 : z ≠ 0 := fun h => (zero_not_mem_ball hρ hρw) (h ▸ hz)
    exact hasDerivAt_z_mul_exp_neg hz0 (hF z hz)
  have hwmem : w ∈ ball w ρ := mem_ball_self hρ
  have hGdiff : DifferentiableOn ℂ G (ball w ρ) :=
    fun z hz => (hG0 z hz).differentiableAt.differentiableWithinAt
  have hGderiv : (ball w ρ).EqOn (deriv G) 0 :=
    fun z hz => (hG0 z hz).deriv
  have hGconst : ∀ z ∈ ball w ρ, G z = G w := by
    intro z hz
    exact isOpen_ball.is_const_of_deriv_eq_zero
      (isPreconnected_ball w ρ) hGdiff hGderiv hz hwmem
  let L : ℂ → ℂ := fun z => F z - F w + log w
  refine ⟨L, ?diff, ?exp⟩
  · intro z hz
    exact ((hF z hz).sub (hasDerivAt_const z (F w))).add
      (hasDerivAt_const z (log w)) |>.differentiableAt
  · intro z hz
    have hz0 : z ≠ 0 := fun h => (zero_not_mem_ball hρ hρw) (h ▸ hz)
    have hGz : z * exp (-F z) = w * exp (-F w) := hGconst z hz
    have hratio : exp (F z - F w) = z / w := by
      have hz_eq : z = exp (F z - F w) * w := by
        calc
          z = z * exp (-F z) * exp (F z) := by
            rw [mul_assoc, ← exp_add, neg_add_cancel, exp_zero, mul_one]
          _ = w * exp (-F w) * exp (F z) := by rw [hGz]
          _ = w * exp (F z - F w) := by
            rw [mul_assoc, ← exp_add]
            congr 1
            ring
          _ = exp (F z - F w) * w := mul_comm _ _
      exact ((div_eq_iff hw).mpr hz_eq).symm
    calc
      exp (L z) = exp (F z - F w) * exp (log w) := by
        simp [L, exp_add, sub_eq_add_neg]
      _ = (z / w) * w := by rw [hratio, exp_log hw]
      _ = z := by field_simp [hw]

theorem exists_continuous_log_univ {h : ℂ → ℂ}
    (hhc : Continuous h) (hne : ∀ z, h z ≠ 0) :
    ∃ φ : ℂ → ℂ, Continuous φ ∧ ∀ z, exp (φ z) = h z := by
  have h0 : (0 : ℂ) ∉ h '' (univ : Set ℂ) := by
    rintro ⟨z, _, rfl⟩; exact hne z rfl
  obtain ⟨φ, hφc, hφ⟩ :=
    exists_continuousOn_eqOn_exp_comp isSimplyConnected_univ isOpen_univ
      hhc.continuousOn h0
  exact ⟨φ, hφc.continuous_of_continuousOn_univ, fun z => hφ (mem_univ z)⟩

theorem log_holomorphic_of_entire_never_zero {h : ℂ → ℂ}
    (hh : Differentiable ℂ h) (hne : ∀ z, h z ≠ 0) :
    ∃ φ : ℂ → ℂ, Differentiable ℂ φ ∧ ∀ z, exp (φ z) = h z := by
  obtain ⟨φ, hφc, hexp⟩ := exists_continuous_log_univ hh.continuous hne
  refine ⟨φ, ?hol, hexp⟩
  intro z₀
  have hw : h z₀ ≠ 0 := hne z₀
  let ρ : ℝ := ‖h z₀‖ / 2
  have hρ : 0 < ρ := half_pos (norm_pos_iff.mpr hw)
  have hρw : ρ < ‖h z₀‖ := half_lt_self (norm_pos_iff.mpr hw)
  obtain ⟨L, hLd, hLexp⟩ := exists_holomorphic_log_on_ball hw hρ hρw
  obtain ⟨δ, hδ, hδball⟩ : ∃ δ > 0, ∀ z, dist z z₀ < δ → dist (h z) (h z₀) < ρ := by
    have hcont := hh.continuous.continuousAt (x := z₀)
    exact (Metric.continuousAt_iff.mp hcont) ρ hρ
  have hδpos : 0 < δ := hδ
  have hhball : ∀ z ∈ ball z₀ δ, h z ∈ ball (h z₀) ρ := fun z hz =>
    hδball z (mem_ball.mp hz)
  have hexp_eq : ∀ z ∈ ball z₀ δ, exp (φ z) = exp (L (h z)) := by
    intro z hz
    rw [hexp z, hLexp (h z) (hhball z hz)]
  let ψ : ℂ → ℂ := fun z => φ z - L (h z)
  have hval : ∀ z ∈ ball z₀ δ, ∃ n : ℤ, ψ z = (n : ℂ) * (2 * π * I) := by
    intro z hz
    obtain ⟨n, hn⟩ := exp_eq_exp_iff_exists_int.mp (hexp_eq z hz)
    exact ⟨n, by simp [ψ, hn, sub_eq_iff_eq_add]⟩
  have hψc' : ContinuousOn ψ (ball z₀ δ) :=
    (hφc.continuousOn.mono fun _ _ => trivial).sub <| by
      have hLc : ContinuousOn L (ball (h z₀) ρ) :=
        fun z hz => (hLd z hz).continuousAt.continuousWithinAt
      exact hLc.comp hh.continuous.continuousOn fun z hz => hhball z hz
  have hconn : IsConnected (ψ '' ball z₀ δ) :=
    (isConnected_ball hδpos).image hψc'
  have hsing := connected_image_lattice_subsingleton hconn hval
  have hz0mem : z₀ ∈ ball z₀ δ := mem_ball_self hδpos
  obtain ⟨n, hn0⟩ := hval z₀ hz0mem
  have hconst : ∀ z ∈ ball z₀ δ, ψ z = (n : ℂ) * (2 * π * I) := by
    intro z hz
    exact (hsing ⟨z, hz, rfl⟩ ⟨z₀, hz0mem, rfl⟩).trans hn0
  have hev : φ =ᶠ[𝓝 z₀] fun z => L (h z) + (n : ℂ) * (2 * π * I) :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds hz0mem) fun z hz =>
      eq_add_of_sub_eq (hconst z hz)
  have hLdh : DifferentiableAt ℂ (fun z => L (h z)) z₀ :=
    (hLd (h z₀) (mem_ball_self hρ)).comp z₀ (hh z₀)
  have hadd :
      DifferentiableAt ℂ (fun z => L (h z) + (n : ℂ) * (2 * π * I)) z₀ :=
    hLdh.add (differentiableAt_const _)
  exact hadd.congr_of_eventuallyEq hev.symm

end
