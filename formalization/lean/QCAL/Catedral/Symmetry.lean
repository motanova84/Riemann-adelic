-- ============================================================
namespace QCAL

lemma gamma_pos (ξ : ℝ) : gamma ξ ≥ γ₁ := sorry
lemma gamma_ge_gamma_one (ξ : ℝ) : gamma ξ ≥ γ₁ := sorry
lemma gamma_real (ξ : DualAdele) : (gamma ξ).im = 0 := sorry

lemma fourier_conj (ψ : HilbertSpace) (ξ : ℝ) :
  (fourier_adelic (star ψ) ξ) = star (fourier_adelic ψ (-ξ)) := sorry

lemma fourier_involution (ψ : HilbertSpace) :
  fourier_adelic (fourier_adelic ψ) = ψ := sorry

lemma conj_of_real (x : ℝ) : (x : ℂ).im = 0 := by simp

theorem H_pi_symmetric (ψ φ : HilbertSpace)
  (hψ : ψ ∈ Domain_H_pi) (hφ : φ ∈ Domain_H_pi) :
  ⟨H_pi ψ, φ⟩ = ⟨ψ, H_pi φ⟩ :=
  by
    rw [H_pi_def]
    rw [innerProduct_def, fourier_transform_adelic]
    rw [fubini_adelic]
    · apply integrable_of_decay
      · exact hψ.decay
      · exact hφ.decay
    simp [fourier_conj, fourier_involution]
    rw [gamma_real]
    simp [conj_of_real]
    simp [mul_comm]
    rfl

end QCAL

-- ============================================================
