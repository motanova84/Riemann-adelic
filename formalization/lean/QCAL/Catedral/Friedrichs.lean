-- ============================================================
namespace QCAL

theorem friedrichs_extension {A : HilbertSpace → HilbertSpace}
  (h_sym : IsSymmetric A Domain_H_pi)
  (h_lower : IsLowerBounded A)
  (h_dense : Dense Domain_H_pi) :
  ∃! A_F : HilbertSpace → HilbertSpace,
    IsSelfAdjoint A_F ∧ A ⊆ A_F := sorry

theorem H_pi_lower_bounded : IsLowerBounded H_pi :=
  by
    use γ₁
    intro ψ hψ
    calc
      (⟨H_pi ψ, ψ⟩).re = ∫ (gamma ξ) * |fourier_adelic ψ ξ|² dξ := by
        rw [H_pi_inner_real]; simp [gamma_def]
      _ ≥ γ₁ * ∫ |fourier_adelic ψ ξ|² dξ := by
        apply integral_mono; exact gamma_ge_gamma_one; intro ξ; exact sq_nonneg _
      _ = γ₁ * ‖fourier_adelic ψ‖² := by rw [norm_sq_integral]
      _ = γ₁ * ‖ψ‖² := by rw [fourier_isometry]

theorem H_pi_essentially_self_adjoint : EssentiallySelfAdjoint :=
  by
    obtain ⟨A_F, ⟨hA_F_self, hA_F_ext⟩, hA_F_unique⟩ :=
      friedrichs_extension H_pi_symmetric H_pi_lower_bounded domain_dense
    have h_eq : A_F = H_pi_closure := sorry
    rw [EssentiallySelfAdjoint]
    rw [h_eq]
    exact hA_F_self

end QCAL

-- ============================================================
