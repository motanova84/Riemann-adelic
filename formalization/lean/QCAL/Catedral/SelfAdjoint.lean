-- ============================================================
namespace QCAL

theorem H_pi_is_self_adjoint : IsSelfAdjoint H_pi :=
  by
    have h_sym : IsSymmetric H_pi Domain_H_pi := H_pi_symmetric
    have h_ess_self : EssentiallySelfAdjoint H_pi := H_pi_essentially_self_adjoint
    have h_closed : IsClosed H_pi := H_pi_closed
    exact ⟨h_sym, h_closed, h_ess_self.maximal_domain⟩

theorem spectrum_real : ∀ (λ : ℂ), λ ∈ spectrum H_pi → λ.im = 0 := sorry

theorem eigenvalues_are_riemann_zeros (n : ℕ) (γ_n : ℝ)
  (h_eigen : H_pi (eigenvector n) = γ_n • eigenvector n) :
  riemann_zeta (1/2 + Complex.I * γ_n) = 0 := sorry

theorem unitary_evolution (t : ℝ) :
  IsUnitary (exp (-Complex.I * H_pi * t / ℏ)) := sorry

theorem probability_conservation (t : ℝ) (ψ : HilbertSpace) :
  ‖exp (-Complex.I * H_pi * t / ℏ) ψ‖ = ‖ψ‖ := sorry

end QCAL

-- ============================================================
