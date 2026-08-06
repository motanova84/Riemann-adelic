-- ============================================================
namespace QCAL

def H_pi (ψ : HilbertSpace) : HilbertSpace := sorry

lemma H_pi_well_defined (ψ : HilbertSpace) (hψ : ψ ∈ Domain_H_pi) :
  H_pi ψ ∈ HilbertSpace := sorry

lemma H_pi_closed : IsClosed H_pi := sorry

def H_pi_def : H_pi = λ ψ => ∫ (gamma ξ) * (fourier_adelic ψ ξ) * (exp (2 * Real.pi * Complex.I * ξ * ·)) dξ := sorry

def H_pi_inner (ψ φ : HilbertSpace) : ℂ := ⟨H_pi ψ, φ⟩
def H_pi_inner_real (ψ : HilbertSpace) : ℝ := (⟨H_pi ψ, ψ⟩).re

end QCAL

-- ============================================================
