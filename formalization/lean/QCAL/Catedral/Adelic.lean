-- ============================================================
namespace QCAL

def DualAdele : Type* := sorry
def TamagawaMeasure : Measure (A_Q^× / Q^×) := sorry
def fourier_transform_adelic (ψ : HilbertSpace) : DualAdele → ℂ := sorry

def fubini_adelic {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  (f : α → β → ℂ) (h_int : Integrable (λ (x,y) => f x y) (μ.prod ν)) :
  ∫ x, ∫ y, f x y ∂ν ∂μ = ∫ y, ∫ x, f x y ∂μ ∂ν := sorry

end QCAL

-- ============================================================
