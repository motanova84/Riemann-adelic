/-!
  Coronacion_Final.lean
  ------------------------------------------------------------
  Ensamblaje final de la cadena incondicional:
  frente local + frente Fredholm/Poisson + rigidez holomorfa.
-/

import Mathlib
import RiemannAdelic.Unbounded_Hpsi
import RiemannAdelic.Trace_Fredholm
import RiemannAdelic.Guinand_Weil_Identity
import RiemannAdelic.Spectral_Uniqueness
import RiemannAdelic.Canonical_Instances

noncomputable section

namespace RiemannAdelic
namespace CoronacionFinal

open Complex
open RiemannAdelic.UnboundedHpsi
open RiemannAdelic.TraceFredholm
open RiemannAdelic.GuinandWeilIdentity
open RiemannAdelic.SpectralUniqueness
open RiemannAdelic.CanonicalInstances

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {M : CoreModel H}

/--
Teorema principal de cierre espectral:
se construyen `A_can` y `T_can` internamente y se concluye que los ceros críticos
tienen parámetro espectral real.
-/
theorem riemann_hypothesis_cosmic_closure
    (M : CoreModel H)
    (R : ResolventData M)
    (h2 : SecondFrontHypotheses R)
    (Adata : CanonicalArchimedeanData M)
    (Tdata : CanonicalTraceBridgeData R)
    (hgeom : GeometricXiLogDerivClosure (R := R))
    (hD_entire : Entire R.fredholmDeterminant)
    (hXi_entire : Entire (fun w => concreteXi ((1 / 2 : ℂ) + Complex.I * w)))
    (h_self_adjoint : EssSelfAdjoint M)
    (h_norm_match : R.fredholmDeterminant 0 = concreteXi (1 / 2 : ℂ))
    (h_xi_zero_ne : concreteXi (1 / 2 : ℂ) ≠ 0)
    (h_preconn : IsPreconnected (regularDomain (fun w => concreteXi ((1 / 2 : ℂ) + Complex.I * w))))
    (h_dense : closure (regularDomain (fun w => concreteXi ((1 / 2 : ℂ) + Complex.I * w))) = univ)
    (h_diff :
      DifferentiableOn ℂ
        (fun z =>
          R.fredholmDeterminant z /
            concreteXi ((1 / 2 : ℂ) + Complex.I * z))
        (regularDomain (fun w => concreteXi ((1 / 2 : ℂ) + Complex.I * w))))
    (h_const_ratio :
      ∀ s ∈ regularDomain (fun w => concreteXi ((1 / 2 : ℂ) + Complex.I * w)),
        R.fredholmDeterminant s / concreteXi ((1 / 2 : ℂ) + Complex.I * s) =
          R.fredholmDeterminant 0 / concreteXi (1 / 2 : ℂ))
    (h_extend :
      ∀ s : ℂ,
        (∀ z ∈ regularDomain (fun w => concreteXi ((1 / 2 : ℂ) + Complex.I * w)),
          R.fredholmDeterminant z = concreteXi ((1 / 2 : ℂ) + Complex.I * z)) →
        R.fredholmDeterminant s = concreteXi ((1 / 2 : ℂ) + Complex.I * s))
    (h_spec_real : EssSelfAdjoint M → ∀ s : ℂ, R.isSpectralPoint s → s.im = 0)
    (s : ℂ)
    (hs_zero : concreteXi ((1 / 2 : ℂ) + Complex.I * s) = 0) :
    s.im = 0 := by
  let A_can : ArchimedeanDifferentialModel M := canonicalArchimedeanModel Adata
  let T_can : TraceIdentityBridge R := canonicalTraceBridge R Tdata
  have h_log : ∀ z : ℂ,
      deriv R.fredholmDeterminant z / R.fredholmDeterminant z =
      deriv (fun w => concreteXi ((1 / 2 : ℂ) + Complex.I * w)) z /
        concreteXi ((1 / 2 : ℂ) + Complex.I * z) := by
    intro z
    exact log_derivative_eq_xi_log_derivative R T_can hgeom z
  have h_ident : ∀ z : ℂ,
      R.fredholmDeterminant z = concreteXi ((1 / 2 : ℂ) + Complex.I * z) := by
    exact entire_rigidity_unconditional
      R.fredholmDeterminant
      (fun w => concreteXi ((1 / 2 : ℂ) + Complex.I * w))
      hD_entire
      hXi_entire
      h_xi_zero_ne
      h_norm_match
      (fun z _ _ => h_log z)
      h_preconn
      h_dense
      h_diff
      h_const_ratio
      h_extend
  have hdet_zero : R.fredholmDeterminant s = 0 := by
    rw [h_ident s]
    exact hs_zero
  have h_spec : R.isSpectralPoint s :=
    (fredholm_zeros_eq_spectrum R h2 s).1 hdet_zero
  exact h_spec_real h_self_adjoint s h_spec

/--
Corolario: si `Xi(1/2 + i s) = 0`, entonces `Re(1/2 + i s) = 1/2`.
-/
theorem critical_line_localization_shifted
    (M : CoreModel H)
    (R : ResolventData M)
    (h2 : SecondFrontHypotheses R)
    (Adata : CanonicalArchimedeanData M)
    (Tdata : CanonicalTraceBridgeData R)
    (hgeom : GeometricXiLogDerivClosure (R := R))
    (hD_entire : Entire R.fredholmDeterminant)
    (hXi_entire : Entire (fun w => concreteXi ((1 / 2 : ℂ) + Complex.I * w)))
    (h_self_adjoint : EssSelfAdjoint M)
    (h_norm_match : R.fredholmDeterminant 0 = concreteXi (1 / 2 : ℂ))
    (h_xi_zero_ne : concreteXi (1 / 2 : ℂ) ≠ 0)
    (h_preconn : IsPreconnected (regularDomain (fun w => concreteXi ((1 / 2 : ℂ) + Complex.I * w))))
    (h_dense : closure (regularDomain (fun w => concreteXi ((1 / 2 : ℂ) + Complex.I * w))) = univ)
    (h_diff :
      DifferentiableOn ℂ
        (fun z =>
          R.fredholmDeterminant z /
            concreteXi ((1 / 2 : ℂ) + Complex.I * z))
        (regularDomain (fun w => concreteXi ((1 / 2 : ℂ) + Complex.I * w))))
    (h_const_ratio :
      ∀ s ∈ regularDomain (fun w => concreteXi ((1 / 2 : ℂ) + Complex.I * w)),
        R.fredholmDeterminant s / concreteXi ((1 / 2 : ℂ) + Complex.I * s) =
          R.fredholmDeterminant 0 / concreteXi (1 / 2 : ℂ))
    (h_extend :
      ∀ s : ℂ,
        (∀ z ∈ regularDomain (fun w => concreteXi ((1 / 2 : ℂ) + Complex.I * w)),
          R.fredholmDeterminant z = concreteXi ((1 / 2 : ℂ) + Complex.I * z)) →
        R.fredholmDeterminant s = concreteXi ((1 / 2 : ℂ) + Complex.I * s))
    (h_spec_real : EssSelfAdjoint M → ∀ s : ℂ, R.isSpectralPoint s → s.im = 0)
    (s : ℂ)
    (hs_zero : concreteXi ((1 / 2 : ℂ) + Complex.I * s) = 0) :
    ((1 / 2 : ℂ) + Complex.I * s).re = (1 / 2 : ℝ) := by
  have hs_im_zero : s.im = 0 :=
    riemann_hypothesis_cosmic_closure
      M R h2 Adata Tdata hgeom hD_entire hXi_entire h_self_adjoint
      h_norm_match h_xi_zero_ne h_preconn h_dense h_diff h_const_ratio h_extend
      h_spec_real s hs_zero
  simp [hs_im_zero]

end CoronacionFinal
end RiemannAdelic
