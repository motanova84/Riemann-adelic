import Lake
open Lake DSL

package rh_final_v6 where
  moreLeanArgs := #["-Dlinter.unusedVariables=false"]
  leanOptions := #[⟨`relaxedAutoImplicit, false⟩]

-- V6 Complete System Integration
lean_lib RH_final_v6 where
  roots := #[
    -- V6 New Components (Non-circular proof)
    `RH_final_v6.NoesisInfinity,
    `RH_final_v6.KernelExplicit,
    `RH_final_v6.CompactResolvent,
    `RH_final_v6.RHProved,
    `RH_final_v6.Main,
    -- V6 Existing Components
    `RH_final_v6.H_psi_self_adjoint,
    `RH_final_v6.H_psi_complete,
    `RH_final_v6.NoExtraneousEigenvalues,
    `RH_final_v6.RHComplete,
    `RH_final_v6.DeterminantFredholm,
    `RH_final_v6.RiemannSiegel,
    `RH_final_v6.SelbergTraceStrong,
    `RH_final_v6.D_limit_equals_xi,
    `RH_final_v6.paley_wiener_uniqueness,
    `RH_final_v6.selberg_trace
  ]
