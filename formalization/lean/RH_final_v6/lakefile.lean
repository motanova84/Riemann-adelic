import Lake
open Lake DSL

package rh_final_v6 where
  moreLeanArgs := #["-Dlinter.unusedVariables=false"]
  leanOptions := #[⟨`relaxedAutoImplicit, false⟩]

lean_lib RHFinal where
  roots := #[`paley_wiener_uniqueness, `selberg_trace, `H_psi_complete, `D_limit_equals_xi, `H_psi_self_adjoint]
  roots := #[
    `paley_wiener_uniqueness,
    `selberg_trace,
    `H_psi_complete,
    `D_limit_equals_xi,
    `D_equals_Xi,
    `rh_final_theorem,
    `spectrum_HΨ_equals_zeta_zeros,
    `heat_kernel_to_delta_plus_primes,
    `spectral_convergence_from_kernel,
    `SelbergTraceStrong,
    `zeta_operator_D,
    `Riemann_Hypothesis_noetic,
    `NuclearityExplicit
  ]
  roots := #[`paley_wiener_uniqueness, `selberg_trace, `H_psi_complete, `D_limit_equals_xi, `spectral_convergence_from_kernel]
