import Lake
open Lake DSL

package rh_final_v6 where
  moreLeanArgs := #["-Dlinter.unusedVariables=false"]
  leanOptions := #[⟨`relaxedAutoImplicit, false⟩]

lean_lib RHFinal where
  roots := #[
    `spectrum_HΨ_equals_zeta_zeros,
    `H_psi_complete,
    `heat_kernel_to_delta_plus_primes,
    `spectral_convergence_from_kernel,
    `paley_wiener_uniqueness,
    `SelbergTraceStrong,
    `D_limit_equals_xi,
    `zeta_operator_D,
    `Riemann_Hypothesis_noetic,
    `NuclearityExplicit,
    `FredholmDetEqualsXi,
    `UniquenessWithoutRH,
    `RHComplete
  ]
