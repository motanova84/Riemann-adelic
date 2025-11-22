import Lake
open Lake DSL

package rh_final_v6 where
  moreLeanArgs := #["-Dlinter.unusedVariables=false"]
  leanOptions := #[⟨`relaxedAutoImplicit, false⟩]

lean_lib RHFinal where
  roots := #[`D_limit_equals_xi, `H_psi_complete, `paley_wiener_uniqueness, `selberg_trace, `spectrum_eq_zeros, `spectrum_HΨ_equals_zeta_zeros]
