import Lake
open Lake DSL

package rh_final_v6 where
  moreLeanArgs := #["-Dlinter.unusedVariables=false"]
  leanOptions := #[⟨`relaxedAutoImplicit, false⟩]

lean_lib RHFinal where
  roots := #[`paley_wiener_uniqueness, `selberg_trace, `H_psi_complete, `D_limit_equals_xi]
