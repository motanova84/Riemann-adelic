import Lake
open Lake DSL

package rh_final_v6 where
  moreLeanArgs := #["-Dlinter.unusedVariables=false"]
  leanOptions := #[⟨`relaxedAutoImplicit, false⟩]

lean_lib RHFinal where
  roots := #[`paley_wiener_uniqueness, `selberg_trace, `H_psi_complete, `D_limit_equals_xi, 
             `SpectralIdentification, `Operator.Hψ, `PaleyWiener.Unicity, 
             `Spectral.MellinIdentification, `Zeta.FunctionalEquation]
  roots := #[`paley_wiener_uniqueness, `selberg_trace, `H_psi_complete, `D_limit_equals_xi, `spectrum_eq_zeros]
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
    `RiemannSiegel,
    `DeterminantFredholm,
    `NoExtraneousEigenvalues,
    `RHComplete
  ]
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
  roots := #[`paley_wiener_uniqueness, `selberg_trace, `H_psi_complete, `D_limit_equals_xi, `spectral_convergence_from_kernel, `zeros_xi_structure]
