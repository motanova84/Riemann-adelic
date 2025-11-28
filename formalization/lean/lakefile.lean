import Lake
open Lake DSL

package «riemann-adelic-lean» where
  -- Configuration for Lake build system
  preferReleaseBuild := true
  moreLeanArgs := #["-DautoImplicit=false"]

-- RHComplete library - Complete RH proof modules
lean_lib RHComplete where
  globs := #[.submodules `RHComplete]
  roots := #[`RHComplete]

-- RH_final_v6 library
lean_lib RH_final_v6 where
  globs := #[.submodules `RH_final_v6]

-- RiemannAdelic library - Base modules
lean_lib RiemannAdelic where
  globs := #[.submodules `RiemannAdelic]
  roots := #[`RiemannAdelic]

-- Operator library - Spectral operators and H_Ψ core
lean_lib Operator where
  globs := #[.submodules `Operator]
  roots := #[`Operator.H_psi_core]

-- Hpsi_selfadjoint - Part 34/∞³ self-adjointness module
lean_lib Hpsi where
  roots := #[`Hpsi_selfadjoint]

-- Main executable
@[default_target]
lean_exe «riemann-adelic-lean» where
  root := `Main
  supportInterpreter := true

-- Require mathlib4 for complete mathematical library support
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "07a2d4e5c3c9e55bb6e37bbf5132fd47d75b9ce2"

require aesop from git
  "https://github.com/leanprover-community/aesop" @ "main"

require proofwidgets from git
  "https://github.com/leanprover-community/proofwidgets4" @ "main"
