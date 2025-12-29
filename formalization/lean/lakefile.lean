import Lake
open Lake DSL

package «riemann-adelic-lean» where
  -- Version and configuration
  version := "6.0"
  -- Require Lean 4.5.0 or higher
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

-- RHOperator library - Operator theory for RH
lean_lib RHOperator where
  globs := #[.submodules `RHOperator]
  roots := #[`RHOperator]

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
