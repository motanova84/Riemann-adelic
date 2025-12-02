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

lean_lib «QCAL» where
  -- QCAL library for universal verification
  roots := #[`QCAL]

-- RH_final_v6 library
lean_lib RH_final_v6 where
  globs := #[.submodules `RH_final_v6]

-- RiemannAdelic library - Base modules
lean_lib RiemannAdelic where
  globs := #[.submodules `RiemannAdelic]
  roots := #[`RiemannAdelic]

-- Adelic library - L-function spectral reconstruction
lean_lib adelic where
  globs := #[.submodules `adelic]
  roots := #[`adelic]

-- Main executable
@[default_target]
lean_exe «riemann-adelic-lean» where
  root := `Main
  supportInterpreter := true

-- Require mathlib4 for complete mathematical library support
-- Using master branch to ensure stable CI (fixed commit refs get deleted from mathlib history)
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

require aesop from git
  "https://github.com/leanprover-community/aesop" @ "main"

require proofwidgets from git
  "https://github.com/leanprover-community/proofwidgets4" @ "main"
