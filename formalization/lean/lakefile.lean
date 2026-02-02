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

-- RHOperator library - Operator theory for RH
lean_lib RHOperator where
  globs := #[.submodules `RHOperator]
  roots := #[`RHOperator]
-- Adelic library - L-function spectral reconstruction
lean_lib adelic where
  globs := #[.submodules `adelic]
  roots := #[`adelic]

-- Arpeth library - H_Ψ operator framework
lean_lib Arpeth where
  globs := #[.submodules `Arpeth]
  roots := #[`Arpeth]

-- Mathlib-style spectral formalization - 6-step RH proof
lean_lib Mathlib where
  globs := #[.submodules `Mathlib]
  roots := #[`Mathlib]

-- HilbertPolyaProof library - Complete operator-theoretic RH proof
lean_lib HilbertPolyaProof where
  globs := #[.submodules `HilbertPolyaProof]
  roots := #[`HilbertPolyaProof]

-- Main executable
@[default_target]
lean_exe «riemann-adelic-lean» where
  root := `Main
  supportInterpreter := true

-- Require mathlib4 for complete mathematical library support
-- Using stable v4.5.0 tag to ensure CI stability
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.5.0"

-- Let Lake resolve aesop version compatible with mathlib v4.5.0
require aesop from git
  "https://github.com/leanprover-community/aesop" @ "master"

-- Let Lake resolve proofwidgets version compatible with mathlib v4.5.0
require proofwidgets from git
  "https://github.com/leanprover-community/proofwidgets4" @ "master"
