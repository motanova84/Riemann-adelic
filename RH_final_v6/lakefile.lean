import Lake
open Lake DSL

package «RH_final_v6» where
  -- Require Lean 4.5.0 or higher
  preferReleaseBuild := true

@[default_target]
lean_lib «RH_final_v6» where
  globs := #[.andSubmodules `RH_final_v6]
  roots := #[`RH_final_v6]

-- Require mathlib4 for complete mathematical library support
-- Using stable v4.5.0 tag to match lean-toolchain
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.5.0"

-- Aesop version compatible with mathlib v4.5.0
require aesop from git
  "https://github.com/leanprover-community/aesop" @ "master"

-- Proofwidgets version compatible with mathlib v4.5.0
require proofwidgets from git
  "https://github.com/leanprover-community/proofwidgets4" @ "v0.0.25"
