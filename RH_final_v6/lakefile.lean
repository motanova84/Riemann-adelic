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

-- Aesop commit used by mathlib v4.5.0 for reproducible builds
require aesop from git
  "https://github.com/leanprover-community/aesop" @ "cebd10ba6d22457e364ba03320cfd9fc7511e520"

-- Proofwidgets commit (v0.0.25) used by mathlib v4.5.0 for reproducible builds
require proofwidgets from git
  "https://github.com/leanprover-community/proofwidgets4" @ "8dd18350791c85c0fc9adbd6254c94a81d260d35"
