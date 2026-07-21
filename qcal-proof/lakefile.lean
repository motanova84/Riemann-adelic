import Lake
open Lake DSL

package «qcal-proof» where
  preferReleaseBuild := true

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.5.0"

@[default_target]
lean_lib QCALProof
