import Lake
open Lake DSL

/-!
# lakefile.lean - RHComplete Build Configuration

This lakefile is specifically configured for the RHComplete proof modules.

Author: José Manuel Mota Burruezo (JMMB Ψ✧)
Date: 2025-11-22
DOI: 10.5281/zenodo.17379721
-/

package RHComplete where
  -- Configure Lean compilation with unicode support and strict auto-implicit
  moreLeanArgs := #[
    "-Dpp.unicode.fun=true",
    "-DrelaxedAutoImplicit=false"
  ]

-- Require mathlib4 for complete mathematical library support
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.15.0"

-- Main library containing all proof modules
@[default_target]
lean_lib RiemannAdelic where
  globs := #[.submodules `RiemannAdelic]
  roots := #[`RiemannAdelic]

-- Individual module declarations for explicit dependency tracking
lean_lib RiemannSiegel where
  roots := #[`RiemannAdelic.RiemannSiegel]

lean_lib NoExtraneousEigenvalues where
  roots := #[`RiemannAdelic.NoExtraneousEigenvalues]

lean_lib DeterminantFredholm where
  roots := #[`RiemannAdelic.DeterminantFredholm]

lean_lib RHComplete where
  roots := #[`RiemannAdelic.RHComplete]

-- Optional executable for running the proof verification
lean_exe rhcomplete_verify where
  root := `Main
  supportInterpreter := true
