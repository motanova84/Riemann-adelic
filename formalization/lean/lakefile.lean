import Lake
open Lake DSL

package riemannAdelic {
  -- configura opciones de compilación
  moreLeanArgs := #["-DautoImplicit=false", "-Dlinter=false"]
}

@[default_target]
lean_lib RiemannAdelic where
  globs := #[
    "axioms_to_lemmas",
    "schwartz_adelic",
    "D_explicit",
    "functional_eq",
    "de_branges",
    "entire_order",
    "positivity",
    "RH_final"
  ]
package riemannAdelic

@[default_target]
lean_lib RiemannAdelic
package «riemann-adelic-lean» where
  -- Version and configuration
  version := "5.1"
  -- Require Lean 4.5.0 or higher
  preferReleaseBuild := true

lean_lib «RiemannAdelic» where
  -- Library configuration for the Riemann Adelic proof modules
  globs := #[.submodules `RiemannAdelic]
  roots := #[`RiemannAdelic]

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
  "https://github.com/leanprover-community/mathlib4.git" @ "master"
