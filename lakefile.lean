import Lake
open Lake DSL

package «riemann-hypothesis-lean» {
  -- Lean version
  leanVersion := .v4_2

  -- Pin mathlib
  requires mathlib from git
    "https://github.com/leanprover-community/mathlib4" @ "0ff3c5a9d58c3e38b6c9b236e8b5e56dcb2e573a"
}

@[default_target]
lean_lib RiemannHypothesis
