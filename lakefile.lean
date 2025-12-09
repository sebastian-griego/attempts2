import Lake
open Lake DSL

package attempts2

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

@[default_target]
lean_lib Attempts2 where
