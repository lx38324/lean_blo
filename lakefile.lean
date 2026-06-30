import Lake
open Lake DSL

package «ousvr-blo-lean» where
  -- This project formalizes the finite-horizon Lyapunov budget skeleton
  -- of the OUSVR-BLO online value-anchor proof.

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"

@[default_target]
lean_lib «OUSVRBLO» where
