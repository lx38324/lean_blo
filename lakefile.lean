import Lake
open Lake DSL

package «ousvr-blo-lean» where
  -- Certificate-sensitive formalization of the OUSVR-BLO restricted/local
  -- fixed-penalty stationarity, gain, proximal-response, and stochastic budgets.

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "81a5d257c8e410db227a6665ed08f64fea08e997"

@[default_target]
lean_lib «OUSVRBLO» where
