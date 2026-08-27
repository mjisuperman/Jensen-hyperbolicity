import Lake
open Lake DSL

package jensen_hyperbolicity

-- The only dependency is mathlib (pinned to the v4.32.0-era commit below).
-- A referee runs `lake build`; the first invocation downloads mathlib automatically.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "81a5d257c8e410db227a6665ed08f64fea08e997"

@[default_target]
lean_lib JensenHyperbolicity
