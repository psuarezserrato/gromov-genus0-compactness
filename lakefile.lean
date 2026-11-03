import Lake
open Lake DSL

package «GromovCompactness» where
  -- Build configuration for Gromov Compactness formalization
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.16.0"

@[default_target]
lean_lib «GromovCompactness» where
  -- Master library containing modules F00–G05
