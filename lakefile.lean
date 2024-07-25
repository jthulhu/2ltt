import Lake
open Lake DSL

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "generalize_proofs_bug"

package tltt where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`linter.unusedVariables, false⟩
  ]

@[default_target]
lean_lib Tltt where

lean_lib Misc where
