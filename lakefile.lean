import Lake
open Lake DSL

package MidenLean where
  leanOptions := #[⟨`autoImplicit, false⟩]

require "leanprover-community" / "mathlib" @ git "v4.28.0"

@[default_target]
lean_lib MidenLean where
  srcDir := "."
