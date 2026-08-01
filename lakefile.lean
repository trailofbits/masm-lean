import Lake
open Lake DSL

package MidenLean where
  leanOptions := #[⟨`autoImplicit, false⟩]

require "leanprover-community" / "mathlib" @ git "v4.28.0"

@[default_target]
lean_lib MidenLean where
  srcDir := "."

/-- Symbolic-framework regression tests. Not part of the default target (they
    are deliberately outside the `MidenLean` import graph), so build them
    explicitly with `lake build MidenLeanTests` — otherwise they rot silently,
    as `Symbolic/TacticTest.lean` did after the `Concrete/` restructure. -/
lean_lib MidenLeanTests where
  srcDir := "."
  roots := #[
    `MidenLean.Symbolic.ControlFlowTest,
    `MidenLean.Symbolic.MemoryAdviceTest,
    `MidenLean.Symbolic.SpikeTest,
    `MidenLean.Symbolic.TacticTest
  ]
