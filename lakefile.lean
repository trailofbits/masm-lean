import Lake
open Lake DSL

package MidenLean where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    -- Linters enabled beyond Lean/Mathlib's defaults. Each is here because it
    -- protects something this library actually cares about, and each currently
    -- reports zero findings, so they are gates rather than aspirations. See
    -- ARCHITECTURE.md for why the rest of Mathlib's set is deliberately not on.
    -- All of these are Mathlib-provided. `leanOptions` are passed as `-D` to
    -- EVERY module, including `Proofs/SimpAttrs.lean` and
    -- `Symbolic/SimpAttrs.lean`, which import only core Lean — and `-D` on an
    -- option that does not exist is a HARD ERROR, not a warning. The `weak.`
    -- prefix is exactly the escape hatch for this: set the option where it is
    -- registered, ignore it where it is not.
    ⟨`weak.linter.style.admit, true⟩,        -- `admit` is `sorry` by another name
    ⟨`weak.linter.style.nativeDecide, true⟩, -- compiler trust must be a reviewed, local act
    -- Core Lean rather than Mathlib, so the `weak.` prefix is belt-and-braces
    -- here; it keeps the list uniform and costs nothing. Flags a theorem passed
    -- as a simp argument whose right-hand side the ambient simp set cannot
    -- normalize, which is what turns `simp [thm]` into a divergence instead of a
    -- readable failure. Measured over the 143 hand-written library modules: one
    -- finding, in `Symbolic/Soundness.lean`, where `simp [execInstruction]` hands
    -- simp a 110-equation match and the check itself runs out of heartbeats;
    -- that one declaration opts out locally with a comment, everything else is
    -- clean. Cost is in the noise (`U64/Shr` 5.76s → 5.72s, `U128/Divmod` 84s).
    ⟨`weak.linter.loopingSimpArgs, true⟩
    -- Measured but NOT yet enabled, because they are not clean and a gate that
    -- fails is not a gate. Backlog, with counts from a full build:
    --   linter.flexible          438 warnings / 75 sites / 25 files
    --   linter.style.multiGoal     8 sites (U128 ShrK0-2, U64 WideningMul)
    --   linter.style.setOption     1 site
    --   linter.style.maxHeartbeats 286 overrides wanting a justification comment
    --   linter.style.longLine      489 lines over 100 characters
    -- They run in CI's advisory job; promote each into this list as it reaches
    -- zero. `flexible` is the valuable one: it flags a rigid tactic depending on
    -- a flexible one, which is the fragility class that has broken this project
    -- repeatedly.
  ]

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
