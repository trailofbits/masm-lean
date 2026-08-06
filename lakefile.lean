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
    -- One focused goal at a time: any tactic leaving several goals is followed
    -- by one `·` block per goal. Goal-ordering dependence is the fragility
    -- class this library keeps rediscovering — a `congr`/`apply` whose
    -- subgoals get reordered silently redirects the next `omega` or `exact`
    -- onto a different limb, and the breakage surfaces far from its cause.
    -- Measured over the 138 hand-written modules under `MidenLean/` (excluding
    -- `Proofs/Generated/`): 8 findings, cleared by focusing the two
    -- `Nat.pow_le_pow_right` side conditions in U128/ShrK0-2 (6) and the
    -- `congr 1` limb peel at the end of U64/WideningMul (2).
    ⟨`weak.linter.style.multiGoal, true⟩,
    -- No `debug`/`pp`/`profiler`/`trace` options, and no UNSCOPED
    -- `maxHeartbeats`. Note it is only the unscoped, file-level form that is
    -- forbidden: `set_option maxHeartbeats N in <decl>` is fine and this
    -- library leans on it heavily (284 occurrences). The file-level form is
    -- the problem, because it silently hands every later declaration in the
    -- file a budget nobody measured for it. One finding, in
    -- `Proofs/StepLemmas.lean`, whose 4M file-level budget re-measured as pure
    -- scaffolding: all 82 step lemmas elaborate inside the 200000 default.
    ⟨`weak.linter.style.setOption, true⟩,
    -- Core Lean rather than Mathlib, so the `weak.` prefix is belt-and-braces
    -- here; it keeps the list uniform and costs nothing. Flags a theorem passed
    -- as a simp argument whose right-hand side the ambient simp set cannot
    -- normalize, which is what turns `simp [thm]` into a divergence instead of a
    -- readable failure. Measured over the 143 hand-written library modules: one
    -- finding, in `Symbolic/Soundness.lean`, where `simp [execInstruction]` hands
    -- simp a 110-equation match and the check itself runs out of heartbeats;
    -- that one declaration opts out locally with a comment, everything else is
    -- clean. Cost is in the noise (`U64/Shr` 5.76s → 5.72s, `U128/Divmod` 84s).
    ⟨`weak.linter.loopingSimpArgs, true⟩,
    -- The most valuable linter here: it flags a RIGID tactic (`rw`, `exact`,
    -- `omega`, and `simp only` too) whose success depends on the goal shape a
    -- preceding FLEXIBLE one (bare `simp`/`simp_all`) happened to leave. That is
    -- precisely the fragility this project keeps rediscovering across Mathlib
    -- bumps: `simp` normalizes slightly differently, and the rigid tactic after
    -- it stops matching. Terminal `simp` calls are correctly not flagged.
    -- Cleared from 438 warnings / 75 reported sites / 25 files. Every fix was a
    -- squeeze — the house rule "non-terminal `simp` becomes `simp only [...]`" —
    -- with no proof restructuring anywhere. Two things learned doing it:
    --   * The reported site count is a LOWER BOUND. The linter's stain stops
    --     propagating at the first fix, so pinning a flagged `simp` unmasks the
    --     next one in the same ladder. Real total was ~105 sites, not 75
    --     (U128/Divmod alone: 15 reported, 30 changed). Probe EVERY occurrence
    --     of an idiom in one pass or you get a cascade of rounds.
    --   * Derive every list with `simp?` in place. Lists do not transfer between
    --     sites that look identical, and the linter's own `Try this:` suggestion
    --     must not be pasted — it re-runs a DEFAULT `simp`, dropping the
    --     arguments the original call passed.
    ⟨`weak.linter.flexible, true⟩
    -- Measured but NOT yet enabled, because they are not clean and a gate that
    -- fails is not a gate. Backlog:
    --   linter.style.maxHeartbeats 286 overrides wanting a justification comment
    --     (measured before StepLemmas' file-level override was deleted, so the
    --      real figure is now 285 or lower; not re-measured, so treat as stale)
    --   linter.style.longLine      489 reported by the linter; 581 raw lines
    --     over 100 characters, so ~92 are exempt under its own rules. Heavily
    --     concentrated: U128/Divmod.lean holds 148 of the 581 and the top ten
    --     files about half, which argues for fixing it per-file when a file is
    --     open for another reason rather than as a sweep.
    -- They run in CI's advisory job; promote each into this list as it reaches
    -- zero.
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
