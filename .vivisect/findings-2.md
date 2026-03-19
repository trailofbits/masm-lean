# Vivisect Findings: masm-lean

Date:  2026-03-18
Scope: MidenLean/ (44 .lean files, ~5800 lines)
Tools: trailmark (summary), manual review,
       contrarian (validation)

## Executive Summary

masm-lean is a Lean 4 formal semantics for the Miden
VM instruction set, with correctness proofs for
generated u64 and word procedures. The core semantics
engine (Semantics.lean) is well-structured: each
instruction handler is a pure function from
MidenState to Option MidenState, with clear failure
modes. Two previously-reported bugs (advLoadW element
reversal, missing u32 precondition checks) have been
fixed with regression tests.

The primary concern is three unproved axioms in the
word comparison proofs (lt, lte, gte), which create
a soundness gap in an otherwise fully-verified
codebase. Several intentional modeling simplifications
(unbounded stack, element-addressed memory, emit as
no-op) are well-documented and acceptable for the
project's purpose.

| Category | Findings | Instances |
|----------|----------|-----------|
| Good     | 7        | --        |
| Bad      | 4        | 7         |
| Broken   | 0        | 0         |
| Absurd   | 1        | 3         |

Coverage: 3/3 targets manually reviewed,
44/44 files reviewed, 2 review passes completed

Biggest risk: Three axioms (word_lt_full_correct,
word_lte_full_correct, word_gte_full_correct) bypass
proof checking entirely. If an axiom statement is
wrong, dependent theorems are silently unsound.

---

## Good

### Felt type definition
Evidence:         Felt.lean:10, ZMod GOLDILOCKS_PRIME
Manual review:    Prime proven via native_decide.
                  Field arithmetic inherited from
                  Mathlib ZMod. isU32/isBool helpers
                  are straightforward comparisons.
Contrarian result: SOUND -- type is a Mathlib wrapper,
                  no custom arithmetic to break.

---

### Instruction dispatch (execInstruction)
Evidence:         Semantics.lean:921-1038,
                  302 functions, 3635 call edges
Manual review:    Complete match on all Instruction
                  constructors. Each arm delegates to
                  a dedicated handler. No fallthrough,
                  no default case, exhaustiveness
                  checked by Lean compiler.
Contrarian result: SOUND -- pure dispatch, no logic.

---

### U32 precondition enforcement
Evidence:         Semantics.lean:453-751
Manual review:    All 34 u32 operations now include
                  isU32 guards. Previously missing
                  (spec AC-7/8/9/11), now fixed.
                  Regression tests at
                  Tests/Semantics.lean:519-573.
Contrarian result: SOUND -- every u32 handler checked.

---

### advLoadW element ordering (fixed)
Evidence:         Semantics.lean:899-906
Manual review:    Previously reversed 4 elements
                  (spec AC-14). Now uses
                  `vals ++ rest` without reverse.
                  Regression test at
                  Tests/Semantics.lean:786-790.
Contrarian result: SOUND -- test confirms ordering.

---

### word_gt_correct proof
Evidence:         Proofs/WordGt.lean:76-158
Manual review:    Full proof by 4-iteration loop
                  induction. Uses one_gt_iteration_body
                  lemma for each step. No axioms, no
                  sorry. Boolean normalization via
                  Felt.ite_val_eq_one and simp.
Contrarian result: SOUND -- Lean type-checked.

---

### Control flow interpreter (execWithEnv)
Evidence:         Semantics.lean:1049-1095
Manual review:    Fuel-bounded recursion. foldlM for
                  sequential ops. ifElse/repeat/
                  whileTrue handle control flow with
                  boolean condition checks. ProcEnv
                  lookup for exec. Clean and correct.
Contrarian result: SOUND -- standard interpreter
                  pattern.

---

### Generated procedure definitions
Evidence:         Generated/U64.lean (458 lines),
                  Generated/Word.lean (154 lines)
Manual review:    Pure instruction lists produced by
                  Rust translator. Proofs verify these
                  exact sequences. Not hand-editable
                  without breaking proofs. Correct
                  by design.
Contrarian result: SOUND -- verified by proofs.

---

## Bad

### Unbounded stack model diverges from Rust
Evidence: State.lean:8, trailmark: 0 entry points
Problem:  Lean uses `List Felt` with no minimum
          depth of 16 and no maximum of 2^16. Rust
          auto-pads to depth 16 with zeros and
          rejects beyond 2^16. Operations on short
          stacks fail in Lean but succeed in Rust
          (accessing zero-padded elements).

Affected locations:
- `State.lean:8` -- `MidenState.stack`: unbounded
  List Felt definition
- `Semantics.lean:155-158` -- `execDup`: fails if
  stack too short, but Rust would auto-pad

Tests:
- Existing tests exercise short stacks, documenting
  the divergence.

---

### Element-addressed memory diverges from Rust
Evidence: State.lean:9-10, Semantics.lean:780-878
Problem:  Lean uses `Nat -> Felt` (per-element).
          Rust uses `BTreeMap<u32, [Felt; 4]>` (per
          word). Be/Le variants compensate. Alignment
          checks (addr % 4 != 0) are present in word
          ops.

Affected locations:
- `State.lean:9-10` -- `MidenState.memory`: Nat ->
  Felt instead of word-addressed
- `Semantics.lean:780-878` -- all memStorew/memLoadw
  handlers: Be/Le variants with different element
  ordering

Tests:
- Tests/Semantics.lean:802-835 -- memory store/load
  round-trip tests

---

### Emit modeled as no-op
Evidence: Semantics.lean:911-914, 1037
Problem:  `execEmit` only checks stack non-empty,
          does not read top. `execEmitImm` (line 1037)
          ignores event ID entirely. Rust's emit
          reads the top element as event ID and
          records it.

Affected locations:
- `Semantics.lean:911-914` -- `execEmit`: no-op
- `Semantics.lean:1037` -- `emitImm`: ignores
  argument

Tests:
- No tests for emit behavior (semantic no-op).

---

### Inconsistent NOT implementation style
Evidence: Semantics.lean:90-95
Problem:  `u32CountLeadingOnes` uses arithmetic NOT
          (`u32Max - 1 - n`) while
          `u32CountTrailingOnes` uses XOR operator
          (`n ^^^ (u32Max - 1)`). Both are correct
          for u32 values but the inconsistency is a
          maintenance risk -- if one is changed, the
          other may be forgotten.

Affected locations:
- `Semantics.lean:90-91` -- `u32CountLeadingOnes`:
  arithmetic subtraction
- `Semantics.lean:94-95` -- `u32CountTrailingOnes`:
  XOR operator

Tests:
- Tests/Semantics.lean:639-650 -- clo/cto tests
  verify correctness of both implementations

---

## Broken

(No broken findings. All previously-reported bugs
have been fixed with regression tests.)

---

## Absurd

### Three unproved axioms in word comparison proofs
Root cause:            word_lt_full_correct,
                       word_lte_full_correct, and
                       word_gte_full_correct are
                       declared as Lean `axiom`
                       instead of proved theorems.
Manual review finding: WordLt.lean:12-24,
                       WordLte.lean:12-24,
                       WordGte.lean:12-24
Unenforced assumption: The axiom statements correctly
                       describe the behavior of the
                       respective word comparison
                       procedures.
Triggering scenario:   If an axiom statement contains
                       an error (wrong comparison
                       direction, wrong boolean
                       associativity, wrong limb
                       order), all theorems that
                       depend on it are unsound.
                       word_gte depends on word_lt
                       which is itself an axiom,
                       creating a two-deep axiom
                       chain.
Trailmark signal:      No privilege boundary detected;
                       these are internal proof
                       components.
Contrarian validation: INCOMPLETE -- axioms cannot
                       be validated by the proof
                       checker by definition. Manual
                       inspection of the axiom
                       statements shows they appear
                       correct (consistent with
                       word_gt_correct's structure),
                       but this is not machine-checked.

Affected locations:
- `Proofs/WordLt.lean:12-24` --
  `word_lt_full_correct`: axiom for word::lt
- `Proofs/WordLte.lean:12-24` --
  `word_lte_full_correct`: axiom for word::lte
- `Proofs/WordGte.lean:12-24` --
  `word_gte_full_correct`: axiom for word::gte

Tests:
- Tests/Semantics.lean exercises word comparison
  with concrete values (but these are execution
  tests, not proof tests; they verify the code
  runs correctly, not that the axiom statements
  are correct).

---

## Test Coverage

| Test | Category | Finding | Purpose |
|------|----------|---------|---------|
| Tests/Semantics.lean:786-790 | Good | advLoadW fixed | Regression: element order |
| Tests/Semantics.lean:519-573 | Good | u32 preconditions | Regression: non-u32 rejection |
| Tests/Semantics.lean:639-650 | Bad | NOT inconsistency | Verifies clo/cto correctness |

---

## Coverage

Modules: 3/3 targets analyzed

| Module | Manual Review | Contrarian | Passes | Status |
|--------|---------------|------------|--------|--------|
| core-semantics | Yes | Yes | 2 | Reviewed |
| generated-procs | Yes | Yes | 2 | Reviewed |
| proofs | Yes | Yes | 2 | Reviewed |

Uncovered: None. All 44 source files reviewed.

---

## Methodology

Findings were identified through manual code review
guided by trailmark structural analysis (302
functions, 3635 call edges, 0 entry points). The
.galvanize/spec.md was used as a reference for
expected behavior and known issues. All spec-documented
bugs (AC-14: advLoadW reversal, AC-7/8/9/11: u32
preconditions) were verified as fixed with regression
tests. Three axioms were identified as the primary
soundness concern through grep for `axiom` and
`sorry` keywords, followed by manual review of proof
structure.
