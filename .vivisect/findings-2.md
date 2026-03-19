# Vivisect Findings: masm-lean

Date:  2026-03-19
Scope: MidenLean/ (99 .lean files, ~8500 lines)
Tools: trailmark (summary), manual review,
       contrarian (validation)

## Executive Summary

masm-lean is a Lean 4 formal semantics for the Miden
VM instruction set, with correctness proofs for
generated u64 and word procedures. The core semantics
engine (Semantics.lean) is well-structured: each
instruction handler is a pure function from
MidenState to Option MidenState, with clear failure
modes.

Since the previous run (2026-03-18), the following
improvements have been made:
- A semantic interpretation layer (Proofs/Interp.lean)
  introduces toU64/toU128 functions and bridge lemmas
  connecting low-level proofs to mathematical
  statements about u64/u128 arithmetic, bitwise ops,
  and comparisons.
- 16 proof files now have _semantic or _toU64
  corollary theorems providing human-readable
  correctness guarantees.
- The NOT style inconsistency (u32CountLeadingOnes)
  has been fixed to use XOR consistently.
- A cross-validation test suite
  (Tests/CrossValidation.lean) validates the Lean
  model against miden-vm Rust test vectors.
- Zero axioms, zero sorry outside generated scaffolds.

The remaining findings are intentional modeling
divergences from the Rust VM (unbounded stack,
element-addressed memory, emit as no-op).

| Category | Findings | Instances |
|----------|----------|-----------|
| Good     | 14       | --        |
| Bad      | 3        | 5         |
| Broken   | 0        | 0         |
| Absurd   | 0        | 0         |

Coverage: 3/3 targets manually reviewed,
99/99 files reviewed, 4 review passes completed

Biggest risk: No critical risks remain. The main
concern is that the unbounded stack model accepts
programs Rust would pad (minor fidelity gap).

---

## Good

### Felt type definition
Evidence:         Felt.lean:10, ZMod GOLDILOCKS_PRIME
Manual review:    Prime proven via native_decide.
                  Field arithmetic inherited from
                  Mathlib ZMod. isU32/isBool helpers
                  are straightforward comparisons.
Contrarian result: SOUND -- type is a Mathlib
                  wrapper, no custom arithmetic to
                  break.

---

### Instruction dispatch (execInstruction)
Evidence:         Semantics.lean:1087-1110,
                  complete match on all Instruction
                  constructors
Manual review:    Each arm delegates to a dedicated
                  handler. No fallthrough, no default
                  case, exhaustiveness checked by
                  Lean compiler.
Contrarian result: SOUND -- pure dispatch, no logic.

---

### U32 precondition enforcement
Evidence:         Semantics.lean:453-751
Manual review:    All 34 u32 operations now include
                  isU32 guards. Previously missing
                  (spec AC-7/8/9/11), now fixed.
                  Regression tests at
                  Tests/Semantics.lean:519-573.
Contrarian result: SOUND -- every u32 handler
                  checked.

---

### advLoadW element ordering (fixed)
Evidence:         Semantics.lean:968-976
Manual review:    Previously reversed 4 elements
                  (spec AC-14). Now uses
                  `vals ++ rest` without reverse.
                  Regression test at
                  Tests/Semantics.lean:786-790.
Contrarian result: SOUND -- test confirms ordering.

---

### word_gt_correct proof
Evidence:         Proofs/Word/Gt.lean
Manual review:    Full proof by 4-iteration loop
                  induction. No axioms, no sorry.
Contrarian result: SOUND -- Lean type-checked.

---

### word_lt proof (formerly axiom, now proved)
Evidence:         Proofs/Word/Lt.lean
Manual review:    Full proof using lt_iteration
                  lemma, structurally identical to
                  word_gt but using .gt instruction
                  (reversed comparison). No axioms,
                  no sorry.
Contrarian result: SOUND -- Lean type-checked.

---

### word_lte proof (formerly axiom, now proved)
Evidence:         Proofs/Word/Lte.lean
Manual review:    Derived from word_gt_correct by
                  composing with not. Full theorem,
                  no axioms.
Contrarian result: SOUND -- Lean type-checked.

---

### word_gte proof (formerly axiom, now proved)
Evidence:         Proofs/Word/Gte.lean
Manual review:    Derived from word_lt by composing
                  with not. Full theorem, no axioms.
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
                  Rust translator. Proofs verify
                  these exact sequences. Not hand-
                  editable without breaking proofs.
Contrarian result: SOUND -- verified by proofs.

---

### Semantic interpretation layer (NEW)
Evidence:         Proofs/Interp.lean (385 lines)
Manual review:    Introduces toU64, toU128
                  interpretation functions mapping
                  u32 limb pairs to Nat. Bridge
                  lemmas (toU64_eq_iff,
                  toU64_lt_iff, toU128_lt_iff,
                  u64_lt_condition_eq) connect
                  low-level overflow-sub patterns
                  to mathematical comparisons.
                  Bitwise composition theorems
                  (toU64_and/or/xor) proved via
                  Nat.testBit decomposition. Carry
                  chain theorem
                  (cross_product_mod_2_64) verified
                  algebraically. All proofs are
                  complete with no axioms.
Contrarian result: SOUND -- pure mathematics,
                  all machine-checked.

---

### Semantic proof corollaries (NEW)
Evidence:         16 files in Proofs/U64/ (And, Or,
                  Xor, Clz, Ctz, Clo, Min, Max,
                  Neq, Sub, WideningAdd,
                  WrappingMul, OverflowingSub, Shl,
                  and others)
Manual review:    Each file now has a _semantic or
                  _toU64 corollary that chains the
                  original _correct theorem with
                  bridge lemmas from Interp.lean.
                  Pattern: rw [original_correct];
                  simp_rw [bridge_lemma]. All
                  corollaries are sorry-free.
Contrarian result: SOUND -- mechanical composition
                  of verified components.

---

### NOT implementation consistency (FIXED)
Evidence:         Semantics.lean:90-91
Manual review:    u32CountLeadingOnes now uses XOR
                  (`n ^^^ (u32Max - 1)`) matching
                  u32CountTrailingOnes. Previously
                  used arithmetic subtraction
                  (`u32Max - 1 - n`). Both are
                  correct for u32 values but the
                  inconsistency was a code smell.
                  Now consistent.
Contrarian result: SOUND -- equivalent operations,
                  style fix only.

---

### Cross-validation test suite (NEW)
Evidence:         Tests/CrossValidation.lean
                  (233 lines)
Manual review:    30+ tests running MASM library
                  procedures through the Lean
                  semantics model against miden-vm
                  Rust test vectors (u64_mod.rs).
                  Covers: wrapping_add,
                  lt/lte/gt/gte, min/max,
                  eq/neq/eqz, divmod,
                  clz/ctz/clo/cto, shl/shr.
                  All tests use #eval with panic!
                  on mismatch.
Contrarian result: SOUND -- independent validation
                  against reference implementation.

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
          word). Be/Le variants compensate.
          Alignment checks (addr % 4 != 0) are
          present in word ops.

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
Evidence: Semantics.lean:978-981, 1109
Problem:  `execEmit` only checks stack non-empty,
          does not read top. `emitImm` (line 1109)
          ignores event ID entirely. Rust's emit
          reads the top element as event ID and
          records it.

Affected locations:
- `Semantics.lean:978-981` -- `execEmit`: no-op
- `Semantics.lean:1109` -- `emitImm`: ignores
  argument

Tests:
- No tests for emit behavior (semantic no-op).

---

## Broken

(No broken findings. All previously-reported bugs
have been fixed with regression tests. advLoadW
reversal fixed at Semantics.lean:975. U32
precondition guards added to all 34 operations.)

---

## Absurd

(No absurd findings. The three unproved axioms
previously categorized as concerns have been
replaced with full proofs:
- word_lt: Proofs/Word/Lt.lean (theorem)
- word_lte: Proofs/Word/Lte.lean (theorem)
- word_gte: Proofs/Word/Gte.lean (theorem)
All four word comparison proofs are now
machine-checked with zero axioms.)

---

## Test Coverage

| Test | Category | Finding | Purpose |
|------|----------|---------|---------|
| Tests/Semantics.lean:786-790 | Good | advLoadW fixed | Regression: element order |
| Tests/Semantics.lean:519-573 | Good | u32 preconditions | Regression: non-u32 rejection |
| Tests/CrossValidation.lean | Good | Cross-validation | Validate Lean model vs Rust |

---

## Coverage

Modules: 3/3 targets analyzed

| Module | Manual Review | Contrarian | Passes | Status |
|--------|---------------|------------|--------|--------|
| core-semantics | Yes | Yes | 4 | Reviewed |
| generated-procs | Yes | Yes | 4 | Reviewed |
| proofs | Yes | Yes | 4 | Reviewed |

Uncovered: None. All 99 source files reviewed.
Generated scaffolding (42 files in Proofs/Generated/)
contains sorry by design and is not imported into the
build.

---

## Spec Divergence Check

Comparing .galvanize/spec.md against implementation:

1. AC-14 (advLoadW reversal): FIXED. Code at line
   975 uses `vals ++ rest` (no reverse). Regression
   test present.
2. AC-7/8/9/11 (u32 preconditions): FIXED. All u32
   ops now check isU32. Regression tests present.
3. AC-5 (stack depth): Documented divergence.
   Unbounded List Felt, no enforcement.
4. AC-13 (memory model): Documented divergence.
   Element-addressed with Be/Le variants.
5. AC-12 (emit): Documented as no-op.

No impl-vs-spec divergences found beyond what the
spec itself documents as intentional.

---

## Methodology

Findings were identified through four passes of
manual code review guided by trailmark structural
analysis. The .galvanize/spec.md was used as a
reference for expected behavior and known issues.
All spec-documented bugs (AC-14: advLoadW reversal,
AC-7/8/9/11: u32 preconditions) were verified as
fixed with regression tests. Three axioms previously
identified as soundness concerns were verified as
replaced with full proofs. Grep for `axiom` and
`sorry` confirmed zero instances outside of
generated scaffolding. Incremental analysis focused
on 19 changed files since commit 56ef14f, including
the new semantic interpretation layer
(Proofs/Interp.lean) and cross-validation test
suite (Tests/CrossValidation.lean).
