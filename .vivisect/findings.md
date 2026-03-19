# Vivisect Findings: masm-lean

Date:  2026-03-19
Scope: MidenLean/ (99 .lean files, ~22000 lines)
Tools: trailmark (summary), manual review,
       contrarian (validation)

## Executive Summary

masm-lean is a Lean 4 formal semantics for the
Miden VM instruction set, with correctness proofs
for generated u64 and word procedures. The core
semantics engine (Semantics.lean, 1179 lines)
implements each instruction handler as a pure
function from MidenState to Option MidenState,
with clear failure modes and exhaustive dispatch.

All previously-reported bugs have been fixed:
- advLoadW element reversal (spec AC-14): fixed
  at Semantics.lean:975 with regression test.
- 34 u32 ops missing isU32 guards (spec
  AC-7/8/9/11): all now enforced with regression
  tests.
- emit/emitImm no-op behavior (spec AC-12): now
  records event IDs in MidenState.events field.
- 3 word comparison axioms (lt, lte, gte): all
  replaced with full machine-checked proofs.
- NOT style inconsistency in u32CountLeadingOnes:
  fixed to use XOR consistently.

The codebase has zero sorry, zero axiom outside
Mathlib dependencies. A semantic interpretation
layer (Proofs/Interp.lean) and cross-validation
test suite (Tests/CrossValidation.lean) provide
additional confidence.

| Category | Findings | Instances |
|----------|----------|-----------|
| Good     | 16       | --        |
| Bad      | 2        | 3         |
| Broken   | 0        | 0         |
| Absurd   | 0        | 0         |

Coverage: 3/3 targets manually reviewed,
99/99 files reviewed, 5 review passes completed

Biggest risk: No critical risks remain. The main
concern is that the element-addressed memory model
diverges from Rust's word-addressed model.

---

## Good

### Felt type definition
Evidence:         Felt.lean:10, ZMod
                  GOLDILOCKS_PRIME
Manual review:    GOLDILOCKS_PRIME = 2^64 - 2^32
                  + 1 proven prime via
                  native_decide. Field arithmetic
                  inherited from Mathlib ZMod.
                  isU32/isBool helpers are
                  straightforward comparisons.
Contrarian result: SOUND -- type is a Mathlib
                  wrapper, no custom arithmetic.

---

### Instruction dispatch (execInstruction)
Evidence:         Semantics.lean:994-1112,
                  complete match on all
                  Instruction constructors
Manual review:    Each arm delegates to a
                  dedicated handler. No
                  fallthrough, no default case,
                  exhaustiveness checked by Lean
                  compiler.
Contrarian result: SOUND -- pure dispatch.

---

### U32 precondition enforcement
Evidence:         Semantics.lean:493-797
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
Contrarian result: SOUND -- test confirms order.

---

### advPush reversal semantics
Evidence:         Semantics.lean:957-962
Manual review:    advPush pops N elements from
                  advice stack one at a time
                  (FIFO onto LIFO), so the result
                  is correctly reversed. The
                  `vals.reverse` matches Rust's
                  N consecutive ADVPOP operations.
Contrarian result: SOUND -- matches Rust VM.

---

### word_gt_correct proof
Evidence:         Proofs/Word/Gt.lean
Manual review:    Full proof by 4-iteration loop
                  induction. No axioms, no sorry.
Contrarian result: SOUND -- Lean type-checked.

---

### word_lt proof (formerly axiom)
Evidence:         Proofs/Word/Lt.lean
Manual review:    Full proof using lt_iteration
                  lemma. No axioms, no sorry.
Contrarian result: SOUND -- Lean type-checked.

---

### word_lte proof (formerly axiom)
Evidence:         Proofs/Word/Lte.lean
Manual review:    Derived from word_gt_correct
                  by composing with not. Full
                  theorem, no axioms.
Contrarian result: SOUND -- Lean type-checked.

---

### word_gte proof (formerly axiom)
Evidence:         Proofs/Word/Gte.lean
Manual review:    Derived from word_lt by
                  composing with not. Full
                  theorem, no axioms.
Contrarian result: SOUND -- Lean type-checked.

---

### Control flow interpreter (execWithEnv)
Evidence:         Semantics.lean:1123-1169
Manual review:    Fuel-bounded recursion. foldlM
                  for sequential ops. ifElse,
                  repeat, whileTrue handle control
                  flow with boolean condition
                  checks. ProcEnv lookup for exec.
Contrarian result: SOUND -- standard interpreter
                  pattern.

---

### Generated procedure definitions
Evidence:         Generated/U64.lean (458 lines),
                  Generated/Word.lean (154 lines)
Manual review:    Pure instruction lists produced
                  by Rust translator. Proofs verify
                  these exact sequences. Not
                  hand-editable without breaking
                  proofs.
Contrarian result: SOUND -- verified by proofs.

---

### Semantic interpretation layer
Evidence:         Proofs/Interp.lean (385 lines)
Manual review:    toU64, toU128 interpretation
                  functions mapping u32 limb pairs
                  to Nat. Bridge lemmas connect
                  low-level proofs to mathematical
                  statements. Carry chain theorem
                  verified algebraically. All
                  proofs complete, no axioms.
Contrarian result: SOUND -- pure mathematics,
                  machine-checked.

---

### Semantic proof corollaries
Evidence:         16 files in Proofs/U64/
Manual review:    Each file has a _semantic or
                  _toU64 corollary chaining the
                  _correct theorem with bridge
                  lemmas from Interp.lean. All
                  corollaries are sorry-free.
Contrarian result: SOUND -- mechanical composition.

---

### Cross-validation test suite
Evidence:         Tests/CrossValidation.lean
                  (233 lines)
Manual review:    30+ tests running MASM library
                  procedures through Lean semantics
                  against miden-vm Rust test
                  vectors. Covers arithmetic,
                  comparison, bitwise, shift ops.
Contrarian result: SOUND -- independent validation
                  against reference implementation.

---

### Emit/emitImm event recording (fixed)
Evidence:         Semantics.lean:983-986,
                  1110-1111; State.lean:16
Manual review:    execEmit reads top stack element
                  as eventId, records in
                  s.events. emitImm records the
                  immediate argument. Previously
                  was a no-op (spec AC-12). Now
                  functional.
Contrarian result: SOUND -- events field correctly
                  threaded through state.

---

### Bounded stack infrastructure
Evidence:         State.lean:75-99
Manual review:    MIN_STACK_DEPTH (16),
                  MAX_STACK_DEPTH (2^16),
                  padStack, wellFormed, and
                  ofStackPadded provide vocabulary
                  for proofs to state well-
                  formedness assumptions. padStack
                  appends zeros to reach minimum
                  depth.
Contrarian result: SOUND -- definitions are
                  correct, used in proofs.

---

## Bad

### Element-addressed memory diverges from Rust
Evidence: State.lean:9-10, Semantics.lean:805-928
Problem:  Lean uses `Nat -> Felt` (per-element).
          Rust uses `BTreeMap<u32, [Felt; 4]>`
          (per word). Be/Le variants compensate
          for element ordering within words.
          Alignment checks (addr % 4 != 0) are
          present in word ops. This is an
          intentional modeling simplification
          documented in spec section 6, AC-13.

Affected locations:
- `State.lean:10` -- `MidenState.memory`:
  Nat -> Felt instead of word-addressed
- `Semantics.lean:830-928` -- all memStorew/
  memLoadw handlers: Be/Le variants with
  different element ordering within words

Tests:
- Tests/Semantics.lean:802-835 -- memory
  store/load round-trip tests

---

### Stack depth not enforced per-instruction
Evidence: State.lean:8, Semantics.lean:147-255
Problem:  Individual instruction handlers operate
          on unbounded `List Felt`. The bounded
          stack infrastructure (wellFormed,
          padStack) provides Prop-level
          constraints but does not prevent
          creating states with fewer than 16
          elements. Operations on short stacks
          return `none` in Lean where Rust would
          auto-pad zeros. This is an intentional
          modeling simplification documented in
          spec section 6, AC-5.

Affected locations:
- `State.lean:8` -- `MidenState.stack`:
  unbounded List Felt definition
- `Semantics.lean:169-172` -- `execDup`: fails
  if stack too short; Rust would auto-pad

Tests:
- Existing tests exercise short stacks,
  documenting the divergence.

---

## Broken

(No broken findings. All previously-reported
bugs have been fixed with regression tests.
advLoadW reversal fixed at Semantics.lean:975.
U32 precondition guards added to all 34
operations. Emit now records events.)

---

## Absurd

(No absurd findings. The three unproved axioms
previously identified as concerns have been
replaced with full machine-checked proofs.
The codebase has zero sorry, zero axiom outside
Mathlib dependencies.)

---

## Test Coverage

| Test | Category | Finding | Purpose |
|------|----------|---------|---------|
| Tests/Semantics.lean:786-790 | Good | advLoadW fixed | Regression: element order |
| Tests/Semantics.lean:519-573 | Good | u32 preconditions | Regression: non-u32 rejection |
| Tests/CrossValidation.lean | Good | Cross-validation | Validate Lean model vs Rust |

---

## Coverage

Modules: 3/3 analyzed

| Module | Manual Review | Contrarian | Passes | Status |
|--------|---------------|------------|--------|--------|
| core-semantics | Yes | Yes | 5 | Reviewed |
| generated-procs | Yes | Yes | 5 | Reviewed |
| proofs | Yes | Yes | 5 | Reviewed |

Uncovered: None. All 99 source files reviewed.
Generated scaffolding (42 files in
Proofs/Generated/) contains sorry by design and
is not imported into the build.

---

## Spec Divergence Check

Comparing .galvanize/spec.md against
implementation:

1. AC-14 (advLoadW reversal): FIXED. Code at
   line 975 uses `vals ++ rest` (no reverse).
   Regression test present.
2. AC-7/8/9/11 (u32 preconditions): FIXED. All
   u32 ops now check isU32. Regression tests
   present.
3. AC-5 (stack depth): Documented divergence.
   Bounded infrastructure added (wellFormed,
   padStack) but not enforced per-instruction.
4. AC-13 (memory model): Documented divergence.
   Element-addressed with Be/Le variants.
5. AC-12 (emit): FIXED. execEmit now reads top
   element as event ID and records it.
   emitImm records immediate argument.

Minor spec documentation issue: spec section 7
describes assert as "top != 0 -> success" but
both Lean and Rust require exactly top == 1.
This is a spec text inaccuracy, not a code bug.

No impl-vs-spec divergences found beyond what
the spec documents as intentional.

---

## Methodology

Findings were identified through five passes of
manual code review guided by trailmark structural
analysis (1034 nodes, 11849 call edges, 831
functions). The .galvanize/spec.md was used as a
reference for expected behavior and known issues.
All spec-documented bugs (AC-14: advLoadW
reversal, AC-7/8/9/11: u32 preconditions,
AC-12: emit no-op) were verified as fixed with
regression tests or functional implementation.
Three axioms previously identified as soundness
concerns were verified as replaced with full
proofs. Grep for `axiom` and `sorry` confirmed
zero instances outside of generated scaffolding.
Incremental analysis (run 11) focused on State.lean
changes (bounded stack infrastructure, Word type)
and Semantics.lean emit implementation update.
