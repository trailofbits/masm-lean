# Vivisect Findings: masm-lean

Date:  2026-03-19 (run 12)
Scope: MidenLean/ (99 .lean files, ~22000 lines)
Tools: trailmark (summary), manual review,
       contrarian (validation)

## Executive Summary

masm-lean is a Lean 4 formal semantics for the
Miden VM instruction set, with correctness proofs
for generated u64 and word procedures. The core
semantics engine (Semantics.lean, 1174 lines)
implements each instruction handler as a pure
function from MidenState to Option MidenState.

The memory model was refactored from element-
addressed (`Nat -> Felt`) to word-addressed
(`Nat -> Word`) in this iteration. This resolves
the most significant previous divergence from the
Rust VM's `BTreeMap<u32, [Felt; 4]>` model. The
new model correctly maps each address to a 4-felt
tuple (Word), with `memStore`/`memLoad` accessing
element 0 and `memStorew`/`memLoadw` accessing the
full word. Be/Le variants handle element ordering
within words, with Le matching Rust's native order.

All previously-reported bugs remain fixed:
- advLoadW element reversal (spec AC-14)
- 34 u32 ops missing isU32 guards (spec AC-7/8/9/11)
- emit/emitImm no-op behavior (spec AC-12)
- 3 word comparison axioms replaced with full proofs

The codebase has zero sorry, zero axiom outside
Mathlib dependencies.

| Category | Findings | Instances |
|----------|----------|-----------|
| Good     | 17       | --        |
| Bad      | 1        | 1         |
| Broken   | 0        | 0         |
| Absurd   | 0        | 0         |

Coverage: 3/3 targets manually reviewed,
99/99 files reviewed, 6 review passes completed

Biggest risk: No critical risks. The one remaining
Bad finding (unbounded stack depth) is an intentional
modeling simplification documented in the spec.

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
Evidence:         Semantics.lean:988-1106,
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
Manual review:    All 34 u32 operations include
                  isU32 guards. Previously missing
                  (spec AC-7/8/9/11), now fixed.
                  Regression tests at
                  Tests/Semantics.lean:519-573.
Contrarian result: SOUND -- every u32 handler
                  checked.

---

### advLoadW element ordering (fixed)
Evidence:         Semantics.lean:962-970
Manual review:    Previously reversed 4 elements
                  (spec AC-14). Now uses
                  `vals ++ rest` without reverse.
                  Regression test at
                  Tests/Semantics.lean:786-790.
Contrarian result: SOUND -- test confirms order.

---

### advPush reversal semantics
Evidence:         Semantics.lean:951-956
Manual review:    advPush pops N elements from
                  advice stack one at a time
                  (FIFO onto LIFO), so the result
                  is correctly reversed. The
                  `vals.reverse` matches Rust's
                  N consecutive ADVPOP operations.
Contrarian result: SOUND -- matches Rust VM.

---

### Word-addressed memory model (NEW -- fixed)
Evidence:         State.lean:6-9,32,43,65-96
Manual review:    Memory is now `Nat -> Word`
                  matching Rust's `BTreeMap<u32,
                  [Felt; 4]>`. Each address maps
                  to a 4-element tuple.
                  `writeMemory` writes full word.
                  `writeMemoryElem0` writes only
                  element 0, preserving 1-3.
                  Default is `Word.zero = (0,0,0,0)`.
                  This resolves the previous Bad
                  finding about element-addressed
                  memory diverging from Rust.
Contrarian result: SOUND -- memory model now
                  matches Rust VM structure.

---

### memLoad/memStore single-element access
Evidence:         Semantics.lean:809-834
Manual review:    memLoad reads `(memory addr).1`
                  (element 0). memStore writes
                  element 0 via writeMemoryElem0.
                  Both match Rust's op_mload /
                  op_mstore which access word[0].
                  Round-trip verified: store v
                  then load returns v.
Contrarian result: SOUND -- element 0 access
                  matches Rust.

---

### memStorewLe/memLoadwLe (Rust-native order)
Evidence:         Semantics.lean:857-907
Manual review:    StorewLe stores (e0,e1,e2,e3)
                  where e0 = stack top after addr.
                  LoadwLe pushes w.1, w.2.1,
                  w.2.2.1, w.2.2.2 (element 0
                  on top). This matches Rust's
                  op_mstorew/op_mloadw where
                  stack[0] -> word[0]. Round-trip
                  tested at
                  Tests/Semantics.lean:1231-1241.
Contrarian result: SOUND -- Le = Rust native
                  order, verified by tests.

---

### word_gt_correct proof
Evidence:         Proofs/Word/Gt.lean
Manual review:    Full proof by 4-iteration loop
                  induction. No axioms, no sorry.
Contrarian result: SOUND -- Lean type-checked.

---

### word_lt/lte/gte proofs (formerly axioms)
Evidence:         Proofs/Word/Lt.lean,
                  Proofs/Word/Lte.lean,
                  Proofs/Word/Gte.lean
Manual review:    All three formerly axiom-based
                  proofs are now complete with
                  full machine-checked proofs.
                  Lt uses lt_iteration lemma;
                  lte/gte derived from gt/lt + not.
Contrarian result: SOUND -- Lean type-checked.

---

### Control flow interpreter (execWithEnv)
Evidence:         Semantics.lean:1117-1163
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
                  Generated/Word.lean (155 lines)
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
                  statements. All proofs complete.
Contrarian result: SOUND -- pure mathematics,
                  machine-checked.

---

### Cross-validation test suite
Evidence:         Tests/CrossValidation.lean
                  (233 lines)
Manual review:    30+ tests running MASM library
                  procedures through Lean semantics
                  against miden-vm Rust test vectors.
Contrarian result: SOUND -- independent validation.

---

### Emit/emitImm event recording (fixed)
Evidence:         Semantics.lean:977-981,
                  1104-1105; State.lean:50
Manual review:    execEmit reads top stack element
                  as eventId, records in s.events.
                  emitImm records the immediate
                  argument. Previously was a no-op
                  (spec AC-12). Now functional.
Contrarian result: SOUND -- events field correctly
                  threaded through state.

---

### Bounded stack infrastructure
Evidence:         State.lean:108-133
Manual review:    MIN_STACK_DEPTH (16),
                  MAX_STACK_DEPTH (2^16),
                  padStack, wellFormed, and
                  ofStackPadded provide vocabulary
                  for proofs. padStack appends
                  zeros to reach minimum depth.
Contrarian result: SOUND -- definitions correct.

---

### StoreWordU32sLe proof (updated for word model)
Evidence:         Proofs/Word/StoreWordU32sLe.lean
Manual review:    Proof fully rewritten for word-
                  addressed memory. Output state
                  has 2-level if/then/else (one per
                  word address) instead of the
                  previous 8-level version. Uses
                  stepMemStorewLe step lemma. No
                  sorry, no axiom.
Contrarian result: SOUND -- Lean type-checked.

---

## Bad

### Stack depth not enforced per-instruction
Evidence: State.lean:38, Semantics.lean:169-172
Problem:  Individual instruction handlers operate
          on unbounded `List Felt`. The bounded
          stack infrastructure (wellFormed,
          padStack at State.lean:117-124) provides
          Prop-level constraints but does not
          prevent creating states with fewer than
          16 elements. Operations on short stacks
          return `none` in Lean where Rust would
          auto-pad zeros. For example, `dup.15` on
          a 10-element stack fails in Lean but
          succeeds in Rust (accessing a zero-padded
          element). This is an intentional modeling
          simplification documented in the spec
          (section 6, AC-5).

Affected locations:
- `State.lean:38` -- `MidenState.stack`:
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
advLoadW reversal fixed at Semantics.lean:962-970.
U32 precondition guards added to all 34
operations. Emit now records events. Memory model
refactored to word-addressed.)

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
| Tests/Semantics.lean:825-858 | Good | memory ops | Store/load round-trip |
| Tests/Semantics.lean:1199-1280 | Good | word memory ops | StorewLe/Be round-trips |
| Tests/CrossValidation.lean | Good | Cross-validation | Lean model vs Rust vectors |

---

## Coverage

Modules: 3/3 analyzed

| Module | Manual Review | Contrarian | Passes | Status |
|--------|---------------|------------|--------|--------|
| core-semantics | Yes | Yes | 6 | Reviewed |
| generated-procs | Yes | Yes | 6 | Reviewed |
| proofs | Yes | Yes | 6 | Reviewed |

Uncovered: None. All 99 source files reviewed.
Generated scaffolding (42 files in
Proofs/Generated/) contains sorry by design and
is not imported into the build.

---

## Spec Divergence Check

Comparing .galvanize/spec.md against
implementation:

1. AC-14 (advLoadW reversal): FIXED. Code at
   line 962-970 uses `vals ++ rest` (no reverse).
   Regression test present.
2. AC-7/8/9/11 (u32 preconditions): FIXED. All
   u32 ops now check isU32. Regression tests
   present.
3. AC-5 (stack depth): Documented divergence.
   Bounded infrastructure added (wellFormed,
   padStack) but not enforced per-instruction.
4. AC-13 (memory model): RESOLVED. Memory is now
   word-addressed (`Nat -> Word`), matching Rust's
   `BTreeMap<u32, [Felt; 4]>`. The spec text
   describing this as "element-addressed" is now
   stale. Be/Le variants remain for element
   ordering within words; Le matches Rust's native
   ordering and is used by generated code.
5. AC-12 (emit): FIXED. execEmit now reads top
   element as event ID and records it. emitImm
   records immediate argument.

Minor spec documentation issue: spec section 7
describes assert as "top != 0 -> success" but
both Lean and Rust require exactly top == 1.
This is a spec text inaccuracy, not a code bug.

**NEW divergence (spec stale):** The spec at
lines 155-156 and 236-240 describes the memory
model as "element-addressed (Nat -> Felt)" with
Be/Le variants compensating. The implementation
now uses word-addressed memory (`Nat -> Word`).
The spec should be updated to reflect this change.

---

## Methodology

Findings were identified through six passes of
manual code review guided by trailmark structural
analysis (1034 nodes, 11849 call edges, 831
functions). The .galvanize/spec.md was used as a
reference for expected behavior and known issues.

Run 12 focused specifically on the memory model
refactor from element-addressed (`Nat -> Felt`)
to word-addressed (`Nat -> Word`). Key areas
verified:
- State.lean: Word type, writeMemory,
  writeMemoryElem0, writeLocal, writeLocalElem0
- Semantics.lean: all 12 memory instruction
  handlers (memLoad/Store/LoadwLe/LoadwBe and
  their Imm variants, locLoad, locStore)
- StepLemmas.lean: stepMemStorewLe updated for
  word model
- Proofs/Word/StoreWordU32sLe.lean: proof
  rewritten for word-addressed output
- Tests/Semantics.lean: memory tests updated for
  word-addressed model
- Round-trip correctness verified for all
  store/load combinations (element and word level)
- Cross-variant behavior (StorewLe -> LoadwBe)
  verified as intentional reversal

All spec-documented bugs verified as fixed. Grep
for `axiom` and `sorry` confirmed zero instances
outside generated scaffolding.
