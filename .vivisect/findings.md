# Vivisect Findings: masm-lean

Date:  2026-03-19 (run 14)
Scope: MidenLean/ (99 .lean files, ~22000 lines)
Tools: trailmark (summary), manual review,
       contrarian (validation)

## Executive Summary

masm-lean is a Lean 4 formal semantics for the Miden
VM instruction set, with machine-checked correctness
proofs for generated u64 and word procedures. The core
semantics engine (Semantics.lean, 1185 lines)
implements each instruction handler as a pure function
from MidenState to Option MidenState. The codebase has
zero sorry, zero axiom outside Mathlib dependencies,
and builds cleanly (0 errors, 0 warnings).

The memory model uses word-addressed storage
(`Nat -> Word`) matching the Rust VM's
`BTreeMap<u32, [Felt; 4]>`. All previously-reported
bugs remain fixed: advLoadW element reversal, 34 u32
ops with isU32 guards, emit/emitImm event recording,
and 3 word comparison axioms replaced with full proofs.

Per-instruction stack depth enforcement is now
complete (AC-50 through AC-53). All 11 handlers with
net positive stack effect have MAX_STACK_DEPTH
overflow guards. Step lemmas carry hov hypotheses.
All 20 proof files carry hlen hypotheses ensuring
sufficient headroom for intermediate stack growth.
Edge case tests verify guard behavior at
Tests/Semantics.lean:1413-1479.

| Category | Findings | Instances |
|----------|----------|-----------|
| Good     | 18       | --        |
| Bad      | 0        | 0         |
| Broken   | 0        | 0         |
| Absurd   | 0        | 0         |

Coverage: 3/3 targets manually reviewed,
99/99 files reviewed, 7 review passes completed

Biggest risk: No critical risks. All previously
identified issues have been resolved with regression
tests and machine-checked proofs.

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
Evidence:         Semantics.lean:1000-1118,
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
Evidence:         Semantics.lean:974-982
Manual review:    Previously reversed 4 elements
                  (spec AC-14). Now uses
                  `vals ++ rest` without reverse.
                  Regression test at
                  Tests/Semantics.lean:786-790.
Contrarian result: SOUND -- test confirms order.

---

### advPush reversal semantics
Evidence:         Semantics.lean:962-968
Manual review:    advPush pops N elements from
                  advice stack one at a time
                  (FIFO onto LIFO), so the result
                  is correctly reversed. The
                  `vals.reverse` matches Rust's
                  N consecutive ADVPOP operations.
Contrarian result: SOUND -- matches Rust VM.

---

### Word-addressed memory model
Evidence:         State.lean:6-9,32,43,65-96
Manual review:    Memory is now `Nat -> Word`
                  matching Rust's `BTreeMap<u32,
                  [Felt; 4]>`. Each address maps
                  to a 4-element tuple.
                  `writeMemory` writes full word.
                  `writeMemoryElem0` writes only
                  element 0, preserving 1-3.
                  Default is `Word.zero = (0,0,0,0)`.
Contrarian result: SOUND -- memory model now
                  matches Rust VM structure.

---

### memLoad/memStore single-element access
Evidence:         Semantics.lean:818-836
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
Evidence:         Semantics.lean:867-927
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
Evidence:         Semantics.lean:1129-1174
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
Evidence:         Semantics.lean:989-993,
                  1116-1117; State.lean:50
Manual review:    execEmit reads top stack element
                  as eventId, records in s.events.
                  emitImm records the immediate
                  argument. Previously was a no-op
                  (spec AC-12). Now functional.
Contrarian result: SOUND -- events field correctly
                  threaded through state.

---

### StoreWordU32sLe proof (word-addressed)
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

### Per-instruction stack depth enforcement
Evidence:         Semantics.lean:158,162,166,173,
                  179,465,471,486,828,935,964;
                  State.lean:110-133;
                  StepLemmas.lean:22,291,337,391,451;
                  Tests/Semantics.lean:1413-1479
Manual review:    All 11 handlers with net positive
                  stack effect have MAX_STACK_DEPTH
                  overflow guards. 5 step lemmas
                  carry hov hypotheses. 20 proof
                  files carry hlen hypotheses
                  (67 references). 8 edge case tests
                  verify boundary behavior (full
                  stack -> none, room -> some).
                  Underflow handled by pattern
                  matching on required elements.
                  wellFormed predicate available for
                  proof hypotheses.
Contrarian result: SOUND -- guards verified in code,
                  tests verified via Lean LSP
                  (0 errors, 0 warnings).

---

### Bounded stack infrastructure
Evidence:         State.lean:108-133
Manual review:    MIN_STACK_DEPTH (16),
                  MAX_STACK_DEPTH (2^16),
                  padStack, wellFormed, and
                  ofStackPadded provide vocabulary
                  for proofs. padStack appends
                  zeros to reach minimum depth.
                  Now actively used: overflow guards
                  reference MAX_STACK_DEPTH; proofs
                  carry wellFormed-derived hlen
                  hypotheses.
Contrarian result: SOUND -- definitions correct,
                  now integrated into handlers
                  and proofs.

---

## Bad

(No Bad findings. The previously-reported "stack
depth not enforced per-instruction" has been resolved
by AC-50 through AC-53. Overflow guards added to all
11 net-positive-stack handlers. Underflow handled by
pattern matching. wellFormed carried as hypothesis.)

---

## Broken

(No Broken findings. All previously-reported bugs
have been fixed with regression tests. advLoadW
reversal fixed at Semantics.lean:974-982. U32
precondition guards added to all 34 operations.
Emit now records events. Memory model refactored
to word-addressed.)

---

## Absurd

(No Absurd findings. The three unproved axioms
previously identified as concerns have been replaced
with full machine-checked proofs. The codebase has
zero sorry, zero axiom outside Mathlib dependencies.)

---

## Test Coverage

| Test | Category | Finding | Purpose |
|------|----------|---------|---------|
| Tests/Semantics.lean:786-790 | Good | advLoadW fixed | Regression: element order |
| Tests/Semantics.lean:519-573 | Good | u32 preconditions | Regression: non-u32 rejection |
| Tests/Semantics.lean:825-858 | Good | memory ops | Store/load round-trip |
| Tests/Semantics.lean:1199-1280 | Good | word memory ops | StorewLe/Be round-trips |
| Tests/Semantics.lean:1418-1423 | Good | stack overflow | push on full stack -> none |
| Tests/Semantics.lean:1426-1431 | Good | stack overflow | push with room -> some |
| Tests/Semantics.lean:1434-1439 | Good | stack overflow | dup on full stack -> none |
| Tests/Semantics.lean:1442-1447 | Good | stack overflow | padw near-full -> none |
| Tests/Semantics.lean:1450-1455 | Good | stack overflow | padw exact fit -> some |
| Tests/Semantics.lean:1458-1463 | Good | stack overflow | advPush full -> none |
| Tests/Semantics.lean:1466-1471 | Good | stack overflow | u32Split full -> none |
| Tests/Semantics.lean:1474-1478 | Good | stack underflow | drop empty -> none |
| Tests/CrossValidation.lean | Good | Cross-validation | Lean model vs Rust vectors |

---

## Coverage

Modules: 3/3 analyzed

| Module | Manual Review | Contrarian | Passes | Status |
|--------|---------------|------------|--------|--------|
| core-semantics | Yes | Yes | 7 | Reviewed |
| generated-procs | Yes | Yes | 7 | Reviewed |
| proofs | Yes | Yes | 7 | Reviewed |

Uncovered: None. All 99 source files reviewed.
Generated scaffolding (42 files in Proofs/Generated/)
contains sorry by design and is not imported into
the build.

---

## Spec Divergence Check

Comparing .galvanize/spec.md against implementation:

1. AC-14 (advLoadW reversal): FIXED. Code at
   line 974-982 uses `vals ++ rest` (no reverse).
   Regression test present.
2. AC-7/8/9/11 (u32 preconditions): FIXED. All
   u32 ops now check isU32. Regression tests
   present.
3. AC-5/50-53 (stack depth): RESOLVED. Overflow
   guards on all 11 net-positive-stack handlers.
   Underflow via pattern matching. wellFormed
   in proofs. Edge case tests present.
4. AC-13 (memory model): RESOLVED. Memory is now
   word-addressed (`Nat -> Word`), matching Rust's
   `BTreeMap<u32, [Felt; 4]>`.
5. AC-12 (emit): FIXED. execEmit now reads top
   element as event ID and records it. emitImm
   records immediate argument.

Spec text staleness: spec.md lines 155-156 and
236-240 describe the memory model as
"element-addressed (Nat -> Felt)". The
implementation now uses word-addressed memory
(`Nat -> Word`). The spec should be updated.

Minor spec text inaccuracy: spec section 7
describes assert as "top != 0 -> success" but
both Lean and Rust require exactly top == 1.

---

## Methodology

Findings were identified through seven passes of
manual code review guided by trailmark structural
analysis (1033 nodes, 11858 call edges, 830
functions). The .galvanize/spec.md was used as a
reference for expected behavior and known issues.

Run 14 is a verification pass after AC-50 through
AC-53 (per-instruction stack depth enforcement)
were implemented. Changes verified:
- 11 overflow guards in Semantics.lean
- 5 step lemmas with hov hypotheses
- 20 proof files with hlen hypotheses (67 refs)
- 8 edge case tests in Tests/Semantics.lean
- Lean LSP: 0 errors, 0 warnings on all key files

The previous Bad finding "stack depth not enforced
per-instruction" is now resolved to Good. All
other findings from run 13 remain stable.
