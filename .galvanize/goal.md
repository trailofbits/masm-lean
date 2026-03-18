# Galvanize Goal: miden-lean Semantics Comparison

**Date:** 2026-03-17
**Initial prompt:** Build an extensive test suite for the
semantics in miden-lean compared to miden-vm, and build a
document of meaningful differences in
miden-lean/COMPARISON.md. For any bugs in miden-lean you
find, generate a regression test and patch the issue.

## Clarified Goal

Systematically compare the Lean 4 executable semantics in
miden-lean (MidenLean/Semantics.lean, Felt.lean, State.lean,
Instruction.lean) against the Rust reference implementation in
miden-vm (processor/src/execution/operations/). Produce:

1. An executable Lean test suite exercising every modeled
   instruction against concrete input/output pairs derived
   from the Rust VM's behavior.
2. A COMPARISON.md documenting every meaningful semantic
   difference, including intentional modeling choices and
   unintentional bugs.
3. Regression tests and patches for any bugs discovered in
   the Lean model.

## Acceptance Criteria

### Tier 1: Core arithmetic and stack instructions
- [x] AC-1: Test suite file exists at
  MidenLean/Tests/Semantics.lean with #eval-based tests
- [x] AC-2: All field arithmetic instructions tested
  (add, sub, mul, div, neg, inv, pow2, incr) including
  edge cases (zero, max felt, overflow)
- [x] AC-3: All field comparison instructions tested
  (eq, neq, lt, lte, gt, gte, isOdd) including
  boundary values
- [x] AC-4: All field boolean instructions tested
  (and, or, xor, not) including non-binary error cases
- [x] AC-5: All stack manipulation instructions tested
  (drop, dropw, padw, dup, dupw, swap, swapw, swapdw,
  movup, movdn, movupw, movdnw, reversew)
- [x] AC-6: All conditional instructions tested
  (cswap, cswapw, cdrop, cdropw) including non-binary
  condition error cases

### Tier 2: U32 operations and precondition checking
- [x] AC-7: All u32 arithmetic instructions tested
  (u32WidenAdd, u32OverflowAdd, u32WrappingAdd,
  u32WidenAdd3, u32OverflowAdd3, u32WrappingAdd3,
  u32OverflowSub, u32WrappingSub, u32WidenMul,
  u32WrappingMul, u32WidenMadd, u32WrappingMadd,
  u32DivMod, u32Div, u32Mod)
- [x] AC-8: All u32 bitwise instructions tested
  (u32And, u32Or, u32Xor, u32Not, u32Shl, u32Shr,
  u32Rotl, u32Rotr, u32Popcnt, u32Clz, u32Ctz,
  u32Clo, u32Cto)
- [x] AC-9: All u32 comparison instructions tested
  (u32Lt, u32Lte, u32Gt, u32Gte, u32Min, u32Max)
- [x] AC-10: All u32 assertion/conversion instructions
  tested (u32Assert, u32Assert2, u32AssertW, u32Test,
  u32TestW, u32Cast, u32Split)
- [x] AC-11: Document and test u32 precondition
  enforcement differences (Rust checks isU32 on all u32
  ops; Lean model checks on some but not all)

### Tier 3: Memory, advice, control flow
- [x] AC-12: Memory load/store instructions tested
  (memLoad, memLoadImm, memStore, memStoreImm,
  memLoadwBe/Le, memStorewBe/Le) including alignment
  and out-of-bounds checks
- [x] AC-13: Document memory model differences
  (Lean's Be/Le variants vs Rust's single word ordering,
  Lean's Nat->Felt vs Rust's BTreeMap)
- [x] AC-14: Advice stack instructions tested
  (advPush, advLoadW) including insufficient-advice
  error cases
- [x] AC-15: Control flow tested (ifElse with true/false
  branches, repeat with various counts, whileTrue,
  exec with ProcEnv)
- [x] AC-16: Assertion instructions tested (assert,
  assertz, assertEq, assertEqw)

### Tier 4: Comparison document and bug fixes
- [x] AC-17: COMPARISON.md exists documenting all
  meaningful differences with categories:
  (a) intentional modeling simplifications,
  (b) missing features/instructions,
  (c) semantic bugs
- [x] AC-18: Each discovered bug has a regression test
  that fails before the fix and passes after
- [x] AC-19: Each discovered bug is patched
- [x] AC-20: lake build succeeds after all patches
- [x] AC-21: Test suite compiles and all tests pass

### Tier 5: Semantic interpretation layer
- [x] AC-22: Define toU64(lo, hi) and toU128(a0, a1, a2, a3)
  interpretation functions in a new file
  (e.g. Proofs/Interp.lean) that compose limbs into
  the natural number they represent:
  toU64 lo hi := hi.val * 2^32 + lo.val
  toU128 a0 a1 a2 a3 := a3.val * 2^96 + a2.val * 2^64
    + a1.val * 2^32 + a0.val
- [x] AC-23: Bridge lemma: per-limb BEq equality iff
  toU64 equality (given isU32 hypotheses)
- [x] AC-24: Bridge lemma: the u32OverflowingSub-based
  comparison pattern used by u64.lt/gt maps to
  Nat.lt on toU64 values (given isU32 hypotheses)
- [x] AC-25: Bridge lemma: the lexicographic 4-limb
  comparison pattern used by word.lt/gt maps to
  Nat.lt on toU128 values (given isU32 hypotheses
  on all limbs)

### Tier 6: Semantic u64 theorems
- [ ] AC-26: u64_lt_correct, u64_lte_correct,
  u64_gt_correct, u64_gte_correct each state result
  in terms of <, <=, >, >= on toU64
- [ ] AC-27: u64_eq_correct, u64_neq_correct,
  u64_eqz_correct each state result in terms of
  equality on toU64 (or toU64 == 0)
- [ ] AC-28: u64_wrapping_add_correct and
  u64_wrapping_sub_correct state output encodes
  (toU64 a +/- toU64 b) % 2^64
- [ ] AC-29: u64_overflowing_add_correct and
  u64_overflowing_sub_correct state output encodes
  sum/difference and carry/borrow in terms of toU64
- [ ] AC-30: u64_wrapping_mul_correct states output
  encodes (toU64 a * toU64 b) % 2^64
- [ ] AC-31: u64_widening_mul_correct states output
  limbs encode toU64 a * toU64 b as a 128-bit value
  (i.e. toU128 of the output = toU64 a * toU64 b)
- [ ] AC-32: u64_widening_add_correct states output
  in terms of toU64

### Tier 7: Semantic u64 bitwise and counting
- [ ] AC-33: u64_and_correct, u64_or_correct,
  u64_xor_correct state result in terms of
  bitwise ops on toU64
- [ ] AC-34: u64_clz_correct, u64_ctz_correct,
  u64_clo_correct, u64_cto_correct state result
  in terms of the corresponding counting function
  on the 64-bit value (not per-limb conditional)
- [ ] AC-35: u64_min_correct, u64_max_correct state
  result encodes min/max of toU64 values

### Tier 8: Semantic word theorems + axiom elimination
- [ ] AC-36: word_lt_correct, word_gt_correct,
  word_lte_correct, word_gte_correct each state
  result in terms of <, >, <=, >= on toU128
- [ ] AC-37: Eliminate axioms word_lt_full_correct,
  word_lte_full_correct, word_gte_full_correct
  (replace with proved theorems)

## Default Quality Requirements
- [x] No crash on any input within stated scope
- [x] Test suite covers happy-path and error cases
- [x] Reasonable performance (tests complete in <5 min)
- [ ] lake build succeeds with zero sorry after all
  changes
- [ ] No new axioms introduced

## Scope Boundaries
**In scope:**
- Comparing instruction-level semantics between Lean
  model and Rust VM implementation
- Testing the executable Lean semantics via #eval
- Documenting differences in COMPARISON.md
- Patching bugs in the Lean model
- State model comparison (stack, memory, advice)
- ~~Proving correctness theorems (only testing)~~
  [revised 2026-03-18] Strengthening correctness
  theorems to prove semantic properties against
  interpretation functions (toU64, toU128) rather
  than restating the implementation
- Eliminating axioms in word comparison proofs

**Out of scope:**
- Modifying miden-vm (Rust) code
- Adding new instructions to the Lean model
- Crypto operations (hperm, merkle, etc.) not modeled
- Performance optimization
- The masm-to-lean Rust translator
- Strengthening theorems that are already
  semantically meaningful (word_reverse, word_eqz,
  word_eq, word_testz, word_test_eq,
  u64_u32assert4 -- these operate on individual
  felts and their current statements are adequate)

## Revision History
- 2026-03-17: Initial clarification
- 2026-03-18: additive: Added Tiers 5-8 for semantic
  theorem strengthening. Goal: every _correct theorem
  should prove a property against interpretation
  functions (toU64, toU128) rather than restating the
  implementation in low-level operations. Also:
  eliminate the 3 word comparison axioms.
