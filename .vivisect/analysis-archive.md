# Correctness Analysis: masm-lean

Date:  2026-03-19 (incremental update from 2026-03-18)
Scope: MidenLean/ (all .lean files excluding .lake/)
Tools: trailmark (summary), manual review, contrarian
       (validation)

## Data Types

### `MidenLean::Felt`
File:       MidenLean/Felt.lean:10
Definition: `abbrev Felt := ZMod GOLDILOCKS_PRIME`

Representation Invariants:
- Value is always in [0, GOLDILOCKS_PRIME) by
  construction (ZMod guarantees this).
- GOLDILOCKS_PRIME = 2^64 - 2^32 + 1 is proven prime
  via native_decide (line 13).

Assumptions:
- Mathlib's ZMod implementation is correct for this
  prime.
- `Fact (Nat.Prime GOLDILOCKS_PRIME)` instance is
  available globally.

Guarantees:
- All field arithmetic (add, sub, mul, inv) is modular
  arithmetic mod p.
- `Felt.isU32` returns true iff val < 2^32.
- `Felt.isBool` returns true iff val is 0 or 1.
- `Felt.lo32` and `Felt.hi32` decompose correctly.

---

### `MidenLean::MidenState`
File:       MidenLean/State.lean:6-14
Definition: `structure MidenState` with fields:
  stack, memory, locals, advice

Representation Invariants:
- stack: List Felt, unbounded (no min/max depth)
  [DIVERGENCE from Rust: Rust enforces min depth 16,
  max depth 2^16]
- memory: Nat -> Felt, 0-initialized, element-addressed
  [DIVERGENCE from Rust: Rust uses BTreeMap<u32,
  [Felt;4]>, word-addressed]
- locals: Nat -> Felt, 0-initialized
- advice: List Felt, consumed from front

Assumptions:
- Callers do not rely on stack depth enforcement.
  [UNCHECKED]
- Memory addresses are validated by instruction
  handlers (addr < 2^32).

Guarantees:
- `writeMemory` is a pure functional update.
- `withStack` replaces only the stack field.

---

## Functions

## Target: core-semantics

### `execAssert`
File:      MidenLean/Semantics.lean:110-113
Signature: `MidenState -> Option MidenState`

Assumptions:
- Stack has at least 1 element.

Invariants:
- Checks `a.val == 1`, not `a.val != 0`.

Guarantees:
- Returns `some` only when top == 1.
- Returns `none` for any other value including 0.
- Pops the top element on success.

Dependencies:
- None

Preliminary category: Good
  Matches Rust behavior (assert checks == 1).

---

### `execCdrop`
File:      MidenLean/Semantics.lean:257-263
Signature: `MidenState -> Option MidenState`

Assumptions:
- Stack has at least 3 elements.
- Top element (condition) must be boolean (0 or 1).

Invariants:
- Lines 260-261: condition 1 keeps b (second element),
  condition 0 keeps a (third element).

Guarantees:
- Returns `none` for non-binary condition.
- Pops 3, pushes 1.

Dependencies:
- None

Preliminary category: Good
  Clean boolean dispatch.

---

### `execAdvPush`
File:      MidenLean/Semantics.lean:892-897
Signature: `Nat -> MidenState -> Option MidenState`

Assumptions:
- Advice stack has at least n elements.

Invariants:
- Lines 895-897: takes n elements, REVERSES them,
  prepends to stack.

Guarantees:
- Elements from advice are reversed before pushing.
- Advice stack is shortened by n.

Dependencies:
- None

Preliminary category: Good
  Lines 895-897:
  ```lean
  let vals := s.advice.take n
  let adv' := s.advice.drop n
  some ((s.withAdvice adv').withStack
        (vals.reverse ++ s.stack))
  ```
  Rust's advpush also reverses (pops one at a time
  from FIFO advice onto LIFO stack), so reverse is
  correct here. The first advice element ends up
  deepest on stack.

---

### `execAdvLoadW`
File:      MidenLean/Semantics.lean:899-907
Signature: `MidenState -> Option MidenState`

Assumptions:
- Stack has at least 4 elements (replaced).
- Advice stack has at least 4 elements.

Invariants:
- Lines 904-906: takes 4, does NOT reverse, prepends
  to rest.

Guarantees:
- Replaces top 4 stack elements with 4 advice elements
  in original order.

Dependencies:
- None

Preliminary category: Good
  Was previously Broken (reversed elements). The spec
  (.galvanize/spec.md, section 6, AC-14) documents
  the fix. Current code at line 906 uses
  `vals ++ rest` (no reverse), matching Rust's
  op_advpopw which also does not reverse.

---

### `execMemStorewBe`
File:      MidenLean/Semantics.lean:780-791
Signature: `MidenState -> Option MidenState`

Assumptions:
- Stack has at least 5 elements (addr + 4 data).
- Address < 2^32 and aligned to 4.

Invariants:
- Lines 786-789: stores in reverse order:
  addr+0 <- e3, addr+1 <- e2, addr+2 <- e1,
  addr+3 <- e0

Guarantees:
- Big-endian word store: most significant element
  (e0) at highest address.
- Stack retains data elements, pops address.

Dependencies:
- MidenState.writeMemory

Preliminary category: Good
  Element-addressed memory model with Be/Le variants
  is an intentional simplification documented in spec.

---

### `execWithEnv`
File:      MidenLean/Semantics.lean:1049-1095
Signature: `ProcEnv -> Nat -> MidenState -> List Op
            -> Option MidenState`

Assumptions:
- Fuel > 0 for any execution.
- ProcEnv resolves procedure names correctly.
- [UNCHECKED] Fuel is sufficient for the program.

Invariants:
- foldlM processes ops sequentially.
- exec dispatches to handler, ifElse/repeat/whileTrue
  handle control flow.
- Control flow ops require boolean conditions (val 0
  or 1), else none.

Guarantees:
- Deterministic execution for given fuel.
- Returns none on insufficient fuel.

Dependencies:
- execInstruction: all instruction handlers
- ProcEnv: procedure resolution

Preliminary category: Good
  Clean recursive interpreter with fuel-bounded
  termination.

---

### `u32CountLeadingOnes`
File:      MidenLean/Semantics.lean:90-91
Signature: `Nat -> Nat`

Assumptions:
- Input is a valid u32 value (< 2^32).

Invariants:
- Line 91: `u32CountLeadingZeros (n ^^^ (u32Max - 1))`

Guarantees:
- Counts leading ones by XOR-inverting and counting
  leading zeros.

Dependencies:
- u32CountLeadingZeros

Preliminary category: Good
  Now uses XOR (`^^^`) consistent with
  `u32CountTrailingOnes`. Previously used arithmetic
  subtraction (`u32Max - 1 - n`), which was correct
  but inconsistent. Fixed in commit 545db0c.

---

### `execU32Not`
File:      MidenLean/Semantics.lean:603-608
Signature: `MidenState -> Option MidenState`

Assumptions:
- Stack top is a u32 value.

Invariants:
- Line 607: `u32Max - 1 - a.val`

Guarantees:
- Returns bitwise NOT of a u32 value.
- Checks isU32 precondition.

Dependencies:
- Felt.isU32

Preliminary category: Good
  `u32Max - 1 - a.val` = `0xFFFFFFFF - a.val` =
  bitwise NOT for u32. Correct.

---

## Target: generated-procs

### `Miden.Core.Math.U64.overflowing_add`
File:      MidenLean/Generated/U64.lean:16-22
Signature: `List Op` (5 instructions)

Assumptions:
- Stack: [b_lo, b_hi, a_lo, a_hi, ...rest]
- All 4 inputs are u32.

Guarantees:
- Produces [overflow, c_lo, c_hi, ...rest]
- Proved correct: u64_overflowing_add_correct

Dependencies:
- u32WidenAdd, u32WidenAdd3, movup, movdn

Preliminary category: Good
  Formally verified.

---

### `Miden.Core.Math.U64.gt`
File:      MidenLean/Generated/U64.lean:126-140
Signature: `List Op` (13 instructions)

Assumptions:
- Stack: [b_lo, b_hi, a_lo, a_hi, ...rest]
- All 4 inputs are u32.

Guarantees:
- Produces [result, ...rest] where result=1 iff a>b
  as u64.

Dependencies:
- u32OverflowSub, movup, swap, eqImm, and, or

Preliminary category: Good
  Used in u64.min proof; logic verified transitively.

---

### `Miden.Core.Word.gt`
File:      MidenLean/Generated/Word.lean:48-69
Signature: `List Op` (repeat-4 loop)

Assumptions:
- Stack: [b0,b1,b2,b3, a0,a1,a2,a3, ...rest]

Guarantees:
- Produces [result, ...rest] where result=1 iff
  a > b as 128-bit words (lexicographic, MSB first).
- Proved correct: word_gt_correct (no axioms).

Dependencies:
- arrange_words_adjacent_le, eq, lt, and, or, movup,
  movdn, swap, push

Preliminary category: Good
  Fully proved without axioms.

---

### `Miden.Core.Word.lt`
File:      MidenLean/Generated/Word.lean:76-97
Signature: `List Op` (repeat-4 loop)

Assumptions:
- Stack: [b0,b1,b2,b3, a0,a1,a2,a3, ...rest]

Guarantees:
- Produces [result, ...rest] where result=1 iff
  a < b as 128-bit words.
- Proved correct: word_lt_full_correct (theorem,
  no axioms). Previously was an axiom; now fully
  proved.

Dependencies:
- arrange_words_adjacent_le, eq, gt, and, or

Preliminary category: Good
  Fully proved without axioms.

---

## Target: proofs

### `word_gt_correct`
File:      MidenLean/Proofs/WordGt.lean:76-158
Signature: theorem

Assumptions:
- Stack is well-formed with 8+ elements.
- wordProcEnv resolves "arrange_words_adjacent_le".

Guarantees:
- word::gt computes lexicographic > on 4-limb words.
- Proof is complete (no axioms, no sorry).

Dependencies:
- one_gt_iteration_body, wordProcEnv,
  word_arrange_words_adjacent_le (implicit via exec)

Preliminary category: Good
  Full proof by induction over 4 loop iterations.

---

### `word_lt_full_correct` (theorem)
File:      MidenLean/Proofs/Word/Lt.lean
Signature: theorem

Assumptions:
- Stack is well-formed with 8+ elements.
- wordProcEnv resolves sub-procedures.

Guarantees:
- word::lt computes lexicographic < on 4-limb words.
- Proof is complete (no axioms, no sorry).

Dependencies:
- wordProcEnv, execWithEnv, lt_iteration lemma

Preliminary category: Good
  Full proof. Previously an axiom; now machine-
  checked.

---

### `word_lte_full_correct` (theorem)
File:      MidenLean/Proofs/Word/Lte.lean
Signature: theorem

Preliminary category: Good
  Derived from word_gt_correct by composing with
  not. Full theorem, no axioms.

---

### `word_gte_full_correct` (theorem)
File:      MidenLean/Proofs/Word/Gte.lean
Signature: theorem

Preliminary category: Good
  Derived from word_lt_full_correct by composing
  with not. Full theorem, no axioms.

---

## Cross-Function Analysis

### Issue 1: Three axioms RESOLVED
Functions: word_lt_full_correct, word_lte_full_correct,
           word_gte_full_correct
Type: Resolved (previously Broken Guarantee Chain)

Description:
All three axioms have been replaced with full proofs.
word_lt is proved via lt_iteration lemma (same
technique as word_gt). word_lte is derived from
word_gt + not. word_gte is derived from word_lt +
not. Zero axioms remain in the project.

Severity: N/A (resolved)

---

### Issue 2: Spec divergence on assert semantics
Functions: execAssert
Type: Implicit Protocol

Description:
The spec (.galvanize/spec.md section 7) says "assert:
top = 0 -> none (failure), top != 0 -> success". The
implementation checks `a.val == 1` (line 112), which
rejects any nonzero value that isn't exactly 1. This
MATCHES Rust (Miden's assert requires exactly 1), so
the code is correct but the spec is misleading.

Severity: Not a code bug. Spec wording issue only.

---

### Issue 3: Semantic proof layer (NEW)
Functions: toU64, toU128, toU64_eq_iff,
           toU64_lt_iff, toU128_lt_iff,
           u64_lt_condition_eq, toU64_and/or/xor,
           cross_product_mod_2_64,
           u64CountLeadingZeros/TrailingZeros/
           LeadingOnes/TrailingOnes
Type: New capability

Description:
Proofs/Interp.lean introduces interpretation functions
(toU64, toU128) that map limb pairs to mathematical
integers. Bridge lemmas connect low-level proof
results to high-level semantic statements. 16 proof
files now have _semantic or _toU64 corollary theorems
chaining original_correct + bridge_lemma.

The semantic layer does NOT introduce new axioms. All
bridge lemmas are proved from first principles using
omega, ZMod.val arithmetic, and Nat.testBit.

Quality: Good -- clean separation of concerns. The
interpretation layer is sound and the corollaries
are straightforward compositions.

---

### Issue 4: Cross-validation test suite (NEW)
Functions: Tests/CrossValidation.lean
Type: New capability

Description:
30+ cross-validation tests running MASM library
procedures through the Lean semantics model against
miden-vm Rust test vectors (u64_mod.rs). Tests cover:
wrapping_add, lt/lte/gt/gte, min/max, eq/neq/eqz,
divmod, clz/ctz/clo/cto, shl/shr.

Quality: Good -- independently validates the Lean
model against the Rust reference implementation.
Catches any semantic divergence between the two.

---

## Misuse Resistance Baseline

### Exported symbols audit

1. `execInstruction`: Safe -- pattern match dispatch,
   no unchecked assumptions on caller.
2. `execWithEnv`: Fuel parameter is caller's
   responsibility. Insufficient fuel silently returns
   none (same as execution failure). No way to
   distinguish "ran out of fuel" from "legitimate
   failure". This is a known modeling choice.
3. `MidenState.ofStack`: Creates state with
   unbounded stack. Caller who creates a 1-element
   stack and runs dup.15 gets none (safe failure).
4. `Felt.toU32`: Returns `a.val % 2^32`, does NOT
   check isU32. A caller who uses toU32 on a non-u32
   felt gets silently truncated result. However, this
   is clearly documented as "Assumes the felt is a
   valid u32."
