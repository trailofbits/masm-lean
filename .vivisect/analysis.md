# Correctness Analysis: masm-lean

Date:  2026-03-18
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
- Line 91: `u32CountLeadingZeros (u32Max - 1 - n)`

Guarantees:
- Counts leading ones by inverting and counting
  leading zeros.

Dependencies:
- u32CountLeadingZeros

Preliminary category: Bad
  Lines 90-91:
  ```lean
  def u32CountLeadingOnes (n : Nat) : Nat :=
    u32CountLeadingZeros (u32Max - 1 - n)
  ```
  Uses `u32Max - 1 - n` (= 2^32 - 1 - n) as the
  bitwise NOT. This is correct for u32 NOT
  (XOR with 0xFFFFFFFF). However,
  `u32CountTrailingOnes` at line 94-95 uses XOR
  operator `^^^` instead:
  ```lean
  def u32CountTrailingOnes (n : Nat) : Nat :=
    u32CountTrailingZeros (n ^^^ (u32Max - 1))
  ```
  Both are equivalent for u32 values, but the
  inconsistency is a code smell.

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
- "Proved" via axiom word_lt_full_correct.

Dependencies:
- arrange_words_adjacent_le, eq, gt, and, or

Preliminary category: Bad
  Relies on unproved axiom. See finding below.

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

### `word_lt_full_correct` (AXIOM)
File:      MidenLean/Proofs/WordLt.lean:12-24
Signature: axiom

Assumptions:
- None (axiom has no proof obligations).

Guarantees:
- Claims word::lt computes lexicographic < on 4-limb
  words.
- NOT VERIFIED -- this is an axiom, not a theorem.

Dependencies:
- wordProcEnv, execWithEnv

Preliminary category: Bad
  Unproved axiom. word_gt_correct was fully proved,
  so lt should be provable by the same technique
  (the loop body uses .gt instead of .lt, with the
  comparison direction flipped). The axiom creates
  a soundness gap.

---

### `word_lte_full_correct` (AXIOM)
File:      MidenLean/Proofs/WordLte.lean:12-24
Signature: axiom

Preliminary category: Bad
  Depends on word_gt_correct (lte = !gt) but encoded
  as an axiom rather than derived. Should be provable
  from word_gt_correct + not.

---

### `word_gte_full_correct` (AXIOM)
File:      MidenLean/Proofs/WordGte.lean:12-24
Signature: axiom

Preliminary category: Bad
  Depends on word_lt which is itself an axiom.
  Double axiom chain: gte -> lt -> axiom.

---

## Cross-Function Analysis

### Issue 1: Three axioms create unverified proof chain
Functions: word_lt_full_correct, word_lte_full_correct,
           word_gte_full_correct
Type: Broken Guarantee Chain

Description:
word_gt_correct is fully proved. word_lt should be
symmetric but is axiomatized instead. word_lte depends
on word_gt (via !gt) but is also axiomatized instead
of being derived. word_gte depends on word_lt (via
!lt) and inherits the lt axiom gap.

The axiom chain means 3 of 4 word comparison theorems
are unverified. An error in the axiom statement (e.g.,
wrong comparison direction, wrong limb ordering) would
not be caught by the proof checker.

Severity: Bad (axioms are not demonstrably wrong, but
they are demonstrably unverified)

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
