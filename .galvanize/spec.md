# Galvanize Spec: miden-lean Semantics Comparison

**Date:** 2026-03-17
**Goal:** Build an executable test suite comparing miden-lean
(Lean 4) semantics against miden-vm (Rust), document all
differences in COMPARISON.md, and fix discovered bugs with
regression tests.

## 1. Purpose and Scope

Compare the Lean 4 executable semantics in miden-lean against
the Rust reference implementation in miden-vm at the
instruction level. The Lean model lives in
MidenLean/Semantics.lean (with supporting types in Felt.lean,
State.lean, Instruction.lean). The Rust reference is in
miden-vm's processor/src/execution/operations/.

Deliverables:
- An executable Lean test suite exercising every modeled
  instruction against concrete input/output pairs derived
  from the Rust VM's behavior.
- A COMPARISON.md documenting every meaningful semantic
  difference.
- Regression tests and patches for all bugs discovered.

Out of scope: modifying miden-vm, adding new instructions to
the Lean model, crypto operations (hperm, merkle, etc.),
proving correctness theorems, performance optimization, and
the masm-to-lean Rust translator.

## 2. Test Suite Structure

### File location

All tests go in a single file:
  MidenLean/Tests/Semantics.lean

This file must be added to the lakefile so `lake build`
compiles it.

### Organization

Tests are organized by instruction category, in this order:

1. Field arithmetic (add, sub, mul, div, neg, inv, pow2, incr)
2. Field comparison (eq, neq, lt, lte, gt, gte, isOdd)
3. Field boolean (and, or, xor, not)
4. Stack manipulation (drop, dropw, padw, dup, dupw, swap,
   swapw, swapdw, movup, movdn, movupw, movdnw, reversew)
5. Conditional ops (cswap, cswapw, cdrop, cdropw)
6. Assertions (assert, assertz, assertEq, assertEqw)
7. U32 assertion/conversion (u32Assert, u32Assert2,
   u32AssertW, u32Test, u32TestW, u32Cast, u32Split)
8. U32 arithmetic (u32WidenAdd, u32OverflowAdd,
   u32WrappingAdd, u32WidenAdd3, u32OverflowAdd3,
   u32WrappingAdd3, u32OverflowSub, u32WrappingSub,
   u32WidenMul, u32WrappingMul, u32WidenMadd,
   u32WrappingMadd, u32DivMod, u32Div, u32Mod)
9. U32 bitwise (u32And, u32Or, u32Xor, u32Not, u32Shl,
   u32Shr, u32Rotl, u32Rotr, u32Popcnt, u32Clz, u32Ctz,
   u32Clo, u32Cto)
10. U32 comparison (u32Lt, u32Lte, u32Gt, u32Gte, u32Min,
    u32Max)
11. Memory (memLoad, memLoadImm, memStore, memStoreImm,
    memLoadwBe, memLoadwLe, memStorewBe, memStorewLe)
12. Advice (advPush, advLoadW)
13. Control flow (ifElse, repeat, whileTrue, exec)

Each section is preceded by a comment block naming the
category. Within each section, tests are ordered: happy-path
first, then edge cases, then error/rejection cases.

### Test format

Each test is a #eval block that constructs a MidenState,
runs an instruction via execInstruction (or execWithEnv for
control flow), and checks the result using decidable
equality. The pattern is:

```lean
#eval do
  let state := MidenState.mk [a, b, c, ...] mem advice
  let result := execInstruction .someInstr state
  guard (result == some expectedState)
```

For error cases (instruction should return none):

```lean
#eval do
  let state := MidenState.mk [a, b] mem advice
  let result := execInstruction .someInstr state
  guard (result == none)
```

Each #eval block must print nothing on success and fail
(or print an error message) on failure. This way `lake
build` succeeding implies all tests pass.

## 3. Test Methodology

For each instruction:

(a) Create a MidenState with specific stack contents,
    memory state, and advice stack as needed.
(b) Run the instruction via execInstruction (or
    execWithEnv for control flow instructions that need
    a ProcEnv).
(c) Check that the result matches the expected output.
    Expected outputs are derived from the Rust VM's
    behavior, either by running the Rust VM or by manual
    computation from the Rust source.
(d) Test both happy-path (valid inputs, normal operation)
    and error/edge cases (invalid inputs that should
    produce none, boundary values).

When deriving expected values from Rust, document the
source (e.g., "Rust's op_add wraps mod p where
p = 2^64 - 2^32 + 1") in a comment above the test.

## 4. Bug Fix Procedure

For each bug found during comparison:

(a) Write a regression test that demonstrates the wrong
    behavior. The test must fail (i.e., the #eval guard
    fails) with the current code. Place this test in the
    appropriate category section of the test file.
(b) Fix the code in the relevant source file.
(c) Verify the regression test now passes and `lake build`
    succeeds with no errors.

Each fix is a separate commit (or at minimum a separately
identifiable change). Regression tests remain in the test
suite permanently -- they are not removed after the fix.

## 5. COMPARISON.md Structure

Create COMPARISON.md in the repository root with these
sections:

### (a) Intentional Modeling Simplifications

Document design choices where the Lean model intentionally
diverges from Rust for tractability or proof convenience.
Each entry states:
- What the Lean model does
- What the Rust VM does
- Why the simplification is acceptable

Known items to document:
- Stack model: unbounded List Felt vs Rust's 16-element
  minimum depth with zero padding and 2^16 max depth.
- Memory model: element-addressed (Nat -> Felt) vs Rust's
  word-addressed (BTreeMap<u32, [Felt; 4]>), with Be/Le
  variants compensating.
- Emit: modeled as stack no-op without reading event ID.
- Error codes: String vs Felt (functionally equivalent for
  semantic correctness).
- Assembled ops: some Lean primitives (cdrop, cdropw, neq,
  dup8-14, movup9-15) correspond to multi-instruction
  sequences in Rust.

### (b) Missing Features/Instructions

List instructions or features present in Rust but not
modeled in Lean. Currently known: crypto operations (hperm,
merkle tree ops, etc.).

### (c) Semantic Bugs (Found and Fixed)

For each bug, document:
- The instruction(s) affected
- What the Lean model did wrong
- What the Rust VM does
- The fix applied
- Reference to the regression test

## 6. Known Issues to Address

These findings from the vivisect must be resolved:

### Broken: advLoadW element ordering is reversed
(AC-14, priority: HIGH)

The execAdvLoadW function reverses the 4 advice elements
before placing them on the stack. Rust's op_advpopw does
not reverse. With advice [a, b, c, d]:
  Lean:  [d, c, b, a, ...rest...]
  Rust:  [a, b, c, d, ...rest...]

Fix: change `vals.reverse ++ rest` to `vals ++ rest` in
MidenLean/Semantics.lean around line 849.

Regression test: construct advice [1, 2, 3, 4], run
advLoadW, verify stack top is [1, 2, 3, 4] not
[4, 3, 2, 1].

### Broken: 28+ u32 ops lack isU32 precondition checks
(AC-7, AC-8, AC-9, AC-11, priority: HIGH)

Every Rust u32 VM operation rejects inputs >= 2^32. The
Lean model omits this check on all u32 arithmetic,
comparison, shift, rotate, and count operations (only
u32And/Or/Xor/Not check isU32).

Fix: add `if !a.isU32 then none else ...` (single-operand)
or `if !a.isU32 || !b.isU32 then none else ...`
(two-operand) guards to each affected handler. The full
list of 34 affected operations is in findings.md.

Regression tests: for each affected operation, include at
least one test with a non-u32 input (e.g., 2^32 or
2^63) and verify the result is none.

Note: adding precondition checks may break existing proofs
that relied on the weaker (unchecked) semantics. After
adding checks, run `lake build` and fix any proof
breakage. If fixing proofs is infeasible for some
operations, document the gap in COMPARISON.md instead
and skip the fix for those operations, but still write
the tests demonstrating the discrepancy.

### Bad: No stack depth enforcement
(AC-5, AC-11, priority: LOW -- document only)

The Lean model uses unbounded List Felt with no minimum
depth of 16 and no maximum of 2^16. This is an intentional
modeling simplification. Document in COMPARISON.md section
(a). Write tests demonstrating that operations work on
small stacks where Rust would pad.

### Bad: Memory model is element-addressed
(AC-13, priority: LOW -- document only)

Lean uses Nat -> Felt; Rust uses BTreeMap<u32, [Felt; 4]>.
Document in COMPARISON.md section (a). Include tests for
both Be and Le word load/store to document which variant
corresponds to Rust's ordering. Note in COMPARISON.md
which variant (if either) matches Rust's element ordering
within words.

### Bad: Emit does not read top element
(AC-12, priority: LOW -- document only)

Lean's execEmit checks stack non-empty but does not read
the top value. Document in COMPARISON.md section (a).

## 7. Edge Cases to Test per Instruction Category

### Field arithmetic
- Zero: add(0, x) = x, mul(0, x) = 0, div(x, 0) = none
- One: mul(1, x) = x, pow2(0) = 1
- Max felt: add(p-1, 1) = 0 (overflow wraps), sub(0, 1)
  = p-1 (underflow wraps)
- Inv: inv(0) = none, inv(1) = 1, inv(x) * x = 1
- Pow2: pow2(63) = 2^63, pow2(64) = none (exponent bound)
- Incr: incr(p-1) = 0

### U32 operations
- Zero: u32WrappingAdd(0, 0) = 0
- One: various ops with 1
- u32_max (2^32 - 1): u32WrappingAdd(u32_max, 1) = 0,
  u32Not(0) = u32_max
- Non-u32 inputs: any value >= 2^32 should produce none
  (after the precondition fix). Test with 2^32 and with
  a large felt like 2^63.
- Division by zero: u32DivMod(x, 0) = none
- Shift/rotate by 0 and by 31
- Bit counting: popcnt(0) = 0, popcnt(u32_max) = 32,
  clz(1) = 31, ctz(2^31) = 31

### Stack manipulation
- Minimum depth: dup.0 on a 1-element stack should work;
  dup.15 on a 15-element stack should fail (none)
- Various positions: movup/movdn with positions 2..8,
  swapw with all four word positions
- dropw on a stack with exactly 4 elements

### Memory
- Aligned word access: addr divisible by 4
- Unaligned word access: addr not divisible by 4 should
  produce none
- Address boundary: addr = 2^32 - 1 (max valid for single
  element), addr = 2^32 should fail
- Store then load: write a value, read it back, verify
  match

### Advice stack
- Empty advice: advPush(n) with empty advice -> none
- Insufficient elements: advPush(3) with 2 elements -> none
- advLoadW with fewer than 4 elements -> none
- Correct ordering after fix: advLoadW with [1,2,3,4]
  produces stack [1,2,3,4,...] not [4,3,2,1,...]

### Control flow
- ifElse: condition = 1 takes true branch, condition = 0
  takes false branch
- ifElse: non-binary condition (e.g., 2) -> none
- repeat: 0 iterations (body never executes), 1 iteration,
  multiple iterations
- whileTrue: condition false on first check (body never
  executes), condition true then false (one iteration)
- exec: procedure exists in ProcEnv, procedure does not
  exist -> none

### Assertions
- assert: top = 0 -> none (failure), top != 0 -> success
- assertz: top = 0 -> success, top != 0 -> none
- assertEq: equal values -> success, unequal -> none
- assertEqw: all four pairs equal -> success, one pair
  differs -> none

## 8. Acceptance Criteria Traceability

| AC   | Spec section(s)          | Notes                  |
|------|--------------------------|------------------------|
| AC-1 | 2 (file location)        |                        |
| AC-2 | 2, 3, 7 (field arith)    |                        |
| AC-3 | 2, 3, 7 (field cmp)      |                        |
| AC-4 | 2, 3, 7 (field bool)     |                        |
| AC-5 | 2, 3, 7 (stack manip)    |                        |
| AC-6 | 2, 3, 7 (conditional)    |                        |
| AC-7 | 2, 3, 6, 7 (u32 arith)   | Precondition fix       |
| AC-8 | 2, 3, 6, 7 (u32 bitwise) | Precondition fix       |
| AC-9 | 2, 3, 7 (u32 cmp)        | Precondition fix       |
| AC-10| 2, 3, 7 (u32 conv)       |                        |
| AC-11| 6 (precondition gaps)    | Fix + document         |
| AC-12| 2, 3, 6, 7 (memory)     |                        |
| AC-13| 5, 6 (memory model)      | Document in COMPARISON |
| AC-14| 2, 3, 6, 7 (advice)     | advLoadW fix           |
| AC-15| 2, 3, 7 (control flow)   |                        |
| AC-16| 2, 3, 7 (assertions)     |                        |
| AC-17| 5 (COMPARISON.md)        |                        |
| AC-18| 4 (regression tests)     |                        |
| AC-19| 4, 6 (bug patches)       |                        |
| AC-20| 4 (lake build)           |                        |
| AC-21| 2 (test compilation)     |                        |

## 9. Execution Order

1. Write the test file scaffold with sections and imports.
2. Implement tests for Tier 1 (AC-1 through AC-6):
   field arithmetic, comparison, boolean, stack, conditional.
   Verify `lake build` passes.
3. Fix advLoadW (Broken finding). Write regression test
   first, then apply fix, then verify.
4. Implement Tier 2 tests (AC-7 through AC-11): u32 ops.
   For each u32 operation, include a non-u32 rejection
   test.
5. Add isU32 precondition guards (Broken finding). Apply
   guards to all 34 affected operations. After each batch,
   run `lake build` and fix any proof breakage.
6. Implement Tier 3 tests (AC-12 through AC-16): memory,
   advice, control flow, assertions.
7. Create COMPARISON.md (AC-17) documenting all findings.
8. Final `lake build` to confirm everything compiles
   (AC-20, AC-21).
