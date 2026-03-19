# masm-lean Setup Output

## File Inventory

33 Lean source files, 3768 total lines (excluding .lake/).

### Core semantics (4 files, 1294 lines)
| File                         | Lines | Role                              |
|------------------------------|------:|-----------------------------------|
| MidenLean/Felt.lean          |    39 | Field element type (ZMod p)       |
| MidenLean/State.lean         |    43 | VM state: stack, memory, locals   |
| MidenLean/Instruction.lean   |   170 | Instruction ADT (all opcodes)     |
| MidenLean/Semantics.lean     |  1048 | Exec handlers + dispatch          |

### Control flow (1 file, 33 lines)
| File                         | Lines | Role                              |
|------------------------------|------:|-----------------------------------|
| MidenLean/Op.lean            |    33 | Op ADT: inst, ifElse, repeat, ... |

### Generated procedures (2 files, 612 lines)
| File                            | Lines | Role                           |
|---------------------------------|------:|--------------------------------|
| MidenLean/Generated/U64.lean    |   458 | u64 library (MASM -> Lean)     |
| MidenLean/Generated/Word.lean   |   154 | word library (MASM -> Lean)    |

### Proof infrastructure (3 files, 449 lines)
| File                              | Lines | Role                         |
|-----------------------------------|------:|------------------------------|
| MidenLean/Proofs/Helpers.lean     |   114 | simp lemmas, felt lemmas     |
| MidenLean/Proofs/StepLemmas.lean  |   257 | Per-instruction step thms    |
| MidenLean/Proofs/Tactics.lean     |    78 | Custom tactics (miden_step)  |

### Correctness proofs (20 files, 1314 lines)
| File                                        | Lines |
|---------------------------------------------|------:|
| MidenLean/Proofs/U64.lean                   |   133 |
| MidenLean/Proofs/U64And.lean                |    42 |
| MidenLean/Proofs/U64Clo.lean                |    71 |
| MidenLean/Proofs/U64Clz.lean                |    72 |
| MidenLean/Proofs/U64Cto.lean                |    69 |
| MidenLean/Proofs/U64Ctz.lean                |    67 |
| MidenLean/Proofs/U64Eq.lean                 |    39 |
| MidenLean/Proofs/U64Gt.lean                 |    62 |
| MidenLean/Proofs/U64Gte.lean                |    55 |
| MidenLean/Proofs/U64Lt.lean                 |    61 |
| MidenLean/Proofs/U64Lte.lean                |    55 |
| MidenLean/Proofs/U64Neq.lean                |    39 |
| MidenLean/Proofs/U64Or.lean                 |    42 |
| MidenLean/Proofs/U64OverflowingSub.lean     |    74 |
| MidenLean/Proofs/U64Sub.lean                |    58 |
| MidenLean/Proofs/U64U32Assert4.lean         |    41 |
| MidenLean/Proofs/U64WideningAdd.lean        |    61 |
| MidenLean/Proofs/U64WrappingMul.lean        |    71 |
| MidenLean/Proofs/U64Xor.lean                |    42 |
| MidenLean/Proofs/Word.lean                  |    96 |
| MidenLean/Proofs/WordTestz.lean             |    82 |

### Other
| File              | Lines | Role                               |
|-------------------|------:|------------------------------------|
| MidenLean.lean    |    31 | Root import (all modules)          |
| lakefile.lean     |    11 | Build config (Mathlib v4.28.0)     |


## Module Dependency Graph

```
lakefile.lean
  |
  v
MidenLean.lean  (root import, imports everything)
  |
  +---> Felt.lean           (Mathlib.Data.ZMod.Basic)
  |       |
  |       v
  +---> State.lean          (depends on Felt)
  |       |
  |       v
  +---> Instruction.lean    (depends on Felt)
  |       |
  |       v
  +---> Op.lean             (depends on Instruction)
  |       |
  |       v
  +---> Semantics.lean      (depends on State, Op)
  |       |
  |       v
  +---> Generated/U64.lean  (depends on Semantics)
  +---> Generated/Word.lean (depends on Semantics)
  |       |
  |       v
  +---> Proofs/Helpers.lean     (depends on Semantics)
  +---> Proofs/StepLemmas.lean  (depends on Helpers)
  +---> Proofs/Tactics.lean     (depends on StepLemmas)
  +---> Proofs/Word.lean        (depends on Helpers, Generated/Word)
  +---> Proofs/WordTestz.lean
  +---> Proofs/U64*.lean        (depend on Tactics, Generated/U64)
```


## Acceptance Criteria (from goal.md)

### Tier 1: Core arithmetic and stack
- AC-1: Test suite at MidenLean/Tests/Semantics.lean
- AC-2: Field arithmetic (add, sub, mul, div, neg, inv, pow2, incr)
- AC-3: Field comparison (eq, neq, lt, lte, gt, gte, isOdd)
- AC-4: Field boolean (and, or, xor, not) + non-binary error
- AC-5: Stack manipulation (drop/w, padw, dup/w, swap/w/dw,
         movup/dn/w, reversew)
- AC-6: Conditional (cswap/w, cdrop/w) + non-binary error

### Tier 2: U32 operations
- AC-7:  U32 arithmetic (all add/sub/mul/div variants)
- AC-8:  U32 bitwise (and/or/xor/not/shl/shr/rotl/rotr/
          popcnt/clz/ctz/clo/cto)
- AC-9:  U32 comparison (lt/lte/gt/gte/min/max)
- AC-10: U32 assertion/conversion (assert/2/W, test/W,
          cast, split)
- AC-11: U32 precondition enforcement differences

### Tier 3: Memory, advice, control flow
- AC-12: Memory load/store instructions
- AC-13: Memory model differences documentation
- AC-14: Advice stack instructions
- AC-15: Control flow (ifElse, repeat, whileTrue, exec)
- AC-16: Assertion instructions

### Tier 4: Comparison document and bug fixes
- AC-17: COMPARISON.md with categorized differences
- AC-18: Regression tests for each bug
- AC-19: Patches for each bug
- AC-20: `lake build` succeeds after patches
- AC-21: Test suite compiles and passes


## Key Entry Points

1. `execInstruction : MidenState -> Instruction -> Option MidenState`
   Single instruction dispatch. Maps each Instruction variant
   to its handler (execAdd, execDrop, etc.). Returns none on
   error (precondition violation, empty stack, etc.).

2. `execWithEnv : ProcEnv -> Nat -> MidenState -> List Op
                  -> Option MidenState`
   Executes a list of Ops with a procedure environment and
   fuel counter. Handles ifElse, repeat, whileTrue, and
   procedure calls (exec target). The fuel parameter bounds
   recursion for termination.

3. `exec : Nat -> MidenState -> List Op -> Option MidenState`
   Convenience wrapper: execWithEnv with empty ProcEnv.

4. `execWithProcs : List Procedure -> Nat -> MidenState
                    -> List Op -> Option MidenState`
   Convenience wrapper: builds ProcEnv from a procedure list.


## Key Observations

### Architecture
- The Lean model is a direct executable semantics: each
  instruction is a function MidenState -> Option MidenState.
  None represents an error (failed assertion, insufficient
  stack depth, division by zero, etc.).
- The field element type is ZMod GOLDILOCKS_PRIME from Mathlib,
  giving access to the full algebraic structure for proofs.
- Memory is modeled as (Nat -> Felt), a total function with
  default value 0. This differs from Rust's BTreeMap<u32, Word>
  which is sparse and word-addressed.
- Stack is an unbounded List Felt (no 16-element depth limit
  as in the real VM).
- Generated/ files are MASM procedures translated to Lean
  Op lists by a Rust tool. These define u64 and word library
  operations as sequences of primitive instructions.

### Proof Structure
- Proofs show that generated MASM procedures compute the
  expected mathematical function. E.g., u64_and_correct shows
  the u64.and procedure computes bitwise AND on the lo/hi
  limbs.
- Custom tactics (miden_step, miden_bind, miden_swap, etc.)
  automate stepping through instruction sequences.
- All proofs assume concrete stack layouts (destructured via
  pattern matching on s.stack).

### Issues and Differences Spotted

#### 1. Missing u32 precondition checks on many operations
The Rust VM enforces that inputs to u32 operations are
actually u32 values. The Lean model only checks isU32 on:
- u32And, u32Or, u32Xor, u32Not (bitwise ops)
- u32Assert, u32Assert2, u32AssertW (explicit assertions)

The following u32 operations do NOT check isU32 on inputs:
- u32WidenAdd, u32OverflowAdd, u32WrappingAdd
- u32WidenAdd3, u32OverflowAdd3, u32WrappingAdd3
- u32OverflowSub, u32WrappingSub
- u32WidenMul, u32WrappingMul
- u32WidenMadd, u32WrappingMadd
- u32DivMod, u32Div, u32Mod
- u32Shl, u32Shr, u32Rotl, u32Rotr
- u32Popcnt, u32Clz, u32Ctz, u32Clo, u32Cto
- u32Lt, u32Lte, u32Gt, u32Gte, u32Min, u32Max

This is a significant modeling gap. The Rust VM would reject
non-u32 inputs to these operations, but the Lean model
silently computes on the full felt value. For example,
u32WrappingAdd on two felt values > 2^32 would produce
(a.val + b.val) % 2^32 in Lean but would fail in Rust.

#### 2. u32CountLeadingOnes uses subtraction, not XOR
Line 91: `u32CountLeadingZeros (u32Max - 1 - a.val)`
The standard way to compute CLO is to invert bits and count
CLZ. The correct 32-bit NOT is XOR with 0xFFFFFFFF
(= 2^32 - 1 = u32Max - 1). The formula u32Max - 1 - a.val
is equivalent to XOR only when a.val < 2^32 (both give
the ones' complement). For felt values >= 2^32, the
subtraction would underflow (Nat subtraction floors at 0),
giving wrong results. This interacts with issue #1 above.

#### 3. u32CountTrailingOnes uses XOR consistently
Line 95: `u32CountTrailingZeros (n ^^^ (u32Max - 1))`
This is correct for 32-bit values but XOR on Nat extends
to arbitrary width, so for values >= 2^32 the XOR would
flip bits beyond bit 31, again interacting with #1.

#### 4. Memory model differences
- Lean: per-element addressing (Nat -> Felt), one felt per
  address. Be/Le variants for word load/store.
- Rust: word-addressed (BTreeMap<u32, [Felt; 4]>), single
  element access extracts from a word.
- Lean has alignment checks (addr % 4 != 0 -> none) for
  word operations, which matches Rust.
- Lean uses Nat addresses; Rust uses u32. Lean checks
  addr < 2^32 on memory ops.

#### 5. Swapdw pattern mismatch
Semantics.lean line 192-193: execSwapdw matches 16 elements
and swaps words 0-1 with words 2-3:
  [a0..a3, b0..b3, c0..c3, d0..d3] ->
  [c0..c3, d0..d3, a0..a1, a2..a3, b0..b3]
Wait -- re-reading: it produces
  c0::c1::c2::c3::d0::d1::d2::d3::
  a0::a1::a2::a3::b0::b1::b2::b3::rest
This swaps the first 8 elements (two words) with the next 8
(two words). This matches the Rust swapdw semantics.

#### 6. execMovdn inserts at wrong position
Line 209: `insertAt rest n top` where rest = stack tail.
The insertAt function puts the element at position n in the
rest list. Since rest already has the top element removed,
position n in rest corresponds to position n+1 in the
original stack. But movdn.n should move the top element to
position n, i.e., position n-1 in the tail. Let me verify:
movdn.2 should give [a, b, c, ...] -> [b, c, a, ...].
With insertAt rest 2 top where rest = [b, c, ...]:
  take 2 = [b, c], drop 2 = [...], result = [b, c, a, ...]
This is position 2 in the output, which is correct for
movdn.2 (element moves from position 0 to position 2).
So this appears correct after all.

#### 7. advPush reversal
Line 840: `vals.reverse ++ s.stack`. The advice values are
reversed before pushing onto the stack. This means the first
advice element ends up deepest. Need to verify this matches
Rust's behavior. In Rust, advpush pops n elements from the
advice stack and pushes them onto the operand stack such that
the first popped advice element is on top. Since advice.take
n gives [first, second, ...], reversing gives
[..., second, first], and prepending to the stack puts
"first" deepest. This may be WRONG -- the Rust VM pushes
elements so that the first advice element ends up on top.
This needs testing.

#### 8. No stack depth enforcement
The Lean model allows the stack to be any length. The real
Miden VM has a minimum stack depth of 16 and operations
that would shrink below that pad with zeros. This is likely
an intentional simplification but affects semantics of drop
on a near-empty stack.

#### 9. Emit semantics
Line 854-857: execEmit only checks that the stack has at
least 1 element, then is a no-op. emitImm (line 980) is
unconditionally `some s`. In Rust, emit pops an event ID
from the stack. The Lean model does not pop anything.

#### 10. u32Shl/u32Shr lack isU32 precondition checks
These operations check b.val > 31 (shift amount bounds)
but do not verify that the value being shifted is actually
a u32. The Rust VM checks both.
