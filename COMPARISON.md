# miden-lean vs miden-vm Semantic Comparison

This document catalogs every meaningful semantic difference between the
Lean 4 executable model (miden-lean) and the Rust reference
implementation (miden-vm). Differences are categorized as bugs (fixed),
intentional simplifications, or missing features.

## Semantic Bugs (Found and Fixed)

### BUG-1: advLoadW reversed element ordering

**File:** `MidenLean/Semantics.lean:842-849`
**Severity:** High

`execAdvLoadW` applied `.reverse` to the 4 advice elements before
placing them on the stack. The Rust VM's `op_advpopw` does NOT reverse
-- it places `word[0]` at stack position 0 (top of stack).

With advice stack = [a, b, c, d]:
- Lean (before fix): stack = [d, c, b, a, ...rest...]
- Rust:              stack = [a, b, c, d, ...rest...]

The `.reverse` was incorrectly carried over from `advPush`, where it IS
correct (advPush compensates for sequential push-to-top behavior;
advLoadW is a bulk overwrite that needs no compensation).

**Fix:** Changed `vals.reverse ++ rest` to `vals ++ rest`.
**Regression test:** `MidenLean/Tests/Semantics.lean` (search for
"REGRESSION(advLoadW)")

### BUG-2: 34 u32 operations lacked isU32 precondition checks

**File:** `MidenLean/Semantics.lean:453-695`
**Severity:** High

Every Rust u32 VM operation uses `require_u32_operands!` to reject
inputs with value >= 2^32. The Lean model only checked `isU32` on four
bitwise operations (u32And, u32Or, u32Xor, u32Not). All other u32
operations -- arithmetic, comparison, shift/rotate, and bit-counting --
accepted arbitrary felt values.

On valid u32 inputs, both models computed the same result. On invalid
inputs (felt values >= 2^32), the Lean model silently computed on the
full felt value while Rust returns `NotU32Values` error. This meant:

1. Proofs about u32 operations proved a weaker statement than
   intended (the model accepts a strictly larger input set).
2. The model could not verify that a procedure correctly rejects
   invalid inputs.
3. Helper functions like `u32CountLeadingOnes` (using Nat
   subtraction) and `u32CountTrailingOnes` (using XOR) produced
   inconsistent wrong answers for non-u32 inputs.

**Affected operations (34 total):**
- Arithmetic: u32WidenAdd, u32OverflowAdd, u32WrappingAdd,
  u32WidenAdd3, u32OverflowAdd3, u32WrappingAdd3,
  u32OverflowSub, u32WrappingSub, u32WidenMul, u32WrappingMul,
  u32WidenMadd, u32WrappingMadd, u32DivMod, u32Div, u32Mod
- Shift/rotate: u32Shl, u32ShlImm, u32Shr, u32ShrImm, u32Rotl,
  u32RotlImm, u32Rotr, u32RotrImm
- Bit counting: u32Popcnt, u32Clz, u32Ctz, u32Clo, u32Cto
- Comparison: u32Lt, u32Lte, u32Gt, u32Gte, u32Min, u32Max

**Fix:** Added `if !a.isU32 || !b.isU32 then none else ...` guards (or
single-operand variants) to all 34 handlers. Updated step lemmas in
`StepLemmas.lean` to carry isU32 hypotheses. Updated `miden_step` tactic
in `Tactics.lean` to resolve isU32 hypotheses via `assumption`.

**Impact on existing proofs:** Correctness theorems that use u32
arithmetic step lemmas now need isU32 hypotheses on their input felts.
Most proofs already carried these hypotheses (e.g.,
u64_wrapping_mul_correct has `ha_lo`, `hb_lo`). Proofs that did not
carry them (e.g., u64_wrapping_sub_correct) need isU32 hypotheses added
to their theorem statements. This is a correctness improvement -- the
theorems now prove strictly stronger statements matching the Rust VM's
actual behavior.

**Regression tests:** `MidenLean/Tests/Semantics.lean` (search for
"REGRESSION(u32-precond)")

## Intentional Modeling Simplifications

### S-1: Unbounded stack depth

**Lean:** `List Felt` (unbounded, no minimum depth)
**Rust:** Minimum 16 elements (zero-padded), maximum 2^16

The Lean model allows operations on stacks smaller than 16 elements.
This is standard in formal machine models (see LNSym, eth-isabelle,
Cairo formal proofs). It avoids modeling the zero-padding logic, which
is an implementation detail not relevant to procedure correctness.

**Impact:** Proofs do not verify stack overflow behavior. Programs that
depend on the zero-initialized padding below the 16th element would need
explicit hypotheses.

### S-2: Element-addressed memory vs word-addressed memory

**Lean:** `Nat -> Felt` (one felt per address, total function)
**Rust:** `BTreeMap<(ContextId, u32), Word>` (word-addressed, sparse)

The Lean model stores one felt per natural number address. Word
operations (memLoadw, memStorew) read/write 4 consecutive addresses. The
Lean model provides separate Be (big-endian) and Le (little-endian)
variants for word operations.

The Rust model stores 4-element Words at word-aligned addresses.
Individual element access uses `split_addr(addr)` to decompose into
(word_addr, index_within_word). The Rust `op_mloadw` reads a Word and
places `word[0]` at stack top; `op_mstorew` writes the top 4 stack
elements as a Word starting from position 1 (after popping the address).

The Rust VM's element ordering within a word is:
- `word[0]` <-> lowest address within the 4-element group
- `word[0]` <-> stack top after mloadw

This matches the Lean Le (little-endian) variant where the lowest
address goes to the stack top.

**Impact:** Proofs using word memory operations must specify which
variant (Be or Le) is being used. For fidelity with the Rust VM, the Le
variants should be preferred.

### S-3: No execution contexts

**Lean:** Single flat memory space
**Rust:** Memory keyed by `(ContextId, address)`

The Lean model does not support multiple execution contexts. This is
appropriate for the current scope (single-procedure correctness proofs)
since all proven procedures execute in a single context.

### S-4: Emit as pure no-op

**Lean:** `execEmit` checks stack >= 1, returns state unchanged
**Rust:** `op_emit` reads top element as event ID, dispatches to host.
Stack is unchanged in both.

The Lean model does not extract the event ID or model host interaction.
This is correct for functional semantics since emit does not modify the
VM state (stack, memory, advice).

### S-5: Error codes as strings

**Lean:** `assertWithError` takes a `String` parameter
**Rust:** Assertions take a `Felt` error code, resolved to a message
via the MAST forest

The Lean model ignores error codes for functional correctness. Both
models fail on assertion violation; only the error reporting differs.

### S-6: Assembled operations as primitives

**Lean:** `cdrop`, `cdropw` are primitive instruction handlers
**Rust:** These are assembled from lower-level VM operations
(CSwap + Drop for cdrop; CSwapW + DropW for cdropw)

The Lean model implements these directly. The semantics are equivalent
-- both produce the same stack state for all valid inputs.

## Missing Features

The following Rust VM operations are not modeled in Lean. These are not
bugs -- the Lean model covers the instruction subset needed for the
proven core library procedures.

### Crypto operations
- `HPerm` (hash permutation)
- `MpVerify` (Merkle path verification)
- `MrUpdate` (Merkle root update)
- `HornerBase`, `HornerExt` (polynomial evaluation)
- `EvalCircuit` (circuit evaluation)
- `LogPrecompile`

### Extension field operations
- `Expacc` (exponentiation accumulation)
- `Ext2Mul` (quadratic extension multiplication)

### System operations
- `SDepth` (stack depth query)
- `Caller` (caller procedure hash)
- `Clk` (clock cycle counter)

### Dynamic dispatch
- `Dyn` (dynamic procedure call via hash)
- `DynCall` (dynamic call with frame)
- `SysCall` (kernel procedure call)

### Stream operations
- `MStream` (memory stream: load 2 words from memory)
- `Pipe` (advice-to-memory pipe)

### Field operations
- `Eqz` (equals zero -- modeled via `eqImm 0`)

## Test Coverage

The test suite at `MidenLean/Tests/Semantics.lean` exercises ~100 test
cases across all modeled instruction categories:

| Category           | Tests | Edge cases                      |
|--------------------|-------|---------------------------------|
| Field arithmetic   | 16    | zero, max, overflow, div-by-0   |
| Field comparison   | 10    | boundary values, equal          |
| Field boolean      | 10    | binary/non-binary inputs        |
| Stack manipulation | 14    | empty stack, various positions  |
| Conditional ops    | 6     | true/false/non-binary           |
| U32 arithmetic     | 12    | carry, borrow, overflow         |
| U32 preconditions  | 8     | non-u32 rejection (regression)  |
| U32 bitwise        | 12    | masks, shifts, rotates, counts  |
| U32 comparison     | 5     | boundary, equal                 |
| U32 assertions     | 6     | valid/invalid, split/cast       |
| Assertions         | 6     | pass/fail for each variant      |
| Advice stack       | 4     | ordering, insufficient          |
| Memory             | 4     | store/load, unwritten, OOB      |
| Control flow       | 6     | ifElse, repeat, while           |

