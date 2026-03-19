# Vivisect Findings: masm-lean

## Good

### Field arithmetic matches Rust
AC-2. add, sub, mul, div, neg, inv, pow2, incr all
produce correct results. pow2 correctly bounds exponent
at 63 (matching Goldilocks field constraint). sub is
assembled from Neg+Add, div from Inv+Mul; Lean's direct
implementations are semantically equivalent.
Files: `MidenLean/Semantics.lean:233-310`

### Field comparison matches Rust
AC-3. eq, neq, lt, lte, gt, gte, isOdd all match. neq
assembled from Eq+Not in Rust; Lean implements directly.
Eqz handled via eqImm 0, which is equivalent.
Files: `MidenLean/Semantics.lean:312-370`

### Field boolean ops match Rust including binary checks
AC-4. and, or, xor, not all check that inputs are binary
(0 or 1) and return none otherwise, matching Rust's
behavior. xor uses a+b-2*a*b which is algebraically
correct for binary inputs.
Files: `MidenLean/Semantics.lean:372-408`

### Stack manipulation verified correct
AC-5. drop, dropw, padw, push, pushList, dup (0..15),
dupw, swap, swapw, swapdw, movup, movdn, movupw, movdnw,
reversew all match Rust semantics. Lean provides some
assembled ops (dup8-14, movup9-15) as primitives -- a
mild overcount but semantically correct.
Files: `MidenLean/Semantics.lean:100-230`

### Conditional operations semantically correct
AC-6. cswap, cswapw check binary condition and swap
accordingly. cdrop, cdropw are assembled in Rust
(CSwap+Drop) but primitive in Lean; manual trace
confirms equivalent behavior. Non-binary conditions
correctly return none.
Files: `MidenLean/Semantics.lean:286-310`

### advPush ordering is correct
AC-14. The `.reverse` in advPush compensates for the
difference between Lean's bulk prepend and Rust's
sequential AdvPop-push-to-top pattern. Both produce
the same final stack ordering: with advice=[a,b,c] and
n=3, both yield stack [c,b,a,...old...].
File: `MidenLean/Semantics.lean:835-840`

### Control flow matches Rust condition-check semantics
AC-15. ifElse checks binary condition, pops it, executes
the appropriate branch. repeat iterates body n times.
whileTrue checks top-of-stack at each iteration
(including first), pops the condition, enters body on 1,
exits on 0. exec looks up procedures by name in ProcEnv.
All match Rust's Split, Repeat, Loop, Call.
Files: `MidenLean/Semantics.lean:1003-1048`

### u32Split and u32Cast output ordering matches Rust
AC-10. u32Split produces [lo, hi] with lo on top,
matching Rust's U32split. u32Cast correctly drops the
high part. u32Assert/Assert2/AssertW and u32Test/TestW
all match.
Files: `MidenLean/Semantics.lean:411-451`

### u32And, u32Or, u32Xor, u32Not check isU32
AC-8 (partial). These four bitwise ops correctly check
isU32 on inputs and return none for non-u32 values,
matching Rust. u32Not computes 0xFFFFFFFF - a.val which
equals bitwise NOT for u32 inputs.
Files: `MidenLean/Semantics.lean:555-581`

### Assertion instructions match Rust
AC-16. assert, assertWithError, assertz, assertzWithError,
assertEq, assertEqWithError, assertEqw all correctly
check the relevant condition and return none on failure.
Error codes are ignored (String vs Felt), which is fine
for functional correctness.
Files: `MidenLean/Semantics.lean:56-98`

### Memory single-element load/store correct
AC-12 (partial). memLoad and memStore correctly read/write
individual felt values, check addr < 2^32, and match
Rust's MLoad/MStore behavior under the element-addressed
abstraction. Word operations use alignment checks
(addr % 4 != 0 -> none).
Files: `MidenLean/Semantics.lean:697-833`

### Emit correctly modeled as stack no-op
AC-12. execEmit checks stack has >= 1 element and returns
state unchanged. Rust's Emit reads top element as event
ID but does not modify the stack. The Lean model omits
host event dispatch, which is reasonable for functional
correctness.
Files: `MidenLean/Semantics.lean:854-857`

## Bad

### No stack depth enforcement
AC-5, AC-11. The Lean model uses an unbounded List Felt
for the stack with no minimum depth. The Rust Miden VM
enforces a minimum stack depth of 16 (padded with zeros)
and a maximum depth of 2^16. This means Lean allows
operations on stacks with fewer than 16 elements that
Rust would pad, and does not reject programs that exceed
the depth limit.
File: `MidenLean/State.lean:6-14`

### Memory model is element-addressed, not word-addressed
AC-13. Lean uses `Nat -> Felt` (one felt per address);
Rust uses `BTreeMap<u32, [Felt; 4]>` (word-addressed).
Lean compensates with Be/Le word-load/store variants
where Rust has a single MLoadW/MStoreW. This is a
reasonable abstraction but proofs must track which
variant (Be or Le) corresponds to Rust's word layout.
No verification exists that one of the two variants
faithfully matches Rust's element ordering within words.
Files: `MidenLean/Semantics.lean:697-833`,
       `MidenLean/State.lean:9-10`

### Emit does not read top element
AC-12. Lean's execEmit checks that the stack is non-empty
but does not actually read the top element value.
Rust's Emit reads the top element as an event ID and
forwards it to the host. While functionally a no-op on
the stack in both cases, a more faithful model would
extract the event ID. Minor fidelity gap.
File: `MidenLean/Semantics.lean:854-857`

## Broken

### advLoadW element ordering is reversed
AC-14. `execAdvLoadW` applies `.reverse` to the 4 advice
elements before placing them on the stack (line 849:
`vals.reverse ++ rest`). Rust's `op_advpopw` does NOT
reverse -- it creates `Word::new([e0, e1, e2, e3])` and
places `word[0]` at stack position 0 (top).

With advice = [a, b, c, d]:
  Lean produces:  [d, c, b, a, ...rest...]
  Rust produces:  [a, b, c, d, ...rest...]

The `.reverse` is correct for `advPush` (compensating
for sequential push-to-top), but `advLoadW` is a single
bulk operation with no such compensation needed.

Fix: change `vals.reverse ++ rest` to `vals ++ rest`.
File: `MidenLean/Semantics.lean:842-849`

### 28+ u32 operations lack isU32 input precondition checks
AC-7, AC-8, AC-9, AC-11. Every Rust u32 VM operation
uses `require_u32_operands!` to reject inputs with
value >= 2^32. The Lean model omits this check on all
u32 arithmetic, comparison, shift, rotate, and count
operations (only u32And/Or/Xor/Not check isU32).

On valid u32 inputs, both models compute the same
result. On invalid inputs (felt values >= 2^32), the
Lean model silently computes on the full felt value
while Rust returns an error. This means:
- Proofs about u32 ops prove a weaker statement (the
  model accepts a strictly larger input set).
- The model cannot verify that a procedure correctly
  rejects invalid inputs.
- Helper functions like u32CountLeadingOnes (line 91,
  uses Nat subtraction instead of XOR) produce
  different wrong answers than u32CountTrailingOnes
  (line 95, uses XOR) for non-u32 inputs, though both
  are correct when preconditions hold.

Affected operations (34 total):
  u32WidenAdd, u32OverflowAdd, u32WrappingAdd,
  u32WidenAdd3, u32OverflowAdd3, u32WrappingAdd3,
  u32OverflowSub, u32WrappingSub,
  u32WidenMul, u32WrappingMul,
  u32WidenMadd, u32WrappingMadd,
  u32DivMod, u32Div, u32Mod,
  u32Shl, u32ShlImm, u32Shr, u32ShrImm,
  u32Rotl, u32RotlImm, u32Rotr, u32RotrImm,
  u32Popcnt, u32Clz, u32Ctz, u32Clo, u32Cto,
  u32Lt, u32Lte, u32Gt, u32Gte, u32Min, u32Max

Fix: add `if !a.isU32 then none else ...` (single-
operand) or `if !a.isU32 || !b.isU32 then none else ...`
(two-operand) guards to each handler.
Files: `MidenLean/Semantics.lean:453-695`

## Absurd
