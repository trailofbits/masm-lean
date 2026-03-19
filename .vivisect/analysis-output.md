# masm-lean Vivisect Analysis Output

## Methodology

Compared every instruction handler in
`MidenLean/Semantics.lean` against the corresponding Rust
implementation in
`miden-vm/processor/src/execution/operations/` and the MASM
assembler in `miden-vm/crates/assembly/src/instruction/`.

For each instruction, verified:
- Precondition enforcement (u32 checks, binary checks, etc.)
- Stack effect (push/pop count)
- Output ordering (which element on top)
- Edge case handling


## Per-Instruction Comparison

### Assertions

| Lean Instruction     | Rust Equivalent     | Match? | Notes           |
|----------------------|---------------------|--------|-----------------|
| assert               | Assert(err_code)    | OK     | See (A1)        |
| assertWithError msg  | Assert(err_code)    | OK     | See (A1)        |
| assertz              | Push(0),Assert      | OK     | Assembled       |
| assertzWithError msg | Push(0),Assert      | OK     | Assembled       |
| assertEq             | Eq,Assert           | OK     | Assembled       |
| assertEqw            | (sequence)          | OK     | Assembled       |

(A1) Lean's `assertWithError` takes a String; Rust's
`Assert` takes a Felt error code. Lean ignores the error
code -- it just calls `execAssert`. Semantically fine for
functional correctness; the error message is a diagnostic
detail.

### Stack Manipulation

| Lean Instruction | Rust Equivalent      | Match? | Notes          |
|------------------|----------------------|--------|----------------|
| drop             | Drop                 | OK     |                |
| dropw            | Drop x4              | OK     | Assembled      |
| padw             | Pad x4               | OK     | Assembled      |
| push v           | Push(v)              | OK     |                |
| pushList vs      | Push x N             | OK     | Assembled      |
| dup n            | Dup0..Dup15          | OK     | See (S1)       |
| dupw n           | (sequence)           | OK     | Assembled      |
| swap n           | Swap (n=1), MovUp    | OK     |                |
| swapw n          | SwapW/SwapW2/SwapW3  | OK     |                |
| swapdw           | SwapDW               | OK     |                |
| movup n          | MovUp2..MovUp8       | OK     | See (S2)       |
| movdn n          | MovDn2..MovDn8       | OK     | Verified       |
| movupw n         | (sequence)           | OK     | Assembled      |
| movdnw n         | (sequence)           | OK     | Assembled      |
| reversew         | (sequence)           | OK     | Assembled      |

(S1) Rust only has Dup0..Dup7, Dup9, Dup11, Dup13, Dup15.
Lean allows Fin 16 (all 0..15). Dup8, Dup10, Dup12, Dup14
are assembled from swap+dup sequences in Rust. The Lean
model provides these as primitives -- a mild overcount of
native ops but semantically correct.

(S2) Rust only has MovUp2..MovUp8. Lean allows n in 2..15.
MovUp9..MovUp15 are assembled in Rust from swap + movup
sequences. Same note as (S1): Lean provides them as
primitives.

### Conditional Operations

| Lean Instruction | Rust Equivalent   | Match? | Notes          |
|------------------|-------------------|--------|----------------|
| cswap            | CSwap             | OK     |                |
| cswapw           | CSwapW            | OK     |                |
| cdrop            | CSwap, Drop       | OK     | See (C1)       |
| cdropw           | CSwapW, Drop x4   | OK     | See (C1)       |

(C1) `cdrop` and `cdropw` are NOT native VM ops in Rust.
They are assembled from CSwap+Drop and CSwapW+Drop*4.
The Lean model treats them as single primitives.
Semantically equivalent -- verified by manual trace:

  Rust cdrop on [c, b, a, ...]:
    CSwap: if c=1: [a, b, ...]; if c=0: [b, a, ...]
    Drop:  if c=1: [b, ...];    if c=0: [a, ...]

  Lean cdrop on [c, b, a, ...]:
    if c=1: [b, ...]; if c=0: [a, ...]

  These match.

### Field Arithmetic

| Lean Instruction | Rust Equivalent  | Match? | Notes          |
|------------------|------------------|--------|----------------|
| add              | Add              | OK     |                |
| addImm v         | Push(v), Add     | OK     | Assembled      |
| sub              | Neg, Add         | OK     | Assembled      |
| subImm v         | Push(v),Neg,Add  | OK     | Assembled      |
| mul              | Mul              | OK     |                |
| mulImm v         | Push(v), Mul     | OK     | Assembled      |
| div              | Inv, Mul         | OK     | Assembled      |
| divImm v         | Push(v),Inv,Mul  | OK     | Assembled      |
| neg              | Neg              | OK     |                |
| inv              | Inv              | OK     |                |
| pow2             | (Expacc seq)     | OK     | See (F1)       |
| incr             | Incr             | OK     |                |

(F1) Lean's `pow2` checks `a.val > 63` and computes
`2^a.val`. The Rust VM uses `Expacc` (exponent
accumulation) across multiple cycles. The Lean version is a
correct mathematical simplification. The pow2 bound of 63
matches: the Goldilocks field has p = 2^64 - 2^32 + 1,
so 2^63 < p and is representable, but 2^64 > p.

### Field Comparison

| Lean Instruction | Rust Equivalent  | Match? | Notes          |
|------------------|------------------|--------|----------------|
| eq               | Eq               | OK     | See (FC1)      |
| eqImm v          | Push(v), Eq      | OK     |                |
| neq              | Eq, Not          | OK     | Assembled      |
| neqImm v         | Push(v),Eq,Not   | OK     | Assembled      |
| lt               | (sequence)       | OK     | Assembled      |
| lte              | (sequence)       | OK     | Assembled      |
| gt               | (sequence)       | OK     | Assembled      |
| gte              | (sequence)       | OK     | Assembled      |
| isOdd            | (sequence)       | OK     | Assembled      |

(FC1) Rust also has `Eqz` as a native op. Lean uses
`eqImm 0` which is semantically equivalent.

### Field Boolean

| Lean Instruction | Rust Equivalent  | Match? | Notes          |
|------------------|------------------|--------|----------------|
| and              | And              | OK     |                |
| or               | Or               | OK     |                |
| xor              | (sequence)       | OK     | See (FB1)      |
| not              | Not              | OK     |                |

(FB1) Rust does not have a native XOR boolean op. The Lean
model computes `a + b - 2*a*b` which is algebraically
correct for binary inputs (the same as a ^^^ b when
a,b in {0,1}).

### U32 Assertions / Conversions

| Lean Instruction | Rust Equivalent     | Match? | Notes         |
|------------------|---------------------|--------|---------------|
| u32Assert        | U32assert2 (self)   | OK     | See (U1)      |
| u32Assert2       | U32assert2          | OK     |               |
| u32AssertW       | U32assert2 x2       | OK     | Assembled     |
| u32Test          | Dup,U32split,       | OK     | Assembled     |
|                  |   Drop,Eqz          |        |               |
| u32TestW         | (long sequence)     | OK     | Assembled     |
| u32Cast          | U32split, Drop      | OK     | Assembled     |
| u32Split         | U32split            | OK     | See (U2)      |

(U1) Rust's native operation is `U32assert2` (checks two
elements). Single-element `u32assert` is assembled from
`Pad, U32assert2, Drop`. The Lean model has both as
primitives.

(U2) Rust `U32split` output: `[lo, hi]` with lo on top
(position 0). Lean: `a.lo32 :: a.hi32 :: rest`. lo32 is
on top. Matches.

### U32 Arithmetic *** FINDINGS ***

| Lean Instruction    | Rust Equivalent      | Match?  | Notes       |
|---------------------|----------------------|---------|-------------|
| u32WidenAdd         | U32add               | **BUG** | (UA1)       |
| u32OverflowAdd      | U32add, Swap         | **BUG** | (UA1)       |
| u32WrappingAdd       | U32add,Swap,Drop     | **BUG** | (UA1)       |
| u32WidenAdd3        | U32add3              | **BUG** | (UA1)       |
| u32OverflowAdd3     | U32add3, Swap        | **BUG** | (UA1)       |
| u32WrappingAdd3     | U32add3              | **BUG** | (UA1)       |
| u32OverflowSub      | U32sub               | **BUG** | (UA1)       |
| u32WrappingSub       | U32sub, Drop         | **BUG** | (UA1)       |
| u32WidenMul         | U32mul               | **BUG** | (UA1)       |
| u32WrappingMul       | U32mul,Swap,Drop     | **BUG** | (UA1)       |
| u32WidenMadd        | U32madd              | **BUG** | (UA1)       |
| u32WrappingMadd     | U32madd              | **BUG** | (UA1)       |
| u32DivMod           | U32div               | **BUG** | (UA1)       |
| u32Div              | U32div, Drop         | **BUG** | (UA1)       |
| u32Mod              | U32div, Swap, Drop   | **BUG** | (UA1)       |

(UA1) **MISSING u32 PRECONDITION CHECK.** Every Rust u32
arithmetic VM operation uses `require_u32_operands!` which
checks that ALL input operands have value < 2^32, returning
`OperationError::NotU32Values` on failure. The Lean model
for all of these operations does NOT check `isU32` on
inputs. On valid u32 inputs both compute the same result;
on invalid inputs (felt values >= 2^32) the Lean model
silently computes garbage while the Rust VM rejects the
operation.

Severity: HIGH for soundness proofs. Any proof about u32
operations that doesn't separately establish isU32
preconditions is proving a weaker statement than the actual
VM guarantees. The Lean model accepts a strictly larger set
of inputs.

Output ordering for all operations verified correct:
- u32WidenAdd:  [sum_lo, carry]    -- matches Rust U32add
- u32OverflowAdd: [carry, sum_lo]  -- matches U32add+Swap
- u32WidenMul:  [lo, hi]           -- matches Rust U32mul
- u32OverflowSub: [borrow, diff]   -- matches Rust U32sub
- u32DivMod:    [rem, quot]        -- matches Rust U32div

### U32 Bitwise *** FINDINGS ***

| Lean Instruction | Rust Equivalent     | Match? | Notes          |
|------------------|---------------------|--------|----------------|
| u32And           | U32and              | OK     |                |
| u32Or            | (a|b=a+b-a&b seq)  | OK     | Assembled      |
| u32Xor           | U32xor              | OK     |                |
| u32Not           | Push(MAX),U32sub    | OK     | See (UB1)      |
| u32Shl           | pow2,U32mul,...     | **BUG**| (UB2)          |
| u32ShlImm        | Push(2^n),U32mul    | **BUG**| (UB2)          |
| u32Shr           | pow2,U32div,...     | **BUG**| (UB2)          |
| u32ShrImm        | Push(2^n),U32div    | **BUG**| (UB2)          |
| u32Rotl          | pow2,U32mul,Add     | **BUG**| (UB2)          |
| u32RotlImm       | Push(2^n),U32mul,Add| **BUG**| (UB2)          |
| u32Rotr          | (complex sequence)  | **BUG**| (UB2)          |
| u32RotrImm       | Push(2^n),U32mul,Add| **BUG**| (UB2)          |
| u32Popcnt        | (bit-parallel seq)  | **BUG**| (UB2)          |
| u32Clz           | advpop + verify     | **BUG**| (UB2),(UB3)    |
| u32Ctz           | advpop + verify     | **BUG**| (UB2),(UB3)    |
| u32Clo           | advpop + verify     | **BUG**| (UB2),(UB3,4)  |
| u32Cto           | advpop + verify     | **BUG**| (UB2),(UB3)    |

(UB1) Lean checks `!a.isU32`, computes `u32Max - 1 - a.val`
(= 0xFFFFFFFF - a.val). Rust assembles to
`Push(u32::MAX), U32assert2, Swap, U32sub, Drop`.
The Rust path checks u32 via U32assert2. Both compute
the same value for u32 inputs. Match.

(UB2) **MISSING u32 PRECONDITION CHECK.** Same issue as
(UA1). Lean's shift/rotate/count ops do not check isU32
on inputs. The Rust implementations use U32mul/U32div/
U32sub etc., all of which enforce u32 via
`require_u32_operands!`.

The Lean shift ops DO check the shift amount (`b.val > 31`
returns none), which is correct. They just don't check
that the VALUE being shifted is u32.

(UB3) **MODELING DIFFERENCE: clz/ctz/clo/cto.** The Rust
VM implements these using non-deterministic advice: the
advice provider computes the answer, pushes it onto the
advice stack, and the VM verifies the answer using
~30-50 cycles of U32 ops. The Lean model computes the
answer directly (deterministic). This is a reasonable
modeling choice for functional correctness, but it means
the Lean model doesn't capture the verification logic.

(UB4) **u32CountLeadingOnes uses subtraction vs XOR.**
Lean line 91: `u32CountLeadingZeros (u32Max - 1 - n)`.
For n in [0, 2^32), this is equivalent to XOR with
0xFFFFFFFF because subtraction and XOR agree on non-
negative values less than the mask. For n >= 2^32 (which
shouldn't happen with proper preconditions), Nat
subtraction would give 0 (underflow to 0), while XOR
would flip higher bits. This is only a problem because of
the missing u32 precondition check (UB2). With proper
u32 preconditions, the formula is correct.

In contrast, `u32CountTrailingOnes` (line 95) uses XOR:
`u32CountTrailingZeros (n ^^^ (u32Max - 1))`.
This inconsistency is cosmetic with proper preconditions
but creates different failure modes for non-u32 inputs.

### U32 Comparison *** FINDINGS ***

| Lean Instruction | Rust Equivalent       | Match? | Notes         |
|------------------|-----------------------|--------|---------------|
| u32Lt            | U32sub,Swap,Drop      | **BUG**| (UC1)         |
| u32Lte           | Swap,U32sub,Swap,     | **BUG**| (UC1)         |
|                  |   Drop,Not            |        |               |
| u32Gt            | Swap,U32sub,Swap,Drop | **BUG**| (UC1)         |
| u32Gte           | U32sub,Swap,Drop,Not  | **BUG**| (UC1)         |
| u32Min           | (U32sub+CSwap seq)    | **BUG**| (UC1)         |
| u32Max           | (U32sub+CSwap seq)    | **BUG**| (UC1)         |

(UC1) **MISSING u32 PRECONDITION CHECK.** Same as (UA1).
All Rust comparison ops are assembled from U32sub which
checks `require_u32_operands!`. Lean's execU32Lt etc. just
compare `.val` without verifying isU32.

Additionally, Lean's u32 comparison ops compare full felt
values (`a.val < b.val`), not u32 values. For felt values
that ARE u32, this gives the same answer. For non-u32 felt
values, the Lean model returns a comparison result while
Rust would reject the inputs.

### Memory Operations

| Lean Instruction    | Rust Equivalent  | Match? | Notes         |
|---------------------|------------------|--------|---------------|
| memLoad             | MLoad            | OK     | See (M1)      |
| memLoadImm addr     | Push(addr),MLoad | OK     | Assembled     |
| memStore            | MStore           | OK     | See (M1)      |
| memStoreImm addr    | Push(addr),MStore| OK     | Assembled     |
| memLoadwBe          | MLoadW           | DIFF   | (M2)          |
| memLoadwBeImm addr  | Push(addr),MLoadW| DIFF   | (M2)          |
| memLoadwLe          | ---              | DIFF   | (M2)          |
| memLoadwLeImm addr  | ---              | DIFF   | (M2)          |
| memStorewBe         | MStoreW          | DIFF   | (M2)          |
| memStorewBeImm addr | Push(addr),MStoreW|DIFF   | (M2)          |
| memStorewLe         | ---              | DIFF   | (M2)          |
| memStorewLeImm addr | ---              | DIFF   | (M2)          |

(M1) **MODELING DIFFERENCE: Memory model.**
- Rust: word-addressed (BTreeMap<u32, [Felt; 4]>). MLoad
  reads element 0 of the word at address `addr`. MStore
  writes element 0 of the word at `addr`.
- Lean: element-addressed (Nat -> Felt). Each address
  holds one Felt.

For single-element load/store, the Lean model is a
correct abstraction IF the mapping from Lean addresses
to Rust word+element addresses is tracked. The Lean model
checks `addr < 2^32`.

(M2) **MODELING DIFFERENCE: Be/Le word variants.**
The Rust VM has exactly one `MLoadW` and one `MStoreW` op.
They load/store a 4-element word. In Rust, `MLoadW` sets
`word[0]` at stack position 0 (top).

The Lean model splits this into Big-Endian and
Little-Endian variants:
- `memLoadwBe`: loads mem[addr] as e3, mem[addr+1] as e2,
  mem[addr+2] as e1, mem[addr+3] as e0; pushes
  [e0, e1, e2, e3, ...] (reversed from memory order).
- `memLoadwLe`: loads mem[addr] as e0, mem[addr+1] as e1,
  etc.; pushes [e0, e1, e2, e3, ...] (same as memory
  order).

The Rust VM loads a word and places word[0] on top. The
element ordering within the word is determined by how the
word was written. Since Lean has element-addressed memory,
the Be/Le distinction captures what Rust achieves through
its word structure. This is a **reasonable modeling
choice** but means proofs must be careful about which
variant they use.

The Lean model also enforces 4-byte alignment
(`addr % 4 != 0 -> none`) and `addr < 2^32`, which
matches Rust's alignment check.

### Procedure Locals

| Lean Instruction | Rust Equivalent    | Match? | Notes          |
|------------------|--------------------|--------|----------------|
| locLoad idx      | (MLoad-based seq)  | OK     | See (L1)       |
| locStore idx     | (MStore-based seq) | OK     | See (L1)       |

(L1) Lean models locals as a separate `Nat -> Felt` map.
Rust implements locals via memory at specific addresses.
This is a valid abstraction.

### Advice Stack

| Lean Instruction | Rust Equivalent    | Match?  | Notes         |
|------------------|--------------------|---------|---------------|
| advPush n        | AdvPop x n         | **BUG** | (IO1)         |
| advLoadW         | AdvPopW            | **BUG** | (IO2)         |

(IO1) **advPush ELEMENT ORDERING IS WRONG.**

Lean's `execAdvPush n` (line 838-840):
```
let vals := s.advice.take n
let adv' := s.advice.drop n
some ((s.withAdvice adv').withStack
      (vals.reverse ++ s.stack))
```

This takes the first n elements from the advice list,
reverses them, and prepends to the stack. So if
advice = [a, b, c, ...] and n=3:
  vals = [a, b, c]
  vals.reverse = [c, b, a]
  result stack: [c, b, a, ...old stack...]

In Rust, `adv_push.n` is assembled as n consecutive
`AdvPop` operations. Each `AdvPop` pops one element from
the front of the advice stack and pushes it onto the
operand stack:
  Step 1: pop a -> stack = [a, ...old...]
  Step 2: pop b -> stack = [b, a, ...old...]
  Step 3: pop c -> stack = [c, b, a, ...old...]

So both produce `[c, b, a, ...old...]` on the stack.

**WAIT: this actually matches.** The reversal in Lean
compensates for the fact that Rust pushes one-at-a-time
(last popped = on top). Let me re-verify:

  advice = [a, b, c, d, ...]
  Lean: take 3 = [a, b, c], reverse = [c, b, a],
        stack = [c, b, a, ...old...]
  Rust: pop a (push), pop b (push), pop c (push),
        stack = [c, b, a, ...old...]

**These are the same.** The reversal is correct.

However, the Rust `AdviceStackBuilder::push_for_adv_push`
documentation says:
  > After `adv_push.n`, the operand stack will have
  > `slice[0]` on top.

And the builder reverses internally so that slice[0] is
popped LAST and ends up on top. This means the user-facing
API ensures `[slice[0], slice[1], ..., slice[n-1]]` on
the operand stack. For this to work with the Lean model,
the advice list in Lean would need to be the
internally-reversed version.

**Verdict: The Lean model's advPush behavior is correct**
as long as the advice list represents the raw advice stack
(front = first to be consumed). The reversal is the right
thing to do.

(IO2) **advLoadW ELEMENT ORDERING.**

Lean's `execAdvLoadW` (lines 842-849):
```
| _ :: _ :: _ :: _ :: rest =>
    if s.advice.length < 4 then none
    else
      let vals := s.advice.take 4
      let adv' := s.advice.drop 4
      some ((s.withAdvice adv').withStack
            (vals.reverse ++ rest))
```

Takes 4 elements, reverses, overwrites top 4 stack
elements. If advice = [a, b, c, d, ...], result
stack = [d, c, b, a, ...rest...].

Rust's `op_advpopw`:
```rust
let word = provider.pop_stack_word()?;
processor.stack_mut().set_word(0, &word);
```

`pop_stack_word` pops 4 elements from front creating
`Word::new([e0, e1, e2, e3])`. `set_word(0, &word)`
places word[0] at position 0 (top).

So if advice = [a, b, c, d, ...]:
  word = [a, b, c, d]
  stack: [a, b, c, d, ...rest...]

**Lean produces [d, c, b, a, ...] but Rust produces
[a, b, c, d, ...].** The reversal is WRONG for advLoadW.

In advPush, the reversal compensates for sequential
push-to-top. But advLoadW is a single bulk operation that
places word[0] at position 0 -- no sequential pushing, so
no reversal needed.

**Severity: HIGH.** This is a confirmed bug. Any proof
relying on advLoadW will have the wrong element ordering.

### Events

| Lean Instruction | Rust Equivalent  | Match? | Notes          |
|------------------|------------------|--------|----------------|
| emit             | Emit             | DIFF   | (EV1)          |
| emitImm eventId  | Push(id), Emit   | DIFF   | (EV1)          |

(EV1) **MODELING DIFFERENCE: Emit semantics.**
- Rust: `Emit` reads the top stack element as an event ID
  (does NOT consume it). The stack is unchanged. The event
  is forwarded to the host. The assembler is responsible
  for pushing the event ID before Emit and dropping it
  after.
- Lean: `execEmit` checks stack has >= 1 element, then
  returns `some s` unchanged. `emitImm` returns `some s`
  unconditionally.

The Lean model correctly captures that Emit is a no-op on
the stack. It doesn't model the event dispatch to the host,
which is reasonable for functional correctness.

**However:** The Lean emit doesn't even read the top
element -- it just checks the stack is non-empty. A more
faithful model would verify the top element exists and
leave the stack unchanged (which is what it does). So this
is actually fine.

### Control Flow

| Lean Construct  | Rust Equivalent    | Match? | Notes          |
|-----------------|--------------------|--------|----------------|
| ifElse t e      | Split              | OK     | See (CF1)      |
| repeat n body   | Repeat             | OK     |                |
| whileTrue body  | Loop               | OK     | See (CF2)      |
| exec target     | Call/Exec          | OK     | By name lookup |

(CF1) Both check condition is binary (0 or 1), pop it,
then execute the appropriate branch. Match.

(CF2) **whileTrue condition-checking.**
Lean's `doWhile` (lines 1025-1037):
- Checks top of stack; if 1, pops it, executes body,
  then loops back to check again.
- If 0, pops it, returns.

Rust's Loop operation:
- Pops the condition from the stack.
- If 1, executes the body, then checks the condition
  again (loop back).
- If 0, exits the loop.

**Match**, but with a subtlety: In the Lean model, the
condition is checked at the TOP of each iteration
(including the first). This means the first element on the
stack must be 1 to enter the loop body. This matches the
Rust `Loop` operation.


## Lean Instruction Enum vs Rust Operation Enum

### In Lean but not in Rust (as native ops):
- `assertz`, `assertzWithError` (assembled: Eqz, Assert)
- `assertEq`, `assertEqWithError` (assembled: Eq, Assert)
- `assertEqw` (assembled: multiple Eq+Assert)
- `dropw` (assembled: Drop x4)
- `padw` (assembled: Pad x4)
- `pushList` (assembled: Push x N)
- `cdrop` (assembled: CSwap, Drop)
- `cdropw` (assembled: CSwapW, Drop x4)
- `sub`, `subImm` (assembled: Neg, Add)
- `div`, `divImm` (assembled: Inv, Mul)
- `pow2` (assembled: exponent accumulation sequence)
- `neq`, `neqImm` (assembled: Eq, Not)
- `lt`, `lte`, `gt`, `gte` (assembled from sequences)
- `isOdd` (assembled)
- `xor` (boolean) (assembled)
- `u32Assert` (single) (assembled: Pad, U32assert2, Drop)
- `u32AssertW` (assembled: U32assert2 x2 + moves)
- `u32Test`, `u32TestW` (assembled)
- `u32Cast` (assembled: U32split, Drop)
- `u32WrappingAdd/3`, `u32OverflowAdd/3`, etc.
  (assembled from U32add/U32add3 + Swap/Drop)
- `u32WrappingSub` (assembled: U32sub, Drop)
- `u32WrappingMul` (assembled: U32mul, Swap, Drop)
- `u32WrappingMadd` (assembled: U32madd, Swap, Drop)
- `u32Div`, `u32Mod` (assembled: U32div + Drop)
- `u32Or` (assembled: Dup, Dup, U32and, Neg, Add, Add)
- `u32Not` (assembled: Push(MAX), U32assert2, Swap,
    U32sub, Drop)
- `u32Shl/Shr/Rotl/Rotr[Imm]` (assembled from pow2 +
    U32mul/U32div)
- `u32Popcnt` (assembled: long bit-parallel sequence)
- `u32Clz/Ctz/Clo/Cto` (assembled: advice + verify)
- `u32Lt/Lte/Gt/Gte/Min/Max` (assembled from U32sub)
- All memory word variants (Be/Le) (Rust has one each)
- `locLoad`, `locStore` (assembled from MLoad/MStore at
    specific addresses)
- `advPush n` (assembled: AdvPop x n)
- `emitImm` (assembled: Push, Emit)

### In Rust but not in Lean:
- `SDepth` (push stack depth)
- `Caller` (push caller hash)
- `Clk` (push clock cycle)
- `Eqz` (compare to zero -- Lean uses eqImm 0)
- `Expacc` (exponent accumulation step)
- `Ext2Mul` (extension field multiplication)
- `MStream` (memory stream)
- `Pipe` (advice -> memory pipe)
- `HPerm` (hash permutation)
- `MpVerify` (Merkle path verification)
- `MrUpdate` (Merkle root update)
- `FriE2F4` (FRI extension operation)
- `Dyn`, `DynCall` (dynamic dispatch)
- `SysCall`, `Call` (procedure call types)
- `HornerBase`, `HornerExt` (Horner evaluation)
- `EvalCircuit` (circuit evaluation)
- `LogPrecompile` (logging)
- `CryptoStream` (cryptographic streaming)

This is expected -- the Lean model covers the subset needed
for word.masm and math/u64.masm library proofs, not the
full VM.


## Confirmed Bugs

### BUG-1: advLoadW reversal (HIGH)

`execAdvLoadW` reverses the 4 advice elements before
placing them on the stack. The Rust `op_advpopw` does NOT
reverse -- it places `word[0]` at stack position 0.

File: `MidenLean/Semantics.lean`, lines 842-849
Fix: Remove `.reverse` from the expression, changing
`vals.reverse ++ rest` to `vals ++ rest`.

### BUG-2: Missing u32 precondition checks (HIGH)

All u32 arithmetic, comparison, bitwise (except And/Or/
Xor/Not), shift, rotate, and count operations lack `isU32`
input validation. The Rust VM enforces these via
`require_u32_operands!` at the VM operation level.

Affected operations (28 total):
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

File: `MidenLean/Semantics.lean`, throughout the u32
section.
Fix: Add `if !a.isU32 || !b.isU32 then none else ...`
(or appropriate single-operand check) to each handler.


## Modeling Differences (Intentional Simplifications)

### DIFF-1: Memory model (element vs word addressed)
Lean: `Nat -> Felt` (element-addressed).
Rust: `BTreeMap<u32, [Felt; 4]>` (word-addressed).
This is a reasonable abstraction. The Be/Le word variants
capture the needed element-order semantics.

### DIFF-2: Stack depth enforcement
Lean: unbounded list, no minimum depth.
Rust: minimum depth 16, padded with zeros.
This means Lean allows operations on stacks with < 16
elements that Rust would pad. Reasonable for proofs that
establish sufficient depth.

### DIFF-3: clz/ctz/clo/cto computation
Lean: deterministic (computes answer directly).
Rust: non-deterministic (advice + verification).
The Lean model is functionally equivalent but doesn't
capture the verification logic.

### DIFF-4: Assembled vs primitive operations
Many Lean instructions are single primitives that Rust
assembles from multiple native VM operations. The Lean
model is a correct abstraction of the assembled behavior.
This is by design -- the Lean model operates at the MASM
instruction level, not the VM operation level.

### DIFF-5: Procedure locals
Lean: separate `Nat -> Felt` map.
Rust: mapped to specific memory addresses.
Valid abstraction.

### DIFF-6: No error codes on assertions
Lean's assertWithError takes a String; Rust takes Felt
error code. Lean ignores it (delegates to execAssert).
Fine for functional correctness.


## Missing Features

- Cryptographic operations (HPerm, MpVerify, MrUpdate,
  FriE2F4, CryptoStream)
- Extension field operations (Ext2Mul, Expacc)
- Dynamic dispatch (Dyn, DynCall)
- System operations (SDepth, Caller, Clk)
- Memory streaming (MStream, Pipe)
- Logging (LogPrecompile)
- Circuit evaluation (EvalCircuit)
- Horner evaluation (HornerBase, HornerExt)

These are out of scope for the current verification target
(u64 and word library procedures).


## Preliminary Categorization

### GOOD (correct, no issues)
- All field arithmetic (add, sub, mul, div, neg, inv,
  pow2, incr)
- All field comparison (eq, neq, lt, lte, gt, gte, isOdd)
- All field boolean (and, or, xor, not)
- All stack manipulation (drop, dropw, padw, push, dup,
  dupw, swap, swapw, swapdw, movup, movdn, movupw,
  movdnw, reversew)
- All conditional operations (cswap, cswapw, cdrop, cdropw)
- All assertion operations (assert, assertz, assertEq,
  assertEqw, u32Assert, u32Assert2, u32AssertW)
- u32 conversions (u32Test, u32TestW, u32Cast, u32Split)
- u32 bitwise: u32And, u32Or, u32Xor, u32Not
- advPush (verified: reversal is correct)
- Memory single-element load/store
- Procedure locals (locLoad, locStore)
- Emit (correctly modeled as no-op on stack)
- Control flow (ifElse, repeat, whileTrue)
- Procedure calls (exec)

### BAD (missing preconditions, wrong on edge cases)
- All 28+ u32 arithmetic/comparison/shift/rotate/count
  ops that lack isU32 input checks (BUG-2)

### BROKEN (demonstrably wrong behavior)
- advLoadW element ordering (BUG-1)

### ABSURD (not applicable -- nothing found)
No instructions found where the semantics are completely
unrelated to the Rust implementation.


## Impact on Existing Proofs

The proofs in `MidenLean/Proofs/` prove correctness of
u64 and word library procedures. These procedures are
sequences of primitive instructions. The proofs typically
assume specific stack layouts.

**BUG-1 impact:** If any proved procedure uses advLoadW,
the proof is establishing an incorrect property. Need to
check which proofs use advLoadW.

**BUG-2 impact:** The u32 precondition gap means proofs
about u32 operations prove: "IF the operation succeeds
(returns Some), THEN the result is correct." But the
model succeeds on a LARGER set of inputs than the Rust VM.
Proofs that assume specific u32 inputs (and establish this
via the stack layout) are still valid -- they just don't
prove that the operation rejects non-u32 inputs.

For the existing proofs, this is likely not a soundness
problem because the procedures are designed to operate on
u32 values and the proof assumptions establish this. But
it means the Lean model could not be used to verify that
a procedure correctly REJECTS invalid inputs.
