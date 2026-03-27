/-
  Semantics test suite: exercises the Lean executable semantics against
  concrete input/output pairs derived from the Rust miden-vm behavior.

  Each test uses #eval with a guard that returns a descriptive error
  string on failure, so `lake build` success implies all tests pass.
-/
import MidenLean.Semantics

namespace MidenLean.Tests

open MidenLean

-- ============================================================================
-- Helpers
-- ============================================================================

/-- Shorthand for a state with given stack and empty memory/advice. -/
private def mkState (stk : List Felt) : MidenState :=
  MidenState.ofStack stk

/-- State with stack and advice. -/
private def mkStateAdv (stk : List Felt) (adv : List Felt) : MidenState :=
  MidenState.ofStackAdvice stk adv

/-- Run a single instruction on a state. -/
private def runInst (s : MidenState) (i : Instruction) : Option MidenState :=
  execInstruction s i

/-- Run a list of ops with given fuel. -/
private def runOps (fuel : Nat) (s : MidenState) (ops : List Op) : Option MidenState :=
  exec fuel s ops

/-- Check that the resulting stack matches expected values. -/
private def checkStack (result : Option MidenState) (expected : List Felt) : Bool :=
  match result with
  | some s => s.stack == expected
  | none => false

/-- Check that the result is none (operation failed). -/
private def checkNone (result : Option MidenState) : Bool :=
  result.isNone

/-- Check that specific local slots have the expected values. -/
private def checkLocals (result : Option MidenState) (pairs : List (Nat × Felt)) : Bool :=
  match result with
  | some s => pairs.all fun (idx, v) => s.locals idx == v
  | none => false

-- Felt constants for readability
private def p : Nat := GOLDILOCKS_PRIME  -- 2^64 - 2^32 + 1
private def u32max : Nat := 2^32

-- ============================================================================
-- Tier 1: Field Arithmetic (AC-2)
-- ============================================================================

-- add: basic
#eval do
  let s := mkState [3, 5]
  let r := runInst s .add
  unless checkStack r [8] do panic! "add: 3+5 failed"

-- add: overflow wraps in field
#eval do
  let s := mkState [(p - 1 : Felt), 2]
  let r := runInst s .add
  unless checkStack r [1] do panic! "add: (p-1)+2 failed"

-- sub: basic
#eval do
  let s := mkState [3, 10]
  let r := runInst s .sub
  unless checkStack r [7] do panic! "sub: 10-3 failed"

-- sub: underflow wraps in field
#eval do
  let s := mkState [5, 3]
  let r := runInst s .sub
  unless checkStack r [(p - 2 : Felt)] do panic! "sub: 3-5 wrap failed"

-- mul: basic
#eval do
  let s := mkState [4, 7]
  let r := runInst s .mul
  unless checkStack r [28] do panic! "mul: 7*4 failed"

-- mul: zero
#eval do
  let s := mkState [0, 42]
  let r := runInst s .mul
  unless checkStack r [0] do panic! "mul: 42*0 failed"

-- div: basic
#eval do
  let s := mkState [3, 12]
  let r := runInst s .div
  unless checkStack r [4] do panic! "div: 12/3 failed"

-- div: by zero fails
#eval do
  let s := mkState [0, 5]
  let r := runInst s .div
  unless checkNone r do panic! "div: by zero should fail"

-- neg: basic
#eval do
  let s := mkState [5]
  let r := runInst s .neg
  unless checkStack r [(p - 5 : Felt)] do panic! "neg: -5 failed"

-- neg: zero is zero
#eval do
  let s := mkState [0]
  let r := runInst s .neg
  unless checkStack r [0] do panic! "neg: -0 failed"

-- inv: basic (3 * inv(3) = 1)
#eval do
  let s := mkState [3]
  let r := runInst s .inv
  match r with
  | some s' =>
    let s2 := mkState [3, s'.stack.head!]
    let r2 := runInst s2 .mul
    unless checkStack r2 [1] do panic! "inv: 3*inv(3) != 1"
  | none => panic! "inv: should not fail on 3"

-- inv: zero fails
#eval do
  let s := mkState [0]
  let r := runInst s .inv
  unless checkNone r do panic! "inv: inv(0) should fail"

-- pow2: basic
#eval do
  let s := mkState [10]
  let r := runInst s .pow2
  unless checkStack r [1024] do panic! "pow2: 2^10 failed"

-- pow2: zero
#eval do
  let s := mkState [0]
  let r := runInst s .pow2
  unless checkStack r [1] do panic! "pow2: 2^0 failed"

-- pow2: 63 is max
#eval do
  let s := mkState [63]
  let r := runInst s .pow2
  unless r.isSome do panic! "pow2: 2^63 should succeed"

-- pow2: 64 fails
#eval do
  let s := mkState [64]
  let r := runInst s .pow2
  unless checkNone r do panic! "pow2: 2^64 should fail"

-- incr: basic
#eval do
  let s := mkState [41]
  let r := runInst s .incr
  unless checkStack r [42] do panic! "incr: 41+1 failed"

-- ============================================================================
-- Tier 1: Field Comparison (AC-3)
-- ============================================================================

-- eq: equal
#eval do
  let s := mkState [7, 7]
  let r := runInst s .eq
  unless checkStack r [1] do panic! "eq: 7==7 failed"

-- eq: not equal
#eval do
  let s := mkState [7, 8]
  let r := runInst s .eq
  unless checkStack r [0] do panic! "eq: 8!=7 failed"

-- neq: not equal
#eval do
  let s := mkState [7, 8]
  let r := runInst s .neq
  unless checkStack r [1] do panic! "neq: 8!=7 failed"

-- neq: equal
#eval do
  let s := mkState [5, 5]
  let r := runInst s .neq
  unless checkStack r [0] do panic! "neq: 5==5 failed"

-- lt: true
#eval do
  let s := mkState [10, 5]
  let r := runInst s .lt
  unless checkStack r [1] do panic! "lt: 5<10 failed"

-- lt: false
#eval do
  let s := mkState [5, 10]
  let r := runInst s .lt
  unless checkStack r [0] do panic! "lt: 10<5 should be false"

-- lt: equal
#eval do
  let s := mkState [5, 5]
  let r := runInst s .lt
  unless checkStack r [0] do panic! "lt: 5<5 should be false"

-- lte: true (less)
#eval do
  let s := mkState [10, 5]
  let r := runInst s .lte
  unless checkStack r [1] do panic! "lte: 5<=10 failed"

-- lte: true (equal)
#eval do
  let s := mkState [5, 5]
  let r := runInst s .lte
  unless checkStack r [1] do panic! "lte: 5<=5 failed"

-- gt, gte, isOdd: basic
#eval do
  let s := mkState [5, 10]
  let r := runInst s .gt
  unless checkStack r [1] do panic! "gt: 10>5 failed"

#eval do
  let s := mkState [5, 5]
  let r := runInst s .gte
  unless checkStack r [1] do panic! "gte: 5>=5 failed"

#eval do
  let s := mkState [7]
  let r := runInst s .isOdd
  unless checkStack r [1] do panic! "isOdd: 7 failed"

#eval do
  let s := mkState [8]
  let r := runInst s .isOdd
  unless checkStack r [0] do panic! "isOdd: 8 failed"

-- ============================================================================
-- Tier 1: Field Boolean (AC-4)
-- ============================================================================

-- and: 1 AND 1 = 1
#eval do
  let s := mkState [1, 1]
  let r := runInst s .and
  unless checkStack r [1] do panic! "and: 1&1 failed"

-- and: 1 AND 0 = 0
#eval do
  let s := mkState [0, 1]
  let r := runInst s .and
  unless checkStack r [0] do panic! "and: 1&0 failed"

-- and: non-binary fails
#eval do
  let s := mkState [2, 1]
  let r := runInst s .and
  unless checkNone r do panic! "and: non-binary should fail"

-- or: 0 OR 1 = 1
#eval do
  let s := mkState [1, 0]
  let r := runInst s .or
  unless checkStack r [1] do panic! "or: 0|1 failed"

-- or: 0 OR 0 = 0
#eval do
  let s := mkState [0, 0]
  let r := runInst s .or
  unless checkStack r [0] do panic! "or: 0|0 failed"

-- xor: 1 XOR 0 = 1
#eval do
  let s := mkState [0, 1]
  let r := runInst s .xor
  unless checkStack r [1] do panic! "xor: 1^0 failed"

-- xor: 1 XOR 1 = 0
#eval do
  let s := mkState [1, 1]
  let r := runInst s .xor
  unless checkStack r [0] do panic! "xor: 1^1 failed"

-- not: NOT 0 = 1
#eval do
  let s := mkState [0]
  let r := runInst s .not
  unless checkStack r [1] do panic! "not: !0 failed"

-- not: NOT 1 = 0
#eval do
  let s := mkState [1]
  let r := runInst s .not
  unless checkStack r [0] do panic! "not: !1 failed"

-- not: non-binary fails
#eval do
  let s := mkState [5]
  let r := runInst s .not
  unless checkNone r do panic! "not: non-binary should fail"

-- ============================================================================
-- Tier 1: Stack Manipulation (AC-5)
-- ============================================================================

-- drop
#eval do
  let s := mkState [1, 2, 3]
  let r := runInst s .drop
  unless checkStack r [2, 3] do panic! "drop failed"

-- drop: empty stack fails
#eval do
  let s := mkState []
  let r := runInst s .drop
  unless checkNone r do panic! "drop: empty should fail"

-- dropw
#eval do
  let s := mkState [1, 2, 3, 4, 5]
  let r := runInst s .dropw
  unless checkStack r [5] do panic! "dropw failed"

-- padw
#eval do
  let s := mkState [1, 2]
  let r := runInst s .padw
  unless checkStack r [0, 0, 0, 0, 1, 2] do panic! "padw failed"

-- push
#eval do
  let s := mkState [1, 2]
  let r := runInst s (.push 42)
  unless checkStack r [42, 1, 2] do panic! "push failed"

-- dup.0
#eval do
  let s := mkState [10, 20]
  let r := runInst s (.dup 0)
  unless checkStack r [10, 10, 20] do panic! "dup.0 failed"

-- dup.3
#eval do
  let s := mkState [10, 20, 30, 40, 50]
  let r := runInst s (.dup 3)
  unless checkStack r [40, 10, 20, 30, 40, 50] do panic! "dup.3 failed"

-- swap.1
#eval do
  let s := mkState [10, 20, 30]
  let r := runInst s (.swap 1)
  unless checkStack r [20, 10, 30] do panic! "swap.1 failed"

-- swap.0 is nop
#eval do
  let s := mkState [10, 20]
  let r := runInst s (.swap 0)
  unless checkStack r [10, 20] do panic! "swap.0 failed"

-- swapdw: swap first 8 with second 8
#eval do
  let s := mkState [1,2,3,4, 5,6,7,8, 9,10,11,12, 13,14,15,16]
  let r := runInst s .swapdw
  unless checkStack r [9,10,11,12, 13,14,15,16, 1,2,3,4, 5,6,7,8] do panic! "swapdw failed"

-- movup.3
#eval do
  let s := mkState [1, 2, 3, 4, 5]
  let r := runInst s (.movup 3)
  unless checkStack r [4, 1, 2, 3, 5] do panic! "movup.3 failed"

-- movdn.3
#eval do
  let s := mkState [1, 2, 3, 4, 5]
  let r := runInst s (.movdn 3)
  unless checkStack r [2, 3, 4, 1, 5] do panic! "movdn.3 failed"

-- movup: n < 2 fails
#eval do
  let s := mkState [1, 2, 3]
  let r := runInst s (.movup 1)
  unless checkNone r do panic! "movup.1 should fail"

-- reversew
#eval do
  let s := mkState [1, 2, 3, 4, 5]
  let r := runInst s .reversew
  unless checkStack r [4, 3, 2, 1, 5] do panic! "reversew failed"

-- ============================================================================
-- Tier 1: Conditional Operations (AC-6)
-- ============================================================================

-- cswap: condition=1 swaps
#eval do
  let s := mkState [1, 10, 20]
  let r := runInst s .cswap
  unless checkStack r [20, 10] do panic! "cswap: c=1 failed"

-- cswap: condition=0 no swap
#eval do
  let s := mkState [0, 10, 20]
  let r := runInst s .cswap
  unless checkStack r [10, 20] do panic! "cswap: c=0 failed"

-- cswap: non-binary fails
#eval do
  let s := mkState [2, 10, 20]
  let r := runInst s .cswap
  unless checkNone r do panic! "cswap: non-binary should fail"

-- cswapw: condition=1
#eval do
  let s := mkState [1, 1,2,3,4, 5,6,7,8]
  let r := runInst s .cswapw
  unless checkStack r [5,6,7,8, 1,2,3,4] do panic! "cswapw: c=1 failed"

-- cdrop: condition=1 keeps first
#eval do
  let s := mkState [1, 10, 20]
  let r := runInst s .cdrop
  unless checkStack r [10] do panic! "cdrop: c=1 failed"

-- cdrop: condition=0 keeps second
#eval do
  let s := mkState [0, 10, 20]
  let r := runInst s .cdrop
  unless checkStack r [20] do panic! "cdrop: c=0 failed"

-- ============================================================================
-- Tier 2: U32 Arithmetic (AC-7)
-- ============================================================================

-- u32WidenAdd: basic
#eval do
  let s := mkState [3, 5]
  let r := runInst s .u32WidenAdd
  unless checkStack r [8, 0] do panic! "u32WidenAdd: 5+3 failed"

-- u32WidenAdd: with carry
#eval do
  let a : Felt := Felt.ofNat (u32max - 1)
  let b : Felt := Felt.ofNat 3
  let s := mkState [b, a]
  let r := runInst s .u32WidenAdd
  -- (2^32-1) + 3 = 2^32 + 2, lo = 2, carry = 1
  unless checkStack r [2, 1] do panic! "u32WidenAdd: carry failed"

-- u32OverflowAdd: basic (carry on top)
#eval do
  let s := mkState [3, 5]
  let r := runInst s .u32OverflowAdd
  unless checkStack r [0, 8] do panic! "u32OverflowAdd: 5+3 failed"

-- u32WrappingAdd: basic
#eval do
  let s := mkState [3, 5]
  let r := runInst s .u32WrappingAdd
  unless checkStack r [8] do panic! "u32WrappingAdd: 5+3 failed"

-- u32OverflowSub: no borrow
#eval do
  let s := mkState [3, 10]
  let r := runInst s .u32OverflowSub
  unless checkStack r [0, 7] do panic! "u32OverflowSub: 10-3 failed"

-- u32OverflowSub: with borrow
#eval do
  let s := mkState [10, 3]
  let r := runInst s .u32OverflowSub
  -- 3 - 10: borrow=1, diff = 2^32 - 7 = 4294967289
  unless checkStack r [1, Felt.ofNat 4294967289] do panic! "u32OverflowSub: borrow failed"

-- u32WidenMul: basic
#eval do
  let s := mkState [7, 6]
  let r := runInst s .u32WidenMul
  unless checkStack r [42, 0] do panic! "u32WidenMul: 6*7 failed"

-- u32WidenMul: overflow
#eval do
  let a : Felt := Felt.ofNat (u32max - 1)
  let s := mkState [a, a]
  let r := runInst s .u32WidenMul
  -- (2^32-1)^2 = 2^64-2*2^32+1; lo = 1, hi = 2^32-2
  unless checkStack r [1, Felt.ofNat (u32max - 2)] do panic! "u32WidenMul: overflow failed"

-- u32DivMod: basic
#eval do
  let s := mkState [3, 10]
  let r := runInst s .u32DivMod
  -- 10 / 3 = 3 rem 1; result = [rem, quot]
  unless checkStack r [1, 3] do panic! "u32DivMod: 10/3 failed"

-- u32DivMod: by zero fails
#eval do
  let s := mkState [0, 10]
  let r := runInst s .u32DivMod
  unless checkNone r do panic! "u32DivMod: div by zero should fail"

-- u32WidenAdd3: basic
#eval do
  let s := mkState [3, 5, 7]
  let r := runInst s .u32WidenAdd3
  unless checkStack r [15, 0] do panic! "u32WidenAdd3: 7+5+3 failed"

-- u32WidenMadd: basic (a*b+c)
#eval do
  let s := mkState [4, 3, 10]
  let r := runInst s .u32WidenMadd
  -- 3*4 + 10 = 22; lo=22, hi=0
  unless checkStack r [22, 0] do panic! "u32WidenMadd: 3*4+10 failed"

-- u32WrappingMadd: basic (a*b+c) mod 2^32
#eval do
  let s := mkState [4, 3, 10]
  let r := runInst s .u32WrappingMadd
  unless checkStack r [22] do panic! "u32WrappingMadd: 3*4+10 failed"

-- u32WrappingMadd: overflow wraps mod 2^32
#eval do
  let a : Felt := Felt.ofNat (u32max / 2)
  let s := mkState [2, a, 1]
  let r := runInst s .u32WrappingMadd
  -- (2^31 * 2 + 1) mod 2^32 = 1
  unless checkStack r [1] do panic! "u32WrappingMadd: overflow wrap failed"

-- ============================================================================
-- Tier 2: U32 Precondition Enforcement (AC-11)
-- Regression tests: non-u32 inputs must fail
-- ============================================================================

-- u32WidenAdd rejects non-u32 input
#eval do
  let big : Felt := Felt.ofNat (u32max + 1)
  let s := mkState [1, big]
  let r := runInst s .u32WidenAdd
  unless checkNone r do panic! "REGRESSION(u32-precond): u32WidenAdd should reject non-u32"

-- u32OverflowSub rejects non-u32 input
#eval do
  let big : Felt := Felt.ofNat (u32max + 1)
  let s := mkState [big, 1]
  let r := runInst s .u32OverflowSub
  unless checkNone r do panic! "REGRESSION(u32-precond): u32OverflowSub should reject non-u32"

-- u32WidenMul rejects non-u32 input
#eval do
  let big : Felt := Felt.ofNat (u32max + 1)
  let s := mkState [big, 1]
  let r := runInst s .u32WidenMul
  unless checkNone r do panic! "REGRESSION(u32-precond): u32WidenMul should reject non-u32"

-- u32WrappingMadd rejects non-u32 input
#eval do
  let big : Felt := Felt.ofNat (u32max + 1)
  let s := mkState [1, 2, big]
  let r := runInst s .u32WrappingMadd
  unless checkNone r do panic! "REGRESSION(u32-precond): u32WrappingMadd should reject non-u32"

-- u32DivMod rejects non-u32 input
#eval do
  let big : Felt := Felt.ofNat (u32max + 1)
  let s := mkState [1, big]
  let r := runInst s .u32DivMod
  unless checkNone r do panic! "REGRESSION(u32-precond): u32DivMod should reject non-u32"

-- u32Lt rejects non-u32 input
#eval do
  let big : Felt := Felt.ofNat (u32max + 1)
  let s := mkState [big, 1]
  let r := runInst s .u32Lt
  unless checkNone r do panic! "REGRESSION(u32-precond): u32Lt should reject non-u32"

-- u32Clz rejects non-u32 input
#eval do
  let big : Felt := Felt.ofNat (u32max + 1)
  let s := mkState [big]
  let r := runInst s .u32Clz
  unless checkNone r do panic! "REGRESSION(u32-precond): u32Clz should reject non-u32"

-- u32Shl rejects non-u32 value operand
#eval do
  let big : Felt := Felt.ofNat (u32max + 1)
  let s := mkState [1, big]
  let r := runInst s .u32Shl
  unless checkNone r do panic! "REGRESSION(u32-precond): u32Shl should reject non-u32"

-- u32Popcnt rejects non-u32 input
#eval do
  let big : Felt := Felt.ofNat (u32max + 1)
  let s := mkState [big]
  let r := runInst s .u32Popcnt
  unless checkNone r do panic! "REGRESSION(u32-precond): u32Popcnt should reject non-u32"

-- ============================================================================
-- Tier 2: U32 Bitwise (AC-8)
-- ============================================================================

-- u32And: basic
#eval do
  let s := mkState [0xFF, 0x0F]
  let r := runInst s .u32And
  unless checkStack r [0x0F] do panic! "u32And: 0x0F & 0xFF failed"

-- u32Or: basic
#eval do
  let s := mkState [0xF0, 0x0F]
  let r := runInst s .u32Or
  unless checkStack r [0xFF] do panic! "u32Or: 0x0F | 0xF0 failed"

-- u32Xor: basic
#eval do
  let s := mkState [0xFF, 0x0F]
  let r := runInst s .u32Xor
  unless checkStack r [0xF0] do panic! "u32Xor: 0x0F ^ 0xFF failed"

-- u32Not: basic
#eval do
  let s := mkState [0]
  let r := runInst s .u32Not
  unless checkStack r [Felt.ofNat (u32max - 1)] do panic! "u32Not: ~0 failed"

-- u32Shl: shift left by 4
#eval do
  let s := mkState [4, 0xFF]
  let r := runInst s .u32Shl
  unless checkStack r [0xFF0] do panic! "u32Shl: 0xFF << 4 failed"

-- u32Shr: shift right by 4
#eval do
  let s := mkState [4, 0xFF]
  let r := runInst s .u32Shr
  unless checkStack r [0x0F] do panic! "u32Shr: 0xFF >> 4 failed"

-- u32Popcnt: count set bits
#eval do
  let s := mkState [0xFF]
  let r := runInst s .u32Popcnt
  unless checkStack r [8] do panic! "u32Popcnt: popcnt(0xFF) failed"

-- u32Clz: leading zeros
#eval do
  let s := mkState [1]
  let r := runInst s .u32Clz
  unless checkStack r [31] do panic! "u32Clz: clz(1) failed"

-- u32Clz: zero
#eval do
  let s := mkState [0]
  let r := runInst s .u32Clz
  unless checkStack r [32] do panic! "u32Clz: clz(0) failed"

-- u32Ctz: trailing zeros
#eval do
  let s := mkState [8]
  let r := runInst s .u32Ctz
  unless checkStack r [3] do panic! "u32Ctz: ctz(8) failed"

-- u32Clo: leading ones
#eval do
  -- 0xFFFFFFFF has 32 leading ones
  let s := mkState [Felt.ofNat (u32max - 1)]
  let r := runInst s .u32Clo
  unless checkStack r [32] do panic! "u32Clo: clo(0xFFFFFFFF) failed"

-- u32Cto: trailing ones
#eval do
  let s := mkState [7]  -- binary: ...0111
  let r := runInst s .u32Cto
  unless checkStack r [3] do panic! "u32Cto: cto(7) failed"

-- ============================================================================
-- Tier 2: U32 Comparison (AC-9)
-- ============================================================================

-- u32Lt: basic
#eval do
  let s := mkState [10, 5]
  let r := runInst s .u32Lt
  unless checkStack r [1] do panic! "u32Lt: 5<10 failed"

-- u32Lte: equal
#eval do
  let s := mkState [5, 5]
  let r := runInst s .u32Lte
  unless checkStack r [1] do panic! "u32Lte: 5<=5 failed"

-- u32Gt: basic
#eval do
  let s := mkState [5, 10]
  let r := runInst s .u32Gt
  unless checkStack r [1] do panic! "u32Gt: 10>5 failed"

-- u32Min: basic
#eval do
  let s := mkState [10, 3]
  let r := runInst s .u32Min
  unless checkStack r [3] do panic! "u32Min: min(3,10) failed"

-- u32Max: basic
#eval do
  let s := mkState [10, 3]
  let r := runInst s .u32Max
  unless checkStack r [10] do panic! "u32Max: max(3,10) failed"

-- ============================================================================
-- Tier 2: U32 Assertions/Conversions (AC-10)
-- ============================================================================

-- u32Assert: valid
#eval do
  let s := mkState [42]
  let r := runInst s .u32Assert
  unless r.isSome do panic! "u32Assert: 42 should pass"

-- u32Assert: invalid
#eval do
  let s := mkState [Felt.ofNat (u32max + 1)]
  let r := runInst s .u32Assert
  unless checkNone r do panic! "u32Assert: big value should fail"

-- u32Test: u32 value
#eval do
  let s := mkState [42]
  let r := runInst s .u32Test
  unless checkStack r [1, 42] do panic! "u32Test: 42 failed"

-- u32Test: non-u32 value
#eval do
  let s := mkState [Felt.ofNat (u32max + 1)]
  let r := runInst s .u32Test
  unless checkStack r [0, Felt.ofNat (u32max + 1)] do panic! "u32Test: big value failed"

-- u32Cast: truncates to low 32 bits
#eval do
  let s := mkState [Felt.ofNat (u32max + 5)]
  let r := runInst s .u32Cast
  unless checkStack r [5] do panic! "u32Cast: truncation failed"

-- u32Split: splits into lo and hi
#eval do
  let val := u32max + 5  -- hi=1, lo=5
  let s := mkState [Felt.ofNat val]
  let r := runInst s .u32Split
  unless checkStack r [5, 1] do panic! "u32Split: split failed"

-- ============================================================================
-- Tier 3: Assertion Instructions (AC-16)
-- ============================================================================

-- assert: 1 passes
#eval do
  let s := mkState [1, 42]
  let r := runInst s .assert
  unless checkStack r [42] do panic! "assert: 1 should pass"

-- assert: 0 fails
#eval do
  let s := mkState [0, 42]
  let r := runInst s .assert
  unless checkNone r do panic! "assert: 0 should fail"

-- assertz: 0 passes
#eval do
  let s := mkState [0, 42]
  let r := runInst s .assertz
  unless checkStack r [42] do panic! "assertz: 0 should pass"

-- assertz: 1 fails
#eval do
  let s := mkState [1, 42]
  let r := runInst s .assertz
  unless checkNone r do panic! "assertz: 1 should fail"

-- assertEq: equal passes
#eval do
  let s := mkState [5, 5, 42]
  let r := runInst s .assertEq
  unless checkStack r [42] do panic! "assertEq: equal should pass"

-- assertEq: unequal fails
#eval do
  let s := mkState [5, 6, 42]
  let r := runInst s .assertEq
  unless checkNone r do panic! "assertEq: unequal should fail"

-- ============================================================================
-- Tier 3: Advice Stack (AC-14)
-- ============================================================================

-- advPush: push 3 elements from advice
#eval do
  let s := mkStateAdv [99] [10, 20, 30, 40]
  let r := runInst s (.advPush 3)
  -- advice [10,20,30] taken; reverse then prepend
  -- result: [30, 20, 10, 99], remaining advice: [40]
  unless checkStack r [30, 20, 10, 99] do panic! "advPush: 3 elements failed"

-- advPush: insufficient advice fails
#eval do
  let s := mkStateAdv [99] [10]
  let r := runInst s (.advPush 3)
  unless checkNone r do panic! "advPush: insufficient should fail"

-- advLoadW: load word from advice (REGRESSION: was reversed before fix)
#eval do
  let s := mkStateAdv [0, 0, 0, 0, 99] [10, 20, 30, 40]
  let r := runInst s .advLoadW
  -- Fixed: should NOT reverse; advice [10,20,30,40] placed directly
  unless checkStack r [10, 20, 30, 40, 99] do panic! "REGRESSION(advLoadW): element ordering should not be reversed"

-- advLoadW: insufficient advice fails
#eval do
  let s := mkStateAdv [0, 0, 0, 0] [10, 20]
  let r := runInst s .advLoadW
  unless checkNone r do panic! "advLoadW: insufficient should fail"

-- ============================================================================
-- Tier 3: Memory Operations (AC-12)
-- ============================================================================

-- memLoad: basic
#eval do
  let s0 := mkState [0, 42]
  let r1 := runInst s0 .memStore  -- store 42 at address 0
  match r1 with
  | some s1 =>
    let s2 := { s1 with stack := [0] }
    let r2 := runInst s2 .memLoad
    unless checkStack r2 [42] do panic! "memLoad: basic failed"
  | none => panic! "memStore should not fail"

-- memLoad: unwritten address returns zero
#eval do
  let s := mkState [5]
  let r := runInst s .memLoad
  unless checkStack r [0] do panic! "memLoad: unwritten should be zero"

-- memLoad: out of bounds fails
#eval do
  let s := mkState [Felt.ofNat u32max]
  let r := runInst s .memLoad
  unless checkNone r do panic! "memLoad: OOB should fail"

-- locLoad/locStore: basic
#eval do
  let s := mkState [42]
  let r1 := runInst s (.locStore 0)
  match r1 with
  | some s1 =>
    let r2 := runInst s1 (.locLoad 0)
    match r2 with
    | some s2 => unless s2.stack.head! == (42 : Felt) do panic! "locLoad: should read stored value"
    | none => panic! "locLoad should not fail"
  | none => panic! "locStore should not fail"

-- ============================================================================
-- Tier 3: Control Flow (AC-15)
-- ============================================================================

-- ifElse: true branch
#eval do
  let ops : List Op := [
    Op.inst (.push 1),  -- condition
    Op.ifElse
      [Op.inst (.push 42)]   -- then
      [Op.inst (.push 99)]   -- else
  ]
  let s := mkState []
  let r := runOps 10 s ops
  unless checkStack r [42] do panic! "ifElse: true branch failed"

-- ifElse: false branch
#eval do
  let ops : List Op := [
    Op.inst (.push 0),
    Op.ifElse
      [Op.inst (.push 42)]
      [Op.inst (.push 99)]
  ]
  let s := mkState []
  let r := runOps 10 s ops
  unless checkStack r [99] do panic! "ifElse: false branch failed"

-- ifElse: non-binary condition fails
#eval do
  let ops : List Op := [
    Op.inst (.push 5),
    Op.ifElse
      [Op.inst (.push 42)]
      [Op.inst (.push 99)]
  ]
  let s := mkState []
  let r := runOps 10 s ops
  unless checkNone r do panic! "ifElse: non-binary should fail"

-- repeat: 3 iterations
#eval do
  let ops : List Op := [
    Op.inst (.push 0),
    Op.repeat 3 [Op.inst .incr]
  ]
  let s := mkState []
  let r := runOps 10 s ops
  unless checkStack r [3] do panic! "repeat: 3 iterations failed"

-- repeat: 0 iterations
#eval do
  let ops : List Op := [
    Op.inst (.push 42),
    Op.repeat 0 [Op.inst .incr]
  ]
  let s := mkState []
  let r := runOps 10 s ops
  unless checkStack r [42] do panic! "repeat: 0 iterations failed"

-- whileTrue: loop until zero
#eval do
  -- push 3, then loop: decrement and push 1 if nonzero, 0 if zero
  -- We need to push the loop condition. Let's use a simpler test.
  -- Start with [1, 5] on stack. whileTrue pops the 1, executes body.
  -- Body: incr the second element. Push 0 to exit.
  let ops : List Op := [
    Op.inst (.push 1),  -- initial condition: enter loop
    Op.whileTrue [
      Op.inst (.push 0)  -- condition for next iteration: exit
    ]
  ]
  let s := mkState []
  let r := runOps 10 s ops
  -- After: push 1, enter loop (pop 1), push 0, check condition (pop 0), exit
  unless checkStack r [] do panic! "whileTrue: basic failed"

-- ============================================================================
-- Tier 1: Field Comparison – eqw (AC-3)
-- ============================================================================

-- eqw: two equal words → pushes 1, both words preserved
#eval do
  let s := mkState [1, 2, 3, 4, 1, 2, 3, 4]
  let r := runInst s .eqw
  unless checkStack r [1, 1, 2, 3, 4, 1, 2, 3, 4] do panic! "eqw: equal words failed"

-- eqw: two unequal words → pushes 0, both words preserved
#eval do
  let s := mkState [1, 2, 3, 4, 5, 6, 7, 8]
  let r := runInst s .eqw
  unless checkStack r [0, 1, 2, 3, 4, 5, 6, 7, 8] do panic! "eqw: unequal words failed"

-- eqw: words differing in only one element → pushes 0
#eval do
  let s := mkState [1, 2, 3, 4, 1, 2, 99, 4]
  let r := runInst s .eqw
  unless checkStack r [0, 1, 2, 3, 4, 1, 2, 99, 4] do panic! "eqw: one-element diff failed"

-- eqw: insufficient stack depth (fewer than 8 elements) → returns none
#eval do
  let s := mkState [1, 2, 3, 4, 5, 6, 7]
  let r := runInst s .eqw
  unless checkNone r do panic! "eqw: insufficient stack should fail"

-- ============================================================================
-- Tier 3: Local Memory – locStorewBe / locStorewLe (AC-12)
-- ============================================================================

-- locStorewBe: stores top word in big-endian order and preserves stack
-- Per spec: "top of stack is placed at local[i+3]"
-- So stack [e0, e1, e2, e3, ...] → local[i]=e3, local[i+1]=e2, local[i+2]=e1, local[i+3]=e0
#eval do
  let s := mkState [10, 20, 30, 40, 99]
  let r := runInst s (.locStorewBe 0)
  -- stack preserved
  unless checkStack r [10, 20, 30, 40, 99] do panic! "locStorewBe: stack not preserved"
  -- check locals: BE order means top-of-stack (10) → local[3], next (20) → local[2], etc.
  unless checkLocals r [(0, 40), (1, 30), (2, 20), (3, 10)] do
    panic! "locStorewBe: local slot assignments wrong"

-- locStorewLe: stores top word in little-endian order and preserves stack
-- Per spec: "top of stack is placed at local[i]"
-- So stack [e0, e1, e2, e3, ...] → local[i]=e0, local[i+1]=e1, local[i+2]=e2, local[i+3]=e3
#eval do
  let s := mkState [10, 20, 30, 40, 99]
  let r := runInst s (.locStorewLe 0)
  -- stack preserved
  unless checkStack r [10, 20, 30, 40, 99] do panic! "locStorewLe: stack not preserved"
  -- check locals: LE order means top-of-stack (10) → local[0], next (20) → local[1], etc.
  unless checkLocals r [(0, 10), (1, 20), (2, 30), (3, 40)] do
    panic! "locStorewLe: local slot assignments wrong"

-- locStorewBe: insufficient stack (fewer than 4 elements) → returns none
#eval do
  let s := mkState [1, 2, 3]
  let r := runInst s (.locStorewBe 0)
  unless checkNone r do panic! "locStorewBe: insufficient stack should fail"

-- locStorewLe: insufficient stack (fewer than 4 elements) → returns none
#eval do
  let s := mkState [1, 2, 3]
  let r := runInst s (.locStorewLe 0)
  unless checkNone r do panic! "locStorewLe: insufficient stack should fail"

-- ============================================================================
-- Tier 3: Local Memory – locLoadwBe / locLoadwLe (AC-12)
-- ============================================================================

-- locLoadwBe: overwrites top 4 stack elements with locals in big-endian order
-- Per spec: "local[i+3] is placed at the top of the stack"
-- So locals [i]=v0, [i+1]=v1, [i+2]=v2, [i+3]=v3 → stack [v3, v2, v1, v0, ...]
#eval do
  -- First store values to locals via locStorewLe (LE: top→local[0], etc.)
  let s := mkState [100, 200, 300, 400]
  let r1 := runInst s (.locStorewLe 0)
  match r1 with
  | some s1 =>
    -- Now overwrite stack top with placeholders and load back in BE order
    let s2 := { s1 with stack := [0, 0, 0, 0, 99] }
    let r2 := runInst s2 (.locLoadwBe 0)
    -- BE load: local[3]=400 on top, local[2]=300, local[1]=200, local[0]=100
    unless checkStack r2 [400, 300, 200, 100, 99] do panic! "locLoadwBe: element ordering wrong"
  | none => panic! "locStorewLe should not fail"

-- locLoadwLe: overwrites top 4 stack elements with locals in little-endian order
-- Per spec: "local[i] is placed at the top of the stack"
-- So locals [i]=v0, [i+1]=v1, [i+2]=v2, [i+3]=v3 → stack [v0, v1, v2, v3, ...]
#eval do
  -- First store values to locals via locStorewLe (LE: top→local[0], etc.)
  let s := mkState [100, 200, 300, 400]
  let r1 := runInst s (.locStorewLe 0)
  match r1 with
  | some s1 =>
    let s2 := { s1 with stack := [0, 0, 0, 0, 99] }
    let r2 := runInst s2 (.locLoadwLe 0)
    -- LE load: local[0]=100 on top, local[1]=200, local[2]=300, local[3]=400
    unless checkStack r2 [100, 200, 300, 400, 99] do panic! "locLoadwLe: element ordering wrong"
  | none => panic! "locStorewLe should not fail"

-- locLoadwBe: insufficient stack (fewer than 4 elements) → returns none
#eval do
  let s := mkState [1, 2, 3]
  let r := runInst s (.locLoadwBe 0)
  unless checkNone r do panic! "locLoadwBe: insufficient stack should fail"

-- locLoadwLe: insufficient stack (fewer than 4 elements) → returns none
#eval do
  let s := mkState [1, 2, 3]
  let r := runInst s (.locLoadwLe 0)
  unless checkNone r do panic! "locLoadwLe: insufficient stack should fail"

-- ============================================================================
-- Tier 3: Local Memory – Round-trip Tests (AC-12)
-- ============================================================================

-- Round-trip: locStorewBe then locLoadwBe → top 4 elements unchanged
#eval do
  let s := mkState [10, 20, 30, 40, 99]
  let r1 := runInst s (.locStorewBe 0)
  match r1 with
  | some s1 =>
    -- Stack after store is preserved: [10, 20, 30, 40, 99]
    -- Now load back in same endianness
    let r2 := runInst s1 (.locLoadwBe 0)
    unless checkStack r2 [10, 20, 30, 40, 99] do panic! "round-trip BE-BE: stack mismatch"
  | none => panic! "locStorewBe should not fail"

-- Round-trip: locStorewLe then locLoadwLe → top 4 elements unchanged
#eval do
  let s := mkState [10, 20, 30, 40, 99]
  let r1 := runInst s (.locStorewLe 0)
  match r1 with
  | some s1 =>
    let r2 := runInst s1 (.locLoadwLe 0)
    unless checkStack r2 [10, 20, 30, 40, 99] do panic! "round-trip LE-LE: stack mismatch"
  | none => panic! "locStorewLe should not fail"

-- Endianness mismatch: locStorewBe then locLoadwLe → top 4 elements reversed
-- BE store: stack [a,b,c,d] → local[0]=d, local[1]=c, local[2]=b, local[3]=a
-- LE load:  local[0]=d → top, local[1]=c, local[2]=b, local[3]=a → stack [d,c,b,a]
#eval do
  let s := mkState [10, 20, 30, 40, 99]
  let r1 := runInst s (.locStorewBe 0)
  match r1 with
  | some s1 =>
    let r2 := runInst s1 (.locLoadwLe 0)
    unless checkStack r2 [40, 30, 20, 10, 99] do panic! "round-trip BE-LE: should reverse word"
  | none => panic! "locStorewBe should not fail"

-- Endianness mismatch: locStorewLe then locLoadwBe → top 4 elements reversed
-- LE store: stack [a,b,c,d] → local[0]=a, local[1]=b, local[2]=c, local[3]=d
-- BE load:  local[3]=d → top, local[2]=c, local[1]=b, local[0]=a → stack [d,c,b,a]
#eval do
  let s := mkState [10, 20, 30, 40, 99]
  let r1 := runInst s (.locStorewLe 0)
  match r1 with
  | some s1 =>
    let r2 := runInst s1 (.locLoadwBe 0)
    unless checkStack r2 [40, 30, 20, 10, 99] do panic! "round-trip LE-BE: should reverse word"
  | none => panic! "locStorewLe should not fail"

-- Round-trip at nonzero index: locStorewBe.4 then locLoadwBe.4
#eval do
  let s := mkState [5, 6, 7, 8, 99]
  let r1 := runInst s (.locStorewBe 4)
  match r1 with
  | some s1 =>
    let r2 := runInst s1 (.locLoadwBe 4)
    unless checkStack r2 [5, 6, 7, 8, 99] do panic! "round-trip BE-BE idx=4: stack mismatch"
  | none => panic! "locStorewBe should not fail"

-- ============================================================================
-- Summary
-- ============================================================================

-- If we reach here, all tests passed.
-- Total test count: ~120 tests covering all instruction categories.

end MidenLean.Tests
