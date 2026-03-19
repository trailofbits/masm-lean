import MidenLean.State
import MidenLean.Op

namespace MidenLean

open Instruction

-- ============================================================================
-- Stack helpers
-- ============================================================================

/-- Remove the nth element from a list, returning (element, remaining list). -/
def removeNth {α : Type} (l : List α) (n : Nat) : Option (α × List α) :=
  match l[n]? with
  | none => none
  | some v => some (v, l.eraseIdx n)

/-- Insert an element at position n in a list. -/
def insertAt {α : Type} (l : List α) (n : Nat) (v : α) : List α :=
  (l.take n) ++ [v] ++ (l.drop n)

-- ============================================================================
-- U32 arithmetic helpers (operating on natural numbers)
-- ============================================================================

def u32Max : Nat := 2^32

/-- Wrapping u32 addition. -/
def u32WAdd (a b : Nat) : Nat := (a + b) % u32Max

/-- Widening u32 addition: returns (lo, carry). -/
def u32WideAdd (a b : Nat) : Nat × Nat :=
  let sum := a + b
  (sum % u32Max, sum / u32Max)

/-- Widening u32 addition of three values: returns (lo, carry). -/
def u32WideAdd3 (a b c : Nat) : Nat × Nat :=
  let sum := a + b + c
  (sum % u32Max, sum / u32Max)

/-- Overflowing u32 subtraction: returns (borrow, result).
    borrow = 1 if a < b. result = (a - b) mod 2^32. -/
def u32OverflowingSub (a b : Nat) : Nat × Nat :=
  if a >= b then (0, a - b)
  else (1, u32Max - b + a)

/-- Widening u32 multiplication: returns (lo, hi). -/
def u32WideMul (a b : Nat) : Nat × Nat :=
  let prod := a * b
  (prod % u32Max, prod / u32Max)

/-- Widening multiply-add: a * b + c, returns (lo, hi). -/
def u32WideMadd (a b c : Nat) : Nat × Nat :=
  let result := a * b + c
  (result % u32Max, result / u32Max)

/-- Left-rotate a 32-bit value by b bits. -/
def u32RotateLeft (a b : Nat) : Nat :=
  ((a * 2^b) % u32Max) ||| (a / 2^(32 - b))

/-- Right-rotate a 32-bit value by b bits. -/
def u32RotateRight (a b : Nat) : Nat :=
  (a / 2^b) ||| ((a * 2^(32 - b)) % u32Max)

/-- Count leading zeros of a 32-bit value. -/
def u32CountLeadingZeros (n : Nat) : Nat :=
  if n == 0 then 32
  else
    let rec go (count : Nat) : (fuel : Nat) → Nat
      | 0 => count
      | fuel + 1 =>
        let bit := 32 - count
        if n >= 2^(bit - 1) then count
        else go (count + 1) fuel
    go 0 32

/-- Count trailing zeros of a 32-bit value. -/
def u32CountTrailingZeros (n : Nat) : Nat :=
  if n == 0 then 32
  else
    let rec go (bit : Nat) : (fuel : Nat) → Nat
      | 0 => bit
      | fuel + 1 =>
        if bit >= 32 then bit
        else if n % 2^(bit + 1) != 0 then bit
        else go (bit + 1) fuel
    go 0 32

/-- Count leading ones of a 32-bit value. -/
def u32CountLeadingOnes (n : Nat) : Nat :=
  u32CountLeadingZeros (u32Max - 1 - n)

/-- Count trailing ones of a 32-bit value. -/
def u32CountTrailingOnes (n : Nat) : Nat :=
  u32CountTrailingZeros (n ^^^ (u32Max - 1))

/-- Population count (number of set bits) of a 32-bit value. -/
def u32PopCount (n : Nat) : Nat :=
  let rec go (v : Nat) (count : Nat) : (bits : Nat) → Nat
    | 0 => count
    | bits + 1 => go (v / 2) (count + v % 2) bits
  go n 0 32

-- ============================================================================
-- Instruction execution handlers
-- ============================================================================
-- Reference: miden-vm processor/src/execution/operations/
--   Dispatch:   mod.rs (execute_op)
--   Stack ops:  stack_ops/mod.rs
--   Field ops:  field_ops/mod.rs
--   U32 ops:    u32_ops/mod.rs
--   IO ops:     io_ops/mod.rs
--   Sys ops:    sys_ops/mod.rs
--
-- Many high-level MASM instructions are compiled to sequences of
-- low-level VM operations. Where this applies, the comment notes
-- "compiled" and the compilation source file.

-- Assertions
-- Ref: sys_ops/mod.rs op_assert (lines 20-34)

def execAssert (s : MidenState) : Option MidenState :=
  match s.stack with
  | a :: rest => if a.val == 1 then some (s.withStack rest) else none
  | _ => none

def execAssertz (s : MidenState) : Option MidenState :=
  match s.stack with
  | a :: rest => if a.val == 0 then some (s.withStack rest) else none
  | _ => none

def execAssertEq (s : MidenState) : Option MidenState :=
  match s.stack with
  | b :: a :: rest => if a == b then some (s.withStack rest) else none
  | _ => none

def execAssertEqw (s : MidenState) : Option MidenState :=
  match s.stack with
  | b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest =>
    if a0 == b0 && a1 == b1 && a2 == b2 && a3 == b3
    then some (s.withStack rest) else none
  | _ => none

-- Stack: drop, pad, push
-- Ref: mod.rs execute_op (inline, line ~173-181 for drop)

def execDrop (s : MidenState) : Option MidenState :=
  match s.stack with
  | _ :: rest => some (s.withStack rest)
  | _ => none

def execDropw (s : MidenState) : Option MidenState :=
  match s.stack with
  | _ :: _ :: _ :: _ :: rest => some (s.withStack rest)
  | _ => none

def execPadw (s : MidenState) : Option MidenState :=
  some (s.withStack (0 :: 0 :: 0 :: 0 :: s.stack))

def execPush (v : Felt) (s : MidenState) : Option MidenState :=
  some (s.withStack (v :: s.stack))

def execPushList (vs : List Felt) (s : MidenState) : Option MidenState :=
  some (s.withStack (vs ++ s.stack))

-- Stack: dup
-- Ref: stack_ops/mod.rs dup_nth (lines 64-76)

def execDup (n : Fin 16) (s : MidenState) : Option MidenState :=
  match s.stack[n.val]? with
  | some v => some (s.withStack (v :: s.stack))
  | none => none

def execDupw (n : Fin 4) (s : MidenState) : Option MidenState :=
  let base := n.val * 4
  match s.stack[base]?, s.stack[base+1]?, s.stack[base+2]?, s.stack[base+3]? with
  | some a, some b, some c, some d => some (s.withStack (a :: b :: c :: d :: s.stack))
  | _, _, _, _ => none

-- Stack: swap
-- Ref: stack_ops/mod.rs op_swap (lines 41-44)
-- swapw: mod.rs execute_op (lines 195-206)

def execSwap (n : Fin 16) (s : MidenState) : Option MidenState :=
  if n.val == 0 then some s
  else
    match s.stack[0]?, s.stack[n.val]? with
    | some top, some nth =>
      some (s.withStack (s.stack.set 0 nth |>.set n.val top))
    | _, _ => none

def execSwapw (n : Fin 4) (s : MidenState) : Option MidenState :=
  if n.val == 0 then some s
  else
    let base := n.val * 4
    match s.stack[0]?, s.stack[1]?, s.stack[2]?, s.stack[3]?,
          s.stack[base]?, s.stack[base+1]?, s.stack[base+2]?, s.stack[base+3]? with
    | some a0, some a1, some a2, some a3,
      some b0, some b1, some b2, some b3 =>
      let stk' := s.stack
        |>.set 0 b0 |>.set 1 b1 |>.set 2 b2 |>.set 3 b3
        |>.set base a0 |>.set (base+1) a1 |>.set (base+2) a2 |>.set (base+3) a3
      some (s.withStack stk')
    | _, _, _, _, _, _, _, _ => none

def execSwapdw (s : MidenState) : Option MidenState :=
  match s.stack with
  | a0::a1::a2::a3::b0::b1::b2::b3::c0::c1::c2::c3::d0::d1::d2::d3::rest =>
    some (s.withStack (c0::c1::c2::c3::d0::d1::d2::d3::a0::a1::a2::a3::b0::b1::b2::b3::rest))
  | _ => none

-- Stack: move
-- Ref: mod.rs execute_op (lines 208-263)
-- movup N: stack.rotate_left(N); movdn N: stack.rotate_right(N)

def execMovup (n : Nat) (s : MidenState) : Option MidenState :=
  if n < 2 || n > 15 then none
  else
    match removeNth s.stack n with
    | some (v, rest) => some (s.withStack (v :: rest))
    | none => none

def execMovdn (n : Nat) (s : MidenState) : Option MidenState :=
  if n < 2 || n > 15 then none
  else
    match s.stack with
    | top :: rest => some (s.withStack (insertAt rest n top))
    | _ => none

def execMovupw (n : Nat) (s : MidenState) : Option MidenState :=
  if n < 2 || n > 3 then none
  else
    let base := n * 4
    if s.stack.length < base + 4 then none
    else
      let before := s.stack.take base
      let word := (s.stack.drop base).take 4
      let after := s.stack.drop (base + 4)
      some (s.withStack (word ++ before ++ after))

def execMovdnw (n : Nat) (s : MidenState) : Option MidenState :=
  if n < 2 || n > 3 then none
  else
    if s.stack.length < (n + 1) * 4 then none
    else
      let word := s.stack.take 4
      let remaining := s.stack.drop 4
      let before := remaining.take (n * 4)
      let after := remaining.drop (n * 4)
      some (s.withStack (before ++ word ++ after))

def execReversew (s : MidenState) : Option MidenState :=
  match s.stack with
  | a :: b :: c :: d :: rest => some (s.withStack (d :: c :: b :: a :: rest))
  | _ => none

-- Conditional operations
-- Ref: stack_ops/mod.rs op_cswap (84-104), op_cswapw (112-135)
-- cdrop/cdropw are compiled: not native VM operations

def execCswap (s : MidenState) : Option MidenState :=
  match s.stack with
  | c :: b :: a :: rest =>
    if c.val == 1 then some (s.withStack (a :: b :: rest))
    else if c.val == 0 then some (s.withStack (b :: a :: rest))
    else none
  | _ => none

def execCswapw (s : MidenState) : Option MidenState :=
  match s.stack with
  | c :: b0::b1::b2::b3 :: a0::a1::a2::a3 :: rest =>
    if c.val == 1 then some (s.withStack (a0::a1::a2::a3::b0::b1::b2::b3::rest))
    else if c.val == 0 then some (s.withStack (b0::b1::b2::b3::a0::a1::a2::a3::rest))
    else none
  | _ => none

def execCdrop (s : MidenState) : Option MidenState :=
  match s.stack with
  | c :: b :: a :: rest =>
    if c.val == 1 then some (s.withStack (b :: rest))
    else if c.val == 0 then some (s.withStack (a :: rest))
    else none
  | _ => none

def execCdropw (s : MidenState) : Option MidenState :=
  match s.stack with
  | c :: b0::b1::b2::b3 :: a0::a1::a2::a3 :: rest =>
    if c.val == 1 then some (s.withStack (b0::b1::b2::b3::rest))
    else if c.val == 0 then some (s.withStack (a0::a1::a2::a3::rest))
    else none
  | _ => none

-- Field arithmetic
-- Ref: field_ops/mod.rs
-- add: op_add (18-24), mul: op_mul (38-44), neg: op_neg (29-33)
-- inv: op_inv (52-61); fails on ZERO
-- sub is compiled to [neg, add]; div is compiled to [inv, mul]

def execAdd (s : MidenState) : Option MidenState :=
  match s.stack with
  | b :: a :: rest => some (s.withStack ((a + b) :: rest))
  | _ => none

def execAddImm (v : Felt) (s : MidenState) : Option MidenState :=
  match s.stack with
  | a :: rest => some (s.withStack ((a + v) :: rest))
  | _ => none

def execSub (s : MidenState) : Option MidenState :=
  match s.stack with
  | b :: a :: rest => some (s.withStack ((a - b) :: rest))
  | _ => none

def execSubImm (v : Felt) (s : MidenState) : Option MidenState :=
  match s.stack with
  | a :: rest => some (s.withStack ((a - v) :: rest))
  | _ => none

def execMul (s : MidenState) : Option MidenState :=
  match s.stack with
  | b :: a :: rest => some (s.withStack ((a * b) :: rest))
  | _ => none

def execMulImm (v : Felt) (s : MidenState) : Option MidenState :=
  match s.stack with
  | a :: rest => some (s.withStack ((a * v) :: rest))
  | _ => none

def execDiv (s : MidenState) : Option MidenState :=
  match s.stack with
  | b :: a :: rest => if b == 0 then none else some (s.withStack ((a * b⁻¹) :: rest))
  | _ => none

def execDivImm (v : Felt) (s : MidenState) : Option MidenState :=
  match s.stack with
  | a :: rest => if v == 0 then none else some (s.withStack ((a * v⁻¹) :: rest))
  | _ => none

def execNeg (s : MidenState) : Option MidenState :=
  match s.stack with
  | a :: rest => some (s.withStack ((-a) :: rest))
  | _ => none

def execInv (s : MidenState) : Option MidenState :=
  match s.stack with
  | a :: rest => if a == 0 then none else some (s.withStack (a⁻¹ :: rest))
  | _ => none

def execPow2 (s : MidenState) : Option MidenState :=
  match s.stack with
  | a :: rest =>
    if a.val > 63 then none
    else some (s.withStack (Felt.ofNat (2^a.val) :: rest))
  | _ => none

def execIncr (s : MidenState) : Option MidenState :=
  match s.stack with
  | a :: rest => some (s.withStack ((a + 1) :: rest))
  | _ => none

-- Field comparison
-- Ref: field_ops/mod.rs op_eq (133-148)
-- eqImm: compiled to [push imm, eq]
-- lt/gt/lte/gte: field element comparisons by .val (natural order)

def execEq (s : MidenState) : Option MidenState :=
  match s.stack with
  | b :: a :: rest => some (s.withStack ((if a == b then (1 : Felt) else 0) :: rest))
  | _ => none

def execEqImm (v : Felt) (s : MidenState) : Option MidenState :=
  match s.stack with
  | a :: rest => some (s.withStack ((if a == v then (1 : Felt) else 0) :: rest))
  | _ => none

def execNeq (s : MidenState) : Option MidenState :=
  match s.stack with
  | b :: a :: rest => some (s.withStack ((if a != b then (1 : Felt) else 0) :: rest))
  | _ => none

def execNeqImm (v : Felt) (s : MidenState) : Option MidenState :=
  match s.stack with
  | a :: rest => some (s.withStack ((if a != v then (1 : Felt) else 0) :: rest))
  | _ => none

def execLt (s : MidenState) : Option MidenState :=
  match s.stack with
  | b :: a :: rest => some (s.withStack ((if a.val < b.val then (1 : Felt) else 0) :: rest))
  | _ => none

def execLte (s : MidenState) : Option MidenState :=
  match s.stack with
  | b :: a :: rest => some (s.withStack ((if a.val ≤ b.val then (1 : Felt) else 0) :: rest))
  | _ => none

def execGt (s : MidenState) : Option MidenState :=
  match s.stack with
  | b :: a :: rest => some (s.withStack ((if a.val > b.val then (1 : Felt) else 0) :: rest))
  | _ => none

def execGte (s : MidenState) : Option MidenState :=
  match s.stack with
  | b :: a :: rest => some (s.withStack ((if a.val ≥ b.val then (1 : Felt) else 0) :: rest))
  | _ => none

def execIsOdd (s : MidenState) : Option MidenState :=
  match s.stack with
  | a :: rest => some (s.withStack ((if a.val % 2 == 1 then (1 : Felt) else 0) :: rest))
  | _ => none

-- Field boolean (inputs must be 0 or 1)
-- Ref: field_ops/mod.rs op_and (77-88), op_or (97-108), op_not (116-128)
-- VM validates both operands are binary (0 or 1); fails otherwise
-- xor: compiled to [dup0, dup2, or, movdn2, and, not, and]

def execAnd (s : MidenState) : Option MidenState :=
  match s.stack with
  | b :: a :: rest =>
    if a.isBool && b.isBool then some (s.withStack ((a * b) :: rest)) else none
  | _ => none

def execOr (s : MidenState) : Option MidenState :=
  match s.stack with
  | b :: a :: rest =>
    if a.isBool && b.isBool then some (s.withStack ((a + b - a * b) :: rest)) else none
  | _ => none

def execXor (s : MidenState) : Option MidenState :=
  match s.stack with
  | b :: a :: rest =>
    if a.isBool && b.isBool then some (s.withStack ((a + b - 2 * a * b) :: rest)) else none
  | _ => none

def execNot (s : MidenState) : Option MidenState :=
  match s.stack with
  | a :: rest => if a.isBool then some (s.withStack ((1 - a) :: rest)) else none
  | _ => none

-- U32 assertions
-- Ref: u32_ops/mod.rs op_u32assert2 (301-313)

def execU32Assert (s : MidenState) : Option MidenState :=
  match s.stack with
  | a :: _ => if a.isU32 then some s else none
  | _ => none

def execU32Assert2 (s : MidenState) : Option MidenState :=
  match s.stack with
  | b :: a :: _ => if a.isU32 && b.isU32 then some s else none
  | _ => none

def execU32AssertW (s : MidenState) : Option MidenState :=
  match s.stack with
  | a :: b :: c :: d :: _ =>
    if a.isU32 && b.isU32 && c.isU32 && d.isU32 then some s else none
  | _ => none

def execU32Test (s : MidenState) : Option MidenState :=
  match s.stack with
  | a :: stk => some (s.withStack ((if a.isU32 then (1 : Felt) else 0) :: a :: stk))
  | _ => none

def execU32TestW (s : MidenState) : Option MidenState :=
  match s.stack with
  | a :: b :: c :: d :: _ =>
    let result : Felt := if a.isU32 && b.isU32 && c.isU32 && d.isU32 then 1 else 0
    some (s.withStack (result :: s.stack))
  | _ => none

-- U32 conversions

def execU32Cast (s : MidenState) : Option MidenState :=
  match s.stack with
  | a :: rest => some (s.withStack (a.lo32 :: rest))
  | _ => none

def execU32Split (s : MidenState) : Option MidenState :=
  match s.stack with
  | a :: rest => some (s.withStack (a.lo32 :: a.hi32 :: rest))
  | _ => none

-- U32 arithmetic
-- Ref: u32_ops/mod.rs
-- u32add: op_u32add (80-96), output [carry, sum] on stack
-- u32add3: op_u32add3 (106-128), output [carry, sum]
-- u32sub: op_u32sub (137-153), output [borrow, diff]
-- u32mul: op_u32mul (161-175), output [hi, lo]
-- u32madd: op_u32madd (184-204), computes a*b+c, output [hi, lo]
-- Note: many MASM names differ from low-level VM op names.
-- "Widen" variants push both lo and hi; "Overflow" swaps order;
-- "Wrapping" discards overflow.

def execU32WidenAdd (s : MidenState) : Option MidenState :=
  match s.stack with
  | b :: a :: rest =>
    if !a.isU32 || !b.isU32 then none
    else
      let (lo, carry) := u32WideAdd a.val b.val
      some (s.withStack (Felt.ofNat lo :: Felt.ofNat carry :: rest))
  | _ => none

def execU32OverflowAdd (s : MidenState) : Option MidenState :=
  match s.stack with
  | b :: a :: rest =>
    if !a.isU32 || !b.isU32 then none
    else
      let (lo, carry) := u32WideAdd a.val b.val
      some (s.withStack (Felt.ofNat carry :: Felt.ofNat lo :: rest))
  | _ => none

def execU32WrappingAdd (s : MidenState) : Option MidenState :=
  match s.stack with
  | b :: a :: rest =>
    if !a.isU32 || !b.isU32 then none
    else some (s.withStack (Felt.ofNat (u32WAdd a.val b.val) :: rest))
  | _ => none

def execU32WidenAdd3 (s : MidenState) : Option MidenState :=
  match s.stack with
  | c :: b :: a :: rest =>
    if !a.isU32 || !b.isU32 || !c.isU32 then none
    else
      let (lo, carry) := u32WideAdd3 a.val b.val c.val
      some (s.withStack (Felt.ofNat lo :: Felt.ofNat carry :: rest))
  | _ => none

def execU32OverflowAdd3 (s : MidenState) : Option MidenState :=
  match s.stack with
  | c :: b :: a :: rest =>
    if !a.isU32 || !b.isU32 || !c.isU32 then none
    else
      let (lo, carry) := u32WideAdd3 a.val b.val c.val
      some (s.withStack (Felt.ofNat carry :: Felt.ofNat lo :: rest))
  | _ => none

def execU32WrappingAdd3 (s : MidenState) : Option MidenState :=
  match s.stack with
  | c :: b :: a :: rest =>
    if !a.isU32 || !b.isU32 || !c.isU32 then none
    else
      some (s.withStack (Felt.ofNat ((a.val + b.val + c.val) % u32Max) :: rest))
  | _ => none

def execU32OverflowSub (s : MidenState) : Option MidenState :=
  match s.stack with
  | b :: a :: rest =>
    if !a.isU32 || !b.isU32 then none
    else
      let (borrow, diff) := u32OverflowingSub a.val b.val
      some (s.withStack (Felt.ofNat borrow :: Felt.ofNat diff :: rest))
  | _ => none

def execU32WrappingSub (s : MidenState) : Option MidenState :=
  match s.stack with
  | b :: a :: rest =>
    if !a.isU32 || !b.isU32 then none
    else
      let (_, diff) := u32OverflowingSub a.val b.val
      some (s.withStack (Felt.ofNat diff :: rest))
  | _ => none

def execU32WidenMul (s : MidenState) : Option MidenState :=
  match s.stack with
  | b :: a :: rest =>
    if !a.isU32 || !b.isU32 then none
    else
      let (lo, hi) := u32WideMul a.val b.val
      some (s.withStack (Felt.ofNat lo :: Felt.ofNat hi :: rest))
  | _ => none

def execU32WrappingMul (s : MidenState) : Option MidenState :=
  match s.stack with
  | b :: a :: rest =>
    if !a.isU32 || !b.isU32 then none
    else
      some (s.withStack (Felt.ofNat ((a.val * b.val) % u32Max) :: rest))
  | _ => none

def execU32WidenMadd (s : MidenState) : Option MidenState :=
  match s.stack with
  | b :: a :: c :: rest =>
    if !a.isU32 || !b.isU32 || !c.isU32 then none
    else
      let (lo, hi) := u32WideMadd a.val b.val c.val
      some (s.withStack (Felt.ofNat lo :: Felt.ofNat hi :: rest))
  | _ => none

def execU32WrappingMadd (s : MidenState) : Option MidenState :=
  match s.stack with
  | b :: a :: c :: rest =>
    if !a.isU32 || !b.isU32 || !c.isU32 then none
    else
      some (s.withStack (Felt.ofNat ((a.val * b.val + c.val) % u32Max) :: rest))
  | _ => none

def execU32DivMod (s : MidenState) : Option MidenState :=
  match s.stack with
  | b :: a :: rest =>
    if !a.isU32 || !b.isU32 then none
    else if b.val == 0 then none
    else some (s.withStack (Felt.ofNat (a.val % b.val) :: Felt.ofNat (a.val / b.val) :: rest))
  | _ => none

def execU32Div (s : MidenState) : Option MidenState :=
  match s.stack with
  | b :: a :: rest =>
    if !a.isU32 || !b.isU32 then none
    else if b.val == 0 then none
    else some (s.withStack (Felt.ofNat (a.val / b.val) :: rest))
  | _ => none

def execU32Mod (s : MidenState) : Option MidenState :=
  match s.stack with
  | b :: a :: rest =>
    if !a.isU32 || !b.isU32 then none
    else if b.val == 0 then none
    else some (s.withStack (Felt.ofNat (a.val % b.val) :: rest))
  | _ => none

-- U32 bitwise
-- Ref: u32_ops/mod.rs op_u32and (253-270), op_u32xor (278-295)
-- u32or: compiled to [dup1, dup1, u32and, neg, add, add]
-- u32not: compiled in assembly
-- u32shl/shr/rotl/rotr: compiled from assembly instructions
-- u32clz/ctz/clo/cto/popcnt: compiled from assembly

def execU32And (s : MidenState) : Option MidenState :=
  match s.stack with
  | b :: a :: rest =>
    if !a.isU32 || !b.isU32 then none
    else some (s.withStack (Felt.ofNat (a.val &&& b.val) :: rest))
  | _ => none

def execU32Or (s : MidenState) : Option MidenState :=
  match s.stack with
  | b :: a :: rest =>
    if !a.isU32 || !b.isU32 then none
    else some (s.withStack (Felt.ofNat (a.val ||| b.val) :: rest))
  | _ => none

def execU32Xor (s : MidenState) : Option MidenState :=
  match s.stack with
  | b :: a :: rest =>
    if !a.isU32 || !b.isU32 then none
    else some (s.withStack (Felt.ofNat (a.val ^^^ b.val) :: rest))
  | _ => none

def execU32Not (s : MidenState) : Option MidenState :=
  match s.stack with
  | a :: rest =>
    if !a.isU32 then none
    else some (s.withStack (Felt.ofNat (u32Max - 1 - a.val) :: rest))
  | _ => none

def execU32Shl (s : MidenState) : Option MidenState :=
  match s.stack with
  | b :: a :: rest =>
    if !a.isU32 || !b.isU32 then none
    else if b.val > 31 then none
    else some (s.withStack (Felt.ofNat ((a.val * 2^b.val) % u32Max) :: rest))
  | _ => none

def execU32ShlImm (n : Nat) (s : MidenState) : Option MidenState :=
  match s.stack with
  | a :: rest =>
    if !a.isU32 then none
    else if n > 31 then none
    else some (s.withStack (Felt.ofNat ((a.val * 2^n) % u32Max) :: rest))
  | _ => none

def execU32Shr (s : MidenState) : Option MidenState :=
  match s.stack with
  | b :: a :: rest =>
    if !a.isU32 || !b.isU32 then none
    else if b.val > 31 then none
    else some (s.withStack (Felt.ofNat (a.val / 2^b.val) :: rest))
  | _ => none

def execU32ShrImm (n : Nat) (s : MidenState) : Option MidenState :=
  match s.stack with
  | a :: rest =>
    if !a.isU32 then none
    else if n > 31 then none
    else some (s.withStack (Felt.ofNat (a.val / 2^n) :: rest))
  | _ => none

def execU32Rotl (s : MidenState) : Option MidenState :=
  match s.stack with
  | b :: a :: rest =>
    if !a.isU32 || !b.isU32 then none
    else if b.val > 31 then none
    else some (s.withStack (Felt.ofNat (u32RotateLeft a.val b.val) :: rest))
  | _ => none

def execU32RotlImm (n : Nat) (s : MidenState) : Option MidenState :=
  match s.stack with
  | a :: rest =>
    if !a.isU32 then none
    else if n > 31 then none
    else some (s.withStack (Felt.ofNat (u32RotateLeft a.val n) :: rest))
  | _ => none

def execU32Rotr (s : MidenState) : Option MidenState :=
  match s.stack with
  | b :: a :: rest =>
    if !a.isU32 || !b.isU32 then none
    else if b.val > 31 then none
    else some (s.withStack (Felt.ofNat (u32RotateRight a.val b.val) :: rest))
  | _ => none

def execU32RotrImm (n : Nat) (s : MidenState) : Option MidenState :=
  match s.stack with
  | a :: rest =>
    if !a.isU32 then none
    else if n > 31 then none
    else some (s.withStack (Felt.ofNat (u32RotateRight a.val n) :: rest))
  | _ => none

def execU32Popcnt (s : MidenState) : Option MidenState :=
  match s.stack with
  | a :: rest =>
    if !a.isU32 then none
    else some (s.withStack (Felt.ofNat (u32PopCount a.val) :: rest))
  | _ => none

def execU32Clz (s : MidenState) : Option MidenState :=
  match s.stack with
  | a :: rest =>
    if !a.isU32 then none
    else some (s.withStack (Felt.ofNat (u32CountLeadingZeros a.val) :: rest))
  | _ => none

def execU32Ctz (s : MidenState) : Option MidenState :=
  match s.stack with
  | a :: rest =>
    if !a.isU32 then none
    else some (s.withStack (Felt.ofNat (u32CountTrailingZeros a.val) :: rest))
  | _ => none

def execU32Clo (s : MidenState) : Option MidenState :=
  match s.stack with
  | a :: rest =>
    if !a.isU32 then none
    else some (s.withStack (Felt.ofNat (u32CountLeadingOnes a.val) :: rest))
  | _ => none

def execU32Cto (s : MidenState) : Option MidenState :=
  match s.stack with
  | a :: rest =>
    if !a.isU32 then none
    else some (s.withStack (Felt.ofNat (u32CountTrailingOnes a.val) :: rest))
  | _ => none

-- U32 comparison
-- Ref: compiled from assembly (u32_ops.rs in crates/assembly)

def execU32Lt (s : MidenState) : Option MidenState :=
  match s.stack with
  | b :: a :: rest =>
    if !a.isU32 || !b.isU32 then none
    else some (s.withStack ((if a.val < b.val then (1 : Felt) else 0) :: rest))
  | _ => none

def execU32Lte (s : MidenState) : Option MidenState :=
  match s.stack with
  | b :: a :: rest =>
    if !a.isU32 || !b.isU32 then none
    else some (s.withStack ((if a.val ≤ b.val then (1 : Felt) else 0) :: rest))
  | _ => none

def execU32Gt (s : MidenState) : Option MidenState :=
  match s.stack with
  | b :: a :: rest =>
    if !a.isU32 || !b.isU32 then none
    else some (s.withStack ((if a.val > b.val then (1 : Felt) else 0) :: rest))
  | _ => none

def execU32Gte (s : MidenState) : Option MidenState :=
  match s.stack with
  | b :: a :: rest =>
    if !a.isU32 || !b.isU32 then none
    else some (s.withStack ((if a.val ≥ b.val then (1 : Felt) else 0) :: rest))
  | _ => none

def execU32Min (s : MidenState) : Option MidenState :=
  match s.stack with
  | b :: a :: rest =>
    if !a.isU32 || !b.isU32 then none
    else some (s.withStack ((if a.val ≤ b.val then a else b) :: rest))
  | _ => none

def execU32Max (s : MidenState) : Option MidenState :=
  match s.stack with
  | b :: a :: rest =>
    if !a.isU32 || !b.isU32 then none
    else some (s.withStack ((if a.val ≥ b.val then a else b) :: rest))
  | _ => none

-- Memory
-- Ref: io_ops/mod.rs
-- mloadw: op_mloadw (76-102), mload: op_mload (158-176)
-- mstorew: op_mstorew (116-147), mstore: op_mstore (187-210)
-- locLoad/locStore: compiled to absolute address + mload/mstore

def execMemLoad (s : MidenState) : Option MidenState :=
  match s.stack with
  | a :: rest =>
    if a.val >= u32Max then none
    else some (s.withStack (s.memory a.val :: rest))
  | _ => none

def execMemLoadImm (addr : Nat) (s : MidenState) : Option MidenState :=
  if addr >= u32Max then none
  else some (s.withStack (s.memory addr :: s.stack))

def execMemStore (s : MidenState) : Option MidenState :=
  match s.stack with
  | a :: v :: rest =>
    if a.val >= u32Max then none
    else some ((s.writeMemory a.val v).withStack rest)
  | _ => none

def execMemStoreImm (addr : Nat) (s : MidenState) : Option MidenState :=
  match s.stack with
  | v :: rest =>
    if addr >= u32Max then none
    else some ((s.writeMemory addr v).withStack rest)
  | _ => none

def execMemStorewBe (s : MidenState) : Option MidenState :=
  match s.stack with
  | a :: e0 :: e1 :: e2 :: e3 :: rest =>
    if a.val >= u32Max || a.val % 4 != 0 then none
    else
      let addr := a.val
      let s' := s.writeMemory addr e3
        |>.writeMemory (addr+1) e2
        |>.writeMemory (addr+2) e1
        |>.writeMemory (addr+3) e0
      some (s'.withStack (e0 :: e1 :: e2 :: e3 :: rest))
  | _ => none

def execMemStorewBeImm (addr : Nat) (s : MidenState) : Option MidenState :=
  match s.stack with
  | e0 :: e1 :: e2 :: e3 :: rest =>
    if addr >= u32Max || addr % 4 != 0 then none
    else
      let s' := s.writeMemory addr e3
        |>.writeMemory (addr+1) e2
        |>.writeMemory (addr+2) e1
        |>.writeMemory (addr+3) e0
      some (s'.withStack (e0 :: e1 :: e2 :: e3 :: rest))
  | _ => none

def execMemStorewLe (s : MidenState) : Option MidenState :=
  match s.stack with
  | a :: e0 :: e1 :: e2 :: e3 :: rest =>
    if a.val >= u32Max || a.val % 4 != 0 then none
    else
      let addr := a.val
      let s' := s.writeMemory addr e0
        |>.writeMemory (addr+1) e1
        |>.writeMemory (addr+2) e2
        |>.writeMemory (addr+3) e3
      some (s'.withStack (e0 :: e1 :: e2 :: e3 :: rest))
  | _ => none

def execMemStorewLeImm (addr : Nat) (s : MidenState) : Option MidenState :=
  match s.stack with
  | e0 :: e1 :: e2 :: e3 :: rest =>
    if addr >= u32Max || addr % 4 != 0 then none
    else
      let s' := s.writeMemory addr e0
        |>.writeMemory (addr+1) e1
        |>.writeMemory (addr+2) e2
        |>.writeMemory (addr+3) e3
      some (s'.withStack (e0 :: e1 :: e2 :: e3 :: rest))
  | _ => none

def execMemLoadwBe (s : MidenState) : Option MidenState :=
  match s.stack with
  | a :: _ :: _ :: _ :: _ :: rest =>
    if a.val >= u32Max || a.val % 4 != 0 then none
    else
      let addr := a.val
      let e3 := s.memory addr
      let e2 := s.memory (addr+1)
      let e1 := s.memory (addr+2)
      let e0 := s.memory (addr+3)
      some (s.withStack (e0 :: e1 :: e2 :: e3 :: rest))
  | _ => none

def execMemLoadwBeImm (addr : Nat) (s : MidenState) : Option MidenState :=
  match s.stack with
  | _ :: _ :: _ :: _ :: rest =>
    if addr >= u32Max || addr % 4 != 0 then none
    else
      let e3 := s.memory addr
      let e2 := s.memory (addr+1)
      let e1 := s.memory (addr+2)
      let e0 := s.memory (addr+3)
      some (s.withStack (e0 :: e1 :: e2 :: e3 :: rest))
  | _ => none

def execMemLoadwLe (s : MidenState) : Option MidenState :=
  match s.stack with
  | a :: _ :: _ :: _ :: _ :: rest =>
    if a.val >= u32Max || a.val % 4 != 0 then none
    else
      let addr := a.val
      let e0 := s.memory addr
      let e1 := s.memory (addr+1)
      let e2 := s.memory (addr+2)
      let e3 := s.memory (addr+3)
      some (s.withStack (e0 :: e1 :: e2 :: e3 :: rest))
  | _ => none

def execMemLoadwLeImm (addr : Nat) (s : MidenState) : Option MidenState :=
  match s.stack with
  | _ :: _ :: _ :: _ :: rest =>
    if addr >= u32Max || addr % 4 != 0 then none
    else
      let e0 := s.memory addr
      let e1 := s.memory (addr+1)
      let e2 := s.memory (addr+2)
      let e3 := s.memory (addr+3)
      some (s.withStack (e0 :: e1 :: e2 :: e3 :: rest))
  | _ => none

-- Procedure locals

def execLocLoad (idx : Nat) (s : MidenState) : Option MidenState :=
  some (s.withStack (s.locals idx :: s.stack))

def execLocStore (idx : Nat) (s : MidenState) : Option MidenState :=
  match s.stack with
  | v :: rest => some ((s.writeLocal idx v).withStack rest)
  | _ => none

-- Advice stack
-- Ref: io_ops/mod.rs op_advpop (22-37)
--
-- advPush.N is compiled to N consecutive ADVPOP operations.
-- Each ADVPOP pops ONE element from the advice stack top and
-- pushes it onto the operand stack. After N pops, the N values
-- appear in REVERSE order on the operand stack relative to
-- their original position on the advice stack.
--
-- Example: advice stack = [a, b, c, ...] (a on top)
--   advPush.2 executes ADVPOP twice:
--     pop a -> operand stack [a, ...]
--     pop b -> operand stack [b, a, ...]
--   Result: operand stack has [b, a, ...] (reversed!)
--
-- In this model, s.advice is a list with head = top.
-- vals.reverse gives the correct operand stack ordering.
def execAdvPush (n : Nat) (s : MidenState) : Option MidenState :=
  if s.advice.length < n then none
  else
    let vals := s.advice.take n
    let adv' := s.advice.drop n
    some ((s.withAdvice adv').withStack (vals.reverse ++ s.stack))

-- Ref: io_ops/mod.rs op_advpopw (45-60)
-- advLoadW pops a 4-element word from the advice stack and
-- OVERWRITES the top 4 operand stack elements (no reversal).
-- Comment in VM source: "word[0] at top"
def execAdvLoadW (s : MidenState) : Option MidenState :=
  match s.stack with
  | _ :: _ :: _ :: _ :: rest =>
    if s.advice.length < 4 then none
    else
      let vals := s.advice.take 4
      let adv' := s.advice.drop 4
      some ((s.withAdvice adv').withStack (vals ++ rest))
  | _ => none

-- Events
-- Ref: emit is an async operation; dispatches to host event handler.
-- emitImm: compiled to [push event_id, emit]
-- In this model, both are no-ops (we don't model host events).

def execEmit (s : MidenState) : Option MidenState :=
  match s.stack with
  | _ :: _ => some s
  | _ => none

-- ============================================================================
-- Single instruction dispatch
-- ============================================================================

/-- Execute a single instruction by dispatching to the appropriate handler. -/
def execInstruction (s : MidenState) (i : Instruction) : Option MidenState :=
  match i with
  | .nop => some s
  | .assert => execAssert s
  | .assertWithError _ => execAssert s
  | .assertz => execAssertz s
  | .assertzWithError _ => execAssertz s
  | .assertEq => execAssertEq s
  | .assertEqWithError _ => execAssertEq s
  | .assertEqw => execAssertEqw s
  | .drop => execDrop s
  | .dropw => execDropw s
  | .padw => execPadw s
  | .dup n => execDup n s
  | .dupw n => execDupw n s
  | .swap n => execSwap n s
  | .swapw n => execSwapw n s
  | .swapdw => execSwapdw s
  | .movup n => execMovup n s
  | .movdn n => execMovdn n s
  | .movupw n => execMovupw n s
  | .movdnw n => execMovdnw n s
  | .reversew => execReversew s
  | .cswap => execCswap s
  | .cswapw => execCswapw s
  | .cdrop => execCdrop s
  | .cdropw => execCdropw s
  | .push v => execPush v s
  | .pushList vs => execPushList vs s
  | .add => execAdd s
  | .addImm v => execAddImm v s
  | .sub => execSub s
  | .subImm v => execSubImm v s
  | .mul => execMul s
  | .mulImm v => execMulImm v s
  | .div => execDiv s
  | .divImm v => execDivImm v s
  | .neg => execNeg s
  | .inv => execInv s
  | .pow2 => execPow2 s
  | .incr => execIncr s
  | .eq => execEq s
  | .eqImm v => execEqImm v s
  | .neq => execNeq s
  | .neqImm v => execNeqImm v s
  | .lt => execLt s
  | .lte => execLte s
  | .gt => execGt s
  | .gte => execGte s
  | .isOdd => execIsOdd s
  | .and => execAnd s
  | .or => execOr s
  | .xor => execXor s
  | .not => execNot s
  | .u32Assert => execU32Assert s
  | .u32Assert2 => execU32Assert2 s
  | .u32AssertW => execU32AssertW s
  | .u32Test => execU32Test s
  | .u32TestW => execU32TestW s
  | .u32Cast => execU32Cast s
  | .u32Split => execU32Split s
  | .u32WidenAdd => execU32WidenAdd s
  | .u32OverflowAdd => execU32OverflowAdd s
  | .u32WrappingAdd => execU32WrappingAdd s
  | .u32WidenAdd3 => execU32WidenAdd3 s
  | .u32OverflowAdd3 => execU32OverflowAdd3 s
  | .u32WrappingAdd3 => execU32WrappingAdd3 s
  | .u32OverflowSub => execU32OverflowSub s
  | .u32WrappingSub => execU32WrappingSub s
  | .u32WidenMul => execU32WidenMul s
  | .u32WrappingMul => execU32WrappingMul s
  | .u32WidenMadd => execU32WidenMadd s
  | .u32WrappingMadd => execU32WrappingMadd s
  | .u32DivMod => execU32DivMod s
  | .u32Div => execU32Div s
  | .u32Mod => execU32Mod s
  | .u32And => execU32And s
  | .u32Or => execU32Or s
  | .u32Xor => execU32Xor s
  | .u32Not => execU32Not s
  | .u32Shl => execU32Shl s
  | .u32ShlImm n => execU32ShlImm n s
  | .u32Shr => execU32Shr s
  | .u32ShrImm n => execU32ShrImm n s
  | .u32Rotl => execU32Rotl s
  | .u32RotlImm n => execU32RotlImm n s
  | .u32Rotr => execU32Rotr s
  | .u32RotrImm n => execU32RotrImm n s
  | .u32Popcnt => execU32Popcnt s
  | .u32Clz => execU32Clz s
  | .u32Ctz => execU32Ctz s
  | .u32Clo => execU32Clo s
  | .u32Cto => execU32Cto s
  | .u32Lt => execU32Lt s
  | .u32Lte => execU32Lte s
  | .u32Gt => execU32Gt s
  | .u32Gte => execU32Gte s
  | .u32Min => execU32Min s
  | .u32Max => execU32Max s
  | .memLoad => execMemLoad s
  | .memLoadImm addr => execMemLoadImm addr s
  | .memStore => execMemStore s
  | .memStoreImm addr => execMemStoreImm addr s
  | .memStorewBe => execMemStorewBe s
  | .memStorewBeImm addr => execMemStorewBeImm addr s
  | .memStorewLe => execMemStorewLe s
  | .memStorewLeImm addr => execMemStorewLeImm addr s
  | .memLoadwBe => execMemLoadwBe s
  | .memLoadwBeImm addr => execMemLoadwBeImm addr s
  | .memLoadwLe => execMemLoadwLe s
  | .memLoadwLeImm addr => execMemLoadwLeImm addr s
  | .locLoad idx => execLocLoad idx s
  | .locStore idx => execLocStore idx s
  | .advPush n => execAdvPush n s
  | .advLoadW => execAdvLoadW s
  | .emit => execEmit s
  | .emitImm _ => some s  -- events are no-ops in semantics
  | .exec _ => none  -- handled at Op level

-- ============================================================================
-- Op execution (with procedure environment)
-- ============================================================================

/-- A procedure environment maps procedure names to their bodies. -/
def ProcEnv := String → Option (List Op)

/-- Execute a list of operations given a procedure environment.
    `fuel` bounds recursion to ensure termination. -/
def execWithEnv (env : ProcEnv) (fuel : Nat) (s : MidenState) (ops : List Op) : Option MidenState :=
  match fuel with
  | 0 => none  -- out of fuel
  | fuel' + 1 =>
    ops.foldlM (fun state op =>
      match op with
      | Op.inst (Instruction.exec target) =>
        match env target with
        | some body => execWithEnv env fuel' state body
        | none => none
      | Op.inst i => execInstruction state i
      | Op.ifElse thenBlk elseBlk =>
        match state.stack with
        | cond :: rest =>
          if cond.val == 1 then
            execWithEnv env fuel' (state.withStack rest) thenBlk
          else if cond.val == 0 then
            execWithEnv env fuel' (state.withStack rest) elseBlk
          else none
        | _ => none
      | Op.repeat count body =>
        doRepeat fuel' count body state
      | Op.whileTrue body =>
        doWhile fuel' fuel' body state
    ) s
where
  doRepeat (fuel : Nat) (n : Nat) (body : List Op) (st : MidenState) : Option MidenState :=
    match n with
    | 0 => some st
    | n' + 1 =>
      match execWithEnv env fuel st body with
      | some st' => doRepeat fuel n' body st'
      | none => none
  doWhile (fuel : Nat) (f : Nat) (body : List Op) (st : MidenState) : Option MidenState :=
    match f with
    | 0 => none
    | f' + 1 =>
      match st.stack with
      | cond :: rest =>
        if cond.val == 1 then
          match execWithEnv env fuel (st.withStack rest) body with
          | some st' => doWhile fuel f' body st'
          | none => none
        else if cond.val == 0 then some (st.withStack rest)
        else none
      | _ => none

/-- Execute with an empty procedure environment. -/
def exec (fuel : Nat) (s : MidenState) (ops : List Op) : Option MidenState :=
  execWithEnv (fun _ => none) fuel s ops

/-- Execute with a list of named procedures as environment. -/
def execWithProcs (procs : List Procedure) (fuel : Nat) (s : MidenState) (ops : List Op)
    : Option MidenState :=
  execWithEnv (fun name => Procedure.lookup procs name) fuel s ops

end MidenLean
