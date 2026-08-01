import MidenLean.Concrete.State
import MidenLean.Op

namespace MidenLean

open Instruction

-- Stack helpers

/-- Remove the nth element from a list, returning (element, remaining list). -/
def removeNth {α : Type} (l : List α) (n : Nat) : Option (α × List α) :=
  match l[n]? with
  | none => none
  | some v => some (v, l.eraseIdx n)

/-- Insert an element at position n in a list. -/
def insertAt {α : Type} (l : List α) (n : Nat) (v : α) : List α :=
  (l.take n) ++ [v] ++ (l.drop n)

-- U32 arithmetic helpers (operating on natural numbers)

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

-- Instruction execution handlers

-- Assertions

def execAssert (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | a :: rest => if a.val == 1 then some (s.withStack rest) else none
  | _ => none

def execAssertz (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | a :: rest => if a.val == 0 then some (s.withStack rest) else none
  | _ => none

def execAssertEq (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | b :: a :: rest => if a == b then some (s.withStack rest) else none
  | _ => none

def execAssertEqw (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest =>
    if a0 == b0 && a1 == b1 && a2 == b2 && a3 == b3
    then some (s.withStack rest) else none
  | _ => none

/-- Compare the top two words on the stack; push 1 if equal, 0 if not.
    Both words remain on the stack below the result. -/
def execEqw (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest =>
    let result : Felt := if a0 == b0 && a1 == b1 && a2 == b2 && a3 == b3
                         then 1 else 0
    some (s.withStack (result :: b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest))
  | _ => none

-- Stack: drop, pad, push

def execDrop (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | _ :: rest => some (s.withStack rest)
  | _ => none

def execDropw (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | _ :: _ :: _ :: _ :: rest => some (s.withStack rest)
  | _ => none

def execPadw (s : Concrete.State) : Option Concrete.State :=
  some (s.withStack (0 :: 0 :: 0 :: 0 :: s.stack))

def execPush (v : Felt) (s : Concrete.State) : Option Concrete.State :=
  some (s.withStack (v :: s.stack))

def execPushList (vs : List Felt) (s : Concrete.State) : Option Concrete.State :=
  some (s.withStack (vs ++ s.stack))

-- Stack: dup

def execDup (n : Fin 16) (s : Concrete.State) : Option Concrete.State :=
  match s.stack[n.val]? with
  | some v => some (s.withStack (v :: s.stack))
  | none => none

def execDupw (n : Fin 4) (s : Concrete.State) : Option Concrete.State :=
  let base := n.val * 4
  match s.stack[base]?, s.stack[base+1]?, s.stack[base+2]?, s.stack[base+3]? with
  | some a, some b, some c, some d => some (s.withStack (a :: b :: c :: d :: s.stack))
  | _, _, _, _ => none

-- Stack: swap

def execSwap (n : Fin 16) (s : Concrete.State) : Option Concrete.State :=
  if n.val == 0 then some s
  else
    match s.stack[0]?, s.stack[n.val]? with
    | some top, some nth =>
      some (s.withStack (s.stack.set 0 nth |>.set n.val top))
    | _, _ => none

def execSwapw (n : Fin 4) (s : Concrete.State) : Option Concrete.State :=
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

def execSwapdw (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | a0::a1::a2::a3::b0::b1::b2::b3::c0::c1::c2::c3::d0::d1::d2::d3::rest =>
    some (s.withStack (c0::c1::c2::c3::d0::d1::d2::d3::a0::a1::a2::a3::b0::b1::b2::b3::rest))
  | _ => none

-- Stack: move

def execMovup (n : Nat) (s : Concrete.State) : Option Concrete.State :=
  if n < 2 || n > 15 then none
  else
    match removeNth s.stack n with
    | some (v, rest) => some (s.withStack (v :: rest))
    | none => none

def execMovdn (n : Nat) (s : Concrete.State) : Option Concrete.State :=
  if n < 2 || n > 15 then none
  else
    match s.stack with
    | top :: rest => some (s.withStack (insertAt rest n top))
    | _ => none

def execMovupw (n : Nat) (s : Concrete.State) : Option Concrete.State :=
  if n < 2 || n > 3 then none
  else
    let base := n * 4
    if s.stack.length < base + 4 then none
    else
      let before := s.stack.take base
      let word := (s.stack.drop base).take 4
      let after := s.stack.drop (base + 4)
      some (s.withStack (word ++ before ++ after))

def execMovdnw (n : Nat) (s : Concrete.State) : Option Concrete.State :=
  if n < 2 || n > 3 then none
  else
    if s.stack.length < (n + 1) * 4 then none
    else
      let word := s.stack.take 4
      let remaining := s.stack.drop 4
      let before := remaining.take (n * 4)
      let after := remaining.drop (n * 4)
      some (s.withStack (before ++ word ++ after))

def execReversew (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | a :: b :: c :: d :: rest => some (s.withStack (d :: c :: b :: a :: rest))
  | _ => none

-- Conditional operations

def execCswap (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | c :: b :: a :: rest =>
    if c.val == 1 then some (s.withStack (a :: b :: rest))
    else if c.val == 0 then some (s.withStack (b :: a :: rest))
    else none
  | _ => none

def execCswapw (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | c :: b0::b1::b2::b3 :: a0::a1::a2::a3 :: rest =>
    if c.val == 1 then some (s.withStack (a0::a1::a2::a3::b0::b1::b2::b3::rest))
    else if c.val == 0 then some (s.withStack (b0::b1::b2::b3::a0::a1::a2::a3::rest))
    else none
  | _ => none

def execCdrop (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | c :: b :: a :: rest =>
    if c.val == 1 then some (s.withStack (b :: rest))
    else if c.val == 0 then some (s.withStack (a :: rest))
    else none
  | _ => none

def execCdropw (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | c :: b0::b1::b2::b3 :: a0::a1::a2::a3 :: rest =>
    if c.val == 1 then some (s.withStack (b0::b1::b2::b3::rest))
    else if c.val == 0 then some (s.withStack (a0::a1::a2::a3::rest))
    else none
  | _ => none

-- Field arithmetic

def execAdd (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | b :: a :: rest => some (s.withStack ((a + b) :: rest))
  | _ => none

def execAddImm (v : Felt) (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | a :: rest => some (s.withStack ((a + v) :: rest))
  | _ => none

def execSub (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | b :: a :: rest => some (s.withStack ((a - b) :: rest))
  | _ => none

def execSubImm (v : Felt) (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | a :: rest => some (s.withStack ((a - v) :: rest))
  | _ => none

def execMul (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | b :: a :: rest => some (s.withStack ((a * b) :: rest))
  | _ => none

def execMulImm (v : Felt) (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | a :: rest => some (s.withStack ((a * v) :: rest))
  | _ => none

def execDiv (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | b :: a :: rest => if b == 0 then none else some (s.withStack ((a * b⁻¹) :: rest))
  | _ => none

def execDivImm (v : Felt) (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | a :: rest => if v == 0 then none else some (s.withStack ((a * v⁻¹) :: rest))
  | _ => none

def execNeg (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | a :: rest => some (s.withStack ((-a) :: rest))
  | _ => none

def execInv (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | a :: rest => if a == 0 then none else some (s.withStack (a⁻¹ :: rest))
  | _ => none

def execPow2 (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | a :: rest =>
    if a.val > 63 then none
    else some (s.withStack (Felt.ofNat (2^a.val) :: rest))
  | _ => none

def execIncr (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | a :: rest => some (s.withStack ((a + 1) :: rest))
  | _ => none

-- Field comparison

def execEq (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | b :: a :: rest => some (s.withStack ((if a == b then (1 : Felt) else 0) :: rest))
  | _ => none

def execEqImm (v : Felt) (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | a :: rest => some (s.withStack ((if a == v then (1 : Felt) else 0) :: rest))
  | _ => none

def execNeq (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | b :: a :: rest => some (s.withStack ((if a != b then (1 : Felt) else 0) :: rest))
  | _ => none

def execNeqImm (v : Felt) (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | a :: rest => some (s.withStack ((if a != v then (1 : Felt) else 0) :: rest))
  | _ => none

def execLt (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | b :: a :: rest => some (s.withStack ((if a.val < b.val then (1 : Felt) else 0) :: rest))
  | _ => none

def execLte (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | b :: a :: rest => some (s.withStack ((if a.val ≤ b.val then (1 : Felt) else 0) :: rest))
  | _ => none

def execGt (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | b :: a :: rest => some (s.withStack ((if a.val > b.val then (1 : Felt) else 0) :: rest))
  | _ => none

def execGte (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | b :: a :: rest => some (s.withStack ((if a.val ≥ b.val then (1 : Felt) else 0) :: rest))
  | _ => none

def execIsOdd (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | a :: rest => some (s.withStack ((if a.val % 2 == 1 then (1 : Felt) else 0) :: rest))
  | _ => none

-- Field boolean (inputs must be 0 or 1)

def execAnd (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | b :: a :: rest =>
    if a.isBool && b.isBool then some (s.withStack ((a * b) :: rest)) else none
  | _ => none

def execOr (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | b :: a :: rest =>
    if a.isBool && b.isBool then some (s.withStack ((a + b - a * b) :: rest)) else none
  | _ => none

def execXor (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | b :: a :: rest =>
    if a.isBool && b.isBool then some (s.withStack ((a + b - 2 * a * b) :: rest)) else none
  | _ => none

def execNot (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | a :: rest => if a.isBool then some (s.withStack ((1 - a) :: rest)) else none
  | _ => none

-- U32 assertions

def execU32Assert (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | a :: _ => if a.isU32 then some s else none
  | _ => none

def execU32Assert2 (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | b :: a :: _ => if a.isU32 && b.isU32 then some s else none
  | _ => none

def execU32AssertW (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | a :: b :: c :: d :: _ =>
    if a.isU32 && b.isU32 && c.isU32 && d.isU32 then some s else none
  | _ => none

def execU32Test (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | a :: stk => some (s.withStack ((if a.isU32 then (1 : Felt) else 0) :: a :: stk))
  | _ => none

def execU32TestW (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | a :: b :: c :: d :: _ =>
    let result : Felt := if a.isU32 && b.isU32 && c.isU32 && d.isU32 then 1 else 0
    some (s.withStack (result :: s.stack))
  | _ => none

-- U32 conversions

def execU32Cast (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | a :: rest => some (s.withStack (a.lo32 :: rest))
  | _ => none

def execU32Split (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | a :: rest => some (s.withStack (a.lo32 :: a.hi32 :: rest))
  | _ => none

-- U32 arithmetic

def execU32WidenAdd (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | b :: a :: rest =>
    if !a.isU32 || !b.isU32 then none
    else
      let (lo, carry) := u32WideAdd a.val b.val
      some (s.withStack (Felt.ofNat lo :: Felt.ofNat carry :: rest))
  | _ => none

def execU32OverflowAdd (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | b :: a :: rest =>
    if !a.isU32 || !b.isU32 then none
    else
      let (lo, carry) := u32WideAdd a.val b.val
      some (s.withStack (Felt.ofNat carry :: Felt.ofNat lo :: rest))
  | _ => none

def execU32WrappingAdd (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | b :: a :: rest =>
    if !a.isU32 || !b.isU32 then none
    else some (s.withStack (Felt.ofNat (u32WAdd a.val b.val) :: rest))
  | _ => none

def execU32WidenAdd3 (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | c :: b :: a :: rest =>
    if !a.isU32 || !b.isU32 || !c.isU32 then none
    else
      let (lo, carry) := u32WideAdd3 a.val b.val c.val
      some (s.withStack (Felt.ofNat lo :: Felt.ofNat carry :: rest))
  | _ => none

def execU32OverflowAdd3 (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | c :: b :: a :: rest =>
    if !a.isU32 || !b.isU32 || !c.isU32 then none
    else
      let (lo, carry) := u32WideAdd3 a.val b.val c.val
      some (s.withStack (Felt.ofNat carry :: Felt.ofNat lo :: rest))
  | _ => none

def execU32WrappingAdd3 (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | c :: b :: a :: rest =>
    if !a.isU32 || !b.isU32 || !c.isU32 then none
    else
      some (s.withStack (Felt.ofNat ((a.val + b.val + c.val) % u32Max) :: rest))
  | _ => none

def execU32OverflowSub (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | b :: a :: rest =>
    if !a.isU32 || !b.isU32 then none
    else
      let (borrow, diff) := u32OverflowingSub a.val b.val
      some (s.withStack (Felt.ofNat borrow :: Felt.ofNat diff :: rest))
  | _ => none

def execU32WrappingSub (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | b :: a :: rest =>
    if !a.isU32 || !b.isU32 then none
    else
      let (_, diff) := u32OverflowingSub a.val b.val
      some (s.withStack (Felt.ofNat diff :: rest))
  | _ => none

def execU32WidenMul (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | b :: a :: rest =>
    if !a.isU32 || !b.isU32 then none
    else
      let (lo, hi) := u32WideMul a.val b.val
      some (s.withStack (Felt.ofNat lo :: Felt.ofNat hi :: rest))
  | _ => none

def execU32WrappingMul (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | b :: a :: rest =>
    if !a.isU32 || !b.isU32 then none
    else
      some (s.withStack (Felt.ofNat ((a.val * b.val) % u32Max) :: rest))
  | _ => none

def execU32WidenMadd (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | b :: a :: c :: rest =>
    if !a.isU32 || !b.isU32 || !c.isU32 then none
    else
      let (lo, hi) := u32WideMadd a.val b.val c.val
      some (s.withStack (Felt.ofNat lo :: Felt.ofNat hi :: rest))
  | _ => none

def execU32WrappingMadd (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | b :: a :: c :: rest =>
    if !a.isU32 || !b.isU32 || !c.isU32 then none
    else
      some (s.withStack (Felt.ofNat ((a.val * b.val + c.val) % u32Max) :: rest))
  | _ => none

def execU32DivMod (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | b :: a :: rest =>
    if !a.isU32 || !b.isU32 then none
    else if b.val == 0 then none
    else some (s.withStack (Felt.ofNat (a.val % b.val) :: Felt.ofNat (a.val / b.val) :: rest))
  | _ => none

def execU32Div (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | b :: a :: rest =>
    if !a.isU32 || !b.isU32 then none
    else if b.val == 0 then none
    else some (s.withStack (Felt.ofNat (a.val / b.val) :: rest))
  | _ => none

def execU32Mod (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | b :: a :: rest =>
    if !a.isU32 || !b.isU32 then none
    else if b.val == 0 then none
    else some (s.withStack (Felt.ofNat (a.val % b.val) :: rest))
  | _ => none

-- U32 bitwise

def execU32And (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | b :: a :: rest =>
    if !a.isU32 || !b.isU32 then none
    else some (s.withStack (Felt.ofNat (a.val &&& b.val) :: rest))
  | _ => none

def execU32Or (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | b :: a :: rest =>
    if !a.isU32 || !b.isU32 then none
    else some (s.withStack (Felt.ofNat (a.val ||| b.val) :: rest))
  | _ => none

def execU32Xor (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | b :: a :: rest =>
    if !a.isU32 || !b.isU32 then none
    else some (s.withStack (Felt.ofNat (a.val ^^^ b.val) :: rest))
  | _ => none

def execU32Not (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | a :: rest =>
    if !a.isU32 then none
    else some (s.withStack (Felt.ofNat (u32Max - 1 - a.val) :: rest))
  | _ => none

def execU32Shl (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | b :: a :: rest =>
    if !a.isU32 || !b.isU32 then none
    else if b.val > 31 then none
    else some (s.withStack (Felt.ofNat ((a.val * 2^b.val) % u32Max) :: rest))
  | _ => none

def execU32ShlImm (n : Nat) (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | a :: rest =>
    if !a.isU32 then none
    else if n > 31 then none
    else some (s.withStack (Felt.ofNat ((a.val * 2^n) % u32Max) :: rest))
  | _ => none

def execU32Shr (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | b :: a :: rest =>
    if !a.isU32 || !b.isU32 then none
    else if b.val > 31 then none
    else some (s.withStack (Felt.ofNat (a.val / 2^b.val) :: rest))
  | _ => none

def execU32ShrImm (n : Nat) (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | a :: rest =>
    if !a.isU32 then none
    else if n > 31 then none
    else some (s.withStack (Felt.ofNat (a.val / 2^n) :: rest))
  | _ => none

def execU32Rotl (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | b :: a :: rest =>
    if !a.isU32 || !b.isU32 then none
    else if b.val > 31 then none
    else some (s.withStack (Felt.ofNat (u32RotateLeft a.val b.val) :: rest))
  | _ => none

def execU32RotlImm (n : Nat) (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | a :: rest =>
    if !a.isU32 then none
    else if n > 31 then none
    else some (s.withStack (Felt.ofNat (u32RotateLeft a.val n) :: rest))
  | _ => none

def execU32Rotr (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | b :: a :: rest =>
    if !a.isU32 || !b.isU32 then none
    else if b.val > 31 then none
    else some (s.withStack (Felt.ofNat (u32RotateRight a.val b.val) :: rest))
  | _ => none

def execU32RotrImm (n : Nat) (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | a :: rest =>
    if !a.isU32 then none
    else if n > 31 then none
    else some (s.withStack (Felt.ofNat (u32RotateRight a.val n) :: rest))
  | _ => none

def execU32Popcnt (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | a :: rest =>
    if !a.isU32 then none
    else some (s.withStack (Felt.ofNat (u32PopCount a.val) :: rest))
  | _ => none

def execU32Clz (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | a :: rest =>
    if !a.isU32 then none
    else some (s.withStack (Felt.ofNat (u32CountLeadingZeros a.val) :: rest))
  | _ => none

def execU32Ctz (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | a :: rest =>
    if !a.isU32 then none
    else some (s.withStack (Felt.ofNat (u32CountTrailingZeros a.val) :: rest))
  | _ => none

def execU32Clo (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | a :: rest =>
    if !a.isU32 then none
    else some (s.withStack (Felt.ofNat (u32CountLeadingOnes a.val) :: rest))
  | _ => none

def execU32Cto (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | a :: rest =>
    if !a.isU32 then none
    else some (s.withStack (Felt.ofNat (u32CountTrailingOnes a.val) :: rest))
  | _ => none

-- U32 comparison

def execU32Lt (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | b :: a :: rest =>
    if !a.isU32 || !b.isU32 then none
    else some (s.withStack ((if a.val < b.val then (1 : Felt) else 0) :: rest))
  | _ => none

def execU32Lte (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | b :: a :: rest =>
    if !a.isU32 || !b.isU32 then none
    else some (s.withStack ((if a.val ≤ b.val then (1 : Felt) else 0) :: rest))
  | _ => none

def execU32Gt (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | b :: a :: rest =>
    if !a.isU32 || !b.isU32 then none
    else some (s.withStack ((if a.val > b.val then (1 : Felt) else 0) :: rest))
  | _ => none

def execU32Gte (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | b :: a :: rest =>
    if !a.isU32 || !b.isU32 then none
    else some (s.withStack ((if a.val ≥ b.val then (1 : Felt) else 0) :: rest))
  | _ => none

def execU32Min (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | b :: a :: rest =>
    if !a.isU32 || !b.isU32 then none
    else some (s.withStack ((if a.val ≤ b.val then a else b) :: rest))
  | _ => none

def execU32Max (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | b :: a :: rest =>
    if !a.isU32 || !b.isU32 then none
    else some (s.withStack ((if a.val ≥ b.val then a else b) :: rest))
  | _ => none

-- Memory

def execMemLoad (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | a :: rest =>
    if a.val >= u32Max then none
    else some (s.withStack (s.memory a.val :: rest))
  | _ => none

def execMemLoadImm (addr : Nat) (s : Concrete.State) : Option Concrete.State :=
  if addr >= u32Max then none
  else some (s.withStack (s.memory addr :: s.stack))

def execMemStore (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | a :: v :: rest =>
    if a.val >= u32Max then none
    else some ((s.writeMemory a.val v).withStack rest)
  | _ => none

def execMemStoreImm (addr : Nat) (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | v :: rest =>
    if addr >= u32Max then none
    else some ((s.writeMemory addr v).withStack rest)
  | _ => none

def execMemStorewBe (s : Concrete.State) : Option Concrete.State :=
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

def execMemStorewBeImm (addr : Nat) (s : Concrete.State) : Option Concrete.State :=
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

def execMemStorewLe (s : Concrete.State) : Option Concrete.State :=
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

def execMemStorewLeImm (addr : Nat) (s : Concrete.State) : Option Concrete.State :=
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

def execMemLoadwBe (s : Concrete.State) : Option Concrete.State :=
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

def execMemLoadwBeImm (addr : Nat) (s : Concrete.State) : Option Concrete.State :=
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

def execMemLoadwLe (s : Concrete.State) : Option Concrete.State :=
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

def execMemLoadwLeImm (addr : Nat) (s : Concrete.State) : Option Concrete.State :=
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

/-- Round a local count up to the next multiple of 4 (word-aligned). -/
def alignLocals (n : Nat) : Nat :=
  (n + 3) / 4 * 4

/-- Base address (relative to `LOCAL_MEM_BASE`) of a fresh local frame pushed
    on top of `frames`. Mirrors the inline allocation in `execProcedure`.
    Statement-level mentions of frame allocation should use this named
    function rather than an inline `match`: unreduced copies of the match
    inside reflected proof terms get duplicated per local-memory address and
    blow the kernel's recursion limit during defeq checking. -/
def localsBase : List LocalFrame → Nat
  | [] => 0
  | f :: _ => f.base + f.alignedNumLocals

/-- Get the current (topmost) local frame, if any. -/
def currentFrame (frames : List LocalFrame) : Option LocalFrame :=
  frames.head?

-- Procedure locals (frame-aware)

def execLocLoad (idx : Nat) (s : Concrete.State) : Option Concrete.State :=
  do
    let v ← s.readLocal? idx
    pure (s.withStack (v :: s.stack))

def execLocStore (idx : Nat) (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | v :: rest =>
      do
        let s' ← s.writeLocal? idx v
        pure (s'.withStack rest)
  | _ => none

/-- Store the top word to locals at index `idx` in big-endian order.
    The word remains on the stack.
    Requires `idx % 4 = 0` and `idx + 4 ≤ frame.numLocals`. -/
def execLocStorewBe (idx : Nat) (s : Concrete.State) : Option Concrete.State :=
  match s.stack, currentFrame s.frames with
  | e0 :: e1 :: e2 :: e3 :: rest, some frame =>
    if idx % 4 != 0 || idx + 4 > frame.numLocals then none
    else
      let baseAddr := frame.localAddr idx
      let s' := s.writeMemory baseAddr e3
        |>.writeMemory (baseAddr + 1) e2
        |>.writeMemory (baseAddr + 2) e1
        |>.writeMemory (baseAddr + 3) e0
      some (s'.withStack (e0 :: e1 :: e2 :: e3 :: rest))
  | _, _ => none

/-- Store the top word to locals at index `idx` in little-endian order.
    The word remains on the stack.
    Requires `idx % 4 = 0` and `idx + 4 ≤ frame.numLocals`. -/
def execLocStorewLe (idx : Nat) (s : Concrete.State) : Option Concrete.State :=
  match s.stack, currentFrame s.frames with
  | e0 :: e1 :: e2 :: e3 :: rest, some frame =>
    if idx % 4 != 0 || idx + 4 > frame.numLocals then none
    else
      let baseAddr := frame.localAddr idx
      let s' := s.writeMemory baseAddr e0
        |>.writeMemory (baseAddr + 1) e1
        |>.writeMemory (baseAddr + 2) e2
        |>.writeMemory (baseAddr + 3) e3
      some (s'.withStack (e0 :: e1 :: e2 :: e3 :: rest))
  | _, _ => none

/-- Load a word from locals at index `idx` in big-endian order,
    overwriting the top word on the stack.
    Requires `idx % 4 = 0` and `idx + 4 ≤ frame.numLocals`. -/
def execLocLoadwBe (idx : Nat) (s : Concrete.State) : Option Concrete.State :=
  match s.stack, currentFrame s.frames with
  | _ :: _ :: _ :: _ :: rest, some frame =>
    if idx % 4 != 0 || idx + 4 > frame.numLocals then none
    else
      let baseAddr := frame.localAddr idx
      let e3 := s.memory baseAddr
      let e2 := s.memory (baseAddr + 1)
      let e1 := s.memory (baseAddr + 2)
      let e0 := s.memory (baseAddr + 3)
      some (s.withStack (e0 :: e1 :: e2 :: e3 :: rest))
  | _, _ => none

/-- Load a word from locals at index `idx` in little-endian order,
    overwriting the top word on the stack.
    Requires `idx % 4 = 0` and `idx + 4 ≤ frame.numLocals`. -/
def execLocLoadwLe (idx : Nat) (s : Concrete.State) : Option Concrete.State :=
  match s.stack, currentFrame s.frames with
  | _ :: _ :: _ :: _ :: rest, some frame =>
    if idx % 4 != 0 || idx + 4 > frame.numLocals then none
    else
      let baseAddr := frame.localAddr idx
      let e0 := s.memory baseAddr
      let e1 := s.memory (baseAddr + 1)
      let e2 := s.memory (baseAddr + 2)
      let e3 := s.memory (baseAddr + 3)
      some (s.withStack (e0 :: e1 :: e2 :: e3 :: rest))
  | _, _ => none

/-- Push the absolute address of local slot `idx` onto the stack.
    Requires an active frame and `idx < frame.numLocals`. -/
def execLocAddr (idx : Nat) (s : Concrete.State) : Option Concrete.State :=
  do
    let addr ← s.localAddr? idx
    pure (s.withStack (Felt.ofNat addr :: s.stack))

-- Advice stack

def execAdvPush (n : Nat) (s : Concrete.State) : Option Concrete.State :=
  if s.advice.length < n then none
  else
    let vals := s.advice.take n
    let adv' := s.advice.drop n
    some ((s.withAdvice adv').withStack (vals.reverse ++ s.stack))

def execAdvLoadW (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | _ :: _ :: _ :: _ :: rest =>
    if s.advice.length < 4 then none
    else
      let vals := s.advice.take 4
      let adv' := s.advice.drop 4
      some ((s.withAdvice adv').withStack (vals ++ rest))
  | _ => none

-- Events

def execEmit (s : Concrete.State) : Option Concrete.State :=
  match s.stack with
  | _ :: _ => some s
  | _ => none

-- Single instruction dispatch

/-- Execute a single instruction by dispatching to the appropriate handler. -/
def execInstruction (s : Concrete.State) (i : Instruction) : Option Concrete.State :=
  match i with
  | .nop => some s
  | .assert => execAssert s
  | .assertWithError _ => execAssert s
  | .assertz => execAssertz s
  | .assertzWithError _ => execAssertz s
  | .assertEq => execAssertEq s
  | .assertEqWithError _ => execAssertEq s
  | .assertEqw => execAssertEqw s
  | .eqw => execEqw s
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
  | .locLoadwBe idx => execLocLoadwBe idx s
  | .locLoadwLe idx => execLocLoadwLe idx s
  | .locStorewBe idx => execLocStorewBe idx s
  | .locStorewLe idx => execLocStorewLe idx s
  | .locaddr idx => execLocAddr idx s
  | .advPush n => execAdvPush n s
  | .advLoadW => execAdvLoadW s
  | .emit => execEmit s
  | .emitImm _ => some s  -- events are no-ops in semantics
  | .exec _ => none  -- handled at Op level

-- Op execution (with procedure environment)

/-- A procedure environment maps procedure names to their bodies. -/
def ProcEnv := String → Option Procedure

/-- Execute a procedure given a procedure environment.
    For procedures with `numLocals = 0`, this directly folds over the op list.
    For procedures with `numLocals > 0`, a local frame is allocated before
    execution and deallocated on return. -/
def execProcedure (env : ProcEnv) (fuel : Nat) (s : Concrete.State) (proc : Procedure) : Option Concrete.State :=
  match proc with
  | ⟨_, numLocals, ops⟩ =>
    match fuel with
    | 0 => none  -- out of fuel
    | fuel' + 1 =>
      match numLocals with
      | 0 =>
        -- Fast path: no frame allocation, exactly as before
        ops.foldlM (fun state op =>
          match op with
          | Op.inst (Instruction.exec target) =>
            match env target with
            | some callee => execProcedure env fuel' state callee
            | none => none
          | Op.inst i => execInstruction state i
          | Op.ifElse thenBlk elseBlk =>
            match state.stack with
            | cond :: rest =>
              if cond.val == 1 then
                execProcedure env fuel' (state.withStack rest) thenBlk
              else if cond.val == 0 then
                execProcedure env fuel' (state.withStack rest) elseBlk
              else none
            | _ => none
          | Op.repeat count body =>
            doRepeat fuel' count body state
          | Op.whileTrue body =>
            doWhile fuel' fuel' body state
        ) s
      | _ + 1 =>
        -- Allocate a local frame for the procedure
        let aligned := alignLocals numLocals
        let base := match s.frames with
          | [] => 0
          | f :: _ => f.base + f.alignedNumLocals
        let frame : LocalFrame := { base, numLocals, alignedNumLocals := aligned }
        let s' := { s with frames := frame :: s.frames }
        let result := ops.foldlM (fun state op =>
          match op with
          | Op.inst (Instruction.exec target) =>
            match env target with
            | some callee => execProcedure env fuel' state callee
            | none => none
          | Op.inst i => execInstruction state i
          | Op.ifElse thenBlk elseBlk =>
            match state.stack with
            | cond :: rest =>
              if cond.val == 1 then
                execProcedure env fuel' (state.withStack rest) thenBlk
              else if cond.val == 0 then
                execProcedure env fuel' (state.withStack rest) elseBlk
              else none
            | _ => none
          | Op.repeat count body =>
            doRepeat fuel' count body state
          | Op.whileTrue body =>
            doWhile fuel' fuel' body state
        ) s'
        -- Deallocate the frame on return
        match result with
        | some r => some { r with frames := s.frames }
        | none => none
where
  doRepeat (fuel : Nat) (n : Nat) (body : List Op) (st : Concrete.State) : Option Concrete.State :=
    match n with
    | 0 => some st
    | n' + 1 =>
      match execProcedure env fuel st body with
      | some st' => doRepeat fuel n' body st'
      | none => none
  doWhile (fuel : Nat) (f : Nat) (body : List Op) (st : Concrete.State) : Option Concrete.State :=
    match f with
    | 0 => none
    | f' + 1 =>
      match st.stack with
      | cond :: rest =>
        if cond.val == 1 then
          match execProcedure env fuel (st.withStack rest) body with
          | some st' => doWhile fuel f' body st'
          | none => none
        else if cond.val == 0 then some (st.withStack rest)
        else none
      | _ => none

/-- Execute a list of operations given a procedure environment.
    This is the low-level block executor used by control-flow blocks and proof chunking. -/
def execOps (env : ProcEnv) (fuel : Nat) (s : Concrete.State) (ops : List Op) : Option Concrete.State :=
  execProcedure env fuel s ops

/-- An empty procedure environment (no inter-procedure calls). -/
def emptyEnv : ProcEnv := fun _ => none

/-- Executing an anonymous compatibility wrapper is the same as executing its body. -/
theorem execProcedure_ofOps (env : ProcEnv) (fuel : Nat) (s : Concrete.State) (ops : List Op) :
    execProcedure env fuel s (Procedure.ofOps ops) = execProcedure env fuel s ops := by
  cases fuel <;> simp [execProcedure, Procedure.ofOps]

/-- Executing a named wrapper with `numLocals = 0` is the same as executing its body. -/
theorem execProcedure_ofNameOps
    (env : ProcEnv) (fuel : Nat) (s : Concrete.State)
    (name : String) (numLocals : Nat) (ops : List Op) (h : numLocals = 0) :
    execProcedure env fuel s (Procedure.ofNameOps name numLocals ops) = execProcedure env fuel s ops := by
  subst h; cases fuel <;> simp [execProcedure, Procedure.ofOps, Procedure.ofNameOps]

/-- Compatibility aliases for proofs which refer to the block executor's loop helpers. -/
abbrev execOps.doRepeat := execProcedure.doRepeat
abbrev execOps.doWhile := execProcedure.doWhile

/-- Concrete execution of a basic block as a foldlM of execInstruction. -/
def Concrete.execBlock (insts : List Instruction) (cs : Concrete.State) :
    Option Concrete.State :=
  insts.foldlM (fun s i => execInstruction s i) cs

end MidenLean
