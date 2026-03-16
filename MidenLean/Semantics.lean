import MidenLean.State
import MidenLean.Op

namespace MidenLean

open Instruction

-- ============================================================================
-- Stack helpers
-- ============================================================================

/-- Remove the nth element from a list, returning (element, remaining list). -/
private def removeNth {α : Type} (l : List α) (n : Nat) : Option (α × List α) :=
  match l[n]? with
  | none => none
  | some v => some (v, l.eraseIdx n)

/-- Insert an element at position n in a list. -/
private def insertAt {α : Type} (l : List α) (n : Nat) (v : α) : List α :=
  (l.take n) ++ [v] ++ (l.drop n)

-- ============================================================================
-- U32 arithmetic helpers (operating on natural numbers)
-- ============================================================================

private def u32Max : Nat := 2^32

/-- Wrapping u32 addition. -/
private def u32WAdd (a b : Nat) : Nat := (a + b) % u32Max

/-- Widening u32 addition: returns (lo, carry). -/
private def u32WideAdd (a b : Nat) : Nat × Nat :=
  let sum := a + b
  (sum % u32Max, sum / u32Max)

/-- Widening u32 addition of three values: returns (lo, carry). -/
private def u32WideAdd3 (a b c : Nat) : Nat × Nat :=
  let sum := a + b + c
  (sum % u32Max, sum / u32Max)

/-- Overflowing u32 subtraction: returns (borrow, result).
    borrow = 1 if a < b. result = (a - b) mod 2^32. -/
private def u32OverflowingSub (a b : Nat) : Nat × Nat :=
  if a >= b then (0, a - b)
  else (1, u32Max - b + a)

/-- Widening u32 multiplication: returns (lo, hi). -/
private def u32WideMul (a b : Nat) : Nat × Nat :=
  let prod := a * b
  (prod % u32Max, prod / u32Max)

/-- Widening multiply-add: a * b + c, returns (lo, hi). -/
private def u32WideMadd (a b c : Nat) : Nat × Nat :=
  let result := a * b + c
  (result % u32Max, result / u32Max)

/-- Left-rotate a 32-bit value by b bits. -/
private def u32RotateLeft (a b : Nat) : Nat :=
  ((a * 2^b) % u32Max) ||| (a / 2^(32 - b))

/-- Right-rotate a 32-bit value by b bits. -/
private def u32RotateRight (a b : Nat) : Nat :=
  (a / 2^b) ||| ((a * 2^(32 - b)) % u32Max)

/-- Count leading zeros of a 32-bit value. -/
private def u32CountLeadingZeros (n : Nat) : Nat :=
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
private def u32CountTrailingZeros (n : Nat) : Nat :=
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
private def u32CountLeadingOnes (n : Nat) : Nat :=
  u32CountLeadingZeros (u32Max - 1 - n)

/-- Count trailing ones of a 32-bit value. -/
private def u32CountTrailingOnes (n : Nat) : Nat :=
  u32CountTrailingZeros (n ^^^ (u32Max - 1))

/-- Population count (number of set bits) of a 32-bit value. -/
private def u32PopCount (n : Nat) : Nat :=
  let rec go (v : Nat) (count : Nat) : (bits : Nat) → Nat
    | 0 => count
    | bits + 1 => go (v / 2) (count + v % 2) bits
  go n 0 32

-- ============================================================================
-- Single instruction step
-- ============================================================================

/-- Execute a single instruction, returning the new state or none on failure. -/
def stepInstruction (s : MidenState) (i : Instruction) : Option MidenState :=
  match i, s.stack with

  -- No-op
  | Instruction.nop, _ => some s

  -- Assertions
  | Instruction.assert, a :: rest =>
    if a.val == 1 then some (s.withStack rest) else none
  | Instruction.assertWithError _, a :: rest =>
    if a.val == 1 then some (s.withStack rest) else none
  | Instruction.assertz, a :: rest =>
    if a.val == 0 then some (s.withStack rest) else none
  | Instruction.assertzWithError _, a :: rest =>
    if a.val == 0 then some (s.withStack rest) else none
  | Instruction.assertEq, b :: a :: rest =>
    if a == b then some (s.withStack rest) else none
  | Instruction.assertEqWithError _, b :: a :: rest =>
    if a == b then some (s.withStack rest) else none
  | Instruction.assertEqw, stk =>
    match stk with
    | b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest =>
      if a0 == b0 && a1 == b1 && a2 == b2 && a3 == b3
      then some (s.withStack rest)
      else none
    | _ => none

  -- Drop
  | Instruction.drop, _ :: rest => some (s.withStack rest)
  | Instruction.dropw, _ :: _ :: _ :: _ :: rest => some (s.withStack rest)

  -- Pad
  | Instruction.padw, stk => some (s.withStack (0 :: 0 :: 0 :: 0 :: stk))

  -- Dup
  | Instruction.dup n, stk =>
    match stk[n.val]? with
    | some v => some (s.withStack (v :: stk))
    | none => none
  | Instruction.dupw n, stk =>
    let base := n.val * 4
    match stk[base]?, stk[base+1]?, stk[base+2]?, stk[base+3]? with
    | some a, some b, some c, some d => some (s.withStack (a :: b :: c :: d :: stk))
    | _, _, _, _ => none

  -- Swap: swap.n swaps top element with element at position n
  | Instruction.swap n, stk =>
    if n.val == 0 then some s  -- swap.0 is nop
    else
      match stk[0]?, stk[n.val]? with
      | some top, some nth =>
        let stk' := stk.set 0 nth |>.set n.val top
        some (s.withStack stk')
      | _, _ => none
  | Instruction.swapw n, stk =>
    if n.val == 0 then some s
    else
      let base := n.val * 4
      match stk[0]?, stk[1]?, stk[2]?, stk[3]?,
            stk[base]?, stk[base+1]?, stk[base+2]?, stk[base+3]? with
      | some a0, some a1, some a2, some a3,
        some b0, some b1, some b2, some b3 =>
        let stk' := stk
          |>.set 0 b0 |>.set 1 b1 |>.set 2 b2 |>.set 3 b3
          |>.set base a0 |>.set (base+1) a1 |>.set (base+2) a2 |>.set (base+3) a3
        some (s.withStack stk')
      | _, _, _, _, _, _, _, _ => none
  | Instruction.swapdw, stk =>
    match stk with
    | a0::a1::a2::a3::b0::b1::b2::b3::c0::c1::c2::c3::d0::d1::d2::d3::rest =>
      -- Swap words: [A,B,C,D,...] -> [C,D,A,B,...]
      some (s.withStack (c0::c1::c2::c3::d0::d1::d2::d3::a0::a1::a2::a3::b0::b1::b2::b3::rest))
    | _ => none

  -- Movup: moves element at position n to the top. Valid for n in {2, ..., 15}.
  | Instruction.movup n, stk =>
    if n < 2 || n > 15 then none
    else
      match removeNth stk n with
      | some (v, rest) => some (s.withStack (v :: rest))
      | none => none

  -- Movdn: moves top element to position n. Valid for n in {2, ..., 15}.
  | Instruction.movdn n, stk =>
    if n < 2 || n > 15 then none
    else
      match stk with
      | top :: rest => some (s.withStack (insertAt rest n top))
      | _ => none

  -- Movupw: move word at position n to the top. Valid for n in {2, 3}.
  | Instruction.movupw n, stk =>
    if n < 2 || n > 3 then none
    else
      let base := n * 4
      if stk.length < base + 4 then none
      else
        let before := stk.take base
        let word := (stk.drop base).take 4
        let after := stk.drop (base + 4)
        some (s.withStack (word ++ before ++ after))

  -- Movdnw: move top word to position n. Valid for n in {2, 3}.
  | Instruction.movdnw n, stk =>
    if n < 2 || n > 3 then none
    else
      if stk.length < (n + 1) * 4 then none
      else
        let word := stk.take 4
        let remaining := stk.drop 4
        let before := remaining.take (n * 4)
        let after := remaining.drop (n * 4)
        some (s.withStack (before ++ word ++ after))

  -- Reversew: reverse top 4 elements
  | Instruction.reversew, a :: b :: c :: d :: rest =>
    some (s.withStack (d :: c :: b :: a :: rest))

  -- Conditional operations
  | Instruction.cswap, c :: b :: a :: rest =>
    if c.val == 1 then some (s.withStack (a :: b :: rest))
    else if c.val == 0 then some (s.withStack (b :: a :: rest))
    else none
  | Instruction.cswapw, stk =>
    match stk with
    | c :: b0::b1::b2::b3 :: a0::a1::a2::a3 :: rest =>
      if c.val == 1 then some (s.withStack (a0::a1::a2::a3::b0::b1::b2::b3::rest))
      else if c.val == 0 then some (s.withStack (b0::b1::b2::b3::a0::a1::a2::a3::rest))
      else none
    | _ => none
  | Instruction.cdrop, c :: b :: a :: rest =>
    if c.val == 1 then some (s.withStack (b :: rest))
    else if c.val == 0 then some (s.withStack (a :: rest))
    else none
  | Instruction.cdropw, stk =>
    match stk with
    | c :: b0::b1::b2::b3 :: a0::a1::a2::a3 :: rest =>
      if c.val == 1 then some (s.withStack (b0::b1::b2::b3::rest))
      else if c.val == 0 then some (s.withStack (a0::a1::a2::a3::rest))
      else none
    | _ => none

  -- Push constants
  | Instruction.push v, stk => some (s.withStack (v :: stk))
  | Instruction.pushList vs, stk => some (s.withStack (vs ++ stk))

  -- Field arithmetic
  | Instruction.add, b :: a :: rest => some (s.withStack ((a + b) :: rest))
  | Instruction.addImm v, a :: rest => some (s.withStack ((a + v) :: rest))
  | Instruction.sub, b :: a :: rest => some (s.withStack ((a - b) :: rest))
  | Instruction.subImm v, a :: rest => some (s.withStack ((a - v) :: rest))
  | Instruction.mul, b :: a :: rest => some (s.withStack ((a * b) :: rest))
  | Instruction.mulImm v, a :: rest => some (s.withStack ((a * v) :: rest))
  | Instruction.div, b :: a :: rest =>
    if b == 0 then none else some (s.withStack ((a * b⁻¹) :: rest))
  | Instruction.divImm v, a :: rest =>
    if v == 0 then none else some (s.withStack ((a * v⁻¹) :: rest))
  | Instruction.neg, a :: rest => some (s.withStack ((-a) :: rest))
  | Instruction.inv, a :: rest =>
    if a == 0 then none else some (s.withStack (a⁻¹ :: rest))
  | Instruction.pow2, a :: rest =>
    if a.val > 63 then none
    else some (s.withStack (Felt.ofNat (2^a.val) :: rest))
  | Instruction.incr, a :: rest => some (s.withStack ((a + 1) :: rest))

  -- Field comparison
  | Instruction.eq, b :: a :: rest =>
    some (s.withStack ((if a == b then (1 : Felt) else 0) :: rest))
  | Instruction.eqImm v, a :: rest =>
    some (s.withStack ((if a == v then (1 : Felt) else 0) :: rest))
  | Instruction.neq, b :: a :: rest =>
    some (s.withStack ((if a != b then (1 : Felt) else 0) :: rest))
  | Instruction.neqImm v, a :: rest =>
    some (s.withStack ((if a != v then (1 : Felt) else 0) :: rest))
  | Instruction.lt, b :: a :: rest =>
    some (s.withStack ((if a.val < b.val then (1 : Felt) else 0) :: rest))
  | Instruction.lte, b :: a :: rest =>
    some (s.withStack ((if a.val ≤ b.val then (1 : Felt) else 0) :: rest))
  | Instruction.gt, b :: a :: rest =>
    some (s.withStack ((if a.val > b.val then (1 : Felt) else 0) :: rest))
  | Instruction.gte, b :: a :: rest =>
    some (s.withStack ((if a.val ≥ b.val then (1 : Felt) else 0) :: rest))
  | Instruction.isOdd, a :: rest =>
    some (s.withStack ((if a.val % 2 == 1 then (1 : Felt) else 0) :: rest))

  -- Field boolean (inputs must be 0 or 1)
  | Instruction.and, b :: a :: rest =>
    if a.isBool && b.isBool
    then some (s.withStack ((a * b) :: rest))
    else none
  | Instruction.or, b :: a :: rest =>
    if a.isBool && b.isBool
    then some (s.withStack ((a + b - a * b) :: rest))
    else none
  | Instruction.xor, b :: a :: rest =>
    if a.isBool && b.isBool
    then some (s.withStack ((a + b - 2 * a * b) :: rest))
    else none
  | Instruction.not, a :: rest =>
    if a.isBool
    then some (s.withStack ((1 - a) :: rest))
    else none

  -- U32 assertions
  | Instruction.u32Assert, stk =>
    match stk with
    | a :: _ => if a.isU32 then some s else none
    | _ => none
  | Instruction.u32Assert2, stk =>
    match stk with
    | b :: a :: _ => if a.isU32 && b.isU32 then some s else none
    | _ => none
  | Instruction.u32AssertW, stk =>
    match stk with
    | a :: b :: c :: d :: _ =>
      if a.isU32 && b.isU32 && c.isU32 && d.isU32 then some s else none
    | _ => none
  | Instruction.u32Test, a :: stk =>
    some (s.withStack ((if a.isU32 then (1 : Felt) else 0) :: a :: stk))
  | Instruction.u32TestW, stk =>
    match stk with
    | a :: b :: c :: d :: _ =>
      let result : Felt := if a.isU32 && b.isU32 && c.isU32 && d.isU32 then 1 else 0
      some (s.withStack (result :: stk))
    | _ => none

  -- U32 conversions
  | Instruction.u32Cast, a :: rest =>
    some (s.withStack (a.lo32 :: rest))
  | Instruction.u32Split, a :: rest =>
    some (s.withStack (a.lo32 :: a.hi32 :: rest))

  -- U32 arithmetic
  | Instruction.u32WidenAdd, b :: a :: rest =>
    let (lo, carry) := u32WideAdd a.val b.val
    some (s.withStack (Felt.ofNat lo :: Felt.ofNat carry :: rest))
  | Instruction.u32OverflowAdd, b :: a :: rest =>
    let (lo, carry) := u32WideAdd a.val b.val
    some (s.withStack (Felt.ofNat carry :: Felt.ofNat lo :: rest))
  | Instruction.u32WrappingAdd, b :: a :: rest =>
    some (s.withStack (Felt.ofNat (u32WAdd a.val b.val) :: rest))
  | Instruction.u32WidenAdd3, c :: b :: a :: rest =>
    let (lo, carry) := u32WideAdd3 a.val b.val c.val
    some (s.withStack (Felt.ofNat lo :: Felt.ofNat carry :: rest))
  | Instruction.u32OverflowAdd3, c :: b :: a :: rest =>
    let (lo, carry) := u32WideAdd3 a.val b.val c.val
    some (s.withStack (Felt.ofNat carry :: Felt.ofNat lo :: rest))
  | Instruction.u32WrappingAdd3, c :: b :: a :: rest =>
    let sum := (a.val + b.val + c.val) % u32Max
    some (s.withStack (Felt.ofNat sum :: rest))
  | Instruction.u32OverflowSub, b :: a :: rest =>
    let (borrow, diff) := u32OverflowingSub a.val b.val
    some (s.withStack (Felt.ofNat borrow :: Felt.ofNat diff :: rest))
  | Instruction.u32WrappingSub, b :: a :: rest =>
    let (_, diff) := u32OverflowingSub a.val b.val
    some (s.withStack (Felt.ofNat diff :: rest))
  | Instruction.u32WidenMul, b :: a :: rest =>
    let (lo, hi) := u32WideMul a.val b.val
    some (s.withStack (Felt.ofNat lo :: Felt.ofNat hi :: rest))
  | Instruction.u32WrappingMul, b :: a :: rest =>
    some (s.withStack (Felt.ofNat ((a.val * b.val) % u32Max) :: rest))
  | Instruction.u32WidenMadd, b :: a :: c :: rest =>
    let (lo, hi) := u32WideMadd a.val b.val c.val
    some (s.withStack (Felt.ofNat lo :: Felt.ofNat hi :: rest))
  | Instruction.u32WrappingMadd, b :: a :: c :: rest =>
    some (s.withStack (Felt.ofNat ((a.val * b.val + c.val) % u32Max) :: rest))
  | Instruction.u32DivMod, b :: a :: rest =>
    if b.val == 0 then none
    else
      let q := a.val / b.val
      let r := a.val % b.val
      some (s.withStack (Felt.ofNat r :: Felt.ofNat q :: rest))
  | Instruction.u32Div, b :: a :: rest =>
    if b.val == 0 then none
    else some (s.withStack (Felt.ofNat (a.val / b.val) :: rest))
  | Instruction.u32Mod, b :: a :: rest =>
    if b.val == 0 then none
    else some (s.withStack (Felt.ofNat (a.val % b.val) :: rest))

  -- U32 bitwise (fail if inputs are not valid u32)
  | Instruction.u32And, b :: a :: rest =>
    if !a.isU32 || !b.isU32 then none
    else some (s.withStack (Felt.ofNat (a.val &&& b.val) :: rest))
  | Instruction.u32Or, b :: a :: rest =>
    if !a.isU32 || !b.isU32 then none
    else some (s.withStack (Felt.ofNat (a.val ||| b.val) :: rest))
  | Instruction.u32Xor, b :: a :: rest =>
    if !a.isU32 || !b.isU32 then none
    else some (s.withStack (Felt.ofNat (a.val ^^^ b.val) :: rest))
  | Instruction.u32Not, a :: rest =>
    if !a.isU32 then none
    else some (s.withStack (Felt.ofNat (u32Max - 1 - a.val) :: rest))
  | Instruction.u32Shl, b :: a :: rest =>
    if b.val > 31 then none
    else some (s.withStack (Felt.ofNat ((a.val * 2^b.val) % u32Max) :: rest))
  | Instruction.u32ShlImm n, a :: rest =>
    if n > 31 then none
    else some (s.withStack (Felt.ofNat ((a.val * 2^n) % u32Max) :: rest))
  | Instruction.u32Shr, b :: a :: rest =>
    if b.val > 31 then none
    else some (s.withStack (Felt.ofNat (a.val / 2^b.val) :: rest))
  | Instruction.u32ShrImm n, a :: rest =>
    if n > 31 then none
    else some (s.withStack (Felt.ofNat (a.val / 2^n) :: rest))
  | Instruction.u32Rotl, b :: a :: rest =>
    if b.val > 31 then none
    else some (s.withStack (Felt.ofNat (u32RotateLeft a.val b.val) :: rest))
  | Instruction.u32RotlImm n, a :: rest =>
    if n > 31 then none
    else some (s.withStack (Felt.ofNat (u32RotateLeft a.val n) :: rest))
  | Instruction.u32Rotr, b :: a :: rest =>
    if b.val > 31 then none
    else some (s.withStack (Felt.ofNat (u32RotateRight a.val b.val) :: rest))
  | Instruction.u32RotrImm n, a :: rest =>
    if n > 31 then none
    else some (s.withStack (Felt.ofNat (u32RotateRight a.val n) :: rest))
  | Instruction.u32Popcnt, a :: rest =>
    some (s.withStack (Felt.ofNat (u32PopCount a.val) :: rest))
  | Instruction.u32Clz, a :: rest =>
    some (s.withStack (Felt.ofNat (u32CountLeadingZeros a.val) :: rest))
  | Instruction.u32Ctz, a :: rest =>
    some (s.withStack (Felt.ofNat (u32CountTrailingZeros a.val) :: rest))
  | Instruction.u32Clo, a :: rest =>
    some (s.withStack (Felt.ofNat (u32CountLeadingOnes a.val) :: rest))
  | Instruction.u32Cto, a :: rest =>
    some (s.withStack (Felt.ofNat (u32CountTrailingOnes a.val) :: rest))

  -- U32 comparison
  | Instruction.u32Lt, b :: a :: rest =>
    some (s.withStack ((if a.val < b.val then (1 : Felt) else 0) :: rest))
  | Instruction.u32Lte, b :: a :: rest =>
    some (s.withStack ((if a.val ≤ b.val then (1 : Felt) else 0) :: rest))
  | Instruction.u32Gt, b :: a :: rest =>
    some (s.withStack ((if a.val > b.val then (1 : Felt) else 0) :: rest))
  | Instruction.u32Gte, b :: a :: rest =>
    some (s.withStack ((if a.val ≥ b.val then (1 : Felt) else 0) :: rest))
  | Instruction.u32Min, b :: a :: rest =>
    some (s.withStack ((if a.val ≤ b.val then a else b) :: rest))
  | Instruction.u32Max, b :: a :: rest =>
    some (s.withStack ((if a.val ≥ b.val then a else b) :: rest))

  -- Memory (absolute addressing)
  | Instruction.memLoad, a :: rest =>
    if a.val >= u32Max then none
    else some (s.withStack (s.memory a.val :: rest))
  | Instruction.memLoadImm addr, stk =>
    if addr >= u32Max then none
    else some (s.withStack (s.memory addr :: stk))
  | Instruction.memStore, a :: v :: rest =>
    if a.val >= u32Max then none
    else some ((s.writeMemory a.val v).withStack rest)
  | Instruction.memStoreImm addr, v :: rest =>
    if addr >= u32Max then none
    else some ((s.writeMemory addr v).withStack rest)

  -- Memory word store (big-endian): store word, leaving it on the stack
  | Instruction.memStorewBe, a :: e0 :: e1 :: e2 :: e3 :: rest =>
    if a.val >= u32Max || a.val % 4 != 0 then none
    else
      let addr := a.val
      let s' := s.writeMemory addr e3
        |>.writeMemory (addr+1) e2
        |>.writeMemory (addr+2) e1
        |>.writeMemory (addr+3) e0
      some (s'.withStack (e0 :: e1 :: e2 :: e3 :: rest))
  | Instruction.memStorewBeImm addr, e0 :: e1 :: e2 :: e3 :: rest =>
    if addr >= u32Max || addr % 4 != 0 then none
    else
      let s' := s.writeMemory addr e3
        |>.writeMemory (addr+1) e2
        |>.writeMemory (addr+2) e1
        |>.writeMemory (addr+3) e0
      some (s'.withStack (e0 :: e1 :: e2 :: e3 :: rest))

  -- Memory word store (little-endian)
  | Instruction.memStorewLe, a :: e0 :: e1 :: e2 :: e3 :: rest =>
    if a.val >= u32Max || a.val % 4 != 0 then none
    else
      let addr := a.val
      let s' := s.writeMemory addr e0
        |>.writeMemory (addr+1) e1
        |>.writeMemory (addr+2) e2
        |>.writeMemory (addr+3) e3
      some (s'.withStack (e0 :: e1 :: e2 :: e3 :: rest))
  | Instruction.memStorewLeImm addr, e0 :: e1 :: e2 :: e3 :: rest =>
    if addr >= u32Max || addr % 4 != 0 then none
    else
      let s' := s.writeMemory addr e0
        |>.writeMemory (addr+1) e1
        |>.writeMemory (addr+2) e2
        |>.writeMemory (addr+3) e3
      some (s'.withStack (e0 :: e1 :: e2 :: e3 :: rest))

  -- Memory word load (big-endian): overwrites top 4 stack elements
  | Instruction.memLoadwBe, a :: _ :: _ :: _ :: _ :: rest =>
    if a.val >= u32Max || a.val % 4 != 0 then none
    else
      let addr := a.val
      let e3 := s.memory addr
      let e2 := s.memory (addr+1)
      let e1 := s.memory (addr+2)
      let e0 := s.memory (addr+3)
      some (s.withStack (e0 :: e1 :: e2 :: e3 :: rest))
  | Instruction.memLoadwBeImm addr, _ :: _ :: _ :: _ :: rest =>
    if addr >= u32Max || addr % 4 != 0 then none
    else
      let e3 := s.memory addr
      let e2 := s.memory (addr+1)
      let e1 := s.memory (addr+2)
      let e0 := s.memory (addr+3)
      some (s.withStack (e0 :: e1 :: e2 :: e3 :: rest))

  -- Memory word load (little-endian)
  | Instruction.memLoadwLe, a :: _ :: _ :: _ :: _ :: rest =>
    if a.val >= u32Max || a.val % 4 != 0 then none
    else
      let addr := a.val
      let e0 := s.memory addr
      let e1 := s.memory (addr+1)
      let e2 := s.memory (addr+2)
      let e3 := s.memory (addr+3)
      some (s.withStack (e0 :: e1 :: e2 :: e3 :: rest))
  | Instruction.memLoadwLeImm addr, _ :: _ :: _ :: _ :: rest =>
    if addr >= u32Max || addr % 4 != 0 then none
    else
      let e0 := s.memory addr
      let e1 := s.memory (addr+1)
      let e2 := s.memory (addr+2)
      let e3 := s.memory (addr+3)
      some (s.withStack (e0 :: e1 :: e2 :: e3 :: rest))

  -- Procedure locals
  | Instruction.locLoad idx, stk =>
    some (s.withStack (s.locals idx :: stk))
  | Instruction.locStore idx, v :: rest =>
    some ((s.writeLocal idx v).withStack rest)

  -- Advice stack
  | Instruction.advPush n, stk =>
    if s.advice.length < n then none
    else
      let vals := s.advice.take n
      let adv' := s.advice.drop n
      -- First popped is deepest: reverse so first advice value ends up deepest
      some ((s.withAdvice adv').withStack (vals.reverse ++ stk))
  | Instruction.advLoadW, _ :: _ :: _ :: _ :: rest =>
    if s.advice.length < 4 then none
    else
      let vals := s.advice.take 4
      let adv' := s.advice.drop 4
      some ((s.withAdvice adv').withStack (vals.reverse ++ rest))

  -- Events (reads top of stack as event ID but does not consume it; stack unchanged)
  | Instruction.emit, _ :: _ => some s
  | Instruction.emitImm _, _ => some s

  -- Exec is handled at the Op level, not here
  | Instruction.exec _, _ => none

  -- Catch-all for insufficient stack depth
  | _, _ => none

-- ============================================================================
-- Op execution (with procedure environment)
-- ============================================================================

/-- A procedure environment maps procedure names to their bodies. -/
def ProcEnv := String → Option (List Op)

/-- Execute a list of operations given a procedure environment.
    `fuel` bounds recursion to ensure termination. -/
def execOps (env : ProcEnv) (fuel : Nat) (s : MidenState) (ops : List Op) : Option MidenState :=
  match fuel with
  | 0 => none  -- out of fuel
  | fuel' + 1 =>
    ops.foldlM (fun state op =>
      match op with
      | Op.inst (Instruction.exec target) =>
        match env target with
        | some body => execOps env fuel' state body
        | none => none
      | Op.inst i => stepInstruction state i
      | Op.ifElse thenBlk elseBlk =>
        match state.stack with
        | cond :: rest =>
          if cond.val == 1 then
            execOps env fuel' (state.withStack rest) thenBlk
          else if cond.val == 0 then
            execOps env fuel' (state.withStack rest) elseBlk
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
      match execOps env fuel st body with
      | some st' => doRepeat fuel n' body st'
      | none => none
  doWhile (fuel : Nat) (f : Nat) (body : List Op) (st : MidenState) : Option MidenState :=
    match f with
    | 0 => none
    | f' + 1 =>
      match st.stack with
      | cond :: rest =>
        if cond.val == 1 then
          match execOps env fuel (st.withStack rest) body with
          | some st' => doWhile fuel f' body st'
          | none => none
        else if cond.val == 0 then some (st.withStack rest)
        else none
      | _ => none

/-- Execute with an empty procedure environment. -/
def exec (fuel : Nat) (s : MidenState) (ops : List Op) : Option MidenState :=
  execOps (fun _ => none) fuel s ops

/-- Execute with a list of named procedures as environment. -/
def execWithProcs (procs : List Procedure) (fuel : Nat) (s : MidenState) (ops : List Op)
    : Option MidenState :=
  execOps (fun name => Procedure.lookup procs name) fuel s ops

end MidenLean
