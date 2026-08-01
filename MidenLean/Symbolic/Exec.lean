import MidenLean.Symbolic.State

/-!
# Symbolic Block Executor

Symbolic execution of basic blocks (straight-line instruction sequences).
Supports all non-control-flow instructions except dynamic-address memory
(address popped from stack).

## Support boundary

Everything outside the supported fragment returns `none`: dynamic-address
memory (`memLoad`/`memStore`/`mem*w*` with a stack address), bare `exec` calls
(handled compositionally via `ProcEnv` specs in `execOps`), and control flow
(`ifElse`/`repeat`/`whileTrue`, decomposed by `miden_vcg` instead). A `none`
here can never produce a "verified" result — the soundness theorems in
`Soundness.lean` only speak about `some` outcomes, so unsupported code fails
loudly at tactic time rather than weakening any theorem.
-/

namespace MidenLean.Symbolic

/-- Result of symbolic execution of a basic block. -/
structure BlockResult where
  state : State
  preconditions : List Precondition

/-- Execute a single instruction symbolically.  Returns none for stack
    underflow, unsupported instructions (dynamic-address memory, `exec` calls),
    or immediate values that violate static guards. Collects preconditions for
    instructions with runtime guards. Supports local memory (locLoad, locStore,
    locStorewBe/Le, locLoadwBe/Le, locaddr), static-address memory
    (memLoadImm, memStoreImm, memLoadw/StorewBe/LeImm), advice instructions
    (advPush, advLoadW), and event instructions (emit, emitImm). -/
def execInstruction (s : State) (i : Instruction) :
    Option (State × List Precondition) :=
  match i with

  -- No-op
  | .nop => some (s, [])

  -- Assertions
  | .assert => match s.stack with
    | a :: rest => some ({ s with stack := rest }, [.eqOne a])
    | _ => none
  | .assertWithError _ => match s.stack with
    | a :: rest => some ({ s with stack := rest }, [.eqOne a])
    | _ => none
  | .assertz => match s.stack with
    | a :: rest => some ({ s with stack := rest }, [.eqZero a])
    | _ => none
  | .assertzWithError _ => match s.stack with
    | a :: rest => some ({ s with stack := rest }, [.eqZero a])
    | _ => none
  | .assertEq => match s.stack with
    | b :: a :: rest => some ({ s with stack := rest }, [.feltEq a b])
    | _ => none
  | .assertEqWithError _ => match s.stack with
    | b :: a :: rest => some ({ s with stack := rest }, [.feltEq a b])
    | _ => none
  -- assertEqw and eqw require 8-element match; handled below
  | .assertEqw => match s.stack with
    | b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest =>
      some ({ s with stack := rest },
            [.feltEq a0 b0, .feltEq a1 b1, .feltEq a2 b2, .feltEq a3 b3])
    | _ => none
  | .eqw => match s.stack with
    | b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest =>
      some ({ s with stack := .eqw4 a0 a1 a2 a3 b0 b1 b2 b3
                       :: b0 :: b1 :: b2 :: b3
                       :: a0 :: a1 :: a2 :: a3 :: rest }, [])
    | _ => none

  -- Stack: drop
  | .drop => match s.stack with
    | _ :: rest => some ({ s with stack := rest }, [])
    | _ => none
  | .dropw => match s.stack with
    | _ :: _ :: _ :: _ :: rest => some ({ s with stack := rest }, [])
    | _ => none

  -- Stack: pad
  | .padw =>
    some ({ s with stack := .lit 0 :: .lit 0 :: .lit 0 :: .lit 0 :: s.stack }, [])

  -- Stack: dup
  | .dup n => match s.stack[n.val]? with
    | some v => some ({ s with stack := v :: s.stack }, [])
    | none => none
  | .dupw n =>
    let base := n.val * 4
    match s.stack[base]?, s.stack[base+1]?, s.stack[base+2]?, s.stack[base+3]? with
    | some a, some b, some c, some d =>
      some ({ s with stack := a :: b :: c :: d :: s.stack }, [])
    | _, _, _, _ => none

  -- Stack: swap
  | .swap n =>
    if n.val == 0 then some (s, [])
    else match s.stack[0]?, s.stack[n.val]? with
    | some top, some nth =>
      some ({ s with stack := s.stack.set 0 nth |>.set n.val top }, [])
    | _, _ => none
  | .swapw n =>
    if n.val == 0 then some (s, [])
    else
      let base := n.val * 4
      match s.stack[0]?, s.stack[1]?, s.stack[2]?, s.stack[3]?,
            s.stack[base]?, s.stack[base+1]?, s.stack[base+2]?, s.stack[base+3]? with
      | some a0, some a1, some a2, some a3,
        some b0, some b1, some b2, some b3 =>
        let stk' := s.stack
          |>.set 0 b0 |>.set 1 b1 |>.set 2 b2 |>.set 3 b3
          |>.set base a0 |>.set (base+1) a1 |>.set (base+2) a2 |>.set (base+3) a3
        some ({ s with stack := stk' }, [])
      | _, _, _, _, _, _, _, _ => none
  | .swapdw => match s.stack with
    | a0::a1::a2::a3::b0::b1::b2::b3::c0::c1::c2::c3::d0::d1::d2::d3::rest =>
      some ({ s with stack := c0::c1::c2::c3::d0::d1::d2::d3::a0::a1::a2::a3::b0::b1::b2::b3::rest }, [])
    | _ => none

  -- Stack: move
  | .movup n =>
    if 2 ≤ n && n ≤ 15 then
      match s.stack[n]? with
      | some v => some ({ s with stack := v :: s.stack.eraseIdx n }, [])
      | none => none
    else none
  | .movdn n =>
    if 2 ≤ n && n ≤ 15 then
      match s.stack with
      | top :: rest =>
        let (front, back) := rest.splitAt n
        if front.length == n then
          some ({ s with stack := front ++ [top] ++ back }, [])
        else none
      | _ => none
    else none
  | .movupw n =>
    if 2 ≤ n && n ≤ 3 then
      let base := n * 4
      if s.stack.length < base + 4 then none
      else
        let before := s.stack.take base
        let word := (s.stack.drop base).take 4
        let after := s.stack.drop (base + 4)
        some ({ s with stack := word ++ before ++ after }, [])
    else none
  | .movdnw n =>
    if 2 ≤ n && n ≤ 3 then
      if s.stack.length < (n + 1) * 4 then none
      else
        let word := s.stack.take 4
        let remaining := s.stack.drop 4
        let before := remaining.take (n * 4)
        let after := remaining.drop (n * 4)
        some ({ s with stack := before ++ word ++ after }, [])
    else none

  -- Stack: reversew
  | .reversew => match s.stack with
    | a :: b :: c :: d :: rest =>
      some ({ s with stack := d :: c :: b :: a :: rest }, [])
    | _ => none

  -- Stack: conditional swap/drop (require boolean condition)
  | .cswap => match s.stack with
    | c :: b :: a :: rest =>
      some ({ s with stack := .ite c a b :: .ite c b a :: rest }, [.isBool c])
    | _ => none
  | .cswapw => match s.stack with
    | c :: b0::b1::b2::b3 :: a0::a1::a2::a3 :: rest =>
      let stk := Expr.ite c a0 b0 :: Expr.ite c a1 b1 :: Expr.ite c a2 b2 :: Expr.ite c a3 b3 ::
        Expr.ite c b0 a0 :: Expr.ite c b1 a1 :: Expr.ite c b2 a2 :: Expr.ite c b3 a3 :: rest
      some ({ s with stack := stk }, [.isBool c])
    | _ => none
  | .cdrop => match s.stack with
    | c :: b :: a :: rest =>
      some ({ s with stack := .ite c b a :: rest }, [.isBool c])
    | _ => none
  | .cdropw => match s.stack with
    | c :: b0::b1::b2::b3 :: a0::a1::a2::a3 :: rest =>
      let stk := Expr.ite c b0 a0 :: Expr.ite c b1 a1 :: Expr.ite c b2 a2 :: Expr.ite c b3 a3 :: rest
      some ({ s with stack := stk }, [.isBool c])
    | _ => none

  -- Constants
  | .push v =>
    some ({ s with stack := .lit v :: s.stack }, [])
  | .pushList vs =>
    some ({ s with stack := vs.map .lit ++ s.stack }, [])

  -- Field arithmetic
  | .add => match s.stack with
    | b :: a :: rest => some ({ s with stack := .add a b :: rest }, [])
    | _ => none
  | .addImm v => match s.stack with
    | a :: rest => some ({ s with stack := .add a (.lit v) :: rest }, [])
    | _ => none
  | .sub => match s.stack with
    | b :: a :: rest => some ({ s with stack := .sub a b :: rest }, [])
    | _ => none
  | .subImm v => match s.stack with
    | a :: rest => some ({ s with stack := .sub a (.lit v) :: rest }, [])
    | _ => none
  | .mul => match s.stack with
    | b :: a :: rest => some ({ s with stack := .mul a b :: rest }, [])
    | _ => none
  | .mulImm v => match s.stack with
    | a :: rest => some ({ s with stack := .mul a (.lit v) :: rest }, [])
    | _ => none
  | .div => match s.stack with
    | b :: a :: rest => some ({ s with stack := .mul a (.inv b) :: rest }, [.nonzero b])
    | _ => none
  | .divImm v => match s.stack with
    | a :: rest =>
      some ({ s with stack := .mul a (.inv (.lit v)) :: rest }, [.nonzero (.lit v)])
    | _ => none
  | .neg => match s.stack with
    | a :: rest => some ({ s with stack := .neg a :: rest }, [])
    | _ => none
  | .inv => match s.stack with
    | a :: rest => some ({ s with stack := .inv a :: rest }, [.nonzero a])
    | _ => none
  | .pow2 => match s.stack with
    | a :: rest => some ({ s with stack := .pow2 a :: rest }, [.valLeq a 63])
    | _ => none
  | .incr => match s.stack with
    | a :: rest => some ({ s with stack := .add a (.lit 1) :: rest }, [])
    | _ => none

  -- Field comparison
  | .eq => match s.stack with
    | b :: a :: rest => some ({ s with stack := .feltEq a b :: rest }, [])
    | _ => none
  | .eqImm v => match s.stack with
    | a :: rest => some ({ s with stack := .feltEq a (.lit v) :: rest }, [])
    | _ => none
  | .neq => match s.stack with
    | b :: a :: rest => some ({ s with stack := .feltNeq a b :: rest }, [])
    | _ => none
  | .neqImm v => match s.stack with
    | a :: rest => some ({ s with stack := .feltNeq a (.lit v) :: rest }, [])
    | _ => none
  | .lt => match s.stack with
    | b :: a :: rest => some ({ s with stack := .feltLt a b :: rest }, [])
    | _ => none
  | .lte => match s.stack with
    | b :: a :: rest => some ({ s with stack := .feltLte a b :: rest }, [])
    | _ => none
  | .gt => match s.stack with
    | b :: a :: rest => some ({ s with stack := .feltGt a b :: rest }, [])
    | _ => none
  | .gte => match s.stack with
    | b :: a :: rest => some ({ s with stack := .feltGte a b :: rest }, [])
    | _ => none
  | .isOdd => match s.stack with
    | a :: rest => some ({ s with stack := .feltIsOdd a :: rest }, [])
    | _ => none

  -- Field boolean
  | .and => match s.stack with
    | b :: a :: rest =>
      some ({ s with stack := .feltAnd a b :: rest }, [.isBool a, .isBool b])
    | _ => none
  | .or => match s.stack with
    | b :: a :: rest =>
      some ({ s with stack := .feltOr a b :: rest }, [.isBool a, .isBool b])
    | _ => none
  | .xor => match s.stack with
    | b :: a :: rest =>
      some ({ s with stack := .feltXor a b :: rest }, [.isBool a, .isBool b])
    | _ => none
  | .not => match s.stack with
    | a :: rest => some ({ s with stack := .feltNot a :: rest }, [.isBool a])
    | _ => none

  -- U32 assertions / conversions
  | .u32Test => match s.stack with
    | a :: rest =>
      some ({ s with stack := .u32IsU32 a :: a :: rest }, [])
    | _ => none
  | .u32TestW => match s.stack with
    | a :: b :: c :: d :: rest =>
      some ({ s with stack := .u32IsU32W a b c d :: a :: b :: c :: d :: rest }, [])
    | _ => none
  | .u32Assert => match s.stack with
    | a :: _ => some (s, [.isU32 a])
    | _ => none
  | .u32Assert2 => match s.stack with
    | b :: a :: _ => some (s, [.isU32 a, .isU32 b])
    | _ => none
  | .u32AssertW => match s.stack with
    | a :: b :: c :: d :: _ =>
      some (s, [.isU32 a, .isU32 b, .isU32 c, .isU32 d])
    | _ => none
  | .u32Cast => match s.stack with
    | a :: rest => some ({ s with stack := .lo32 a :: rest }, [])
    | _ => none
  | .u32Split => match s.stack with
    | a :: rest => some ({ s with stack := .lo32 a :: .hi32 a :: rest }, [])
    | _ => none

  -- U32 arithmetic
  -- u32WidenAdd: [b, a] → [lo, carry]
  | .u32WidenAdd => match s.stack with
    | b :: a :: rest =>
      some ({ s with stack := .u32AddLo a b :: .u32AddHi a b :: rest },
            [.isU32 a, .isU32 b])
    | _ => none
  -- u32OverflowAdd: [b, a] → [carry, lo]
  | .u32OverflowAdd => match s.stack with
    | b :: a :: rest =>
      some ({ s with stack := .u32AddHi a b :: .u32AddLo a b :: rest },
            [.isU32 a, .isU32 b])
    | _ => none
  | .u32WrappingAdd => match s.stack with
    | b :: a :: rest =>
      some ({ s with stack := .u32WAdd a b :: rest }, [.isU32 a, .isU32 b])
    | _ => none
  -- u32WidenAdd3: [c, b, a] → [lo, carry]
  | .u32WidenAdd3 => match s.stack with
    | c :: b :: a :: rest =>
      some ({ s with stack := .u32Add3Lo a b c :: .u32Add3Hi a b c :: rest },
            [.isU32 a, .isU32 b, .isU32 c])
    | _ => none
  -- u32OverflowAdd3: [c, b, a] → [carry, lo]
  | .u32OverflowAdd3 => match s.stack with
    | c :: b :: a :: rest =>
      some ({ s with stack := .u32Add3Hi a b c :: .u32Add3Lo a b c :: rest },
            [.isU32 a, .isU32 b, .isU32 c])
    | _ => none
  | .u32WrappingAdd3 => match s.stack with
    | c :: b :: a :: rest =>
      some ({ s with stack := .u32WAdd3 a b c :: rest },
            [.isU32 a, .isU32 b, .isU32 c])
    | _ => none
  -- u32OverflowSub: [b, a] → [borrow, diff]
  | .u32OverflowSub => match s.stack with
    | b :: a :: rest =>
      some ({ s with stack := .u32SubBorrow a b :: .u32SubDiff a b :: rest },
            [.isU32 a, .isU32 b])
    | _ => none
  | .u32WrappingSub => match s.stack with
    | b :: a :: rest =>
      some ({ s with stack := .u32WSub a b :: rest }, [.isU32 a, .isU32 b])
    | _ => none
  -- u32WidenMul: [b, a] → [lo, hi]
  | .u32WidenMul => match s.stack with
    | b :: a :: rest =>
      some ({ s with stack := .u32MulLo a b :: .u32MulHi a b :: rest },
            [.isU32 a, .isU32 b])
    | _ => none
  | .u32WrappingMul => match s.stack with
    | b :: a :: rest =>
      some ({ s with stack := .u32WMul a b :: rest }, [.isU32 a, .isU32 b])
    | _ => none
  -- u32WidenMadd: [b, a, c] → [lo, hi]
  | .u32WidenMadd => match s.stack with
    | b :: a :: c :: rest =>
      some ({ s with stack := .u32MaddLo a b c :: .u32MaddHi a b c :: rest },
            [.isU32 a, .isU32 b, .isU32 c])
    | _ => none
  | .u32WrappingMadd => match s.stack with
    | b :: a :: c :: rest =>
      some ({ s with stack := .u32WMadd a b c :: rest },
            [.isU32 a, .isU32 b, .isU32 c])
    | _ => none
  -- u32DivMod: [b, a] → [rem, quot]
  | .u32DivMod => match s.stack with
    | b :: a :: rest =>
      some ({ s with stack := .u32DivRem a b :: .u32DivQuot a b :: rest },
            [.isU32 a, .isU32 b, .nonzero b])
    | _ => none
  | .u32Div => match s.stack with
    | b :: a :: rest =>
      some ({ s with stack := .u32DivQuot a b :: rest },
            [.isU32 a, .isU32 b, .nonzero b])
    | _ => none
  | .u32Mod => match s.stack with
    | b :: a :: rest =>
      some ({ s with stack := .u32DivRem a b :: rest },
            [.isU32 a, .isU32 b, .nonzero b])
    | _ => none

  -- U32 bitwise
  | .u32And => match s.stack with
    | b :: a :: rest =>
      some ({ s with stack := .u32And a b :: rest }, [.isU32 a, .isU32 b])
    | _ => none
  | .u32Or => match s.stack with
    | b :: a :: rest =>
      some ({ s with stack := .u32Or a b :: rest }, [.isU32 a, .isU32 b])
    | _ => none
  | .u32Xor => match s.stack with
    | b :: a :: rest =>
      some ({ s with stack := .u32Xor a b :: rest }, [.isU32 a, .isU32 b])
    | _ => none
  | .u32Not => match s.stack with
    | a :: rest => some ({ s with stack := .u32Not a :: rest }, [.isU32 a])
    | _ => none
  | .u32Shl => match s.stack with
    | b :: a :: rest =>
      some ({ s with stack := .u32Shl a b :: rest },
            [.isU32 a, .isU32 b, .valLeq b 31])
    | _ => none
  | .u32ShlImm n =>
    if n ≤ 31 then
      match s.stack with
      | a :: rest =>
        some ({ s with stack := .u32Shl a (.lit (Felt.ofNat n)) :: rest }, [.isU32 a])
      | _ => none
    else none
  | .u32Shr => match s.stack with
    | b :: a :: rest =>
      some ({ s with stack := .u32Shr a b :: rest },
            [.isU32 a, .isU32 b, .valLeq b 31])
    | _ => none
  | .u32ShrImm n =>
    if n ≤ 31 then
      match s.stack with
      | a :: rest =>
        some ({ s with stack := .u32Shr a (.lit (Felt.ofNat n)) :: rest }, [.isU32 a])
      | _ => none
    else none
  | .u32Rotl => match s.stack with
    | b :: a :: rest =>
      some ({ s with stack := .u32Rotl a b :: rest },
            [.isU32 a, .isU32 b, .valLeq b 31])
    | _ => none
  | .u32RotlImm n =>
    if n ≤ 31 then
      match s.stack with
      | a :: rest =>
        some ({ s with stack := .u32Rotl a (.lit (Felt.ofNat n)) :: rest }, [.isU32 a])
      | _ => none
    else none
  | .u32Rotr => match s.stack with
    | b :: a :: rest =>
      some ({ s with stack := .u32Rotr a b :: rest },
            [.isU32 a, .isU32 b, .valLeq b 31])
    | _ => none
  | .u32RotrImm n =>
    if n ≤ 31 then
      match s.stack with
      | a :: rest =>
        some ({ s with stack := .u32Rotr a (.lit (Felt.ofNat n)) :: rest }, [.isU32 a])
      | _ => none
    else none

  -- U32 bit counting
  | .u32Popcnt => match s.stack with
    | a :: rest => some ({ s with stack := .u32Popcnt a :: rest }, [.isU32 a])
    | _ => none
  | .u32Clz => match s.stack with
    | a :: rest => some ({ s with stack := .u32Clz a :: rest }, [.isU32 a])
    | _ => none
  | .u32Ctz => match s.stack with
    | a :: rest => some ({ s with stack := .u32Ctz a :: rest }, [.isU32 a])
    | _ => none
  | .u32Clo => match s.stack with
    | a :: rest => some ({ s with stack := .u32Clo a :: rest }, [.isU32 a])
    | _ => none
  | .u32Cto => match s.stack with
    | a :: rest => some ({ s with stack := .u32Cto a :: rest }, [.isU32 a])
    | _ => none

  -- U32 comparison
  | .u32Lt => match s.stack with
    | b :: a :: rest =>
      some ({ s with stack := .u32Lt a b :: rest }, [.isU32 a, .isU32 b])
    | _ => none
  | .u32Lte => match s.stack with
    | b :: a :: rest =>
      some ({ s with stack := .u32Lte a b :: rest }, [.isU32 a, .isU32 b])
    | _ => none
  | .u32Gt => match s.stack with
    | b :: a :: rest =>
      some ({ s with stack := .u32Gt a b :: rest }, [.isU32 a, .isU32 b])
    | _ => none
  | .u32Gte => match s.stack with
    | b :: a :: rest =>
      some ({ s with stack := .u32Gte a b :: rest }, [.isU32 a, .isU32 b])
    | _ => none
  | .u32Min => match s.stack with
    | b :: a :: rest =>
      some ({ s with stack := .u32Min a b :: rest }, [.isU32 a, .isU32 b])
    | _ => none
  | .u32Max => match s.stack with
    | b :: a :: rest =>
      some ({ s with stack := .u32Max a b :: rest }, [.isU32 a, .isU32 b])
    | _ => none

  -- Local memory: locLoad
  | .locLoad idx =>
    match s.frames with
    | frame :: _ =>
      if idx < frame.numLocals then
        some ({ s with stack := s.memory (frame.localAddr idx) :: s.stack }, [])
      else none
    | [] => none

  -- Local memory: locStore
  | .locStore idx =>
    match s.stack, s.frames with
    | v :: rest, frame :: _ =>
      if idx < frame.numLocals then
        let addr := frame.localAddr idx
        some ({ s with stack := rest,
                       memory := fun a => if a = addr then v else s.memory a }, [])
      else none
    | _, _ => none

  -- Local memory: locStorewBe (big-endian word store, word stays on stack)
  | .locStorewBe idx =>
    match s.stack, currentFrame s.frames with
    | e0 :: e1 :: e2 :: e3 :: rest, some frame =>
      if idx % 4 != 0 || idx + 4 > frame.numLocals then none
      else
        let baseAddr := frame.localAddr idx
        some ({ s with
          stack := e0 :: e1 :: e2 :: e3 :: rest,
          memory := fun a =>
            if a = baseAddr then e3
            else if a = baseAddr + 1 then e2
            else if a = baseAddr + 2 then e1
            else if a = baseAddr + 3 then e0
            else s.memory a }, [])
    | _, _ => none

  -- Local memory: locStorewLe (little-endian word store, word stays on stack)
  | .locStorewLe idx =>
    match s.stack, currentFrame s.frames with
    | e0 :: e1 :: e2 :: e3 :: rest, some frame =>
      if idx % 4 != 0 || idx + 4 > frame.numLocals then none
      else
        let baseAddr := frame.localAddr idx
        some ({ s with
          stack := e0 :: e1 :: e2 :: e3 :: rest,
          memory := fun a =>
            if a = baseAddr then e0
            else if a = baseAddr + 1 then e1
            else if a = baseAddr + 2 then e2
            else if a = baseAddr + 3 then e3
            else s.memory a }, [])
    | _, _ => none

  -- Local memory: locLoadwBe (big-endian word load, overwrites top 4)
  | .locLoadwBe idx =>
    match s.stack, currentFrame s.frames with
    | _ :: _ :: _ :: _ :: rest, some frame =>
      if idx % 4 != 0 || idx + 4 > frame.numLocals then none
      else
        let baseAddr := frame.localAddr idx
        let e3 := s.memory baseAddr
        let e2 := s.memory (baseAddr + 1)
        let e1 := s.memory (baseAddr + 2)
        let e0 := s.memory (baseAddr + 3)
        some ({ s with stack := e0 :: e1 :: e2 :: e3 :: rest }, [])
    | _, _ => none

  -- Local memory: locLoadwLe (little-endian word load, overwrites top 4)
  | .locLoadwLe idx =>
    match s.stack, currentFrame s.frames with
    | _ :: _ :: _ :: _ :: rest, some frame =>
      if idx % 4 != 0 || idx + 4 > frame.numLocals then none
      else
        let baseAddr := frame.localAddr idx
        let e0 := s.memory baseAddr
        let e1 := s.memory (baseAddr + 1)
        let e2 := s.memory (baseAddr + 2)
        let e3 := s.memory (baseAddr + 3)
        some ({ s with stack := e0 :: e1 :: e2 :: e3 :: rest }, [])
    | _, _ => none

  -- Local memory: locaddr (push absolute address)
  | .locaddr idx =>
    match s.frames with
    | frame :: _ =>
      if idx < frame.numLocals then
        some ({ s with stack := .lit (Felt.ofNat (frame.localAddr idx)) :: s.stack }, [])
      else none
    | [] => none

  -- Static-address memory: memLoadImm
  | .memLoadImm addr =>
    if addr >= u32Max then none
    else some ({ s with stack := s.memory addr :: s.stack }, [])

  -- Static-address memory: memStoreImm
  | .memStoreImm addr =>
    match s.stack with
    | v :: rest =>
      if addr >= u32Max then none
      else some ({ s with stack := rest,
                          memory := fun a => if a = addr then v else s.memory a }, [])
    | _ => none

  -- Static-address memory: memLoadwBeImm (big-endian word load)
  | .memLoadwBeImm addr =>
    match s.stack with
    | _ :: _ :: _ :: _ :: rest =>
      if addr >= u32Max || addr % 4 != 0 then none
      else
        let e3 := s.memory addr
        let e2 := s.memory (addr + 1)
        let e1 := s.memory (addr + 2)
        let e0 := s.memory (addr + 3)
        some ({ s with stack := e0 :: e1 :: e2 :: e3 :: rest }, [])
    | _ => none

  -- Static-address memory: memStorewBeImm (big-endian word store, word stays on stack)
  | .memStorewBeImm addr =>
    match s.stack with
    | e0 :: e1 :: e2 :: e3 :: rest =>
      if addr >= u32Max || addr % 4 != 0 then none
      else
        some ({ s with
          stack := e0 :: e1 :: e2 :: e3 :: rest,
          memory := fun a =>
            if a = addr then e3
            else if a = addr + 1 then e2
            else if a = addr + 2 then e1
            else if a = addr + 3 then e0
            else s.memory a }, [])
    | _ => none

  -- Static-address memory: memLoadwLeImm (little-endian word load)
  | .memLoadwLeImm addr =>
    match s.stack with
    | _ :: _ :: _ :: _ :: rest =>
      if addr >= u32Max || addr % 4 != 0 then none
      else
        let e0 := s.memory addr
        let e1 := s.memory (addr + 1)
        let e2 := s.memory (addr + 2)
        let e3 := s.memory (addr + 3)
        some ({ s with stack := e0 :: e1 :: e2 :: e3 :: rest }, [])
    | _ => none

  -- Static-address memory: memStorewLeImm (little-endian word store, word stays on stack)
  | .memStorewLeImm addr =>
    match s.stack with
    | e0 :: e1 :: e2 :: e3 :: rest =>
      if addr >= u32Max || addr % 4 != 0 then none
      else
        some ({ s with
          stack := e0 :: e1 :: e2 :: e3 :: rest,
          memory := fun a =>
            if a = addr then e0
            else if a = addr + 1 then e1
            else if a = addr + 2 then e2
            else if a = addr + 3 then e3
            else s.memory a }, [])
    | _ => none

  -- Advice: advPush n
  | .advPush n =>
    if s.advice.length < n then none
    else
      let vals := s.advice.take n
      let adv' := s.advice.drop n
      some ({ s with stack := vals.reverse ++ s.stack, advice := adv' }, [])

  -- Advice: advLoadW (need 4 on stack and 4 in advice)
  | .advLoadW => match s.stack with
    | _ :: _ :: _ :: _ :: rest =>
      if s.advice.length < 4 then none
      else
        let vals := s.advice.take 4
        let adv' := s.advice.drop 4
        some ({ s with stack := vals ++ rest, advice := adv' }, [])
    | _ => none

  -- Events: emit (no-op, requires ≥ 1 element on stack)
  | .emit => match s.stack with
    | _ :: _ => some (s, [])
    | _ => none

  -- Events: emitImm (always succeeds, no-op)
  | .emitImm _ => some (s, [])

  -- Unsupported: dynamic-address memory (address from stack), `exec` calls
  | .memLoad | .memStore
  | .memLoadwBe | .memStorewBe
  | .memLoadwLe | .memStorewLe
  | .exec _ => none

/-- The step function used inside execBlock's fold. -/
def execBlockStep (acc : State × List Precondition) (inst : Instruction) :
    Option (State × List Precondition) :=
  match execInstruction acc.1 inst with
  | some (s', preconds) => some (s', preconds.reverse ++ acc.2)
  | none => none

/-- Execute a basic block: fold execInstruction over a list of instructions.
    Preconditions are accumulated via prepend and reversed at the end. -/
def execBlock (ops : List Instruction) (s : State) :
    Option BlockResult :=
  match ops.foldlM execBlockStep (s, []) with
  | some (fs, fp) => some { state := fs, preconditions := fp.reverse }
  | none => none

/-- Extract instructions from a basic block (all ops must be Op.inst). -/
def extractBlock (ops : List Op) : Option (List Instruction) :=
  ops.mapM fun
    | .inst i => some i
    | _ => none

-- ============================================================================
-- Compositional calls: symbolic procedure environment
-- ============================================================================

/-- A symbolic specification of a procedure: given an input symbolic state,
    produce the output state and any required preconditions. -/
structure Spec where
  transform : State → Option BlockResult

/-- Symbolic procedure environment mapping procedure names to symbolic specs. -/
abbrev ProcEnv := String → Option Spec

/-- Execute a single op with a symbolic procedure environment.
    Handles `Op.inst (.exec target)` by looking up the target in the ProcEnv,
    `Op.inst i` by delegating to execInstruction, and returns none for
    control-flow ops (ifElse, repeat, whileTrue). -/
def execOp (senv : ProcEnv) (acc : BlockResult) (op : Op) :
    Option BlockResult :=
  match op with
  | .inst (.exec target) =>
    match senv target with
    | some spec => do
      let result ← spec.transform acc.state
      return { state := result.state,
               preconditions := acc.preconditions ++ result.preconditions }
    | none => none
  | .inst i => do
    let (s', preconds) ← execInstruction acc.state i
    return { state := s', preconditions := acc.preconditions ++ preconds }
  | _ => none  -- control flow handled by Phase 4

/-- Execute a sequence of ops with a symbolic procedure environment. -/
def execOps (senv : ProcEnv) (ops : List Op) (s : State) :
    Option BlockResult :=
  ops.foldlM (execOp senv) { state := s, preconditions := [] }

end MidenLean.Symbolic
