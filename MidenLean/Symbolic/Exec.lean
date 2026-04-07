import MidenLean.Symbolic.State

/-!
# Symbolic Block Executor

Symbolic execution of basic blocks (straight-line instruction sequences).
Supports all non-memory, non-control-flow instructions in the Instruction type.
-/

namespace MidenLean.Symbolic

/-- Result of symbolic execution of a basic block. -/
structure BlockResult where
  state : State
  preconditions : List Precondition
  deriving Repr, BEq

/-- Execute a single instruction symbolically.  Returns none for stack
    underflow, unsupported instructions (memory, exec, advice), or immediate
    values that violate static guards. Collects preconditions for instructions
    with runtime guards. -/
def execInstruction (s : State) (i : Instruction) :
    Option (State × List Precondition) :=
  match i with

  -- No-op
  | .nop => some (s, [])

  -- Assertions
  | .assert => match s.stack with
    | a :: rest => some ({ stack := rest }, [.eqOne a])
    | _ => none
  | .assertWithError _ => match s.stack with
    | a :: rest => some ({ stack := rest }, [.eqOne a])
    | _ => none
  | .assertz => match s.stack with
    | a :: rest => some ({ stack := rest }, [.eqZero a])
    | _ => none
  | .assertzWithError _ => match s.stack with
    | a :: rest => some ({ stack := rest }, [.eqZero a])
    | _ => none
  | .assertEq => match s.stack with
    | b :: a :: rest => some ({ stack := rest }, [.feltEq a b])
    | _ => none
  | .assertEqWithError _ => match s.stack with
    | b :: a :: rest => some ({ stack := rest }, [.feltEq a b])
    | _ => none
  -- assertEqw and eqw require 8-element match; handled below
  | .assertEqw => match s.stack with
    | b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest =>
      some ({ stack := rest },
            [.feltEq a0 b0, .feltEq a1 b1, .feltEq a2 b2, .feltEq a3 b3])
    | _ => none
  | .eqw => match s.stack with
    | b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest =>
      some ({ stack := .eqw4 a0 a1 a2 a3 b0 b1 b2 b3
                       :: b0 :: b1 :: b2 :: b3
                       :: a0 :: a1 :: a2 :: a3 :: rest }, [])
    | _ => none

  -- Stack: drop
  | .drop => match s.stack with
    | _ :: rest => some ({ stack := rest }, [])
    | _ => none
  | .dropw => match s.stack with
    | _ :: _ :: _ :: _ :: rest => some ({ stack := rest }, [])
    | _ => none

  -- Stack: pad
  | .padw =>
    some ({ stack := .lit 0 :: .lit 0 :: .lit 0 :: .lit 0 :: s.stack }, [])

  -- Stack: dup
  | .dup n => match s.stack[n.val]? with
    | some v => some ({ stack := v :: s.stack }, [])
    | none => none
  | .dupw n =>
    let base := n.val * 4
    match s.stack[base]?, s.stack[base+1]?, s.stack[base+2]?, s.stack[base+3]? with
    | some a, some b, some c, some d =>
      some ({ stack := a :: b :: c :: d :: s.stack }, [])
    | _, _, _, _ => none

  -- Stack: swap
  | .swap n =>
    if n.val == 0 then some (s, [])
    else match s.stack[0]?, s.stack[n.val]? with
    | some top, some nth =>
      some ({ stack := s.stack.set 0 nth |>.set n.val top }, [])
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
        some ({ stack := stk' }, [])
      | _, _, _, _, _, _, _, _ => none
  | .swapdw => match s.stack with
    | a0::a1::a2::a3::b0::b1::b2::b3::c0::c1::c2::c3::d0::d1::d2::d3::rest =>
      some ({ stack := c0::c1::c2::c3::d0::d1::d2::d3::a0::a1::a2::a3::b0::b1::b2::b3::rest }, [])
    | _ => none

  -- Stack: move
  | .movup n =>
    if 2 ≤ n && n ≤ 15 then
      match s.stack[n]? with
      | some v => some ({ stack := v :: s.stack.eraseIdx n }, [])
      | none => none
    else none
  | .movdn n =>
    if 2 ≤ n && n ≤ 15 then
      match s.stack with
      | top :: rest =>
        let (front, back) := rest.splitAt n
        if front.length == n then
          some ({ stack := front ++ [top] ++ back }, [])
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
        some ({ stack := word ++ before ++ after }, [])
    else none
  | .movdnw n =>
    if 2 ≤ n && n ≤ 3 then
      if s.stack.length < (n + 1) * 4 then none
      else
        let word := s.stack.take 4
        let remaining := s.stack.drop 4
        let before := remaining.take (n * 4)
        let after := remaining.drop (n * 4)
        some ({ stack := before ++ word ++ after }, [])
    else none

  -- Stack: reversew
  | .reversew => match s.stack with
    | a :: b :: c :: d :: rest =>
      some ({ stack := d :: c :: b :: a :: rest }, [])
    | _ => none

  -- Stack: conditional (cswap/cdrop require concrete condition; return none)
  | .cswap => none
  | .cswapw => none
  | .cdrop => none
  | .cdropw => none

  -- Constants
  | .push v =>
    some ({ stack := .lit v :: s.stack }, [])
  | .pushList vs =>
    some ({ stack := vs.map .lit ++ s.stack }, [])

  -- Field arithmetic
  | .add => match s.stack with
    | b :: a :: rest => some ({ stack := .add a b :: rest }, [])
    | _ => none
  | .addImm v => match s.stack with
    | a :: rest => some ({ stack := .add a (.lit v) :: rest }, [])
    | _ => none
  | .sub => match s.stack with
    | b :: a :: rest => some ({ stack := .sub a b :: rest }, [])
    | _ => none
  | .subImm v => match s.stack with
    | a :: rest => some ({ stack := .sub a (.lit v) :: rest }, [])
    | _ => none
  | .mul => match s.stack with
    | b :: a :: rest => some ({ stack := .mul a b :: rest }, [])
    | _ => none
  | .mulImm v => match s.stack with
    | a :: rest => some ({ stack := .mul a (.lit v) :: rest }, [])
    | _ => none
  | .div => match s.stack with
    | b :: a :: rest => some ({ stack := .mul a (.inv b) :: rest }, [.nonzero b])
    | _ => none
  | .divImm v => match s.stack with
    | a :: rest =>
      some ({ stack := .mul a (.inv (.lit v)) :: rest }, [.nonzero (.lit v)])
    | _ => none
  | .neg => match s.stack with
    | a :: rest => some ({ stack := .neg a :: rest }, [])
    | _ => none
  | .inv => match s.stack with
    | a :: rest => some ({ stack := .inv a :: rest }, [.nonzero a])
    | _ => none
  | .pow2 => match s.stack with
    | a :: rest => some ({ stack := .pow2 a :: rest }, [.valLeq a 63])
    | _ => none
  | .incr => match s.stack with
    | a :: rest => some ({ stack := .add a (.lit 1) :: rest }, [])
    | _ => none

  -- Field comparison
  | .eq => match s.stack with
    | b :: a :: rest => some ({ stack := .feltEq a b :: rest }, [])
    | _ => none
  | .eqImm v => match s.stack with
    | a :: rest => some ({ stack := .feltEq a (.lit v) :: rest }, [])
    | _ => none
  | .neq => match s.stack with
    | b :: a :: rest => some ({ stack := .feltNeq a b :: rest }, [])
    | _ => none
  | .neqImm v => match s.stack with
    | a :: rest => some ({ stack := .feltNeq a (.lit v) :: rest }, [])
    | _ => none
  | .lt => match s.stack with
    | b :: a :: rest => some ({ stack := .feltLt a b :: rest }, [])
    | _ => none
  | .lte => match s.stack with
    | b :: a :: rest => some ({ stack := .feltLte a b :: rest }, [])
    | _ => none
  | .gt => match s.stack with
    | b :: a :: rest => some ({ stack := .feltGt a b :: rest }, [])
    | _ => none
  | .gte => match s.stack with
    | b :: a :: rest => some ({ stack := .feltGte a b :: rest }, [])
    | _ => none
  | .isOdd => match s.stack with
    | a :: rest => some ({ stack := .feltIsOdd a :: rest }, [])
    | _ => none

  -- Field boolean
  | .and => match s.stack with
    | b :: a :: rest =>
      some ({ stack := .feltAnd a b :: rest }, [.isBool a, .isBool b])
    | _ => none
  | .or => match s.stack with
    | b :: a :: rest =>
      some ({ stack := .feltOr a b :: rest }, [.isBool a, .isBool b])
    | _ => none
  | .xor => match s.stack with
    | b :: a :: rest =>
      some ({ stack := .feltXor a b :: rest }, [.isBool a, .isBool b])
    | _ => none
  | .not => match s.stack with
    | a :: rest => some ({ stack := .feltNot a :: rest }, [.isBool a])
    | _ => none

  -- U32 assertions / conversions
  | .u32Test => none   -- result depends on concrete value; unsupported symbolically
  | .u32TestW => none  -- result depends on concrete values; unsupported symbolically
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
    | a :: rest => some ({ stack := .lo32 a :: rest }, [])
    | _ => none
  | .u32Split => match s.stack with
    | a :: rest => some ({ stack := .lo32 a :: .hi32 a :: rest }, [])
    | _ => none

  -- U32 arithmetic
  -- u32WidenAdd: [b, a] → [lo, carry]
  | .u32WidenAdd => match s.stack with
    | b :: a :: rest =>
      some ({ stack := .u32AddLo a b :: .u32AddHi a b :: rest },
            [.isU32 a, .isU32 b])
    | _ => none
  -- u32OverflowAdd: [b, a] → [carry, lo]
  | .u32OverflowAdd => match s.stack with
    | b :: a :: rest =>
      some ({ stack := .u32AddHi a b :: .u32AddLo a b :: rest },
            [.isU32 a, .isU32 b])
    | _ => none
  | .u32WrappingAdd => match s.stack with
    | b :: a :: rest =>
      some ({ stack := .u32WAdd a b :: rest }, [.isU32 a, .isU32 b])
    | _ => none
  -- u32WidenAdd3: [c, b, a] → [lo, carry]
  | .u32WidenAdd3 => match s.stack with
    | c :: b :: a :: rest =>
      some ({ stack := .u32Add3Lo a b c :: .u32Add3Hi a b c :: rest },
            [.isU32 a, .isU32 b, .isU32 c])
    | _ => none
  -- u32OverflowAdd3: [c, b, a] → [carry, lo]
  | .u32OverflowAdd3 => match s.stack with
    | c :: b :: a :: rest =>
      some ({ stack := .u32Add3Hi a b c :: .u32Add3Lo a b c :: rest },
            [.isU32 a, .isU32 b, .isU32 c])
    | _ => none
  | .u32WrappingAdd3 => match s.stack with
    | c :: b :: a :: rest =>
      some ({ stack := .u32WAdd3 a b c :: rest },
            [.isU32 a, .isU32 b, .isU32 c])
    | _ => none
  -- u32OverflowSub: [b, a] → [borrow, diff]
  | .u32OverflowSub => match s.stack with
    | b :: a :: rest =>
      some ({ stack := .u32SubBorrow a b :: .u32SubDiff a b :: rest },
            [.isU32 a, .isU32 b])
    | _ => none
  | .u32WrappingSub => match s.stack with
    | b :: a :: rest =>
      some ({ stack := .u32WSub a b :: rest }, [.isU32 a, .isU32 b])
    | _ => none
  -- u32WidenMul: [b, a] → [lo, hi]
  | .u32WidenMul => match s.stack with
    | b :: a :: rest =>
      some ({ stack := .u32MulLo a b :: .u32MulHi a b :: rest },
            [.isU32 a, .isU32 b])
    | _ => none
  | .u32WrappingMul => match s.stack with
    | b :: a :: rest =>
      some ({ stack := .u32WMul a b :: rest }, [.isU32 a, .isU32 b])
    | _ => none
  -- u32WidenMadd: [b, a, c] → [lo, hi]
  | .u32WidenMadd => match s.stack with
    | b :: a :: c :: rest =>
      some ({ stack := .u32MaddLo a b c :: .u32MaddHi a b c :: rest },
            [.isU32 a, .isU32 b, .isU32 c])
    | _ => none
  | .u32WrappingMadd => match s.stack with
    | b :: a :: c :: rest =>
      some ({ stack := .u32WMadd a b c :: rest },
            [.isU32 a, .isU32 b, .isU32 c])
    | _ => none
  -- u32DivMod: [b, a] → [rem, quot]
  | .u32DivMod => match s.stack with
    | b :: a :: rest =>
      some ({ stack := .u32DivRem a b :: .u32DivQuot a b :: rest },
            [.isU32 a, .isU32 b, .nonzero b])
    | _ => none
  | .u32Div => match s.stack with
    | b :: a :: rest =>
      some ({ stack := .u32DivQuot a b :: rest },
            [.isU32 a, .isU32 b, .nonzero b])
    | _ => none
  | .u32Mod => match s.stack with
    | b :: a :: rest =>
      some ({ stack := .u32DivRem a b :: rest },
            [.isU32 a, .isU32 b, .nonzero b])
    | _ => none

  -- U32 bitwise
  | .u32And => match s.stack with
    | b :: a :: rest =>
      some ({ stack := .u32And a b :: rest }, [.isU32 a, .isU32 b])
    | _ => none
  | .u32Or => match s.stack with
    | b :: a :: rest =>
      some ({ stack := .u32Or a b :: rest }, [.isU32 a, .isU32 b])
    | _ => none
  | .u32Xor => match s.stack with
    | b :: a :: rest =>
      some ({ stack := .u32Xor a b :: rest }, [.isU32 a, .isU32 b])
    | _ => none
  | .u32Not => match s.stack with
    | a :: rest => some ({ stack := .u32Not a :: rest }, [.isU32 a])
    | _ => none
  | .u32Shl => match s.stack with
    | b :: a :: rest =>
      some ({ stack := .u32Shl a b :: rest },
            [.isU32 a, .isU32 b, .valLeq b 31])
    | _ => none
  | .u32ShlImm n =>
    if n ≤ 31 then
      match s.stack with
      | a :: rest =>
        some ({ stack := .u32Shl a (.lit (Felt.ofNat n)) :: rest }, [.isU32 a])
      | _ => none
    else none
  | .u32Shr => match s.stack with
    | b :: a :: rest =>
      some ({ stack := .u32Shr a b :: rest },
            [.isU32 a, .isU32 b, .valLeq b 31])
    | _ => none
  | .u32ShrImm n =>
    if n ≤ 31 then
      match s.stack with
      | a :: rest =>
        some ({ stack := .u32Shr a (.lit (Felt.ofNat n)) :: rest }, [.isU32 a])
      | _ => none
    else none
  | .u32Rotl => match s.stack with
    | b :: a :: rest =>
      some ({ stack := .u32Rotl a b :: rest },
            [.isU32 a, .isU32 b, .valLeq b 31])
    | _ => none
  | .u32RotlImm n =>
    if n ≤ 31 then
      match s.stack with
      | a :: rest =>
        some ({ stack := .u32Rotl a (.lit (Felt.ofNat n)) :: rest }, [.isU32 a])
      | _ => none
    else none
  | .u32Rotr => match s.stack with
    | b :: a :: rest =>
      some ({ stack := .u32Rotr a b :: rest },
            [.isU32 a, .isU32 b, .valLeq b 31])
    | _ => none
  | .u32RotrImm n =>
    if n ≤ 31 then
      match s.stack with
      | a :: rest =>
        some ({ stack := .u32Rotr a (.lit (Felt.ofNat n)) :: rest }, [.isU32 a])
      | _ => none
    else none

  -- U32 bit counting
  | .u32Popcnt => match s.stack with
    | a :: rest => some ({ stack := .u32Popcnt a :: rest }, [.isU32 a])
    | _ => none
  | .u32Clz => match s.stack with
    | a :: rest => some ({ stack := .u32Clz a :: rest }, [.isU32 a])
    | _ => none
  | .u32Ctz => match s.stack with
    | a :: rest => some ({ stack := .u32Ctz a :: rest }, [.isU32 a])
    | _ => none
  | .u32Clo => match s.stack with
    | a :: rest => some ({ stack := .u32Clo a :: rest }, [.isU32 a])
    | _ => none
  | .u32Cto => match s.stack with
    | a :: rest => some ({ stack := .u32Cto a :: rest }, [.isU32 a])
    | _ => none

  -- U32 comparison
  | .u32Lt => match s.stack with
    | b :: a :: rest =>
      some ({ stack := .u32Lt a b :: rest }, [.isU32 a, .isU32 b])
    | _ => none
  | .u32Lte => match s.stack with
    | b :: a :: rest =>
      some ({ stack := .u32Lte a b :: rest }, [.isU32 a, .isU32 b])
    | _ => none
  | .u32Gt => match s.stack with
    | b :: a :: rest =>
      some ({ stack := .u32Gt a b :: rest }, [.isU32 a, .isU32 b])
    | _ => none
  | .u32Gte => match s.stack with
    | b :: a :: rest =>
      some ({ stack := .u32Gte a b :: rest }, [.isU32 a, .isU32 b])
    | _ => none
  | .u32Min => match s.stack with
    | b :: a :: rest =>
      some ({ stack := .u32Min a b :: rest }, [.isU32 a, .isU32 b])
    | _ => none
  | .u32Max => match s.stack with
    | b :: a :: rest =>
      some ({ stack := .u32Max a b :: rest }, [.isU32 a, .isU32 b])
    | _ => none

  -- Unsupported: memory, locals, advice, events, exec
  | .memLoad | .memLoadImm _ | .memStore | .memStoreImm _
  | .memLoadwBe | .memLoadwBeImm _ | .memStorewBe | .memStorewBeImm _
  | .memLoadwLe | .memLoadwLeImm _ | .memStorewLe | .memStorewLeImm _
  | .locLoad _ | .locStore _ | .locLoadwBe _ | .locLoadwLe _
  | .locStorewBe _ | .locStorewLe _ | .locaddr _
  | .advPush _ | .advLoadW
  | .emit | .emitImm _
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

/-- Concrete execution of a basic block as a foldlM of execInstruction. -/
def concreteExecBlock (insts : List Instruction) (cs : MidenState) :
    Option MidenState :=
  insts.foldlM (fun s i => MidenLean.execInstruction s i) cs

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
