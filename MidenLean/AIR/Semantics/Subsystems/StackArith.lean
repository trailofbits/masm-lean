import MidenLean.AIR.Semantics.Check
/-!
# StackArith AIR Implementation Layer: Step 9 bounded slice

This file extends the Rust-facing `StackArith` implementation layer from `ADD`
only to the current bounded slice: field ops through `EXT2MUL`, plus the first
`u32` grouped blocks (`U32SPLIT`, `U32ASSERT2`, `U32ADD`, `U32ADD3`,
`U32SUB`) with
the minimal shared grouped constraints needed by Rust AIR.

Each rule follows the documented and Rust-backed gated pattern

`is_transition * selector * body = 0`.

This file mirrors the currently extracted Rust AIR. It is not the place to
weaken the intended mathematical spec when Rust and the docs diverge; such
divergences should instead be modeled as spec/implementation gaps.

This subsystem file covers only op-specific arithmetic bodies and the bounded
shared grouped constraints required for these `u32` slices. Shared visible
stack-shift behavior still belongs to `StackGeneral`.
-/

namespace MidenLean.AIR.Semantics.Subsystems.StackArith

open MidenLean
open MidenLean.AIR.Semantics
open MidenLean.AIR.Semantics.Builder
open MidenLean.AIR.Semantics.Check

/-- Current-row decoder flag `b0` (`col 7`). -/
def opBit0Col : MainCol := ⟨7, by decide⟩
/-- Current-row decoder flag `b1` (`col 8`). -/
def opBit1Col : MainCol := ⟨8, by decide⟩
/-- Current-row decoder flag `b2` (`col 9`). -/
def opBit2Col : MainCol := ⟨9, by decide⟩
/-- Current-row decoder flag `b3` (`col 10`). -/
def opBit3Col : MainCol := ⟨10, by decide⟩
/-- Current-row decoder flag `b4` (`col 11`). -/
def opBit4Col : MainCol := ⟨11, by decide⟩
/-- Current-row decoder flag `b5` (`col 12`). -/
def opBit5Col : MainCol := ⟨12, by decide⟩
/-- Current-row decoder flag `b6` (`col 13`). -/
def opBit6Col : MainCol := ⟨13, by decide⟩

/-- Visible-stack `s0` column (`col 30`). -/
def s0Col : MainCol := ⟨30, by decide⟩
/-- Visible-stack `s1` column (`col 31`). -/
def s1Col : MainCol := ⟨31, by decide⟩
/-- Visible-stack `s2` column (`col 32`). -/
def s2Col : MainCol := ⟨32, by decide⟩
/-- Visible-stack `s3` column (`col 33`). -/
def s3Col : MainCol := ⟨33, by decide⟩
/-- User-op helper `h0` column (`col 16`). -/
def uopH0Col : MainCol := ⟨16, by decide⟩
/-- User-op helper `h1` column (`col 17`). -/
def uopH1Col : MainCol := ⟨17, by decide⟩
/-- User-op helper `h2` column (`col 18`). -/
def uopH2Col : MainCol := ⟨18, by decide⟩
/-- User-op helper `h3` column (`col 19`). -/
def uopH3Col : MainCol := ⟨19, by decide⟩
/-- User-op helper `h4` column (`col 20`). -/
def uopH4Col : MainCol := ⟨20, by decide⟩

/-- Current-row decoder flag expression `b0`. -/
def opBit0 : FExpr := FExpr.curr opBit0Col
/-- Current-row decoder flag expression `b1`. -/
def opBit1 : FExpr := FExpr.curr opBit1Col
/-- Current-row decoder flag expression `b2`. -/
def opBit2 : FExpr := FExpr.curr opBit2Col
/-- Current-row decoder flag expression `b3`. -/
def opBit3 : FExpr := FExpr.curr opBit3Col
/-- Current-row decoder flag expression `b4`. -/
def opBit4 : FExpr := FExpr.curr opBit4Col
/-- Current-row decoder flag expression `b5`. -/
def opBit5 : FExpr := FExpr.curr opBit5Col
/-- Current-row decoder flag expression `b6`. -/
def opBit6 : FExpr := FExpr.curr opBit6Col

def notOpBit0 : FExpr := FExpr.minus (FExpr.const 1) opBit0
def notOpBit1 : FExpr := FExpr.minus (FExpr.const 1) opBit1
def notOpBit2 : FExpr := FExpr.minus (FExpr.const 1) opBit2
def notOpBit3 : FExpr := FExpr.minus (FExpr.const 1) opBit3
def notOpBit4 : FExpr := FExpr.minus (FExpr.const 1) opBit4
def notOpBit5 : FExpr := FExpr.minus (FExpr.const 1) opBit5
def notOpBit6 : FExpr := FExpr.minus (FExpr.const 1) opBit6

/-- Canonical `s0` leaf used by the field and `u32` AIR rules. -/
def s0 : FExpr := FExpr.curr s0Col
/-- Canonical `s1` leaf used by the field and `u32` AIR rules. -/
def s1 : FExpr := FExpr.curr s1Col
/-- Canonical `s2` leaf used by the `EXPACC` AIR rules. -/
def s2 : FExpr := FExpr.curr s2Col
/-- Canonical `s3` leaf used by the `EXPACC` AIR rules. -/
def s3 : FExpr := FExpr.curr s3Col
/-- Canonical next-row `s0` leaf used by the field and `u32` AIR rules. -/
def s0Next : FExpr := FExpr.next s0Col
/-- Canonical next-row `s1` leaf used by the `EXPACC` AIR rules. -/
def s1Next : FExpr := FExpr.next s1Col
/-- Canonical next-row `s2` leaf used by the `EXPACC` AIR rules. -/
def s2Next : FExpr := FExpr.next s2Col
/-- Canonical next-row `s3` leaf used by the `EXPACC` AIR rules. -/
def s3Next : FExpr := FExpr.next s3Col
/-- Canonical current-row user-op helper `h0` leaf. -/
def uopH0 : FExpr := FExpr.curr uopH0Col
/-- Canonical current-row user-op helper `h1` leaf. -/
def uopH1 : FExpr := FExpr.curr uopH1Col
/-- Canonical current-row user-op helper `h2` leaf. -/
def uopH2 : FExpr := FExpr.curr uopH2Col
/-- Canonical current-row user-op helper `h3` leaf. -/
def uopH3 : FExpr := FExpr.curr uopH3Col
/-- Canonical current-row user-op helper `h4` leaf. -/
def uopH4 : FExpr := FExpr.curr uopH4Col

/-- Constant `2^16`. -/
def twoPow16 : FExpr := FExpr.const 65536
/-- Constant `2^32`. -/
def twoPow32 : FExpr := FExpr.const 4294967296
/-- Constant `2^48`. -/
def twoPow48 : FExpr := FExpr.const 281474976710656
/-- Constant `2^32 - 1`. -/
def twoPow32MinusOne : FExpr := FExpr.const 4294967295

/-- Rust `u32_v_lo = h1*2^16 + h0`. -/
def u32VLo : FExpr := FExpr.plus (FExpr.times uopH1 twoPow16) uopH0
/-- Rust `u32_v_hi = h3*2^16 + h2`. -/
def u32VHi : FExpr := FExpr.plus (FExpr.times uopH3 twoPow16) uopH2
/-- Rust `u32_v48 = h2*2^32 + u32_v_lo`. -/
def u32V48 : FExpr := FExpr.plus (FExpr.times uopH2 twoPow32) u32VLo
/-- Rust `u32_v64 = h3*2^48 + u32_v48`. -/
def u32V64 : FExpr := FExpr.plus (FExpr.times uopH3 twoPow48) u32V48
/-- Rust `u32_v_hi_comp = 1 - h4 * ((2^32 - 1) - u32_v_hi)`. -/
def u32VHiComp : FExpr :=
  FExpr.minus (FExpr.const 1) (FExpr.times uopH4 (FExpr.minus twoPow32MinusOne u32VHi))

/-- Canonical selector for the `ADD` opcode `010_0010` (`b6..b0`). -/
def isAdd : FExpr :=
  FExpr.times notOpBit6
    (FExpr.times opBit5
      (FExpr.times notOpBit4
        (FExpr.times notOpBit3
          (FExpr.times notOpBit2
            (FExpr.times opBit1 notOpBit0)))))

/-- Canonical AIR constraint for field `ADD`. -/
def add : BaseConstraint :=
  whenTransition <| gate isAdd <| assertEq s0Next (FExpr.plus s0 s1)

/-- Canonical selector for the `NEG` opcode `000_0010` (`b6..b0`). -/
def isNeg : FExpr :=
  FExpr.times notOpBit6
    (FExpr.times notOpBit5
      (FExpr.times notOpBit4
        (FExpr.times notOpBit3
          (FExpr.times notOpBit2
            (FExpr.times opBit1 notOpBit0)))))

/-- Canonical selector for the `MUL` opcode `010_0011` (`b6..b0`). -/
def isMul : FExpr :=
  FExpr.times notOpBit6
    (FExpr.times opBit5
      (FExpr.times notOpBit4
        (FExpr.times notOpBit3
          (FExpr.times notOpBit2
            (FExpr.times opBit1 opBit0)))))

/-- Canonical AIR constraint for field `NEG`. -/
def neg : BaseConstraint :=
  whenTransition <| gate isNeg <| assertEq s0Next (FExpr.minus (FExpr.const 0) s0)

/-- Canonical AIR constraint for field `MUL`. -/
def mul : BaseConstraint :=
  whenTransition <| gate isMul <| assertEq s0Next (FExpr.times s0 s1)

/-- Canonical selector for the `INV` opcode `000_0011` (`b6..b0`). -/
def isInv : FExpr :=
  FExpr.times notOpBit6
    (FExpr.times notOpBit5
      (FExpr.times notOpBit4
        (FExpr.times notOpBit3
          (FExpr.times notOpBit2
            (FExpr.times opBit1 opBit0)))))

/-- Canonical selector for the `INCR` opcode `000_0100` (`b6..b0`). -/
def isIncr : FExpr :=
  FExpr.times notOpBit6
    (FExpr.times notOpBit5
      (FExpr.times notOpBit4
        (FExpr.times notOpBit3
          (FExpr.times opBit2
            (FExpr.times notOpBit1 notOpBit0)))))

/-- Canonical selector for the `NOT` opcode `000_0101` (`b6..b0`). -/
def isNot : FExpr :=
  FExpr.times notOpBit6
    (FExpr.times notOpBit5
      (FExpr.times notOpBit4
        (FExpr.times notOpBit3
          (FExpr.times opBit2
            (FExpr.times notOpBit1 opBit0)))))

/-- Canonical selector for the `AND` opcode `010_0100` (`b6..b0`). -/
def isAnd : FExpr :=
  FExpr.times notOpBit6
    (FExpr.times opBit5
      (FExpr.times notOpBit4
        (FExpr.times notOpBit3
          (FExpr.times opBit2
            (FExpr.times notOpBit1 notOpBit0)))))

/-- Canonical selector for the `OR` opcode `010_0101` (`b6..b0`). -/
def isOr : FExpr :=
  FExpr.times notOpBit6
    (FExpr.times opBit5
      (FExpr.times notOpBit4
        (FExpr.times notOpBit3
          (FExpr.times opBit2
            (FExpr.times notOpBit1 opBit0)))))

/-- Canonical selector for the `EQ` opcode `010_0001` (`b6..b0`). -/
def isEq : FExpr :=
  FExpr.times notOpBit6
    (FExpr.times opBit5
      (FExpr.times notOpBit4
        (FExpr.times notOpBit3
          (FExpr.times notOpBit2
            (FExpr.times notOpBit1 opBit0)))))

/-- Canonical selector for the `EQZ` opcode `000_0001` (`b6..b0`). -/
def isEqz : FExpr :=
  FExpr.times notOpBit6
    (FExpr.times notOpBit5
      (FExpr.times notOpBit4
        (FExpr.times notOpBit3
          (FExpr.times notOpBit2
            (FExpr.times notOpBit1 opBit0)))))

/-- Canonical selector for the `EXPACC` opcode `000_1111` (`b6..b0`). -/
def isExpacc : FExpr :=
  FExpr.times notOpBit6
    (FExpr.times notOpBit5
      (FExpr.times notOpBit4
        (FExpr.times opBit3
          (FExpr.times opBit2
            (FExpr.times opBit1 opBit0)))))

/-- Canonical selector for the `EXT2MUL` opcode `001_1001` (`b6..b0`). -/
def isExt2Mul : FExpr :=
  FExpr.times notOpBit6
    (FExpr.times notOpBit5
      (FExpr.times opBit4
        (FExpr.times opBit3
          (FExpr.times notOpBit2
            (FExpr.times notOpBit1 opBit0)))))

/-- Canonical degree-6 selector for `U32ADD` (`100_000x`).
The last opcode bit is intentionally omitted (forced elsewhere in decoder constraints). -/
def isU32Add : FExpr :=
  FExpr.times opBit6
    (FExpr.times notOpBit5
      (FExpr.times notOpBit4
        (FExpr.times notOpBit3
          (FExpr.times notOpBit2 notOpBit1))))

/-- Canonical degree-6 selector for `U32MUL` (`100_010x`). -/
def isU32Mul : FExpr :=
  FExpr.times opBit6
    (FExpr.times notOpBit5
      (FExpr.times notOpBit4
        (FExpr.times notOpBit3
          (FExpr.times opBit2 notOpBit1))))

/-- Canonical degree-6 selector for `U32SPLIT` (`100_100x`). -/
def isU32Split : FExpr :=
  FExpr.times opBit6
    (FExpr.times notOpBit5
      (FExpr.times notOpBit4
        (FExpr.times opBit3
          (FExpr.times notOpBit2 notOpBit1))))

/-- Canonical degree-6 selector for `U32ASSERT2` (`100_101x`). -/
def isU32Assert2 : FExpr :=
  FExpr.times opBit6
    (FExpr.times notOpBit5
      (FExpr.times notOpBit4
        (FExpr.times opBit3
          (FExpr.times notOpBit2 opBit1))))

/-- Canonical degree-6 selector for `U32ADD3` (`100_110x`). -/
def isU32Add3 : FExpr :=
  FExpr.times opBit6
    (FExpr.times notOpBit5
      (FExpr.times notOpBit4
        (FExpr.times opBit3
          (FExpr.times opBit2 notOpBit1))))

/-- Canonical degree-6 selector for `U32SUB` (`100_001x`). -/
def isU32Sub : FExpr :=
  FExpr.times opBit6
    (FExpr.times notOpBit5
      (FExpr.times notOpBit4
        (FExpr.times notOpBit3
          (FExpr.times notOpBit2 opBit1))))

/-- Canonical degree-6 selector for `U32DIV` (`100_011x`). -/
def isU32Div : FExpr :=
  FExpr.times opBit6
    (FExpr.times notOpBit5
      (FExpr.times notOpBit4
        (FExpr.times notOpBit3
          (FExpr.times opBit2 opBit1)))))

/-- Canonical degree-6 selector for `U32MADD` (`100_111x`). -/
def isU32Madd : FExpr :=
  FExpr.times opBit6
    (FExpr.times notOpBit5
      (FExpr.times notOpBit4
        (FExpr.times opBit3
          (FExpr.times opBit2 opBit1))))

/-- Rust shared grouped selector:
`is_u32split + is_u32mul + is_u32madd`. -/
def u32SplitMulMadd : FExpr := FExpr.plus (FExpr.plus isU32Split isU32Mul) isU32Madd

/-- Rust shared grouped selector:
`is_u32split + is_u32add + is_u32add3 + is_u32mul + is_u32madd`. -/
def u32TwoOutputs : FExpr :=
  FExpr.plus (FExpr.plus (FExpr.plus (FExpr.plus isU32Split isU32Add) isU32Add3) isU32Mul) isU32Madd

/-- Canonical AIR constraint for field `INV`.
Matches Rust form `s0' * s0 - 1 = 0`. -/
def inv : BaseConstraint :=
  whenTransition <| gate isInv <| assertEq (FExpr.times s0Next s0) (FExpr.const 1)

/-- Canonical AIR constraint for field `INCR`. -/
def incr : BaseConstraint :=
  whenTransition <| gate isIncr <| assertEq s0Next (FExpr.plus s0 (FExpr.const 1))

/-- Canonical `NOT` binaryity integrity constraint: `s0 * (s0 - 1) = 0`. -/
def notBinary : BaseConstraint :=
  gate isNot <| assertZero (FExpr.times s0 (FExpr.minus s0 (FExpr.const 1)))

/-- Canonical `NOT` transition constraint: `s0 + s0' - 1 = 0`. -/
def notValue : BaseConstraint :=
  whenTransition <| gate isNot <| assertEq (FExpr.plus s0 s0Next) (FExpr.const 1)

/-- Canonical `AND` binaryity integrity constraint on `s0`. -/
def andS0Binary : BaseConstraint :=
  gate isAnd <| assertZero (FExpr.times s0 (FExpr.minus s0 (FExpr.const 1)))

/-- Canonical `AND` binaryity integrity constraint on `s1`. -/
def andS1Binary : BaseConstraint :=
  gate isAnd <| assertZero (FExpr.times s1 (FExpr.minus s1 (FExpr.const 1)))

/-- Canonical `AND` transition constraint: `s0' - s0*s1 = 0`. -/
def andValue : BaseConstraint :=
  whenTransition <| gate isAnd <| assertEq s0Next (FExpr.times s0 s1)

/-- Canonical `OR` binaryity integrity constraint on `s0`. -/
def orS0Binary : BaseConstraint :=
  gate isOr <| assertZero (FExpr.times s0 (FExpr.minus s0 (FExpr.const 1)))

/-- Canonical `OR` binaryity integrity constraint on `s1`. -/
def orS1Binary : BaseConstraint :=
  gate isOr <| assertZero (FExpr.times s1 (FExpr.minus s1 (FExpr.const 1)))

/-- Canonical `OR` transition constraint: `s0' - (s0 + s1 - s0*s1) = 0`. -/
def orValue : BaseConstraint :=
  whenTransition <| gate isOr <| assertEq s0Next (FExpr.minus (FExpr.plus s0 s1) (FExpr.times s0 s1))

/-- Canonical `EQ` transition constraint: `(s0 - s1) * s0' = 0`. -/
def eqZeroProduct : BaseConstraint :=
  whenTransition <| gate isEq <| assertZero (FExpr.times (FExpr.minus s0 s1) s0Next)

/-- Canonical `EQ` transition constraint:
`s0' - (1 - (s0 - s1) * h0) = 0`. -/
def eqValue : BaseConstraint :=
  whenTransition <| gate isEq <| assertEq s0Next
    (FExpr.minus (FExpr.const 1) (FExpr.times (FExpr.minus s0 s1) uopH0))

/-- Canonical `EQZ` transition constraint: `s0 * s0' = 0`. -/
def eqzZeroProduct : BaseConstraint :=
  whenTransition <| gate isEqz <| assertZero (FExpr.times s0 s0Next)

/-- Canonical `EQZ` transition constraint:
`s0' - (1 - s0 * h0) = 0`. -/
def eqzValue : BaseConstraint :=
  whenTransition <| gate isEqz <| assertEq s0Next
    (FExpr.minus (FExpr.const 1) (FExpr.times s0 uopH0))

/-- Canonical `EXPACC` transition constraint:
`s1' - s1*s1 = 0`. -/
def expaccExpSquare : BaseConstraint :=
  whenTransition <| gate isExpacc <| assertEq s1Next (FExpr.times s1 s1)

/-- Canonical `EXPACC` transition constraint:
`h0 - 1 - (s1 - 1)*s0' = 0`. -/
def expaccExpVal : BaseConstraint :=
  whenTransition <| gate isExpacc <| assertZero
    (FExpr.minus (FExpr.minus uopH0 (FExpr.const 1))
      (FExpr.times (FExpr.minus s1 (FExpr.const 1)) s0Next))

/-- Canonical `EXPACC` transition constraint:
`s2' - s2*h0 = 0`. -/
def expaccAccUpdate : BaseConstraint :=
  whenTransition <| gate isExpacc <| assertEq s2Next (FExpr.times s2 uopH0)

/-- Canonical `EXPACC` transition constraint:
`s3 - 2*s3' - s0' = 0`. -/
def expaccExpShift : BaseConstraint :=
  whenTransition <| gate isExpacc <| assertZero
    (FExpr.minus (FExpr.minus s3 (FExpr.times s3Next (FExpr.const 2))) s0Next)

/-- Canonical `EXPACC` transition constraint:
`s0' * (s0' - 1) = 0`. -/
def expaccBitBinary : BaseConstraint :=
  whenTransition <| gate isExpacc <| assertZero
    (FExpr.times s0Next (FExpr.minus s0Next (FExpr.const 1)))

/-- Canonical `EXT2MUL` transition constraint:
`s0' - s0 = 0`. -/
def ext2mulD0Unchanged : BaseConstraint :=
  whenTransition <| gate isExt2Mul <| assertEq s0Next s0

/-- Canonical `EXT2MUL` transition constraint:
`s1' - s1 = 0`. -/
def ext2mulD1Unchanged : BaseConstraint :=
  whenTransition <| gate isExt2Mul <| assertEq s1Next s1

/-- Canonical `EXT2MUL` transition constraint:
`s2' - (s2*s0 + 7*s3*s1) = 0`. -/
def ext2mulC0 : BaseConstraint :=
  whenTransition <| gate isExt2Mul <| assertEq s2Next
    (FExpr.plus (FExpr.times s2 s0)
      (FExpr.times (FExpr.const 7) (FExpr.times s3 s1)))

/-- Canonical `EXT2MUL` transition constraint:
`s3' - ((s2 + s3)*(s0 + s1) - s2*s0 - s3*s1) = 0`. -/
def ext2mulC1 : BaseConstraint :=
  whenTransition <| gate isExt2Mul <| assertEq s3Next
    (FExpr.minus
      (FExpr.minus (FExpr.times (FExpr.plus s2 s3) (FExpr.plus s0 s1))
        (FExpr.times s2 s0))
      (FExpr.times s3 s1))

/-- Canonical grouped `u32` integrity constraint from Rust:
`(is_u32split + is_u32mul + is_u32madd) * (u32_v_hi_comp * u32_v_lo) = 0`. -/
def u32SplitMulMaddValidity : BaseConstraint :=
  gate u32SplitMulMadd <| assertZero (FExpr.times u32VHiComp u32VLo)

/-- Canonical grouped `u32` transition constraint from Rust:
`u32_two_outputs * (s0' - u32_v_lo) = 0`. -/
def u32TwoOutputsLo : BaseConstraint :=
  whenTransition <| gate u32TwoOutputs <| assertEq s0Next u32VLo

/-- Canonical grouped `u32` transition constraint from Rust:
`u32_two_outputs * (s1' - u32_v_hi) = 0`. -/
def u32TwoOutputsHi : BaseConstraint :=
  whenTransition <| gate u32TwoOutputs <| assertEq s1Next u32VHi

/-- Canonical `U32SPLIT` integrity constraint:
`s0 - u32_v64 = 0`. -/
def u32SplitInput : BaseConstraint :=
  gate isU32Split <| assertEq s0 u32V64

/-- Canonical `U32ADD` integrity constraint:
`s0 + s1 - u32_v48 = 0`. -/
def u32AddInput : BaseConstraint :=
  gate isU32Add <| assertEq (FExpr.plus s0 s1) u32V48

/-- Canonical `U32ADD3` integrity constraint:
`s0 + s1 + s2 - u32_v48 = 0`. -/
def u32Add3Input : BaseConstraint :=
  gate isU32Add3 <| assertEq (FExpr.plus (FExpr.plus s0 s1) s2) u32V48

/-- Canonical `U32MUL` integrity constraint:
`s0 * s1 - u32_v64 = 0`. -/
def u32Mul : BaseConstraint :=
  gate isU32Mul <| assertEq (FExpr.times s0 s1) u32V64

/-- Canonical `U32MADD` integrity constraint:
`s0 * s1 + s2 - u32_v64 = 0`. -/
def u32Madd : BaseConstraint :=
  gate isU32Madd <| assertEq (FExpr.plus (FExpr.times s0 s1) s2) u32V64

/-- Canonical `U32SUB` transition constraint:
`s1 - s0 - s1' + s0' * 2^32 = 0`. -/
def u32SubDiff : BaseConstraint :=
  whenTransition <| gate isU32Sub <| assertZero
    (FExpr.plus (FExpr.minus (FExpr.minus s1 s0) s1Next) (FExpr.times s0Next twoPow32))

/-- Canonical `U32SUB` transition constraint:
`s0' * (s0' - 1) = 0`. -/
def u32SubBorrowBinary : BaseConstraint :=
  whenTransition <| gate isU32Sub <| assertZero
    (FExpr.times s0Next (FExpr.minus s0Next (FExpr.const 1)))

/-- Canonical `U32SUB` transition constraint:
`s1' - u32_v_lo = 0`. -/
def u32SubLow : BaseConstraint :=
  whenTransition <| gate isU32Sub <| assertEq s1Next u32VLo

/-- Canonical `U32DIV` transition constraint:
`s1 - (s0 * s1' + s0') = 0`. -/
def u32DivDividend : BaseConstraint :=
  whenTransition <| gate isU32Div <| assertZero
    (FExpr.minus s1 (FExpr.plus (FExpr.times s0 s1Next) s0Next))

/-- Canonical `U32DIV` transition constraint:
`s1 - s1' - u32_v_lo = 0`. -/
def u32DivLow : BaseConstraint :=
  whenTransition <| gate isU32Div <| assertZero
    (FExpr.minus (FExpr.minus s1 s1Next) u32VLo)

/-- Canonical `U32DIV` transition constraint:
`s0 - s0' - (u32_v_hi + 1) = 0`. -/
def u32DivHigh : BaseConstraint :=
  whenTransition <| gate isU32Div <| assertZero
    (FExpr.minus (FExpr.minus s0 s0Next) (FExpr.plus u32VHi (FExpr.const 1)))

/-- Canonical `U32ASSERT2` transition constraint:
`s0' - u32_v_hi = 0`. -/
def u32Assert2Hi : BaseConstraint :=
  whenTransition <| gate isU32Assert2 <| assertEq s0Next u32VHi

/-- Canonical `U32ASSERT2` transition constraint:
`s1' - u32_v_lo = 0`. -/
def u32Assert2Lo : BaseConstraint :=
  whenTransition <| gate isU32Assert2 <| assertEq s1Next u32VLo

/-- Step 9 bounded-slice canonical `StackArith` base constraints. -/
def base : BaseConstraintSet := allOf
  [add, neg, mul, inv, incr, notBinary, notValue, andS0Binary, andS1Binary, andValue,
   orS0Binary, orS1Binary, orValue, eqZeroProduct, eqValue, eqzZeroProduct, eqzValue,
   expaccExpSquare, expaccExpVal, expaccAccUpdate, expaccExpShift, expaccBitBinary,
   ext2mulD0Unchanged, ext2mulD1Unchanged, ext2mulC0, ext2mulC1,
   u32SplitMulMaddValidity, u32TwoOutputsLo, u32TwoOutputsHi, u32SplitInput, u32AddInput,
   u32Add3Input, u32Mul, u32Madd, u32SubDiff, u32SubBorrowBinary, u32SubLow,
   u32DivDividend, u32DivLow, u32DivHigh, u32Assert2Hi, u32Assert2Lo]

private def addCurr (j : MainCol) : Felt :=
  match j.val with
  | 8 => 1
  | 12 => 1
  | 30 => 3
  | 31 => 4
  | _ => 0

private def goodAddNext (j : MainCol) : Felt :=
  match j.val with
  | 30 => 7
  | _ => 0

private def badAddNext (j : MainCol) : Felt :=
  match j.val with
  | 30 => 8
  | _ => 0

private def goodAddRow : AirRow := {
  curr := addCurr
  next := goodAddNext
  isTransition := 1
}

private def badAddRow : AirRow := {
  curr := addCurr
  next := badAddNext
  isTransition := 1
}

private def negCurr (j : MainCol) : Felt :=
  match j.val with
  | 8 => 1
  | 30 => 3
  | _ => 0

private def goodNegNext (j : MainCol) : Felt :=
  match j.val with
  | 30 => (0 : Felt) - 3
  | _ => 0

private def badNegNext (j : MainCol) : Felt :=
  match j.val with
  | 30 => 2
  | _ => 0

private def goodNegRow : AirRow := {
  curr := negCurr
  next := goodNegNext
  isTransition := 1
}

private def badNegRow : AirRow := {
  curr := negCurr
  next := badNegNext
  isTransition := 1
}

private def mulCurr (j : MainCol) : Felt :=
  match j.val with
  | 7 => 1
  | 8 => 1
  | 12 => 1
  | 30 => 3
  | 31 => 4
  | _ => 0

private def goodMulNext (j : MainCol) : Felt :=
  match j.val with
  | 30 => 12
  | _ => 0

private def badMulNext (j : MainCol) : Felt :=
  match j.val with
  | 30 => 11
  | _ => 0

private def goodMulRow : AirRow := {
  curr := mulCurr
  next := goodMulNext
  isTransition := 1
}

private def badMulRow : AirRow := {
  curr := mulCurr
  next := badMulNext
  isTransition := 1
}

private def invCurr (j : MainCol) : Felt :=
  match j.val with
  | 7 => 1
  | 8 => 1
  | 30 => 1
  | _ => 0

private def goodInvNext (j : MainCol) : Felt :=
  match j.val with
  | 30 => 1
  | _ => 0

private def badInvNext (j : MainCol) : Felt :=
  match j.val with
  | 30 => 2
  | _ => 0

private def goodInvRow : AirRow := {
  curr := invCurr
  next := goodInvNext
  isTransition := 1
}

private def badInvRow : AirRow := {
  curr := invCurr
  next := badInvNext
  isTransition := 1
}

private def incrCurr (j : MainCol) : Felt :=
  match j.val with
  | 9 => 1
  | 30 => 3
  | _ => 0

private def goodIncrNext (j : MainCol) : Felt :=
  match j.val with
  | 30 => 4
  | _ => 0

private def badIncrNext (j : MainCol) : Felt :=
  match j.val with
  | 30 => 5
  | _ => 0

private def goodIncrRow : AirRow := {
  curr := incrCurr
  next := goodIncrNext
  isTransition := 1
}

private def badIncrRow : AirRow := {
  curr := incrCurr
  next := badIncrNext
  isTransition := 1
}

private def notCurr (j : MainCol) : Felt :=
  match j.val with
  | 7 => 1
  | 9 => 1
  | 30 => 1
  | _ => 0

private def goodNotNext (j : MainCol) : Felt :=
  match j.val with
  | 30 => 0
  | _ => 0

private def badNotNext (j : MainCol) : Felt :=
  match j.val with
  | 30 => 1
  | _ => 0

private def goodNotRow : AirRow := {
  curr := notCurr
  next := goodNotNext
  isTransition := 1
}

private def badNotRow : AirRow := {
  curr := notCurr
  next := badNotNext
  isTransition := 1
}

private def andCurr (j : MainCol) : Felt :=
  match j.val with
  | 9 => 1
  | 12 => 1
  | 30 => 1
  | 31 => 1
  | _ => 0

private def goodAndNext (j : MainCol) : Felt :=
  match j.val with
  | 30 => 1
  | _ => 0

private def badAndNext (j : MainCol) : Felt :=
  match j.val with
  | 30 => 0
  | _ => 0

private def goodAndRow : AirRow := {
  curr := andCurr
  next := goodAndNext
  isTransition := 1
}

private def badAndRow : AirRow := {
  curr := andCurr
  next := badAndNext
  isTransition := 1
}

private def orCurr (j : MainCol) : Felt :=
  match j.val with
  | 7 => 1
  | 9 => 1
  | 12 => 1
  | 30 => 1
  | 31 => 0
  | _ => 0

private def goodOrNext (j : MainCol) : Felt :=
  match j.val with
  | 30 => 1
  | _ => 0

private def badOrNext (j : MainCol) : Felt :=
  match j.val with
  | 30 => 0
  | _ => 0

private def goodOrRow : AirRow := {
  curr := orCurr
  next := goodOrNext
  isTransition := 1
}

private def badOrRow : AirRow := {
  curr := orCurr
  next := badOrNext
  isTransition := 1
}

private def eqCurr (j : MainCol) : Felt :=
  match j.val with
  | 7 => 1
  | 12 => 1
  | 16 => 1
  | 30 => 4
  | 31 => 3
  | _ => 0

private def goodEqNext (j : MainCol) : Felt :=
  match j.val with
  | 30 => 0
  | _ => 0

private def badEqNext (j : MainCol) : Felt :=
  match j.val with
  | 30 => 1
  | _ => 0

private def goodEqRow : AirRow := {
  curr := eqCurr
  next := goodEqNext
  isTransition := 1
}

private def badEqRow : AirRow := {
  curr := eqCurr
  next := badEqNext
  isTransition := 1
}

private def eqzCurr (j : MainCol) : Felt :=
  match j.val with
  | 7 => 1
  | 30 => 0
  | _ => 0

private def goodEqzNext (j : MainCol) : Felt :=
  match j.val with
  | 30 => 1
  | _ => 0

private def badEqzNext (j : MainCol) : Felt :=
  match j.val with
  | 30 => 0
  | _ => 0

private def goodEqzRow : AirRow := {
  curr := eqzCurr
  next := goodEqzNext
  isTransition := 1
}

private def badEqzRow : AirRow := {
  curr := eqzCurr
  next := badEqzNext
  isTransition := 1
}

private def expaccCurr (j : MainCol) : Felt :=
  match j.val with
  | 7 => 1
  | 8 => 1
  | 9 => 1
  | 10 => 1
  | 16 => 2
  | 31 => 2
  | 32 => 3
  | 33 => 5
  | _ => 0

private def goodExpaccNext (j : MainCol) : Felt :=
  match j.val with
  | 30 => 1
  | 31 => 4
  | 32 => 6
  | 33 => 2
  | _ => 0

private def badExpaccNext (j : MainCol) : Felt :=
  match j.val with
  | 30 => 1
  | 31 => 5
  | 32 => 6
  | 33 => 2
  | _ => 0

private def goodExpaccRow : AirRow := {
  curr := expaccCurr
  next := goodExpaccNext
  isTransition := 1
}

private def badExpaccRow : AirRow := {
  curr := expaccCurr
  next := badExpaccNext
  isTransition := 1
}

private def ext2mulCurr (j : MainCol) : Felt :=
  match j.val with
  | 7 => 1
  | 10 => 1
  | 11 => 1
  | 30 => 2
  | 31 => 3
  | 32 => 5
  | 33 => 7
  | _ => 0

private def goodExt2MulNext (j : MainCol) : Felt :=
  match j.val with
  | 30 => 2
  | 31 => 3
  | 32 => 157
  | 33 => 29
  | _ => 0

private def badExt2MulNext (j : MainCol) : Felt :=
  match j.val with
  | 30 => 2
  | 31 => 3
  | 32 => 158
  | 33 => 29
  | _ => 0

private def goodExt2MulRow : AirRow := {
  curr := ext2mulCurr
  next := goodExt2MulNext
  isTransition := 1
}

private def badExt2MulRow : AirRow := {
  curr := ext2mulCurr
  next := badExt2MulNext
  isTransition := 1
}

private def u32SplitCurr (j : MainCol) : Felt :=
  match j.val with
  | 10 => 1
  | 13 => 1
  | _ => 0

private def goodU32SplitNext (j : MainCol) : Felt :=
  match j.val with
  | _ => 0

private def badU32SplitNext (j : MainCol) : Felt :=
  match j.val with
  | 30 => 1
  | _ => 0

private def goodU32SplitRow : AirRow := {
  curr := u32SplitCurr
  next := goodU32SplitNext
  isTransition := 1
}

private def badU32SplitRow : AirRow := {
  curr := u32SplitCurr
  next := badU32SplitNext
  isTransition := 1
}

private def u32Assert2Curr (j : MainCol) : Felt :=
  match j.val with
  | 8 => 1
  | 10 => 1
  | 13 => 1
  | 16 => 9
  | 18 => 4
  | _ => 0

private def goodU32Assert2Next (j : MainCol) : Felt :=
  match j.val with
  | 30 => 4
  | 31 => 9
  | _ => 0

private def badU32Assert2Next (j : MainCol) : Felt :=
  match j.val with
  | 30 => 4
  | 31 => 8
  | _ => 0

private def goodU32Assert2Row : AirRow := {
  curr := u32Assert2Curr
  next := goodU32Assert2Next
  isTransition := 1
}

private def badU32Assert2Row : AirRow := {
  curr := u32Assert2Curr
  next := badU32Assert2Next
  isTransition := 1
}

private def u32SubCurr (j : MainCol) : Felt :=
  match j.val with
  | 8 => 1
  | 13 => 1
  | 16 => 4
  | 30 => 5
  | 31 => 9
  | _ => 0

private def goodU32SubNext (j : MainCol) : Felt :=
  match j.val with
  | 30 => 0
  | 31 => 4
  | _ => 0

private def badU32SubNext (j : MainCol) : Felt :=
  match j.val with
  | 30 => 0
  | 31 => 5
  | _ => 0

private def goodU32SubRow : AirRow := {
  curr := u32SubCurr
  next := goodU32SubNext
  isTransition := 1
}

private def badU32SubRow : AirRow := {
  curr := u32SubCurr
  next := badU32SubNext
  isTransition := 1
}

#eval checkBase goodAddRow base
#eval checkBase badAddRow base
#eval checkBase goodNegRow base
#eval checkBase badNegRow base
#eval checkBase goodMulRow base
#eval checkBase badMulRow base
#eval checkBase goodInvRow base
#eval checkBase badInvRow base
#eval checkBase goodIncrRow base
#eval checkBase badIncrRow base
#eval checkBase goodNotRow base
#eval checkBase badNotRow base
#eval checkBase goodAndRow base
#eval checkBase badAndRow base
#eval checkBase goodOrRow base
#eval checkBase badOrRow base
#eval checkBase goodEqRow base
#eval checkBase badEqRow base
#eval checkBase goodEqzRow base
#eval checkBase badEqzRow base
#eval checkBase goodExpaccRow base
#eval checkBase badExpaccRow base
#eval checkBase goodExt2MulRow base
#eval checkBase badExt2MulRow base
#eval checkBase goodU32SplitRow base
#eval checkBase badU32SplitRow base
#eval checkBase goodU32Assert2Row base
#eval checkBase badU32Assert2Row base
#eval checkBase goodU32SubRow base
#eval checkBase badU32SubRow base

end MidenLean.AIR.Semantics.Subsystems.StackArith
