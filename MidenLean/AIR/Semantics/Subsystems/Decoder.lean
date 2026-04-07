import MidenLean.AIR.Semantics.Check
/-!
# Decoder AIR Implementation Layer (Partial)

This file encodes a partial canonical decoder AIR slice backed by
`air/src/constraints/decoder/mod.rs`.

The current file covers only the first requested structural slice:

- in-span boundary, binary, and transition rules,
- opcode-bit binary rules,
- extra degree-reduction columns `e0` and `e1`,
- opcode-family bit exclusions,
- batch-flag binary rules,
- group-count transition rules.

The remaining decoder constraints are still TODO.
-/

namespace MidenLean.AIR.Semantics.Subsystems.Decoder

open MidenLean
open MidenLean.AIR.Semantics
open MidenLean.AIR.Semantics.Builder
open MidenLean.AIR.Semantics.Check

/-- Decoder trace columns start at main-trace column `6`. -/
def decoderTraceOffset : Nat := 6

/-- Current-row decoder address column (`col 6`). -/
def addrCol : MainCol := ⟨decoderTraceOffset + 0, by decide⟩

/-- Current-row decoder opcode bit `b0` (`col 7`). -/
def opBit0Col : MainCol := ⟨decoderTraceOffset + 1, by decide⟩
/-- Current-row decoder opcode bit `b1` (`col 8`). -/
def opBit1Col : MainCol := ⟨decoderTraceOffset + 2, by decide⟩
/-- Current-row decoder opcode bit `b2` (`col 9`). -/
def opBit2Col : MainCol := ⟨decoderTraceOffset + 3, by decide⟩
/-- Current-row decoder opcode bit `b3` (`col 10`). -/
def opBit3Col : MainCol := ⟨decoderTraceOffset + 4, by decide⟩
/-- Current-row decoder opcode bit `b4` (`col 11`). -/
def opBit4Col : MainCol := ⟨decoderTraceOffset + 5, by decide⟩
/-- Current-row decoder opcode bit `b5` (`col 12`). -/
def opBit5Col : MainCol := ⟨decoderTraceOffset + 6, by decide⟩
/-- Current-row decoder opcode bit `b6` (`col 13`). -/
def opBit6Col : MainCol := ⟨decoderTraceOffset + 7, by decide⟩

/-- Current-row decoder hasher lane `h0` (`col 14`). -/
def decoderH0Col : MainCol := ⟨decoderTraceOffset + 8, by decide⟩
/-- Current-row decoder hasher lane `h1` (`col 15`). -/
def decoderH1Col : MainCol := ⟨decoderTraceOffset + 9, by decide⟩
/-- Current-row decoder hasher lane `h2` (`col 16`). -/
def decoderH2Col : MainCol := ⟨decoderTraceOffset + 10, by decide⟩
/-- Current-row decoder hasher lane `h3` (`col 17`). -/
def decoderH3Col : MainCol := ⟨decoderTraceOffset + 11, by decide⟩
/-- Current-row decoder hasher lane `h4` (`col 18`). -/
def decoderH4Col : MainCol := ⟨decoderTraceOffset + 12, by decide⟩
/-- Current-row decoder hasher lane `h5` (`col 19`). -/
def decoderH5Col : MainCol := ⟨decoderTraceOffset + 13, by decide⟩
/-- Current-row decoder hasher lane `h6` (`col 20`). -/
def decoderH6Col : MainCol := ⟨decoderTraceOffset + 14, by decide⟩
/-- Current-row decoder hasher lane `h7` (`col 21`). -/
def decoderH7Col : MainCol := ⟨decoderTraceOffset + 15, by decide⟩

/-- Current-row in-span flag `sp` (`col 22`). -/
def inSpanCol : MainCol := ⟨decoderTraceOffset + 16, by decide⟩
/-- Current-row group-count column `gc` (`col 23`). -/
def groupCountCol : MainCol := ⟨decoderTraceOffset + 17, by decide⟩
/-- Current-row op-index column `ox` (`col 24`). -/
def opIndexCol : MainCol := ⟨decoderTraceOffset + 18, by decide⟩

/-- Current-row batch flag `c0` (`col 25`). -/
def batchFlag0Col : MainCol := ⟨decoderTraceOffset + 19, by decide⟩
/-- Current-row batch flag `c1` (`col 26`). -/
def batchFlag1Col : MainCol := ⟨decoderTraceOffset + 20, by decide⟩
/-- Current-row batch flag `c2` (`col 27`). -/
def batchFlag2Col : MainCol := ⟨decoderTraceOffset + 21, by decide⟩

/-- Current-row extra column `e0` (`col 28`). -/
def extra0Col : MainCol := ⟨decoderTraceOffset + 22, by decide⟩
/-- Current-row extra column `e1` (`col 29`). -/
def extra1Col : MainCol := ⟨decoderTraceOffset + 23, by decide⟩

/-- Current-row visible stack top `s0` (`col 30`). -/
def s0Col : MainCol := ⟨decoderTraceOffset + 24, by decide⟩

/-- Current-row decoder address expression. -/
def addr : FExpr := FExpr.curr addrCol

/-- Current-row decoder opcode bit expressions. -/
def opBit0 : FExpr := FExpr.curr opBit0Col
def opBit1 : FExpr := FExpr.curr opBit1Col
def opBit2 : FExpr := FExpr.curr opBit2Col
def opBit3 : FExpr := FExpr.curr opBit3Col
def opBit4 : FExpr := FExpr.curr opBit4Col
def opBit5 : FExpr := FExpr.curr opBit5Col
def opBit6 : FExpr := FExpr.curr opBit6Col

/-- Next-row decoder opcode bit expressions. -/
def opBit0Next : FExpr := FExpr.next opBit0Col
def opBit1Next : FExpr := FExpr.next opBit1Col
def opBit2Next : FExpr := FExpr.next opBit2Col
def opBit3Next : FExpr := FExpr.next opBit3Col
def opBit4Next : FExpr := FExpr.next opBit4Col
def opBit5Next : FExpr := FExpr.next opBit5Col
def opBit6Next : FExpr := FExpr.next opBit6Col

/-- Current-row decoder hasher-lane expressions. -/
def decoderH0 : FExpr := FExpr.curr decoderH0Col
def decoderH1 : FExpr := FExpr.curr decoderH1Col
def decoderH2 : FExpr := FExpr.curr decoderH2Col
def decoderH3 : FExpr := FExpr.curr decoderH3Col
def decoderH4 : FExpr := FExpr.curr decoderH4Col
def decoderH5 : FExpr := FExpr.curr decoderH5Col
def decoderH6 : FExpr := FExpr.curr decoderH6Col
def decoderH7 : FExpr := FExpr.curr decoderH7Col

/-- Current-row in-span flag `sp`. -/
def inSpan : FExpr := FExpr.curr inSpanCol
/-- Next-row in-span flag `sp'`. -/
def inSpanNext : FExpr := FExpr.next inSpanCol

/-- Current-row group-count expression `gc`. -/
def groupCount : FExpr := FExpr.curr groupCountCol
/-- Next-row group-count expression `gc'`. -/
def groupCountNext : FExpr := FExpr.next groupCountCol

/-- Current-row op-index expression `ox`. -/
def opIndex : FExpr := FExpr.curr opIndexCol

/-- Current-row batch-flag expressions. -/
def batchFlag0 : FExpr := FExpr.curr batchFlag0Col
def batchFlag1 : FExpr := FExpr.curr batchFlag1Col
def batchFlag2 : FExpr := FExpr.curr batchFlag2Col

/-- Current-row extra-column expressions. -/
def extra0 : FExpr := FExpr.curr extra0Col
def extra1 : FExpr := FExpr.curr extra1Col

/-- Current-row visible stack-top expression `s0`. -/
def s0 : FExpr := FExpr.curr s0Col

/-- Canonical `1 - x` helper. -/
def oneMinus (x : FExpr) : FExpr := FExpr.minus (FExpr.const 1) x

def notOpBit0 : FExpr := oneMinus opBit0
def notOpBit1 : FExpr := oneMinus opBit1
def notOpBit2 : FExpr := oneMinus opBit2
def notOpBit3 : FExpr := oneMinus opBit3
def notOpBit4 : FExpr := oneMinus opBit4
def notOpBit5 : FExpr := oneMinus opBit5
def notOpBit6 : FExpr := oneMinus opBit6

def notOpBit0Next : FExpr := oneMinus opBit0Next
def notOpBit1Next : FExpr := oneMinus opBit1Next
def notOpBit2Next : FExpr := oneMinus opBit2Next
def notOpBit3Next : FExpr := oneMinus opBit3Next
def notOpBit4Next : FExpr := oneMinus opBit4Next
def notOpBit5Next : FExpr := oneMinus opBit5Next
def notOpBit6Next : FExpr := oneMinus opBit6Next

/-- Canonical binary constraint `x * (x - 1) = 0`. -/
def assertBinary (x : FExpr) : BaseConstraint :=
  assertZero <| FExpr.times x (FExpr.minus x (FExpr.const 1))

/-- Current-row group-count decrement `gc - gc'`. -/
def deltaGc : FExpr := FExpr.minus groupCount groupCountNext

/-- Canonical selector for `SPAN` (`101_0110`). -/
def isSpan : FExpr :=
  FExpr.times opBit6
    (FExpr.times notOpBit5
      (FExpr.times opBit4
        (FExpr.times notOpBit3
          (FExpr.times opBit2
            (FExpr.times opBit1 notOpBit0)))))

/-- Canonical selector for `RESPAN` (`111_1000`). -/
def isRespan : FExpr :=
  FExpr.times opBit6
    (FExpr.times opBit5
      (FExpr.times opBit4
        (FExpr.times opBit3
          (FExpr.times notOpBit2
            (FExpr.times notOpBit1 notOpBit0)))))

/-- Canonical selector for `END` (`111_0000`). -/
def isEnd : FExpr :=
  FExpr.times opBit6
    (FExpr.times opBit5
      (FExpr.times opBit4
        (FExpr.times notOpBit3
          (FExpr.times notOpBit2
            (FExpr.times notOpBit1 notOpBit0)))))

/-- Canonical selector for `PUSH` (`101_1011`). -/
def isPush : FExpr :=
  FExpr.times opBit6
    (FExpr.times notOpBit5
      (FExpr.times opBit4
        (FExpr.times opBit3
          (FExpr.times notOpBit2
            (FExpr.times opBit1 opBit0)))))

/-- Canonical selector for `HALT` (`111_1100`). -/
def isHalt : FExpr :=
  FExpr.times opBit6
    (FExpr.times opBit5
      (FExpr.times opBit4
        (FExpr.times opBit3
          (FExpr.times opBit2
            (FExpr.times notOpBit1 notOpBit0)))))

/-- Canonical next-row selector for `RESPAN` (`111_1000`). -/
def isRespanNext : FExpr :=
  FExpr.times opBit6Next
    (FExpr.times opBit5Next
      (FExpr.times opBit4Next
        (FExpr.times opBit3Next
          (FExpr.times notOpBit2Next
            (FExpr.times notOpBit1Next notOpBit0Next)))))

/-- Canonical next-row selector for `END` (`111_0000`). -/
def isEndNext : FExpr :=
  FExpr.times opBit6Next
    (FExpr.times opBit5Next
      (FExpr.times opBit4Next
        (FExpr.times notOpBit3Next
          (FExpr.times notOpBit2Next
            (FExpr.times notOpBit1Next notOpBit0Next)))))

/-- Canonical first-row constraint `sp[0] = 0`. -/
def inSpanFirst : BaseConstraint :=
  gate (FExpr.boundary BoundaryFlag.first) <| assertZero inSpan

/-- Canonical in-span binary constraint. -/
def inSpanBinary : BaseConstraint := assertBinary inSpan

/-- Canonical transition constraint `SPAN -> sp' = 1`. -/
def inSpanAfterSpan : BaseConstraint :=
  whenTransition <| gate isSpan <| assertZero (oneMinus inSpanNext)

/-- Canonical transition constraint `RESPAN -> sp' = 1`. -/
def inSpanAfterRespan : BaseConstraint :=
  whenTransition <| gate isRespan <| assertZero (oneMinus inSpanNext)

/-- Partial in-span decoder constraints. -/
def inSpanPartial1 : BaseConstraintSet :=
  [inSpanFirst, inSpanBinary, inSpanAfterSpan, inSpanAfterRespan]

/-- Canonical opcode-bit binary constraints. -/
def opBit0Binary : BaseConstraint := assertBinary opBit0
def opBit1Binary : BaseConstraint := assertBinary opBit1
def opBit2Binary : BaseConstraint := assertBinary opBit2
def opBit3Binary : BaseConstraint := assertBinary opBit3
def opBit4Binary : BaseConstraint := assertBinary opBit4
def opBit5Binary : BaseConstraint := assertBinary opBit5
def opBit6Binary : BaseConstraint := assertBinary opBit6

/-- Partial opcode-bit binary constraints. -/
def opBitsBinaryPartial1 : BaseConstraintSet :=
  [opBit0Binary, opBit1Binary, opBit2Binary, opBit3Binary, opBit4Binary, opBit5Binary, opBit6Binary]

/-- Canonical extra-column constraint `e0 = b6 * (1 - b5) * b4`. -/
def extra0Correct : BaseConstraint :=
  assertZero <|
    FExpr.minus extra0 (FExpr.times opBit6 (FExpr.times notOpBit5 opBit4))

/-- Canonical extra-column constraint `e1 = b6 * b5`. -/
def extra1Correct : BaseConstraint :=
  assertZero <| FExpr.minus extra1 (FExpr.times opBit6 opBit5)

/-- Partial extra-column constraints. -/
def extraColumnsPartial1 : BaseConstraintSet := [extra0Correct, extra1Correct]

/-- Canonical U32-prefix exclusion `b6 * (1 - b5) * (1 - b4) * b0 = 0`. -/
def u32PrefixBit0 : BaseConstraint :=
  assertZero <|
    FExpr.times (FExpr.times opBit6 (FExpr.times notOpBit5 notOpBit4)) opBit0

/-- Canonical very-high prefix exclusion `b6 * b5 * b0 = 0`. -/
def veryHighBit0 : BaseConstraint :=
  assertZero <| FExpr.times (FExpr.times opBit6 opBit5) opBit0

/-- Canonical very-high prefix exclusion `b6 * b5 * b1 = 0`. -/
def veryHighBit1 : BaseConstraint :=
  assertZero <| FExpr.times (FExpr.times opBit6 opBit5) opBit1

/-- Partial grouped opcode-bit constraints. -/
def opBitGroupPartial1 : BaseConstraintSet := [u32PrefixBit0, veryHighBit0, veryHighBit1]

/-- Canonical batch-flag binary constraints. -/
def batchFlag0Binary : BaseConstraint := assertBinary batchFlag0
def batchFlag1Binary : BaseConstraint := assertBinary batchFlag1
def batchFlag2Binary : BaseConstraint := assertBinary batchFlag2

/-- Partial batch-flag binary constraints. -/
def batchFlagsBinaryPartial1 : BaseConstraintSet :=
  [batchFlag0Binary, batchFlag1Binary, batchFlag2Binary]

/-- Canonical group-count delta binary constraint inside spans. -/
def groupCountDeltaBinary : BaseConstraint :=
  whenTransition <|
    assertZero <| FExpr.times inSpan (FExpr.times deltaGc (FExpr.minus deltaGc (FExpr.const 1)))

/-- Canonical group-count decrement side condition `h0 = 0` unless the opcode is `PUSH`. -/
def groupCountDecrementH0OrPush : BaseConstraint :=
  whenTransition <|
    assertZero <|
      FExpr.times inSpan
        (FExpr.times deltaGc
          (FExpr.times (oneMinus isPush) decoderH0))

/-- Canonical decrement-forcing rule for `SPAN`, `RESPAN`, and `PUSH`. -/
def groupCountSpanDecrement : BaseConstraint :=
  whenTransition <|
    assertZero <|
      FExpr.times
        (FExpr.plus isSpan (FExpr.plus isRespan isPush))
        (FExpr.minus deltaGc (FExpr.const 1))

/-- Canonical hold rule before next-row `END` or `RESPAN`. -/
def groupCountHoldBeforeEndOrRespan : BaseConstraint :=
  whenTransition <|
    assertZero <| FExpr.times deltaGc (FExpr.plus isEndNext isRespanNext)

/-- Canonical `END -> gc = 0` constraint. -/
def groupCountZeroAtEnd : BaseConstraint :=
  assertZero <| FExpr.times isEnd groupCount

/-- Partial group-count constraints. -/
def groupCountPartial1 : BaseConstraintSet :=
  [groupCountDeltaBinary,
   groupCountDecrementH0OrPush,
   groupCountSpanDecrement,
   groupCountHoldBeforeEndOrRespan,
   groupCountZeroAtEnd]

/-- Alias for next-row opcode bit `b0`. -/
def b0Next : FExpr := opBit0Next
/-- Alias for next-row opcode bit `b1`. -/
def b1Next : FExpr := opBit1Next
/-- Alias for next-row opcode bit `b2`. -/
def b2Next : FExpr := opBit2Next
/-- Alias for next-row opcode bit `b3`. -/
def b3Next : FExpr := opBit3Next
/-- Alias for next-row opcode bit `b4`. -/
def b4Next : FExpr := opBit4Next
/-- Alias for next-row opcode bit `b5`. -/
def b5Next : FExpr := opBit5Next
/-- Alias for next-row opcode bit `b6`. -/
def b6Next : FExpr := opBit6Next

/-- Next-row decoder address expression `addr'`. -/
def addrNext : FExpr := FExpr.next addrCol

/-- Next-row decoder hasher lane `h0` expression. -/
def decoderH0Next : FExpr := FExpr.next decoderH0Col
/-- Next-row decoder hasher lane `h1` expression. -/
def decoderH1Next : FExpr := FExpr.next decoderH1Col
/-- Next-row decoder hasher lane `h2` expression. -/
def decoderH2Next : FExpr := FExpr.next decoderH2Col
/-- Next-row decoder hasher lane `h3` expression. -/
def decoderH3Next : FExpr := FExpr.next decoderH3Col
/-- Next-row decoder hasher lane `h4` expression. -/
def decoderH4Next : FExpr := FExpr.next decoderH4Col
/-- Next-row decoder hasher lane `h5` expression. -/
def decoderH5Next : FExpr := FExpr.next decoderH5Col
/-- Next-row decoder hasher lane `h6` expression. -/
def decoderH6Next : FExpr := FExpr.next decoderH6Col
/-- Next-row decoder hasher lane `h7` expression. -/
def decoderH7Next : FExpr := FExpr.next decoderH7Col

/-- Alias for the in-span flag `sp`. -/
def sp : FExpr := inSpan
/-- Alias for the next-row in-span flag `sp'`. -/
def spNext : FExpr := inSpanNext

/-- Alias for the group-count column `gc`. -/
def gc : FExpr := groupCount
/-- Alias for the next-row group-count column `gc'`. -/
def gcNext : FExpr := groupCountNext

/-- Alias for the op-index column `ox`. -/
def ox : FExpr := opIndex
/-- Next-row op-index expression `ox'`. -/
def oxNext : FExpr := FExpr.next opIndexCol

/-- Canonical selector for `SPLIT` (`101_0100`). -/
def isSplit : FExpr :=
  FExpr.times opBit6
    (FExpr.times notOpBit5
      (FExpr.times opBit4
        (FExpr.times notOpBit3
          (FExpr.times opBit2
            (FExpr.times notOpBit1 notOpBit0)))))

/-- Canonical selector for `LOOP` (`101_0101`). -/
def isLoop : FExpr :=
  FExpr.times opBit6
    (FExpr.times notOpBit5
      (FExpr.times opBit4
        (FExpr.times notOpBit3
          (FExpr.times opBit2
            (FExpr.times notOpBit1 opBit0)))))

/-- Canonical selector for `JOIN` (`101_0111`). -/
def isJoin : FExpr :=
  FExpr.times opBit6
    (FExpr.times notOpBit5
      (FExpr.times opBit4
        (FExpr.times notOpBit3
          (FExpr.times opBit2
            (FExpr.times opBit1 opBit0)))))

/-- Canonical selector for `DYN` (`101_1000`). -/
def isDyn : FExpr :=
  FExpr.times opBit6
    (FExpr.times notOpBit5
      (FExpr.times opBit4
        (FExpr.times opBit3
          (FExpr.times notOpBit2
            (FExpr.times notOpBit1 notOpBit0)))))

/-- Canonical selector for `DYNCALL` (`101_1100`). -/
def isDyncall : FExpr :=
  FExpr.times opBit6
    (FExpr.times notOpBit5
      (FExpr.times opBit4
        (FExpr.times opBit3
          (FExpr.times opBit2
            (FExpr.times notOpBit1 notOpBit0)))))

/-- Canonical selector for `SYSCALL` (`110_1000`). -/
def isSyscall : FExpr :=
  FExpr.times opBit6
    (FExpr.times opBit5
      (FExpr.times notOpBit4
        (FExpr.times opBit3
          (FExpr.times notOpBit2
            (FExpr.times notOpBit1 notOpBit0)))))

/-- Canonical selector for `CALL` (`110_1100`). -/
def isCall : FExpr :=
  FExpr.times opBit6
    (FExpr.times opBit5
      (FExpr.times notOpBit4
        (FExpr.times opBit3
          (FExpr.times opBit2
            (FExpr.times notOpBit1 notOpBit0)))))

/-- Canonical selector for `REPEAT` (`111_0100`). -/
def isRepeat : FExpr :=
  FExpr.times opBit6
    (FExpr.times opBit5
      (FExpr.times opBit4
        (FExpr.times notOpBit3
          (FExpr.times opBit2
            (FExpr.times notOpBit1 notOpBit0)))))

/-- Canonical next-row selector for `REPEAT` (`111_0100`). -/
def isRepeatNext : FExpr :=
  FExpr.times opBit6Next
    (FExpr.times opBit5Next
      (FExpr.times opBit4Next
        (FExpr.times notOpBit3Next
          (FExpr.times opBit2Next
            (FExpr.times notOpBit1Next notOpBit0Next)))))

/-- Canonical next-row selector for `HALT` (`111_1100`). -/
def isHaltNext : FExpr :=
  FExpr.times opBit6Next
    (FExpr.times opBit5Next
      (FExpr.times opBit4Next
        (FExpr.times opBit3Next
          (FExpr.times opBit2Next
            (FExpr.times notOpBit1Next notOpBit0Next)))))

/-- Shared selector `SPLIT + LOOP`. -/
def splitOrLoop : FExpr := FExpr.plus isSplit isLoop

/-- Shared selector `SPAN + RESPAN`. -/
def spanOrRespan : FExpr := FExpr.plus isSpan isRespan

/-- Shared selector `1` when group count stays unchanged inside a span. -/
def fSgc : FExpr :=
  FExpr.times sp (FExpr.times spNext (oneMinus deltaGc))

/-- Next-row opcode value `b0' + 2*b1' + ... + 64*b6'`. -/
def opNext : FExpr :=
  FExpr.plus b0Next
    (FExpr.plus (FExpr.times (FExpr.const 2) b1Next)
      (FExpr.plus (FExpr.times (FExpr.const 4) b2Next)
        (FExpr.plus (FExpr.times (FExpr.const 8) b3Next)
          (FExpr.plus (FExpr.times (FExpr.const 16) b4Next)
            (FExpr.plus (FExpr.times (FExpr.const 32) b5Next)
              (FExpr.times (FExpr.const 64) b6Next))))))

/-- Shared selector for a new group start inside a span. -/
def newGroup : FExpr := FExpr.minus deltaGc isPush

/-- Batch flag selector for an 8-group batch. -/
def fG8 : FExpr := batchFlag0

/-- Batch flag selector for a 4-group batch. -/
def fG4 : FExpr :=
  FExpr.times (oneMinus batchFlag0)
    (FExpr.times batchFlag1 (oneMinus batchFlag2))

/-- Batch flag selector for a 2-group batch. -/
def fG2 : FExpr :=
  FExpr.times (oneMinus batchFlag0)
    (FExpr.times (oneMinus batchFlag1) batchFlag2)

/-- Batch flag selector for a 1-group batch. -/
def fG1 : FExpr :=
  FExpr.times (oneMinus batchFlag0)
    (FExpr.times batchFlag1 batchFlag2)

/-- Shared selector for batches with at most 4 groups. -/
def smallBatch : FExpr := FExpr.plus fG1 (FExpr.plus fG2 fG4)

/-- Shared selector for batches with at most 2 groups. -/
def tinyBatch : FExpr := FExpr.plus fG1 fG2

/-- Control-flow selector covering `SPAN`, `JOIN`, `SPLIT`, and `LOOP`. -/
def controlFlowBlockStart : FExpr :=
  FExpr.plus isSpan (FExpr.plus isJoin (FExpr.plus isSplit isLoop))

/-- Control-flow selector covering `END`, `REPEAT`, `RESPAN`, and `HALT`. -/
def controlFlowBlockTransition : FExpr :=
  FExpr.plus isEnd (FExpr.plus isRepeat (FExpr.plus isRespan isHalt))

/-- Control-flow selector covering `DYN` and `DYNCALL`. -/
def controlFlowDynamic : FExpr := FExpr.plus isDyn isDyncall

/-- Control-flow selector covering `SYSCALL` and `CALL`. -/
def controlFlowProcedure : FExpr := FExpr.plus isSyscall isCall

/-- Shared control-flow selector `f_ctrl`. -/
def controlFlowFlag : FExpr :=
  FExpr.plus controlFlowBlockStart
    (FExpr.plus controlFlowBlockTransition
      (FExpr.plus controlFlowDynamic controlFlowProcedure))

/-- Canonical `SPLIT`/`LOOP` branch-bit binary constraint on `s0`. -/
def splitLoopS0Binary : BaseConstraint :=
  gate splitOrLoop <| assertZero <| FExpr.times s0 (FExpr.minus s0 (FExpr.const 1))

/-- Canonical `DYN -> h4 = 0` constraint. -/
def dynH4Zero : BaseConstraint := gate isDyn <| assertZero decoderH4

/-- Canonical `DYN -> h5 = 0` constraint. -/
def dynH5Zero : BaseConstraint := gate isDyn <| assertZero decoderH5

/-- Canonical `DYN -> h6 = 0` constraint. -/
def dynH6Zero : BaseConstraint := gate isDyn <| assertZero decoderH6

/-- Canonical `DYN -> h7 = 0` constraint. -/
def dynH7Zero : BaseConstraint := gate isDyn <| assertZero decoderH7

/-- Canonical `REPEAT -> s0 = 1` constraint. -/
def repeatS0One : BaseConstraint := gate isRepeat <| assertZero (oneMinus s0)

/-- Canonical `REPEAT -> h4 = 1` loop-body constraint. -/
def repeatH4One : BaseConstraint := gate isRepeat <| assertZero (oneMinus decoderH4)

/-- Canonical `END -> isLoopH5 * s0 = 0` constraint. -/
def endLoopS0Zero : BaseConstraint :=
  gate isEnd <| assertZero <| FExpr.times decoderH5 s0

/-- Canonical `END` followed by `REPEAT` carry constraint for `h0`. -/
def endRepeatCarryH0 : BaseConstraint :=
  whenTransition <|
    assertZero <|
      FExpr.times isEnd
        (FExpr.times isRepeatNext (FExpr.minus decoderH0Next decoderH0))

/-- Canonical `END` followed by `REPEAT` carry constraint for `h1`. -/
def endRepeatCarryH1 : BaseConstraint :=
  whenTransition <|
    assertZero <|
      FExpr.times isEnd
        (FExpr.times isRepeatNext (FExpr.minus decoderH1Next decoderH1))

/-- Canonical `END` followed by `REPEAT` carry constraint for `h2`. -/
def endRepeatCarryH2 : BaseConstraint :=
  whenTransition <|
    assertZero <|
      FExpr.times isEnd
        (FExpr.times isRepeatNext (FExpr.minus decoderH2Next decoderH2))

/-- Canonical `END` followed by `REPEAT` carry constraint for `h3`. -/
def endRepeatCarryH3 : BaseConstraint :=
  whenTransition <|
    assertZero <|
      FExpr.times isEnd
        (FExpr.times isRepeatNext (FExpr.minus decoderH3Next decoderH3))

/-- Canonical `END` followed by `REPEAT` carry constraint for `h4`. -/
def endRepeatCarryH4 : BaseConstraint :=
  whenTransition <|
    assertZero <|
      FExpr.times isEnd
        (FExpr.times isRepeatNext (FExpr.minus decoderH4Next decoderH4))

/-- Canonical `HALT -> HALT'` absorbing transition constraint. -/
def haltAbsorbing : BaseConstraint :=
  whenTransition <| gate isHalt <| assertZero (oneMinus isHaltNext)

/-- Remaining general decoder constraints. -/
def generalConstraints : BaseConstraintSet :=
  [splitLoopS0Binary,
   dynH4Zero,
   dynH5Zero,
   dynH6Zero,
   dynH7Zero,
   repeatS0One,
   repeatH4One,
   endLoopS0Zero,
   endRepeatCarryH0,
   endRepeatCarryH1,
   endRepeatCarryH2,
   endRepeatCarryH3,
   endRepeatCarryH4,
   haltAbsorbing]

/-- Canonical op-group shift constraint for `h0`. -/
def h0Shift : BaseConstraint :=
  whenTransition <|
    assertZero <|
      FExpr.times
        (FExpr.plus spanOrRespan (FExpr.plus isPush fSgc))
        (FExpr.minus decoderH0
          (FExpr.plus (FExpr.times decoderH0Next (FExpr.const 128)) opNext))

/-- Canonical `h0 = 0` constraint before next-row `END` or `RESPAN`. -/
def h0ZeroBeforeEndOrRespan : BaseConstraint :=
  whenTransition <|
    assertZero <|
      FExpr.times sp
        (FExpr.times (FExpr.plus isEndNext isRespanNext) decoderH0)

/-- Remaining op-group decoding constraints. -/
def opGroupDecodingConstraints : BaseConstraintSet :=
  [h0Shift, h0ZeroBeforeEndOrRespan]

/-- Canonical `SPAN`/`RESPAN` op-index reset constraint. -/
def opIndexSpanRespanReset : BaseConstraint :=
  whenTransition <|
    assertZero <| FExpr.times spanOrRespan oxNext

/-- Canonical new-group op-index reset constraint. -/
def opIndexNewGroupReset : BaseConstraint :=
  whenTransition <|
    assertZero <| FExpr.times sp (FExpr.times newGroup oxNext)

/-- Canonical in-span op-index increment constraint. -/
def opIndexIncrement : BaseConstraint :=
  whenTransition <|
    assertZero <|
      FExpr.times sp
        (FExpr.times spNext
          (FExpr.times (oneMinus newGroup)
            (FExpr.minus (FExpr.minus oxNext ox) (FExpr.const 1))))

/-- Canonical op-index range constraint `ox ∈ {0, ..., 8}`. -/
def opIndexRange : BaseConstraint :=
  assertZero <|
    FExpr.times ox
      (FExpr.times (FExpr.minus ox (FExpr.const 1))
        (FExpr.times (FExpr.minus ox (FExpr.const 2))
          (FExpr.times (FExpr.minus ox (FExpr.const 3))
            (FExpr.times (FExpr.minus ox (FExpr.const 4))
              (FExpr.times (FExpr.minus ox (FExpr.const 5))
                (FExpr.times (FExpr.minus ox (FExpr.const 6))
                  (FExpr.times (FExpr.minus ox (FExpr.const 7))
                    (FExpr.minus ox (FExpr.const 8)))))))))

/-- Remaining op-index constraints. -/
def opIndexConstraints : BaseConstraintSet :=
  [opIndexSpanRespanReset, opIndexNewGroupReset, opIndexIncrement, opIndexRange]

/-- Canonical batch-flag sum constraint for `SPAN`/`RESPAN`. -/
def batchFlagSpanSum : BaseConstraint :=
  assertZero <| FExpr.minus spanOrRespan (FExpr.plus fG1 (FExpr.plus fG2 (FExpr.plus fG4 fG8)))

/-- Canonical zero-batch-flags constraint outside `SPAN`/`RESPAN`. -/
def batchFlagZeroWhenNotSpan : BaseConstraint :=
  assertZero <|
    FExpr.times (oneMinus spanOrRespan)
      (FExpr.plus batchFlag0 (FExpr.plus batchFlag1 batchFlag2))

/-- Canonical `h4 = 0` constraint for batches with at most 4 groups. -/
def batchFlagH4Zero : BaseConstraint := gate smallBatch <| assertZero decoderH4

/-- Canonical `h5 = 0` constraint for batches with at most 4 groups. -/
def batchFlagH5Zero : BaseConstraint := gate smallBatch <| assertZero decoderH5

/-- Canonical `h6 = 0` constraint for batches with at most 4 groups. -/
def batchFlagH6Zero : BaseConstraint := gate smallBatch <| assertZero decoderH6

/-- Canonical `h7 = 0` constraint for batches with at most 4 groups. -/
def batchFlagH7Zero : BaseConstraint := gate smallBatch <| assertZero decoderH7

/-- Canonical `h2 = 0` constraint for batches with at most 2 groups. -/
def batchFlagH2Zero : BaseConstraint := gate tinyBatch <| assertZero decoderH2

/-- Canonical `h3 = 0` constraint for batches with at most 2 groups. -/
def batchFlagH3Zero : BaseConstraint := gate tinyBatch <| assertZero decoderH3

/-- Canonical `h1 = 0` constraint for 1-group batches. -/
def batchFlagH1Zero : BaseConstraint := gate fG1 <| assertZero decoderH1

/-- Remaining batch-flag constraints. -/
def batchFlagConstraints : BaseConstraintSet :=
  [batchFlagSpanSum,
   batchFlagZeroWhenNotSpan,
   batchFlagH4Zero,
   batchFlagH5Zero,
   batchFlagH6Zero,
   batchFlagH7Zero,
   batchFlagH2Zero,
   batchFlagH3Zero,
   batchFlagH1Zero]

/-- Canonical in-span address hold constraint. -/
def blockAddrHoldInSpan : BaseConstraint :=
  whenTransition <| assertZero <| FExpr.times sp (FExpr.minus addrNext addr)

/-- Canonical `RESPAN -> addr' = addr + 32` constraint. -/
def blockAddrRespanIncrement : BaseConstraint :=
  whenTransition <|
    assertZero <|
      FExpr.times isRespan
        (FExpr.minus (FExpr.minus addrNext addr) (FExpr.const 32))

/-- Canonical `HALT -> addr = 0` constraint. -/
def blockAddrHaltZero : BaseConstraint := assertZero <| FExpr.times isHalt addr

/-- Remaining block-address constraints. -/
def blockAddressConstraints : BaseConstraintSet :=
  [blockAddrHoldInSpan, blockAddrRespanIncrement, blockAddrHaltZero]

/-- Canonical control-flow complement constraint `1 - sp - f_ctrl = 0`. -/
def spComplementControlFlow : BaseConstraint :=
  assertZero <| FExpr.minus (oneMinus sp) controlFlowFlag

/-- Remaining control-flow constraints. -/
def controlFlowConstraints : BaseConstraintSet := [spComplementControlFlow]

/-- Full decoder base constraints. -/
def base : BaseConstraintSet := allOf <|
  inSpanPartial1 ++
    opBitsBinaryPartial1 ++
    extraColumnsPartial1 ++
    opBitGroupPartial1 ++
    batchFlagsBinaryPartial1 ++
    generalConstraints ++
    groupCountPartial1 ++
    opGroupDecodingConstraints ++
    opIndexConstraints ++
    batchFlagConstraints ++
    blockAddressConstraints ++
    controlFlowConstraints

private def goodBaseCurr (j : MainCol) : Felt :=
  match j.val with
  | 9 => 1
  | 10 => 1
  | 11 => 1
  | 12 => 1
  | 13 => 1
  | 29 => 1
  | _ => 0

private def goodBaseNext (j : MainCol) : Felt :=
  match j.val with
  | 9 => 1
  | 10 => 1
  | 11 => 1
  | 12 => 1
  | 13 => 1
  | _ => 0

private def badBaseCurr (j : MainCol) : Felt :=
  match j.val with
  | 7 => 2
  | 9 => 1
  | 10 => 1
  | 11 => 1
  | 12 => 1
  | 13 => 1
  | 29 => 1
  | _ => 0

private def goodBaseRow : AirRow := {
  curr := goodBaseCurr
  next := goodBaseNext
  isTransition := 1
}

private def badBaseRow : AirRow := {
  curr := badBaseCurr
  next := goodBaseNext
  isTransition := 1
}

#eval checkBase goodBaseRow base
#eval checkBase badBaseRow base

end MidenLean.AIR.Semantics.Subsystems.Decoder
