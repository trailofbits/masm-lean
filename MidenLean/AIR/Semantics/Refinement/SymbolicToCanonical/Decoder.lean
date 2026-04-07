import MidenLean.AIR.Semantics.Tactics
import MidenLean.AIR.Semantics.Subsystems.Decoder
import MidenLean.AIR.Constraints.Symbolic.Decoder

set_option maxHeartbeats 32000000

/-!
# Symbolic-to-Canonical Decoder Refinement

This bridge is intentionally honest about the current decoder mismatch.
The extracted symbolic decoder reuses the low-degree helper columns `e0`/`e1`
(`cols 28`/`29`) inside many opcode-family selectors, while the canonical
decoder semantics expands those selectors back into raw opcode bits.

As a result, the direct bridge theorems split into two classes:

- constraints that are definitionally the same and can be proved outright;
- constraints whose unconditional bridge is currently false or under-refined,
  because they need the `e0`/`e1` defining equations and, in several `e1`
  cases, additional low-bit facts for `b0`/`b1`.

The second class is kept as commented `sorry` placeholders on purpose.
-/

namespace MidenLean.AIR.Semantics.Refinement.SymbolicToCanonical

open MidenLean
open MidenLean.AIR
open MidenLean.AIR.Semantics
open MidenLean.AIR.Semantics.Tactics
open MidenLean.AIR.Semantics.Builder

private def decoderLowBit0Zero (r : AirRow) : Prop :=
  r.curr ⟨7, by decide⟩ = 0

private def decoderLowBit1Zero (r : AirRow) : Prop :=
  r.curr ⟨8, by decide⟩ = 0

private def decoderLowBit0ZeroNext (r : AirRow) : Prop :=
  r.next ⟨7, by decide⟩ = 0

private def decoderLowBit1ZeroNext (r : AirRow) : Prop :=
  r.next ⟨8, by decide⟩ = 0

private def decoderExtraCol0Eq (r : AirRow) : Prop :=
  r.curr ⟨28, by decide⟩ =
    r.curr ⟨13, by decide⟩ * (1 - r.curr ⟨12, by decide⟩) * r.curr ⟨11, by decide⟩

private def decoderExtraCol1Eq (r : AirRow) : Prop :=
  r.curr ⟨29, by decide⟩ =
    r.curr ⟨13, by decide⟩ * r.curr ⟨12, by decide⟩

private def decoderExtraCol1EqNext (r : AirRow) : Prop :=
  r.next ⟨29, by decide⟩ =
    r.next ⟨13, by decide⟩ * r.next ⟨12, by decide⟩

private theorem decoderLowBit0Zero' (r : AirRow) (h : decoderLowBit0Zero r) :
    r.curr 7 = 0 := by
  simpa [decoderLowBit0Zero] using h

private theorem decoderLowBit1Zero' (r : AirRow) (h : decoderLowBit1Zero r) :
    r.curr 8 = 0 := by
  simpa [decoderLowBit1Zero] using h

private theorem decoderExtraCol0Eq' (r : AirRow) (h : decoderExtraCol0Eq r) :
    r.curr 28 = r.curr 13 * (1 - r.curr 12) * r.curr 11 := by
  simpa [decoderExtraCol0Eq] using h

private theorem decoderExtraCol1Eq' (r : AirRow) (h : decoderExtraCol1Eq r) :
    r.curr 29 = r.curr 13 * r.curr 12 := by
  simpa [decoderExtraCol1Eq] using h

private def decoderSpanSymSel (r : AirRow) : Felt :=
  (((1 - r.curr 7) * r.curr 8) * r.curr 9) * ((1 - r.curr 10) * r.curr 28)

private def decoderRespanSymSel (r : AirRow) : Felt :=
  ((1 - r.curr 9) * r.curr 10) * (r.curr 11 * r.curr 29)

private def decoderSplitLoopSymSel (r : AirRow) : Felt :=
  ((((1 - r.curr 7) * (1 - r.curr 8)) * r.curr 9) * ((1 - r.curr 10) * r.curr 28)) +
    (((r.curr 7 * (1 - r.curr 8)) * r.curr 9) * ((1 - r.curr 10) * r.curr 28))

private def decoderDynSymSel (r : AirRow) : Felt :=
  ((((1 - r.curr 7) * (1 - r.curr 8)) * (1 - r.curr 9)) * (r.curr 10 * r.curr 28))

private def decoderRepeatSymSel (r : AirRow) : Felt :=
  (r.curr 9 * (1 - r.curr 10)) * (r.curr 11 * r.curr 29)

private def decoderEndSymSel (r : AirRow) : Felt :=
  ((1 - r.curr 9) * (1 - r.curr 10)) * (r.curr 11 * r.curr 29)

private def decoderHaltSymSel (r : AirRow) : Felt :=
  (r.curr 9 * r.curr 10) * (r.curr 11 * r.curr 29)

private def decoderPushSymSel (r : AirRow) : Felt :=
  ((r.curr 7 * r.curr 8) * (1 - r.curr 9)) * (r.curr 10 * r.curr 28)

private def decoderRepeatNextSymSel (r : AirRow) : Felt :=
  (r.next ⟨9, by decide⟩ * (1 - r.next ⟨10, by decide⟩)) *
    (r.next ⟨11, by decide⟩ * r.next ⟨29, by decide⟩)

private def decoderEndNextSymSel (r : AirRow) : Felt :=
  ((1 - r.next ⟨9, by decide⟩) * (1 - r.next ⟨10, by decide⟩)) *
    (r.next ⟨11, by decide⟩ * r.next ⟨29, by decide⟩)

private def decoderRespanNextSymSel (r : AirRow) : Felt :=
  ((1 - r.next ⟨9, by decide⟩) * r.next ⟨10, by decide⟩) *
    (r.next ⟨11, by decide⟩ * r.next ⟨29, by decide⟩)

private def decoderHaltNextSymSel (r : AirRow) : Felt :=
  (r.next ⟨9, by decide⟩ * r.next ⟨10, by decide⟩) *
    (r.next ⟨11, by decide⟩ * r.next ⟨29, by decide⟩)

private def decoderControlFlowBlockStartSymSel (r : AirRow) : Felt :=
  (r.curr 28 * (1 - r.curr 10)) * r.curr 9

private def decoderControlFlowTransitionSymSel (r : AirRow) : Felt :=
  r.curr 29 * r.curr 11

private def decoderControlFlowDynamicSymSel (r : AirRow) : Felt :=
  ((1 - r.curr 7) * (1 - r.curr 8)) * (r.curr 10 * r.curr 28)

private def decoderControlFlowProcedureSymSel (r : AirRow) : Felt :=
  (r.curr 10 * (1 - r.curr 11)) * r.curr 29

private theorem decoderSpanSel_eval (r : AirRow) (h_e0 : decoderExtraCol0Eq r) :
    Subsystems.Decoder.isSpan.eval r = decoderSpanSymSel r := by
  have h_e0' := decoderExtraCol0Eq' r h_e0
  simp [decoderSpanSymSel, Subsystems.Decoder.isSpan, Subsystems.Decoder.opBit0,
    Subsystems.Decoder.opBit1, Subsystems.Decoder.opBit2, Subsystems.Decoder.opBit3,
    Subsystems.Decoder.opBit4, Subsystems.Decoder.opBit5, Subsystems.Decoder.opBit6,
    Subsystems.Decoder.notOpBit0, Subsystems.Decoder.notOpBit3, Subsystems.Decoder.notOpBit5,
    Subsystems.Decoder.oneMinus, Subsystems.Decoder.opBit0Col, Subsystems.Decoder.opBit1Col,
    Subsystems.Decoder.opBit2Col, Subsystems.Decoder.opBit3Col, Subsystems.Decoder.opBit4Col,
    Subsystems.Decoder.opBit5Col, Subsystems.Decoder.opBit6Col, Subsystems.Decoder.decoderTraceOffset,
    FExpr.eval, AirRow.baseAt, AirRow.base]
  rw [h_e0']
  ring_nf

private theorem decoderRespanSel_eval (r : AirRow)
    (h_b0 : decoderLowBit0Zero r) (h_b1 : decoderLowBit1Zero r)
    (h_e1 : decoderExtraCol1Eq r) :
    Subsystems.Decoder.isRespan.eval r = decoderRespanSymSel r := by
  have h_b0' := decoderLowBit0Zero' r h_b0
  have h_b1' := decoderLowBit1Zero' r h_b1
  have h_e1' := decoderExtraCol1Eq' r h_e1
  simp [decoderRespanSymSel, Subsystems.Decoder.isRespan, Subsystems.Decoder.opBit0,
    Subsystems.Decoder.opBit1, Subsystems.Decoder.opBit2, Subsystems.Decoder.opBit3,
    Subsystems.Decoder.opBit4, Subsystems.Decoder.opBit5, Subsystems.Decoder.opBit6,
    Subsystems.Decoder.notOpBit0, Subsystems.Decoder.notOpBit1, Subsystems.Decoder.notOpBit2,
    Subsystems.Decoder.oneMinus, Subsystems.Decoder.opBit0Col, Subsystems.Decoder.opBit1Col,
    Subsystems.Decoder.opBit2Col, Subsystems.Decoder.opBit3Col, Subsystems.Decoder.opBit4Col,
    Subsystems.Decoder.opBit5Col, Subsystems.Decoder.opBit6Col, Subsystems.Decoder.decoderTraceOffset,
    FExpr.eval, AirRow.baseAt, AirRow.base]
  rw [h_b0', h_b1', h_e1']
  ring_nf

private theorem decoderSplitLoopSel_eval (r : AirRow) (h_e0 : decoderExtraCol0Eq r) :
    Subsystems.Decoder.splitOrLoop.eval r = decoderSplitLoopSymSel r := by
  have h_e0' := decoderExtraCol0Eq' r h_e0
  simp [decoderSplitLoopSymSel, Subsystems.Decoder.splitOrLoop, Subsystems.Decoder.isSplit,
    Subsystems.Decoder.isLoop, Subsystems.Decoder.opBit0, Subsystems.Decoder.opBit1,
    Subsystems.Decoder.opBit2, Subsystems.Decoder.opBit3, Subsystems.Decoder.opBit4,
    Subsystems.Decoder.opBit5, Subsystems.Decoder.opBit6, Subsystems.Decoder.notOpBit0,
    Subsystems.Decoder.notOpBit1, Subsystems.Decoder.notOpBit3, Subsystems.Decoder.notOpBit5,
    Subsystems.Decoder.oneMinus, Subsystems.Decoder.opBit0Col, Subsystems.Decoder.opBit1Col,
    Subsystems.Decoder.opBit2Col, Subsystems.Decoder.opBit3Col, Subsystems.Decoder.opBit4Col,
    Subsystems.Decoder.opBit5Col, Subsystems.Decoder.opBit6Col, Subsystems.Decoder.decoderTraceOffset,
    FExpr.eval, AirRow.baseAt, AirRow.base]
  rw [h_e0']
  ring_nf

private theorem decoderDynSel_eval (r : AirRow) (h_e0 : decoderExtraCol0Eq r) :
    Subsystems.Decoder.isDyn.eval r = decoderDynSymSel r := by
  have h_e0' := decoderExtraCol0Eq' r h_e0
  simp [decoderDynSymSel, Subsystems.Decoder.isDyn, Subsystems.Decoder.opBit0,
    Subsystems.Decoder.opBit1, Subsystems.Decoder.opBit2, Subsystems.Decoder.opBit3,
    Subsystems.Decoder.opBit4, Subsystems.Decoder.opBit5, Subsystems.Decoder.opBit6,
    Subsystems.Decoder.notOpBit0, Subsystems.Decoder.notOpBit1, Subsystems.Decoder.notOpBit2,
    Subsystems.Decoder.notOpBit5, Subsystems.Decoder.oneMinus, Subsystems.Decoder.opBit0Col,
    Subsystems.Decoder.opBit1Col, Subsystems.Decoder.opBit2Col, Subsystems.Decoder.opBit3Col,
    Subsystems.Decoder.opBit4Col, Subsystems.Decoder.opBit5Col, Subsystems.Decoder.opBit6Col,
    Subsystems.Decoder.decoderTraceOffset, FExpr.eval, AirRow.baseAt, AirRow.base]
  rw [h_e0']
  ring_nf

private theorem decoderRepeatSel_eval (r : AirRow)
    (h_b0 : decoderLowBit0Zero r) (h_b1 : decoderLowBit1Zero r)
    (h_e1 : decoderExtraCol1Eq r) :
    Subsystems.Decoder.isRepeat.eval r = decoderRepeatSymSel r := by
  have h_b0' := decoderLowBit0Zero' r h_b0
  have h_b1' := decoderLowBit1Zero' r h_b1
  have h_e1' := decoderExtraCol1Eq' r h_e1
  simp [decoderRepeatSymSel, Subsystems.Decoder.isRepeat, Subsystems.Decoder.opBit0,
    Subsystems.Decoder.opBit1, Subsystems.Decoder.opBit2, Subsystems.Decoder.opBit3,
    Subsystems.Decoder.opBit4, Subsystems.Decoder.opBit5, Subsystems.Decoder.opBit6,
    Subsystems.Decoder.notOpBit0, Subsystems.Decoder.notOpBit1, Subsystems.Decoder.notOpBit3,
    Subsystems.Decoder.oneMinus, Subsystems.Decoder.opBit0Col, Subsystems.Decoder.opBit1Col,
    Subsystems.Decoder.opBit2Col, Subsystems.Decoder.opBit3Col, Subsystems.Decoder.opBit4Col,
    Subsystems.Decoder.opBit5Col, Subsystems.Decoder.opBit6Col, Subsystems.Decoder.decoderTraceOffset,
    FExpr.eval, AirRow.baseAt, AirRow.base]
  rw [h_b0', h_b1', h_e1']
  ring_nf

private theorem decoderEndSel_eval (r : AirRow)
    (h_b0 : decoderLowBit0Zero r) (h_b1 : decoderLowBit1Zero r)
    (h_e1 : decoderExtraCol1Eq r) :
    Subsystems.Decoder.isEnd.eval r = decoderEndSymSel r := by
  have h_b0' := decoderLowBit0Zero' r h_b0
  have h_b1' := decoderLowBit1Zero' r h_b1
  have h_e1' := decoderExtraCol1Eq' r h_e1
  simp [decoderEndSymSel, Subsystems.Decoder.isEnd, Subsystems.Decoder.opBit0,
    Subsystems.Decoder.opBit1, Subsystems.Decoder.opBit2, Subsystems.Decoder.opBit3,
    Subsystems.Decoder.opBit4, Subsystems.Decoder.opBit5, Subsystems.Decoder.opBit6,
    Subsystems.Decoder.notOpBit0, Subsystems.Decoder.notOpBit1, Subsystems.Decoder.notOpBit2,
    Subsystems.Decoder.notOpBit3, Subsystems.Decoder.oneMinus, Subsystems.Decoder.opBit0Col,
    Subsystems.Decoder.opBit1Col, Subsystems.Decoder.opBit2Col, Subsystems.Decoder.opBit3Col,
    Subsystems.Decoder.opBit4Col, Subsystems.Decoder.opBit5Col, Subsystems.Decoder.opBit6Col,
    Subsystems.Decoder.decoderTraceOffset, FExpr.eval, AirRow.baseAt, AirRow.base]
  rw [h_b0', h_b1', h_e1']
  ring_nf

private theorem decoderHaltSel_eval (r : AirRow)
    (h_b0 : decoderLowBit0Zero r) (h_b1 : decoderLowBit1Zero r)
    (h_e1 : decoderExtraCol1Eq r) :
    Subsystems.Decoder.isHalt.eval r = decoderHaltSymSel r := by
  have h_b0' := decoderLowBit0Zero' r h_b0
  have h_b1' := decoderLowBit1Zero' r h_b1
  have h_e1' := decoderExtraCol1Eq' r h_e1
  simp [decoderHaltSymSel, Subsystems.Decoder.isHalt, Subsystems.Decoder.opBit0,
    Subsystems.Decoder.opBit1, Subsystems.Decoder.opBit2, Subsystems.Decoder.opBit3,
    Subsystems.Decoder.opBit4, Subsystems.Decoder.opBit5, Subsystems.Decoder.opBit6,
    Subsystems.Decoder.notOpBit0, Subsystems.Decoder.notOpBit1, Subsystems.Decoder.oneMinus,
    Subsystems.Decoder.opBit0Col, Subsystems.Decoder.opBit1Col, Subsystems.Decoder.opBit2Col,
    Subsystems.Decoder.opBit3Col, Subsystems.Decoder.opBit4Col, Subsystems.Decoder.opBit5Col,
    Subsystems.Decoder.opBit6Col, Subsystems.Decoder.decoderTraceOffset, FExpr.eval,
    AirRow.baseAt, AirRow.base]
  rw [h_b0', h_b1', h_e1']
  ring_nf

private theorem decoderPushSel_eval (r : AirRow) (h_e0 : decoderExtraCol0Eq r) :
    Subsystems.Decoder.isPush.eval r = decoderPushSymSel r := by
  have h_e0' := decoderExtraCol0Eq' r h_e0
  simp [decoderPushSymSel, Subsystems.Decoder.isPush, Subsystems.Decoder.opBit0,
    Subsystems.Decoder.opBit1, Subsystems.Decoder.opBit2, Subsystems.Decoder.opBit3,
    Subsystems.Decoder.opBit4, Subsystems.Decoder.opBit5, Subsystems.Decoder.opBit6,
    Subsystems.Decoder.notOpBit2, Subsystems.Decoder.notOpBit5, Subsystems.Decoder.oneMinus,
    Subsystems.Decoder.opBit0Col, Subsystems.Decoder.opBit1Col, Subsystems.Decoder.opBit2Col,
    Subsystems.Decoder.opBit3Col, Subsystems.Decoder.opBit4Col, Subsystems.Decoder.opBit5Col,
    Subsystems.Decoder.opBit6Col, Subsystems.Decoder.decoderTraceOffset, FExpr.eval,
    AirRow.baseAt, AirRow.base]
  rw [h_e0']
  ring_nf

private theorem decoderRepeatNextSel_eval (r : AirRow)
    (h_b0_next : decoderLowBit0ZeroNext r) (h_b1_next : decoderLowBit1ZeroNext r)
    (h_e1_next : decoderExtraCol1EqNext r) :
    Subsystems.Decoder.isRepeatNext.eval r = decoderRepeatNextSymSel r := by
  simp [decoderRepeatNextSymSel, Subsystems.Decoder.isRepeatNext, Subsystems.Decoder.opBit0Next,
    Subsystems.Decoder.opBit1Next, Subsystems.Decoder.opBit2Next, Subsystems.Decoder.opBit3Next,
    Subsystems.Decoder.opBit4Next, Subsystems.Decoder.opBit5Next, Subsystems.Decoder.opBit6Next,
    Subsystems.Decoder.notOpBit0Next, Subsystems.Decoder.notOpBit1Next, Subsystems.Decoder.notOpBit3Next,
    Subsystems.Decoder.oneMinus, Subsystems.Decoder.opBit0Col, Subsystems.Decoder.opBit1Col,
    Subsystems.Decoder.opBit2Col, Subsystems.Decoder.opBit3Col, Subsystems.Decoder.opBit4Col,
    Subsystems.Decoder.opBit5Col, Subsystems.Decoder.opBit6Col, Subsystems.Decoder.decoderTraceOffset,
    FExpr.eval, AirRow.baseAt, AirRow.base]
  rw [h_b0_next, h_b1_next, h_e1_next]
  ring_nf

private theorem decoderEndNextSel_eval (r : AirRow)
    (h_b0_next : decoderLowBit0ZeroNext r) (h_b1_next : decoderLowBit1ZeroNext r)
    (h_e1_next : decoderExtraCol1EqNext r) :
    Subsystems.Decoder.isEndNext.eval r = decoderEndNextSymSel r := by
  simp [decoderEndNextSymSel, Subsystems.Decoder.isEndNext, Subsystems.Decoder.opBit0Next,
    Subsystems.Decoder.opBit1Next, Subsystems.Decoder.opBit2Next, Subsystems.Decoder.opBit3Next,
    Subsystems.Decoder.opBit4Next, Subsystems.Decoder.opBit5Next, Subsystems.Decoder.opBit6Next,
    Subsystems.Decoder.notOpBit0Next, Subsystems.Decoder.notOpBit1Next, Subsystems.Decoder.notOpBit2Next,
    Subsystems.Decoder.notOpBit3Next, Subsystems.Decoder.oneMinus, Subsystems.Decoder.opBit0Col,
    Subsystems.Decoder.opBit1Col, Subsystems.Decoder.opBit2Col, Subsystems.Decoder.opBit3Col,
    Subsystems.Decoder.opBit4Col, Subsystems.Decoder.opBit5Col, Subsystems.Decoder.opBit6Col,
    Subsystems.Decoder.decoderTraceOffset, FExpr.eval, AirRow.baseAt, AirRow.base]
  rw [h_b0_next, h_b1_next, h_e1_next]
  ring_nf

private theorem decoderRespanNextSel_eval (r : AirRow)
    (h_b0_next : decoderLowBit0ZeroNext r) (h_b1_next : decoderLowBit1ZeroNext r)
    (h_e1_next : decoderExtraCol1EqNext r) :
    Subsystems.Decoder.isRespanNext.eval r = decoderRespanNextSymSel r := by
  simp [decoderRespanNextSymSel, Subsystems.Decoder.isRespanNext, Subsystems.Decoder.opBit0Next,
    Subsystems.Decoder.opBit1Next, Subsystems.Decoder.opBit2Next, Subsystems.Decoder.opBit3Next,
    Subsystems.Decoder.opBit4Next, Subsystems.Decoder.opBit5Next, Subsystems.Decoder.opBit6Next,
    Subsystems.Decoder.notOpBit0Next, Subsystems.Decoder.notOpBit1Next, Subsystems.Decoder.notOpBit2Next,
    Subsystems.Decoder.oneMinus, Subsystems.Decoder.opBit0Col, Subsystems.Decoder.opBit1Col,
    Subsystems.Decoder.opBit2Col, Subsystems.Decoder.opBit3Col, Subsystems.Decoder.opBit4Col,
    Subsystems.Decoder.opBit5Col, Subsystems.Decoder.opBit6Col, Subsystems.Decoder.decoderTraceOffset,
    FExpr.eval, AirRow.baseAt, AirRow.base]
  rw [h_b0_next, h_b1_next, h_e1_next]
  ring_nf

private theorem decoderHaltNextSel_eval (r : AirRow)
    (h_b0_next : decoderLowBit0ZeroNext r) (h_b1_next : decoderLowBit1ZeroNext r)
    (h_e1_next : decoderExtraCol1EqNext r) :
    Subsystems.Decoder.isHaltNext.eval r = decoderHaltNextSymSel r := by
  simp [decoderHaltNextSymSel, Subsystems.Decoder.isHaltNext, Subsystems.Decoder.opBit0Next,
    Subsystems.Decoder.opBit1Next, Subsystems.Decoder.opBit2Next, Subsystems.Decoder.opBit3Next,
    Subsystems.Decoder.opBit4Next, Subsystems.Decoder.opBit5Next, Subsystems.Decoder.opBit6Next,
    Subsystems.Decoder.notOpBit0Next, Subsystems.Decoder.notOpBit1Next, Subsystems.Decoder.oneMinus,
    Subsystems.Decoder.opBit0Col, Subsystems.Decoder.opBit1Col, Subsystems.Decoder.opBit2Col,
    Subsystems.Decoder.opBit3Col, Subsystems.Decoder.opBit4Col, Subsystems.Decoder.opBit5Col,
    Subsystems.Decoder.opBit6Col, Subsystems.Decoder.decoderTraceOffset, FExpr.eval,
    AirRow.baseAt, AirRow.base]
  rw [h_b0_next, h_b1_next, h_e1_next]
  ring_nf

private theorem decoderControlFlowBlockStartSel_eval (r : AirRow) (h_e0 : decoderExtraCol0Eq r) :
    Subsystems.Decoder.controlFlowBlockStart.eval r = decoderControlFlowBlockStartSymSel r := by
  have h_e0' := decoderExtraCol0Eq' r h_e0
  simp [decoderControlFlowBlockStartSymSel, Subsystems.Decoder.controlFlowBlockStart,
    Subsystems.Decoder.isSpan, Subsystems.Decoder.isJoin, Subsystems.Decoder.isSplit,
    Subsystems.Decoder.isLoop, Subsystems.Decoder.opBit0, Subsystems.Decoder.opBit1,
    Subsystems.Decoder.opBit2, Subsystems.Decoder.opBit3, Subsystems.Decoder.opBit4,
    Subsystems.Decoder.opBit5, Subsystems.Decoder.opBit6, Subsystems.Decoder.notOpBit0,
    Subsystems.Decoder.notOpBit1, Subsystems.Decoder.notOpBit3, Subsystems.Decoder.notOpBit5,
    Subsystems.Decoder.oneMinus, Subsystems.Decoder.opBit0Col, Subsystems.Decoder.opBit1Col,
    Subsystems.Decoder.opBit2Col, Subsystems.Decoder.opBit3Col, Subsystems.Decoder.opBit4Col,
    Subsystems.Decoder.opBit5Col, Subsystems.Decoder.opBit6Col, Subsystems.Decoder.decoderTraceOffset,
    FExpr.eval, AirRow.baseAt, AirRow.base]
  rw [h_e0']
  ring_nf

private theorem decoderControlFlowTransitionSel_eval (r : AirRow)
    (h_b0 : decoderLowBit0Zero r) (h_b1 : decoderLowBit1Zero r)
    (h_e1 : decoderExtraCol1Eq r) :
    Subsystems.Decoder.controlFlowBlockTransition.eval r = decoderControlFlowTransitionSymSel r := by
  have h_b0' := decoderLowBit0Zero' r h_b0
  have h_b1' := decoderLowBit1Zero' r h_b1
  have h_e1' := decoderExtraCol1Eq' r h_e1
  simp [decoderControlFlowTransitionSymSel, Subsystems.Decoder.controlFlowBlockTransition,
    Subsystems.Decoder.isEnd, Subsystems.Decoder.isRepeat, Subsystems.Decoder.isRespan,
    Subsystems.Decoder.isHalt, Subsystems.Decoder.opBit0, Subsystems.Decoder.opBit1,
    Subsystems.Decoder.opBit2, Subsystems.Decoder.opBit3, Subsystems.Decoder.opBit4,
    Subsystems.Decoder.opBit5, Subsystems.Decoder.opBit6, Subsystems.Decoder.notOpBit0,
    Subsystems.Decoder.notOpBit1, Subsystems.Decoder.notOpBit2, Subsystems.Decoder.notOpBit3,
    Subsystems.Decoder.oneMinus, Subsystems.Decoder.opBit0Col, Subsystems.Decoder.opBit1Col,
    Subsystems.Decoder.opBit2Col, Subsystems.Decoder.opBit3Col, Subsystems.Decoder.opBit4Col,
    Subsystems.Decoder.opBit5Col, Subsystems.Decoder.opBit6Col, Subsystems.Decoder.decoderTraceOffset,
    FExpr.eval, AirRow.baseAt, AirRow.base]
  rw [h_b0', h_b1', h_e1']
  ring_nf

private theorem decoderControlFlowDynamicSel_eval (r : AirRow) (h_e0 : decoderExtraCol0Eq r) :
    Subsystems.Decoder.controlFlowDynamic.eval r = decoderControlFlowDynamicSymSel r := by
  have h_e0' := decoderExtraCol0Eq' r h_e0
  simp [decoderControlFlowDynamicSymSel, Subsystems.Decoder.controlFlowDynamic,
    Subsystems.Decoder.isDyn, Subsystems.Decoder.isDyncall, Subsystems.Decoder.opBit0,
    Subsystems.Decoder.opBit1, Subsystems.Decoder.opBit2, Subsystems.Decoder.opBit3,
    Subsystems.Decoder.opBit4, Subsystems.Decoder.opBit5, Subsystems.Decoder.opBit6,
    Subsystems.Decoder.notOpBit0, Subsystems.Decoder.notOpBit1, Subsystems.Decoder.notOpBit2,
    Subsystems.Decoder.notOpBit5, Subsystems.Decoder.oneMinus, Subsystems.Decoder.opBit0Col,
    Subsystems.Decoder.opBit1Col, Subsystems.Decoder.opBit2Col, Subsystems.Decoder.opBit3Col,
    Subsystems.Decoder.opBit4Col, Subsystems.Decoder.opBit5Col, Subsystems.Decoder.opBit6Col,
    Subsystems.Decoder.decoderTraceOffset, FExpr.eval, AirRow.baseAt, AirRow.base]
  rw [h_e0']
  ring_nf

private theorem decoderControlFlowProcedureSel_eval (r : AirRow)
    (h_b0 : decoderLowBit0Zero r) (h_b1 : decoderLowBit1Zero r)
    (h_e1 : decoderExtraCol1Eq r) :
    Subsystems.Decoder.controlFlowProcedure.eval r = decoderControlFlowProcedureSymSel r := by
  have h_b0' := decoderLowBit0Zero' r h_b0
  have h_b1' := decoderLowBit1Zero' r h_b1
  have h_e1' := decoderExtraCol1Eq' r h_e1
  simp [decoderControlFlowProcedureSymSel, Subsystems.Decoder.controlFlowProcedure,
    Subsystems.Decoder.isSyscall, Subsystems.Decoder.isCall, Subsystems.Decoder.opBit0,
    Subsystems.Decoder.opBit1, Subsystems.Decoder.opBit2, Subsystems.Decoder.opBit3,
    Subsystems.Decoder.opBit4, Subsystems.Decoder.opBit5, Subsystems.Decoder.opBit6,
    Subsystems.Decoder.notOpBit0, Subsystems.Decoder.notOpBit1, Subsystems.Decoder.notOpBit2,
    Subsystems.Decoder.notOpBit4, Subsystems.Decoder.oneMinus, Subsystems.Decoder.opBit0Col,
    Subsystems.Decoder.opBit1Col, Subsystems.Decoder.opBit2Col, Subsystems.Decoder.opBit3Col,
    Subsystems.Decoder.opBit4Col, Subsystems.Decoder.opBit5Col, Subsystems.Decoder.opBit6Col,
    Subsystems.Decoder.decoderTraceOffset, FExpr.eval, AirRow.baseAt, AirRow.base]
  rw [h_b0', h_b1', h_e1']
  ring_nf

private theorem decoderOpIndexRange_eval (r : AirRow) :
    Subsystems.Decoder.opIndexRange.eval r =
      r.curr ⟨24, by decide⟩ *
        ((r.curr ⟨24, by decide⟩ - 1) *
          ((r.curr ⟨24, by decide⟩ - 2) *
            ((r.curr ⟨24, by decide⟩ - 3) *
              ((r.curr ⟨24, by decide⟩ - 4) *
                ((r.curr ⟨24, by decide⟩ - 5) *
                  ((r.curr ⟨24, by decide⟩ - 6) *
                    ((r.curr ⟨24, by decide⟩ - 7) * (r.curr ⟨24, by decide⟩ - 8)))))))) := by
  simp [Subsystems.Decoder.opIndexRange, Subsystems.Decoder.ox, Subsystems.Decoder.opIndex,
    Subsystems.Decoder.opIndexCol, Subsystems.Decoder.decoderTraceOffset, FExpr.eval,
    Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr, AirRow.baseAt, AirRow.base]

private theorem decoderAddr_eval (r : AirRow) :
    Subsystems.Decoder.addr.eval r = r.curr ⟨6, by decide⟩ := by
  simp [Subsystems.Decoder.addr, Subsystems.Decoder.addrCol, Subsystems.Decoder.decoderTraceOffset,
    FExpr.eval, AirRow.baseAt, AirRow.base]

private theorem decoderAddrNext_eval (r : AirRow) :
    Subsystems.Decoder.addrNext.eval r = r.next ⟨6, by decide⟩ := by
  simp [Subsystems.Decoder.addrNext, Subsystems.Decoder.addrCol, Subsystems.Decoder.decoderTraceOffset,
    FExpr.eval, AirRow.baseAt, AirRow.base]

private theorem decoderH0_eval (r : AirRow) :
    Subsystems.Decoder.decoderH0.eval r = r.curr ⟨14, by decide⟩ := by
  simp [Subsystems.Decoder.decoderH0, Subsystems.Decoder.decoderH0Col,
    Subsystems.Decoder.decoderTraceOffset, FExpr.eval, AirRow.baseAt, AirRow.base]

private theorem decoderH0Next_eval (r : AirRow) :
    Subsystems.Decoder.decoderH0Next.eval r = r.next ⟨14, by decide⟩ := by
  simp [Subsystems.Decoder.decoderH0Next, Subsystems.Decoder.decoderH0Col,
    Subsystems.Decoder.decoderTraceOffset, FExpr.eval, AirRow.baseAt, AirRow.base]

private theorem decoderInSpan_eval (r : AirRow) :
    Subsystems.Decoder.inSpan.eval r = r.curr ⟨22, by decide⟩ := by
  simp [Subsystems.Decoder.inSpan, Subsystems.Decoder.inSpanCol, Subsystems.Decoder.decoderTraceOffset,
    FExpr.eval, AirRow.baseAt, AirRow.base]

private theorem decoderInSpanNext_eval (r : AirRow) :
    Subsystems.Decoder.inSpanNext.eval r = r.next ⟨22, by decide⟩ := by
  simp [Subsystems.Decoder.inSpanNext, Subsystems.Decoder.inSpanCol, Subsystems.Decoder.decoderTraceOffset,
    FExpr.eval, AirRow.baseAt, AirRow.base]

private theorem decoderSp_eval (r : AirRow) :
    Subsystems.Decoder.sp.eval r = r.curr ⟨22, by decide⟩ := by
  simpa [Subsystems.Decoder.sp] using decoderInSpan_eval r

private theorem decoderSpNext_eval (r : AirRow) :
    Subsystems.Decoder.spNext.eval r = r.next ⟨22, by decide⟩ := by
  simpa [Subsystems.Decoder.spNext] using decoderInSpanNext_eval r

private theorem decoderGroupCount_eval (r : AirRow) :
    Subsystems.Decoder.groupCount.eval r = r.curr ⟨23, by decide⟩ := by
  simp [Subsystems.Decoder.groupCount, Subsystems.Decoder.groupCountCol,
    Subsystems.Decoder.decoderTraceOffset, FExpr.eval, AirRow.baseAt, AirRow.base]

private theorem decoderGroupCountNext_eval (r : AirRow) :
    Subsystems.Decoder.groupCountNext.eval r = r.next ⟨23, by decide⟩ := by
  simp [Subsystems.Decoder.groupCountNext, Subsystems.Decoder.groupCountCol,
    Subsystems.Decoder.decoderTraceOffset, FExpr.eval, AirRow.baseAt, AirRow.base]

private theorem decoderDeltaGc_eval (r : AirRow) :
    Subsystems.Decoder.deltaGc.eval r = r.curr ⟨23, by decide⟩ - r.next ⟨23, by decide⟩ := by
  simp [Subsystems.Decoder.deltaGc]
  rw [decoderGroupCount_eval r, decoderGroupCountNext_eval r]

private theorem decoderOpIndex_eval (r : AirRow) :
    Subsystems.Decoder.opIndex.eval r = r.curr ⟨24, by decide⟩ := by
  simp [Subsystems.Decoder.opIndex, Subsystems.Decoder.opIndexCol, Subsystems.Decoder.decoderTraceOffset,
    FExpr.eval, AirRow.baseAt, AirRow.base]

private theorem decoderOpIndexNext_eval (r : AirRow) :
    Subsystems.Decoder.oxNext.eval r = r.next ⟨24, by decide⟩ := by
  simp [Subsystems.Decoder.oxNext, Subsystems.Decoder.opIndexCol, Subsystems.Decoder.decoderTraceOffset,
    FExpr.eval, AirRow.baseAt, AirRow.base]

private theorem decoderBatchFlag0_eval (r : AirRow) :
    Subsystems.Decoder.batchFlag0.eval r = r.curr ⟨25, by decide⟩ := by
  simp [Subsystems.Decoder.batchFlag0, Subsystems.Decoder.batchFlag0Col,
    Subsystems.Decoder.decoderTraceOffset, FExpr.eval, AirRow.baseAt, AirRow.base]

private theorem decoderBatchFlag1_eval (r : AirRow) :
    Subsystems.Decoder.batchFlag1.eval r = r.curr ⟨26, by decide⟩ := by
  simp [Subsystems.Decoder.batchFlag1, Subsystems.Decoder.batchFlag1Col,
    Subsystems.Decoder.decoderTraceOffset, FExpr.eval, AirRow.baseAt, AirRow.base]

private theorem decoderBatchFlag2_eval (r : AirRow) :
    Subsystems.Decoder.batchFlag2.eval r = r.curr ⟨27, by decide⟩ := by
  simp [Subsystems.Decoder.batchFlag2, Subsystems.Decoder.batchFlag2Col,
    Subsystems.Decoder.decoderTraceOffset, FExpr.eval, AirRow.baseAt, AirRow.base]

private theorem decoderOpNext_eval (r : AirRow) :
    Subsystems.Decoder.opNext.eval r =
      r.next ⟨7, by decide⟩ +
        (r.next ⟨8, by decide⟩ * Felt.ofNat 2) +
        (r.next ⟨9, by decide⟩ * Felt.ofNat 4) +
        (r.next ⟨10, by decide⟩ * Felt.ofNat 8) +
        (r.next ⟨11, by decide⟩ * Felt.ofNat 16) +
        (r.next ⟨12, by decide⟩ * Felt.ofNat 32) +
        (r.next ⟨13, by decide⟩ * Felt.ofNat 64) := by
  simp [Subsystems.Decoder.opNext, Subsystems.Decoder.b0Next, Subsystems.Decoder.b1Next,
    Subsystems.Decoder.b2Next, Subsystems.Decoder.b3Next, Subsystems.Decoder.b4Next,
    Subsystems.Decoder.b5Next, Subsystems.Decoder.b6Next, Subsystems.Decoder.opBit0Next,
    Subsystems.Decoder.opBit1Next, Subsystems.Decoder.opBit2Next, Subsystems.Decoder.opBit3Next,
    Subsystems.Decoder.opBit4Next, Subsystems.Decoder.opBit5Next, Subsystems.Decoder.opBit6Next,
    Subsystems.Decoder.opBit0Col, Subsystems.Decoder.opBit1Col, Subsystems.Decoder.opBit2Col,
    Subsystems.Decoder.opBit3Col, Subsystems.Decoder.opBit4Col, Subsystems.Decoder.opBit5Col,
    Subsystems.Decoder.opBit6Col, Subsystems.Decoder.decoderTraceOffset, FExpr.eval,
    AirRow.baseAt, AirRow.base]
  ring_nf
  rw [show (Felt.ofNat 4 : Felt) = 4 by rfl, show (Felt.ofNat 8 : Felt) = 8 by rfl,
    show (Felt.ofNat 16 : Felt) = 16 by rfl, show (Felt.ofNat 32 : Felt) = 32 by rfl,
    show (Felt.ofNat 64 : Felt) = 64 by rfl]

private theorem decoderFSgc_eval (r : AirRow) :
    Subsystems.Decoder.fSgc.eval r =
      (r.curr ⟨22, by decide⟩ * r.next ⟨22, by decide⟩) *
        (1 - (r.curr ⟨23, by decide⟩ - r.next ⟨23, by decide⟩)) := by
  simp [Subsystems.Decoder.fSgc, FExpr.eval, Subsystems.Decoder.oneMinus]
  rw [decoderSp_eval r, decoderSpNext_eval r, decoderDeltaGc_eval r]
  ring_nf

private theorem decoderSpanOrRespanSel_eval (r : AirRow)
    (h_b0 : decoderLowBit0Zero r) (h_b1 : decoderLowBit1Zero r)
    (h_e0 : decoderExtraCol0Eq r) (h_e1 : decoderExtraCol1Eq r) :
    Subsystems.Decoder.spanOrRespan.eval r = decoderSpanSymSel r + decoderRespanSymSel r := by
  simp [Subsystems.Decoder.spanOrRespan]
  rw [decoderSpanSel_eval r h_e0, decoderRespanSel_eval r h_b0 h_b1 h_e1]

private theorem decoderEndOrRespanNextSel_eval (r : AirRow)
    (h_b0_next : decoderLowBit0ZeroNext r) (h_b1_next : decoderLowBit1ZeroNext r)
    (h_e1_next : decoderExtraCol1EqNext r) :
    Subsystems.Decoder.isEndNext.eval r + Subsystems.Decoder.isRespanNext.eval r =
      decoderEndNextSymSel r + decoderRespanNextSymSel r := by
  rw [decoderEndNextSel_eval r h_b0_next h_b1_next h_e1_next,
    decoderRespanNextSel_eval r h_b0_next h_b1_next h_e1_next]

private theorem decoderNewGroup_eval (r : AirRow) (h_e0 : decoderExtraCol0Eq r) :
    Subsystems.Decoder.newGroup.eval r =
      (r.curr ⟨23, by decide⟩ - r.next ⟨23, by decide⟩) - decoderPushSymSel r := by
  simp [Subsystems.Decoder.newGroup]
  rw [decoderDeltaGc_eval r, decoderPushSel_eval r h_e0]

private theorem decoderBatchSelectorSum_eval (r : AirRow) :
    Subsystems.Decoder.fG1.eval r + (Subsystems.Decoder.fG2.eval r +
        (Subsystems.Decoder.fG4.eval r + Subsystems.Decoder.fG8.eval r)) =
      (((((1 - r.curr ⟨25, by decide⟩) * r.curr ⟨26, by decide⟩) * r.curr ⟨27, by decide⟩) +
          (((1 - r.curr ⟨25, by decide⟩) * (1 - r.curr ⟨26, by decide⟩)) * r.curr ⟨27, by decide⟩)) +
        (((1 - r.curr ⟨25, by decide⟩) * r.curr ⟨26, by decide⟩) * (1 - r.curr ⟨27, by decide⟩))) +
      r.curr ⟨25, by decide⟩ := by
  simp [Subsystems.Decoder.fG1, Subsystems.Decoder.fG2, Subsystems.Decoder.fG4, Subsystems.Decoder.fG8,
    Subsystems.Decoder.oneMinus, FExpr.eval]
  rw [decoderBatchFlag0_eval r, decoderBatchFlag1_eval r, decoderBatchFlag2_eval r]
  ring_nf

private theorem decoderBatchFlagSum_eval (r : AirRow) :
    Subsystems.Decoder.batchFlag0.eval r + (Subsystems.Decoder.batchFlag1.eval r +
        Subsystems.Decoder.batchFlag2.eval r) =
      r.curr ⟨25, by decide⟩ + (r.curr ⟨26, by decide⟩ + r.curr ⟨27, by decide⟩) := by
  rw [decoderBatchFlag0_eval r, decoderBatchFlag1_eval r, decoderBatchFlag2_eval r]

private theorem decoderControlFlowFlag_eval (r : AirRow)
    (h_b0 : decoderLowBit0Zero r) (h_b1 : decoderLowBit1Zero r)
    (h_e0 : decoderExtraCol0Eq r) (h_e1 : decoderExtraCol1Eq r) :
    Subsystems.Decoder.controlFlowFlag.eval r =
      decoderControlFlowBlockStartSymSel r +
        (decoderControlFlowTransitionSymSel r +
          (decoderControlFlowDynamicSymSel r + decoderControlFlowProcedureSymSel r)) := by
  simp [Subsystems.Decoder.controlFlowFlag]
  rw [decoderControlFlowBlockStartSel_eval r h_e0,
    decoderControlFlowTransitionSel_eval r h_b0 h_b1 h_e1,
    decoderControlFlowDynamicSel_eval r h_e0,
    decoderControlFlowProcedureSel_eval r h_b0 h_b1 h_e1]

theorem bridge_decoder_0 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[0]! (toSymbolicFrame r) =
      Subsystems.Decoder.inSpanFirst.eval r := by
  rw [Constraints.Symbolic.Decoder.base]
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => f.is_first_row * f.colCurr 22) (toSymbolicFrame r) =
    Subsystems.Decoder.inSpanFirst.eval r
  have h22 : 22 < MainWidth := by decide
  simp only [Subsystems.Decoder.inSpanFirst, Subsystems.Decoder.inSpan,
    Subsystems.Decoder.inSpanCol, Subsystems.Decoder.decoderTraceOffset,
    toSymbolicFrame, FExpr.eval, Builder.gate, Builder.assertZero, BaseConstraint.eval,
    BaseConstraint.expr, AirRow.boundary, AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, h22]
  have hCurr :
      (r.isFirst * if h : True then r.curr ⟨22, h22⟩ else 0) =
        r.isFirst * r.curr ⟨22, Subsystems.Decoder.inSpanCol._proof_1⟩ := by
    simp
  rw [hCurr]

theorem bridge_decoder_1 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[1]! (toSymbolicFrame r) =
      Subsystems.Decoder.inSpanBinary.eval r := by
  rw [Constraints.Symbolic.Decoder.base]
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => f.colCurr 22 * (f.colCurr 22 - 1)) (toSymbolicFrame r) =
    Subsystems.Decoder.inSpanBinary.eval r
  have h22 : 22 < MainWidth := by decide
  simp only [Subsystems.Decoder.inSpanBinary, Subsystems.Decoder.assertBinary,
    Subsystems.Decoder.inSpan, Subsystems.Decoder.inSpanCol, Subsystems.Decoder.decoderTraceOffset,
    toSymbolicFrame, FExpr.eval, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, h22]
  simp

/- `base[2]` and `base[3]` are the first selector-compression mismatches.
`base[2]` uses `e0` in place of the expanded `b6 * (1 - b5) * b4` span factor,
and `base[3]` uses `e1` while also omitting the low-bit factors `(1 - b1) * (1 - b0)`.
Representative counterexamples were confirmed for both shapes. -/

theorem bridge_decoder_2 (r : AirRow)
    (h_e0 : decoderExtraCol0Eq r) :
    Constraints.Symbolic.Decoder.base[2]! (toSymbolicFrame r) =
      Subsystems.Decoder.inSpanAfterSpan.eval r := by
  let spNext : Felt := r.next ⟨22, by decide⟩
  have h_sym :
      Constraints.Symbolic.Decoder.base[2]! (toSymbolicFrame r) =
        r.isTransition * (decoderSpanSymSel r * (1 - spNext)) := by
    rw [Constraints.Symbolic.Decoder.base]
    rw [getElem!_pos (h := by native_decide)]
    change (fun f =>
      f.is_transition * (((((1 - f.colCurr 7) * f.colCurr 8) * f.colCurr 9) *
        ((1 - f.colCurr 10) * f.colCurr 28)) * (1 - f.colNext 22))) (toSymbolicFrame r) =
      r.isTransition * (decoderSpanSymSel r * (1 - spNext))
    simp [decoderSpanSymSel, spNext, toSymbolicFrame, MainWidth,
      SymbolicFrame.colCurr, SymbolicFrame.colNext]
  have h_can :
      Subsystems.Decoder.inSpanAfterSpan.eval r =
        r.isTransition * (Subsystems.Decoder.isSpan.eval r * (1 - spNext)) := by
    simp [spNext, Subsystems.Decoder.inSpanAfterSpan, Builder.whenTransition, Builder.gate,
      Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr, FExpr.eval,
      AirRow.boundary, AirRow.baseAt, AirRow.base, Subsystems.Decoder.oneMinus,
      Subsystems.Decoder.inSpanNext, Subsystems.Decoder.inSpanCol,
      Subsystems.Decoder.decoderTraceOffset]
  rw [h_sym, h_can, decoderSpanSel_eval r h_e0]

theorem bridge_decoder_3 (r : AirRow)
    (h_b0 : decoderLowBit0Zero r) (h_b1 : decoderLowBit1Zero r)
    (h_e1 : decoderExtraCol1Eq r) :
    Constraints.Symbolic.Decoder.base[3]! (toSymbolicFrame r) =
      Subsystems.Decoder.inSpanAfterRespan.eval r := by
  let spNext : Felt := r.next ⟨22, by decide⟩
  have h_sym :
      Constraints.Symbolic.Decoder.base[3]! (toSymbolicFrame r) =
        r.isTransition * (decoderRespanSymSel r * (1 - spNext)) := by
    rw [Constraints.Symbolic.Decoder.base]
    rw [getElem!_pos (h := by native_decide)]
    change (fun f =>
      f.is_transition * ((((1 - f.colCurr 9) * f.colCurr 10) *
        (f.colCurr 11 * f.colCurr 29)) * (1 - f.colNext 22))) (toSymbolicFrame r) =
      r.isTransition * (decoderRespanSymSel r * (1 - spNext))
    simp [decoderRespanSymSel, spNext, toSymbolicFrame, MainWidth,
      SymbolicFrame.colCurr, SymbolicFrame.colNext]
  have h_can :
      Subsystems.Decoder.inSpanAfterRespan.eval r =
        r.isTransition * (Subsystems.Decoder.isRespan.eval r * (1 - spNext)) := by
    simp [spNext, Subsystems.Decoder.inSpanAfterRespan, Builder.whenTransition, Builder.gate,
      Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr, FExpr.eval,
      AirRow.boundary, AirRow.baseAt, AirRow.base, Subsystems.Decoder.oneMinus,
      Subsystems.Decoder.inSpanNext, Subsystems.Decoder.inSpanCol,
      Subsystems.Decoder.decoderTraceOffset]
  rw [h_sym, h_can, decoderRespanSel_eval r h_b0 h_b1 h_e1]

theorem bridge_decoder_4 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[4]! (toSymbolicFrame r) =
      Subsystems.Decoder.opBit0Binary.eval r := by
  rw [Constraints.Symbolic.Decoder.base]
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => f.colCurr 7 * (f.colCurr 7 - 1)) (toSymbolicFrame r) =
    Subsystems.Decoder.opBit0Binary.eval r
  have h7 : 7 < MainWidth := by decide
  simp only [Subsystems.Decoder.opBit0Binary, Subsystems.Decoder.assertBinary,
    Subsystems.Decoder.opBit0, Subsystems.Decoder.opBit0Col, Subsystems.Decoder.decoderTraceOffset,
    toSymbolicFrame, FExpr.eval, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, h7]
  simp

theorem bridge_decoder_5 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[5]! (toSymbolicFrame r) =
      Subsystems.Decoder.opBit1Binary.eval r := by
  rw [Constraints.Symbolic.Decoder.base]
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => f.colCurr 8 * (f.colCurr 8 - 1)) (toSymbolicFrame r) =
    Subsystems.Decoder.opBit1Binary.eval r
  have h8 : 8 < MainWidth := by decide
  simp only [Subsystems.Decoder.opBit1Binary, Subsystems.Decoder.assertBinary,
    Subsystems.Decoder.opBit1, Subsystems.Decoder.opBit1Col, Subsystems.Decoder.decoderTraceOffset,
    toSymbolicFrame, FExpr.eval, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, h8]
  simp

theorem bridge_decoder_6 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[6]! (toSymbolicFrame r) =
      Subsystems.Decoder.opBit2Binary.eval r := by
  rw [Constraints.Symbolic.Decoder.base]
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => f.colCurr 9 * (f.colCurr 9 - 1)) (toSymbolicFrame r) =
    Subsystems.Decoder.opBit2Binary.eval r
  have h9 : 9 < MainWidth := by decide
  simp only [Subsystems.Decoder.opBit2Binary, Subsystems.Decoder.assertBinary,
    Subsystems.Decoder.opBit2, Subsystems.Decoder.opBit2Col, Subsystems.Decoder.decoderTraceOffset,
    toSymbolicFrame, FExpr.eval, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, h9]
  simp

theorem bridge_decoder_7 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[7]! (toSymbolicFrame r) =
      Subsystems.Decoder.opBit3Binary.eval r := by
  rw [Constraints.Symbolic.Decoder.base]
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => f.colCurr 10 * (f.colCurr 10 - 1)) (toSymbolicFrame r) =
    Subsystems.Decoder.opBit3Binary.eval r
  have h10 : 10 < MainWidth := by decide
  simp only [Subsystems.Decoder.opBit3Binary, Subsystems.Decoder.assertBinary,
    Subsystems.Decoder.opBit3, Subsystems.Decoder.opBit3Col, Subsystems.Decoder.decoderTraceOffset,
    toSymbolicFrame, FExpr.eval, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, h10]
  simp

theorem bridge_decoder_8 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[8]! (toSymbolicFrame r) =
      Subsystems.Decoder.opBit4Binary.eval r := by
  rw [Constraints.Symbolic.Decoder.base]
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => f.colCurr 11 * (f.colCurr 11 - 1)) (toSymbolicFrame r) =
    Subsystems.Decoder.opBit4Binary.eval r
  have h11 : 11 < MainWidth := by decide
  simp only [Subsystems.Decoder.opBit4Binary, Subsystems.Decoder.assertBinary,
    Subsystems.Decoder.opBit4, Subsystems.Decoder.opBit4Col, Subsystems.Decoder.decoderTraceOffset,
    toSymbolicFrame, FExpr.eval, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, h11]
  simp

theorem bridge_decoder_9 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[9]! (toSymbolicFrame r) =
      Subsystems.Decoder.opBit5Binary.eval r := by
  rw [Constraints.Symbolic.Decoder.base]
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => f.colCurr 12 * (f.colCurr 12 - 1)) (toSymbolicFrame r) =
    Subsystems.Decoder.opBit5Binary.eval r
  have h12 : 12 < MainWidth := by decide
  simp only [Subsystems.Decoder.opBit5Binary, Subsystems.Decoder.assertBinary,
    Subsystems.Decoder.opBit5, Subsystems.Decoder.opBit5Col, Subsystems.Decoder.decoderTraceOffset,
    toSymbolicFrame, FExpr.eval, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, h12]
  simp

theorem bridge_decoder_10 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[10]! (toSymbolicFrame r) =
      Subsystems.Decoder.opBit6Binary.eval r := by
  rw [Constraints.Symbolic.Decoder.base]
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => f.colCurr 13 * (f.colCurr 13 - 1)) (toSymbolicFrame r) =
    Subsystems.Decoder.opBit6Binary.eval r
  have h13 : 13 < MainWidth := by decide
  simp only [Subsystems.Decoder.opBit6Binary, Subsystems.Decoder.assertBinary,
    Subsystems.Decoder.opBit6, Subsystems.Decoder.opBit6Col, Subsystems.Decoder.decoderTraceOffset,
    toSymbolicFrame, FExpr.eval, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, h13]
  simp

theorem bridge_decoder_11 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[11]! (toSymbolicFrame r) =
      Subsystems.Decoder.extra0Correct.eval r := by
  rw [Constraints.Symbolic.Decoder.base]
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => f.colCurr 28 - ((f.colCurr 13 * (1 - f.colCurr 12)) * f.colCurr 11))
      (toSymbolicFrame r) = Subsystems.Decoder.extra0Correct.eval r
  have h11 : 11 < MainWidth := by decide
  have h12 : 12 < MainWidth := by decide
  have h13 : 13 < MainWidth := by decide
  have h28 : 28 < MainWidth := by decide
  simp only [Subsystems.Decoder.extra0Correct, Subsystems.Decoder.extra0, Subsystems.Decoder.opBit6,
    Subsystems.Decoder.notOpBit5, Subsystems.Decoder.opBit5, Subsystems.Decoder.opBit4,
    Subsystems.Decoder.oneMinus, Subsystems.Decoder.extra0Col, Subsystems.Decoder.opBit6Col,
    Subsystems.Decoder.opBit5Col, Subsystems.Decoder.opBit4Col, Subsystems.Decoder.decoderTraceOffset,
    toSymbolicFrame, FExpr.eval, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, h11, h12, h13, h28]
  ring_nf
  simp

theorem bridge_decoder_12 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[12]! (toSymbolicFrame r) =
      Subsystems.Decoder.extra1Correct.eval r := by
  rw [Constraints.Symbolic.Decoder.base]
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => f.colCurr 29 - (f.colCurr 13 * f.colCurr 12)) (toSymbolicFrame r) =
    Subsystems.Decoder.extra1Correct.eval r
  have h12 : 12 < MainWidth := by decide
  have h13 : 13 < MainWidth := by decide
  have h29 : 29 < MainWidth := by decide
  simp only [Subsystems.Decoder.extra1Correct, Subsystems.Decoder.extra1, Subsystems.Decoder.opBit6,
    Subsystems.Decoder.opBit5, Subsystems.Decoder.extra1Col, Subsystems.Decoder.opBit6Col,
    Subsystems.Decoder.opBit5Col, Subsystems.Decoder.decoderTraceOffset, toSymbolicFrame,
    FExpr.eval, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr, AirRow.baseAt,
    AirRow.base, SymbolicFrame.colCurr, h12, h13, h29]
  simp

theorem bridge_decoder_13 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[13]! (toSymbolicFrame r) =
      Subsystems.Decoder.u32PrefixBit0.eval r := by
  rw [Constraints.Symbolic.Decoder.base]
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => (((f.colCurr 13 * (1 - f.colCurr 12)) * (1 - f.colCurr 11)) * f.colCurr 7))
      (toSymbolicFrame r) = Subsystems.Decoder.u32PrefixBit0.eval r
  have h7 : 7 < MainWidth := by decide
  have h11 : 11 < MainWidth := by decide
  have h12 : 12 < MainWidth := by decide
  have h13 : 13 < MainWidth := by decide
  simp only [Subsystems.Decoder.u32PrefixBit0, Subsystems.Decoder.opBit6,
    Subsystems.Decoder.notOpBit5, Subsystems.Decoder.opBit5, Subsystems.Decoder.notOpBit4,
    Subsystems.Decoder.opBit4, Subsystems.Decoder.opBit0, Subsystems.Decoder.oneMinus,
    Subsystems.Decoder.opBit6Col, Subsystems.Decoder.opBit5Col, Subsystems.Decoder.opBit4Col,
    Subsystems.Decoder.opBit0Col, Subsystems.Decoder.decoderTraceOffset, toSymbolicFrame,
    FExpr.eval, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr, AirRow.baseAt,
    AirRow.base, SymbolicFrame.colCurr, h7, h11, h12, h13]
  ring_nf
  simp

theorem bridge_decoder_14 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[14]! (toSymbolicFrame r) =
      Subsystems.Decoder.veryHighBit0.eval r := by
  rw [Constraints.Symbolic.Decoder.base]
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => ((f.colCurr 13 * f.colCurr 12) * f.colCurr 7)) (toSymbolicFrame r) =
    Subsystems.Decoder.veryHighBit0.eval r
  have h7 : 7 < MainWidth := by decide
  have h12 : 12 < MainWidth := by decide
  have h13 : 13 < MainWidth := by decide
  simp only [Subsystems.Decoder.veryHighBit0, Subsystems.Decoder.opBit6, Subsystems.Decoder.opBit5,
    Subsystems.Decoder.opBit0, Subsystems.Decoder.opBit6Col, Subsystems.Decoder.opBit5Col,
    Subsystems.Decoder.opBit0Col, Subsystems.Decoder.decoderTraceOffset, toSymbolicFrame,
    FExpr.eval, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr, AirRow.baseAt,
    AirRow.base, SymbolicFrame.colCurr, h7, h12, h13]
  simp

theorem bridge_decoder_15 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[15]! (toSymbolicFrame r) =
      Subsystems.Decoder.veryHighBit1.eval r := by
  rw [Constraints.Symbolic.Decoder.base]
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => ((f.colCurr 13 * f.colCurr 12) * f.colCurr 8)) (toSymbolicFrame r) =
    Subsystems.Decoder.veryHighBit1.eval r
  have h8 : 8 < MainWidth := by decide
  have h12 : 12 < MainWidth := by decide
  have h13 : 13 < MainWidth := by decide
  simp only [Subsystems.Decoder.veryHighBit1, Subsystems.Decoder.opBit6, Subsystems.Decoder.opBit5,
    Subsystems.Decoder.opBit1, Subsystems.Decoder.opBit6Col, Subsystems.Decoder.opBit5Col,
    Subsystems.Decoder.opBit1Col, Subsystems.Decoder.decoderTraceOffset, toSymbolicFrame,
    FExpr.eval, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr, AirRow.baseAt,
    AirRow.base, SymbolicFrame.colCurr, h8, h12, h13]
  simp

theorem bridge_decoder_16 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[16]! (toSymbolicFrame r) =
      Subsystems.Decoder.batchFlag0Binary.eval r := by
  rw [Constraints.Symbolic.Decoder.base]
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => f.colCurr 25 * (f.colCurr 25 - 1)) (toSymbolicFrame r) =
    Subsystems.Decoder.batchFlag0Binary.eval r
  have h25 : 25 < MainWidth := by decide
  simp only [Subsystems.Decoder.batchFlag0Binary, Subsystems.Decoder.assertBinary,
    Subsystems.Decoder.batchFlag0, Subsystems.Decoder.batchFlag0Col, Subsystems.Decoder.decoderTraceOffset,
    toSymbolicFrame, FExpr.eval, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, h25]
  simp

theorem bridge_decoder_17 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[17]! (toSymbolicFrame r) =
      Subsystems.Decoder.batchFlag1Binary.eval r := by
  rw [Constraints.Symbolic.Decoder.base]
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => f.colCurr 26 * (f.colCurr 26 - 1)) (toSymbolicFrame r) =
    Subsystems.Decoder.batchFlag1Binary.eval r
  have h26 : 26 < MainWidth := by decide
  simp only [Subsystems.Decoder.batchFlag1Binary, Subsystems.Decoder.assertBinary,
    Subsystems.Decoder.batchFlag1, Subsystems.Decoder.batchFlag1Col, Subsystems.Decoder.decoderTraceOffset,
    toSymbolicFrame, FExpr.eval, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, h26]
  simp

theorem bridge_decoder_18 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[18]! (toSymbolicFrame r) =
      Subsystems.Decoder.batchFlag2Binary.eval r := by
  rw [Constraints.Symbolic.Decoder.base]
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => f.colCurr 27 * (f.colCurr 27 - 1)) (toSymbolicFrame r) =
    Subsystems.Decoder.batchFlag2Binary.eval r
  have h27 : 27 < MainWidth := by decide
  simp only [Subsystems.Decoder.batchFlag2Binary, Subsystems.Decoder.assertBinary,
    Subsystems.Decoder.batchFlag2, Subsystems.Decoder.batchFlag2Col, Subsystems.Decoder.decoderTraceOffset,
    toSymbolicFrame, FExpr.eval, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, h27]
  simp

/- `base[19]` through `base[32]` all use the compressed control-flow selectors.
The `SPAN`/`LOOP`/`DYN` shapes depend on `e0`, and the `RESPAN`/`REPEAT`/`END`/`HALT`
shapes depend on `e1` while also dropping low-bit factors in the symbolic extractor.
The direct unconditional bridge is therefore intentionally left open here. -/

theorem bridge_decoder_19 (r : AirRow)
    (h_e0 : decoderExtraCol0Eq r) :
    Constraints.Symbolic.Decoder.base[19]! (toSymbolicFrame r) =
      Subsystems.Decoder.splitLoopS0Binary.eval r := by
  let s0 : Felt := r.curr ⟨30, by decide⟩
  have h_sym :
      Constraints.Symbolic.Decoder.base[19]! (toSymbolicFrame r) =
        decoderSplitLoopSymSel r * (s0 * (s0 - 1)) := by
    rw [Constraints.Symbolic.Decoder.base]
    rw [getElem!_pos (h := by native_decide)]
    change (fun f =>
      ((((((1 - f.colCurr 7) * (1 - f.colCurr 8)) * f.colCurr 9) * ((1 - f.colCurr 10) * f.colCurr 28)) +
          (((f.colCurr 7 * (1 - f.colCurr 8)) * f.colCurr 9) * ((1 - f.colCurr 10) * f.colCurr 28))) *
        (f.s 0 * (f.s 0 - 1)))) (toSymbolicFrame r) =
      decoderSplitLoopSymSel r * (s0 * (s0 - 1))
    simp [decoderSplitLoopSymSel, s0, toSymbolicFrame, MainWidth,
      SymbolicFrame.colCurr, SymbolicFrame.s]
  have h_can :
      Subsystems.Decoder.splitLoopS0Binary.eval r =
        Subsystems.Decoder.splitOrLoop.eval r * (s0 * (s0 - 1)) := by
    simp [s0, Subsystems.Decoder.splitLoopS0Binary, Subsystems.Decoder.s0,
      Subsystems.Decoder.s0Col, Builder.gate, Builder.assertZero, BaseConstraint.eval,
      BaseConstraint.expr, FExpr.eval, AirRow.baseAt, AirRow.base,
      Subsystems.Decoder.decoderTraceOffset]
  rw [h_sym, h_can, decoderSplitLoopSel_eval r h_e0]

theorem bridge_decoder_20 (r : AirRow)
    (h_e0 : decoderExtraCol0Eq r) :
    Constraints.Symbolic.Decoder.base[20]! (toSymbolicFrame r) =
      Subsystems.Decoder.dynH4Zero.eval r := by
  let h4 : Felt := r.curr ⟨18, by decide⟩
  have h_sym :
      Constraints.Symbolic.Decoder.base[20]! (toSymbolicFrame r) =
        decoderDynSymSel r * h4 := by
    rw [Constraints.Symbolic.Decoder.base]
    rw [getElem!_pos (h := by native_decide)]
    change (fun f =>
      (((((1 - f.colCurr 7) * (1 - f.colCurr 8)) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)) *
        f.h 2)) (toSymbolicFrame r) =
      decoderDynSymSel r * h4
    simp [decoderDynSymSel, h4, toSymbolicFrame, MainWidth,
      SymbolicFrame.colCurr, SymbolicFrame.h]
  have h_can :
      Subsystems.Decoder.dynH4Zero.eval r =
        Subsystems.Decoder.isDyn.eval r * h4 := by
    simp [h4, Subsystems.Decoder.dynH4Zero, Subsystems.Decoder.decoderH4,
      Subsystems.Decoder.decoderH4Col, Builder.gate, Builder.assertZero,
      BaseConstraint.eval, BaseConstraint.expr, FExpr.eval, AirRow.baseAt, AirRow.base,
      Subsystems.Decoder.decoderTraceOffset]
  rw [h_sym, h_can, decoderDynSel_eval r h_e0]

theorem bridge_decoder_21 (r : AirRow)
    (h_e0 : decoderExtraCol0Eq r) :
    Constraints.Symbolic.Decoder.base[21]! (toSymbolicFrame r) =
      Subsystems.Decoder.dynH5Zero.eval r := by
  let h5 : Felt := r.curr ⟨19, by decide⟩
  have h_sym :
      Constraints.Symbolic.Decoder.base[21]! (toSymbolicFrame r) =
        decoderDynSymSel r * h5 := by
    rw [Constraints.Symbolic.Decoder.base]
    rw [getElem!_pos (h := by native_decide)]
    change (fun f =>
      (((((1 - f.colCurr 7) * (1 - f.colCurr 8)) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)) *
        f.h 3)) (toSymbolicFrame r) =
      decoderDynSymSel r * h5
    simp [decoderDynSymSel, h5, toSymbolicFrame, MainWidth,
      SymbolicFrame.colCurr, SymbolicFrame.h]
  have h_can :
      Subsystems.Decoder.dynH5Zero.eval r =
        Subsystems.Decoder.isDyn.eval r * h5 := by
    simp [h5, Subsystems.Decoder.dynH5Zero, Subsystems.Decoder.decoderH5,
      Subsystems.Decoder.decoderH5Col, Builder.gate, Builder.assertZero,
      BaseConstraint.eval, BaseConstraint.expr, FExpr.eval, AirRow.baseAt, AirRow.base,
      Subsystems.Decoder.decoderTraceOffset]
  rw [h_sym, h_can, decoderDynSel_eval r h_e0]

theorem bridge_decoder_22 (r : AirRow)
    (h_e0 : decoderExtraCol0Eq r) :
    Constraints.Symbolic.Decoder.base[22]! (toSymbolicFrame r) =
      Subsystems.Decoder.dynH6Zero.eval r := by
  let h6 : Felt := r.curr ⟨20, by decide⟩
  have h_sym :
      Constraints.Symbolic.Decoder.base[22]! (toSymbolicFrame r) =
        decoderDynSymSel r * h6 := by
    rw [Constraints.Symbolic.Decoder.base]
    rw [getElem!_pos (h := by native_decide)]
    change (fun f =>
      (((((1 - f.colCurr 7) * (1 - f.colCurr 8)) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)) *
        f.h 4)) (toSymbolicFrame r) =
      decoderDynSymSel r * h6
    simp [decoderDynSymSel, h6, toSymbolicFrame, MainWidth,
      SymbolicFrame.colCurr, SymbolicFrame.h]
  have h_can :
      Subsystems.Decoder.dynH6Zero.eval r =
        Subsystems.Decoder.isDyn.eval r * h6 := by
    simp [h6, Subsystems.Decoder.dynH6Zero, Subsystems.Decoder.decoderH6,
      Subsystems.Decoder.decoderH6Col, Builder.gate, Builder.assertZero,
      BaseConstraint.eval, BaseConstraint.expr, FExpr.eval, AirRow.baseAt, AirRow.base,
      Subsystems.Decoder.decoderTraceOffset]
  rw [h_sym, h_can, decoderDynSel_eval r h_e0]

theorem bridge_decoder_23 (r : AirRow)
    (h_e0 : decoderExtraCol0Eq r) :
    Constraints.Symbolic.Decoder.base[23]! (toSymbolicFrame r) =
      Subsystems.Decoder.dynH7Zero.eval r := by
  let h7 : Felt := r.curr ⟨21, by decide⟩
  have h_sym :
      Constraints.Symbolic.Decoder.base[23]! (toSymbolicFrame r) =
        decoderDynSymSel r * h7 := by
    rw [Constraints.Symbolic.Decoder.base]
    rw [getElem!_pos (h := by native_decide)]
    change (fun f =>
      (((((1 - f.colCurr 7) * (1 - f.colCurr 8)) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)) *
        f.h 5)) (toSymbolicFrame r) =
      decoderDynSymSel r * h7
    simp [decoderDynSymSel, h7, toSymbolicFrame, MainWidth,
      SymbolicFrame.colCurr, SymbolicFrame.h]
  have h_can :
      Subsystems.Decoder.dynH7Zero.eval r =
        Subsystems.Decoder.isDyn.eval r * h7 := by
    simp [h7, Subsystems.Decoder.dynH7Zero, Subsystems.Decoder.decoderH7,
      Subsystems.Decoder.decoderH7Col, Builder.gate, Builder.assertZero,
      BaseConstraint.eval, BaseConstraint.expr, FExpr.eval, AirRow.baseAt, AirRow.base,
      Subsystems.Decoder.decoderTraceOffset]
  rw [h_sym, h_can, decoderDynSel_eval r h_e0]

theorem bridge_decoder_24 (r : AirRow)
    (h_b0 : decoderLowBit0Zero r) (h_b1 : decoderLowBit1Zero r)
    (h_e1 : decoderExtraCol1Eq r) :
    Constraints.Symbolic.Decoder.base[24]! (toSymbolicFrame r) =
      Subsystems.Decoder.repeatS0One.eval r := by
  let s0 : Felt := r.curr ⟨30, by decide⟩
  have h_sym :
      Constraints.Symbolic.Decoder.base[24]! (toSymbolicFrame r) =
        decoderRepeatSymSel r * (1 - s0) := by
    rw [Constraints.Symbolic.Decoder.base]
    rw [getElem!_pos (h := by native_decide)]
    change (fun f =>
      (((f.colCurr 9 * (1 - f.colCurr 10)) * (f.colCurr 11 * f.colCurr 29)) *
        (1 - f.s 0))) (toSymbolicFrame r) =
      decoderRepeatSymSel r * (1 - s0)
    simp [decoderRepeatSymSel, s0, toSymbolicFrame, MainWidth,
      SymbolicFrame.colCurr, SymbolicFrame.s]
  have h_can :
      Subsystems.Decoder.repeatS0One.eval r =
        Subsystems.Decoder.isRepeat.eval r * (1 - s0) := by
    simp [s0, Subsystems.Decoder.repeatS0One, Subsystems.Decoder.s0, Subsystems.Decoder.s0Col,
      Builder.gate, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
      FExpr.eval, AirRow.baseAt, AirRow.base, Subsystems.Decoder.oneMinus,
      Subsystems.Decoder.decoderTraceOffset]
  rw [h_sym, h_can, decoderRepeatSel_eval r h_b0 h_b1 h_e1]

theorem bridge_decoder_25 (r : AirRow)
    (h_b0 : decoderLowBit0Zero r) (h_b1 : decoderLowBit1Zero r)
    (h_e1 : decoderExtraCol1Eq r) :
    Constraints.Symbolic.Decoder.base[25]! (toSymbolicFrame r) =
      Subsystems.Decoder.repeatH4One.eval r := by
  let h4 : Felt := r.curr ⟨18, by decide⟩
  have h_sym :
      Constraints.Symbolic.Decoder.base[25]! (toSymbolicFrame r) =
        decoderRepeatSymSel r * (1 - h4) := by
    rw [Constraints.Symbolic.Decoder.base]
    rw [getElem!_pos (h := by native_decide)]
    change (fun f =>
      (((f.colCurr 9 * (1 - f.colCurr 10)) * (f.colCurr 11 * f.colCurr 29)) *
        (1 - f.h 2))) (toSymbolicFrame r) =
      decoderRepeatSymSel r * (1 - h4)
    simp [decoderRepeatSymSel, h4, toSymbolicFrame, MainWidth,
      SymbolicFrame.colCurr, SymbolicFrame.h]
  have h_can :
      Subsystems.Decoder.repeatH4One.eval r =
        Subsystems.Decoder.isRepeat.eval r * (1 - h4) := by
    simp [h4, Subsystems.Decoder.repeatH4One, Subsystems.Decoder.decoderH4,
      Subsystems.Decoder.decoderH4Col, Builder.gate, Builder.assertZero, BaseConstraint.eval,
      BaseConstraint.expr, FExpr.eval, AirRow.baseAt, AirRow.base, Subsystems.Decoder.oneMinus,
      Subsystems.Decoder.decoderTraceOffset]
  rw [h_sym, h_can, decoderRepeatSel_eval r h_b0 h_b1 h_e1]

theorem bridge_decoder_26 (r : AirRow)
    (h_b0 : decoderLowBit0Zero r) (h_b1 : decoderLowBit1Zero r)
    (h_e1 : decoderExtraCol1Eq r) :
    Constraints.Symbolic.Decoder.base[26]! (toSymbolicFrame r) =
      Subsystems.Decoder.endLoopS0Zero.eval r := by
  let h5 : Felt := r.curr ⟨19, by decide⟩
  let s0 : Felt := r.curr ⟨30, by decide⟩
  have h_sym :
      Constraints.Symbolic.Decoder.base[26]! (toSymbolicFrame r) =
        decoderEndSymSel r * h5 * s0 := by
    rw [Constraints.Symbolic.Decoder.base]
    rw [getElem!_pos (h := by native_decide)]
    change (fun f =>
      (((((1 - f.colCurr 9) * (1 - f.colCurr 10)) * (f.colCurr 11 * f.colCurr 29)) * f.h 3) *
        f.s 0)) (toSymbolicFrame r) =
      decoderEndSymSel r * h5 * s0
    simp [decoderEndSymSel, h5, s0, toSymbolicFrame, MainWidth,
      SymbolicFrame.colCurr, SymbolicFrame.h, SymbolicFrame.s]
  have h_can :
      Subsystems.Decoder.endLoopS0Zero.eval r =
        Subsystems.Decoder.isEnd.eval r * h5 * s0 := by
    simp [h5, s0, Subsystems.Decoder.endLoopS0Zero, Subsystems.Decoder.decoderH5,
      Subsystems.Decoder.decoderH5Col, Subsystems.Decoder.s0, Subsystems.Decoder.s0Col,
      Builder.gate, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr, FExpr.eval,
      AirRow.baseAt, AirRow.base, Subsystems.Decoder.decoderTraceOffset]
    ac_rfl
  rw [h_sym, h_can, decoderEndSel_eval r h_b0 h_b1 h_e1]

theorem bridge_decoder_27 (r : AirRow)
    (h_b0 : decoderLowBit0Zero r) (h_b1 : decoderLowBit1Zero r)
    (h_e1 : decoderExtraCol1Eq r)
    (h_b0_next : decoderLowBit0ZeroNext r) (h_b1_next : decoderLowBit1ZeroNext r)
    (h_e1_next : decoderExtraCol1EqNext r) :
    Constraints.Symbolic.Decoder.base[27]! (toSymbolicFrame r) =
      Subsystems.Decoder.endRepeatCarryH0.eval r := by
  let delta : Felt := r.next ⟨14, by decide⟩ - r.curr ⟨14, by decide⟩
  have h_sym :
      Constraints.Symbolic.Decoder.base[27]! (toSymbolicFrame r) =
        r.isTransition * decoderEndSymSel r * decoderRepeatNextSymSel r * delta := by
    rw [Constraints.Symbolic.Decoder.base]
    rw [getElem!_pos (h := by native_decide)]
    change (fun f =>
      f.is_transition * (((((1 - f.colCurr 9) * (1 - f.colCurr 10)) * (f.colCurr 11 * f.colCurr 29)) *
        ((f.colNext 9 * (1 - f.colNext 10)) * (f.colNext 11 * f.colNext 29))) *
        (f.colNext 14 - f.colCurr 14))) (toSymbolicFrame r) =
      r.isTransition * decoderEndSymSel r * decoderRepeatNextSymSel r * delta
    simp [decoderEndSymSel, decoderRepeatNextSymSel, delta, toSymbolicFrame, MainWidth,
      SymbolicFrame.colCurr, SymbolicFrame.colNext]
    ring_nf
  have h_can :
      Subsystems.Decoder.endRepeatCarryH0.eval r =
        r.isTransition * Subsystems.Decoder.isEnd.eval r * Subsystems.Decoder.isRepeatNext.eval r * delta := by
    simp [delta, Subsystems.Decoder.endRepeatCarryH0, Subsystems.Decoder.decoderH0Next,
      Subsystems.Decoder.decoderH0, Subsystems.Decoder.decoderH0Col,
      Subsystems.Decoder.decoderTraceOffset, Builder.whenTransition, Builder.assertZero,
      BaseConstraint.eval, BaseConstraint.expr]
    ac_rfl
  rw [h_sym, h_can, decoderEndSel_eval r h_b0 h_b1 h_e1,
    decoderRepeatNextSel_eval r h_b0_next h_b1_next h_e1_next]

theorem bridge_decoder_28 (r : AirRow)
    (h_b0 : decoderLowBit0Zero r) (h_b1 : decoderLowBit1Zero r)
    (h_e1 : decoderExtraCol1Eq r)
    (h_b0_next : decoderLowBit0ZeroNext r) (h_b1_next : decoderLowBit1ZeroNext r)
    (h_e1_next : decoderExtraCol1EqNext r) :
    Constraints.Symbolic.Decoder.base[28]! (toSymbolicFrame r) =
      Subsystems.Decoder.endRepeatCarryH1.eval r := by
  let delta : Felt := r.next ⟨15, by decide⟩ - r.curr ⟨15, by decide⟩
  have h_sym :
      Constraints.Symbolic.Decoder.base[28]! (toSymbolicFrame r) =
        r.isTransition * decoderEndSymSel r * decoderRepeatNextSymSel r * delta := by
    rw [Constraints.Symbolic.Decoder.base]
    rw [getElem!_pos (h := by native_decide)]
    change (fun f =>
      f.is_transition * (((((1 - f.colCurr 9) * (1 - f.colCurr 10)) * (f.colCurr 11 * f.colCurr 29)) *
        ((f.colNext 9 * (1 - f.colNext 10)) * (f.colNext 11 * f.colNext 29))) *
        (f.colNext 15 - f.colCurr 15))) (toSymbolicFrame r) =
      r.isTransition * decoderEndSymSel r * decoderRepeatNextSymSel r * delta
    simp [decoderEndSymSel, decoderRepeatNextSymSel, delta, toSymbolicFrame, MainWidth,
      SymbolicFrame.colCurr, SymbolicFrame.colNext]
    ring_nf
  have h_can :
      Subsystems.Decoder.endRepeatCarryH1.eval r =
        r.isTransition * Subsystems.Decoder.isEnd.eval r * Subsystems.Decoder.isRepeatNext.eval r * delta := by
    simp [delta, Subsystems.Decoder.endRepeatCarryH1, Subsystems.Decoder.decoderH1Next,
      Subsystems.Decoder.decoderH1, Subsystems.Decoder.decoderH1Col,
      Subsystems.Decoder.decoderTraceOffset, Builder.whenTransition, Builder.assertZero,
      BaseConstraint.eval, BaseConstraint.expr]
    ac_rfl
  rw [h_sym, h_can, decoderEndSel_eval r h_b0 h_b1 h_e1,
    decoderRepeatNextSel_eval r h_b0_next h_b1_next h_e1_next]

theorem bridge_decoder_29 (r : AirRow)
    (h_b0 : decoderLowBit0Zero r) (h_b1 : decoderLowBit1Zero r)
    (h_e1 : decoderExtraCol1Eq r)
    (h_b0_next : decoderLowBit0ZeroNext r) (h_b1_next : decoderLowBit1ZeroNext r)
    (h_e1_next : decoderExtraCol1EqNext r) :
    Constraints.Symbolic.Decoder.base[29]! (toSymbolicFrame r) =
      Subsystems.Decoder.endRepeatCarryH2.eval r := by
  let delta : Felt := r.next ⟨16, by decide⟩ - r.curr ⟨16, by decide⟩
  have h_sym :
      Constraints.Symbolic.Decoder.base[29]! (toSymbolicFrame r) =
        r.isTransition * decoderEndSymSel r * decoderRepeatNextSymSel r * delta := by
    rw [Constraints.Symbolic.Decoder.base]
    rw [getElem!_pos (h := by native_decide)]
    change (fun f =>
      f.is_transition * (((((1 - f.colCurr 9) * (1 - f.colCurr 10)) * (f.colCurr 11 * f.colCurr 29)) *
        ((f.colNext 9 * (1 - f.colNext 10)) * (f.colNext 11 * f.colNext 29))) *
        (f.h' 0 - f.h 0))) (toSymbolicFrame r) =
      r.isTransition * decoderEndSymSel r * decoderRepeatNextSymSel r * delta
    simp [decoderEndSymSel, decoderRepeatNextSymSel, delta, toSymbolicFrame, MainWidth,
      SymbolicFrame.colCurr, SymbolicFrame.colNext, SymbolicFrame.h, SymbolicFrame.h']
    ring_nf
  have h_can :
      Subsystems.Decoder.endRepeatCarryH2.eval r =
        r.isTransition * Subsystems.Decoder.isEnd.eval r * Subsystems.Decoder.isRepeatNext.eval r * delta := by
    simp [delta, Subsystems.Decoder.endRepeatCarryH2, Subsystems.Decoder.decoderH2Next,
      Subsystems.Decoder.decoderH2, Subsystems.Decoder.decoderH2Col,
      Subsystems.Decoder.decoderTraceOffset, Builder.whenTransition, Builder.assertZero,
      BaseConstraint.eval, BaseConstraint.expr]
    ac_rfl
  rw [h_sym, h_can, decoderEndSel_eval r h_b0 h_b1 h_e1,
    decoderRepeatNextSel_eval r h_b0_next h_b1_next h_e1_next]

theorem bridge_decoder_30 (r : AirRow)
    (h_b0 : decoderLowBit0Zero r) (h_b1 : decoderLowBit1Zero r)
    (h_e1 : decoderExtraCol1Eq r)
    (h_b0_next : decoderLowBit0ZeroNext r) (h_b1_next : decoderLowBit1ZeroNext r)
    (h_e1_next : decoderExtraCol1EqNext r) :
    Constraints.Symbolic.Decoder.base[30]! (toSymbolicFrame r) =
      Subsystems.Decoder.endRepeatCarryH3.eval r := by
  let delta : Felt := r.next ⟨17, by decide⟩ - r.curr ⟨17, by decide⟩
  have h_sym :
      Constraints.Symbolic.Decoder.base[30]! (toSymbolicFrame r) =
        r.isTransition * decoderEndSymSel r * decoderRepeatNextSymSel r * delta := by
    rw [Constraints.Symbolic.Decoder.base]
    rw [getElem!_pos (h := by native_decide)]
    change (fun f =>
      f.is_transition * (((((1 - f.colCurr 9) * (1 - f.colCurr 10)) * (f.colCurr 11 * f.colCurr 29)) *
        ((f.colNext 9 * (1 - f.colNext 10)) * (f.colNext 11 * f.colNext 29))) *
        (f.h' 1 - f.h 1))) (toSymbolicFrame r) =
      r.isTransition * decoderEndSymSel r * decoderRepeatNextSymSel r * delta
    simp [decoderEndSymSel, decoderRepeatNextSymSel, delta, toSymbolicFrame, MainWidth,
      SymbolicFrame.colCurr, SymbolicFrame.colNext, SymbolicFrame.h, SymbolicFrame.h']
    ring_nf
  have h_can :
      Subsystems.Decoder.endRepeatCarryH3.eval r =
        r.isTransition * Subsystems.Decoder.isEnd.eval r * Subsystems.Decoder.isRepeatNext.eval r * delta := by
    simp [delta, Subsystems.Decoder.endRepeatCarryH3, Subsystems.Decoder.decoderH3Next,
      Subsystems.Decoder.decoderH3, Subsystems.Decoder.decoderH3Col,
      Subsystems.Decoder.decoderTraceOffset, Builder.whenTransition, Builder.assertZero,
      BaseConstraint.eval, BaseConstraint.expr]
    ac_rfl
  rw [h_sym, h_can, decoderEndSel_eval r h_b0 h_b1 h_e1,
    decoderRepeatNextSel_eval r h_b0_next h_b1_next h_e1_next]

theorem bridge_decoder_31 (r : AirRow)
    (h_b0 : decoderLowBit0Zero r) (h_b1 : decoderLowBit1Zero r)
    (h_e1 : decoderExtraCol1Eq r)
    (h_b0_next : decoderLowBit0ZeroNext r) (h_b1_next : decoderLowBit1ZeroNext r)
    (h_e1_next : decoderExtraCol1EqNext r) :
    Constraints.Symbolic.Decoder.base[31]! (toSymbolicFrame r) =
      Subsystems.Decoder.endRepeatCarryH4.eval r := by
  let delta : Felt := r.next ⟨18, by decide⟩ - r.curr ⟨18, by decide⟩
  have h_sym :
      Constraints.Symbolic.Decoder.base[31]! (toSymbolicFrame r) =
        r.isTransition * decoderEndSymSel r * decoderRepeatNextSymSel r * delta := by
    rw [Constraints.Symbolic.Decoder.base]
    rw [getElem!_pos (h := by native_decide)]
    change (fun f =>
      f.is_transition * (((((1 - f.colCurr 9) * (1 - f.colCurr 10)) * (f.colCurr 11 * f.colCurr 29)) *
        ((f.colNext 9 * (1 - f.colNext 10)) * (f.colNext 11 * f.colNext 29))) *
        (f.h' 2 - f.h 2))) (toSymbolicFrame r) =
      r.isTransition * decoderEndSymSel r * decoderRepeatNextSymSel r * delta
    simp [decoderEndSymSel, decoderRepeatNextSymSel, delta, toSymbolicFrame, MainWidth,
      SymbolicFrame.colCurr, SymbolicFrame.colNext, SymbolicFrame.h, SymbolicFrame.h']
    ring_nf
  have h_can :
      Subsystems.Decoder.endRepeatCarryH4.eval r =
        r.isTransition * Subsystems.Decoder.isEnd.eval r * Subsystems.Decoder.isRepeatNext.eval r * delta := by
    simp [delta, Subsystems.Decoder.endRepeatCarryH4, Subsystems.Decoder.decoderH4Next,
      Subsystems.Decoder.decoderH4, Subsystems.Decoder.decoderH4Col,
      Subsystems.Decoder.decoderTraceOffset, Builder.whenTransition, Builder.assertZero,
      BaseConstraint.eval, BaseConstraint.expr]
    ac_rfl
  rw [h_sym, h_can, decoderEndSel_eval r h_b0 h_b1 h_e1,
    decoderRepeatNextSel_eval r h_b0_next h_b1_next h_e1_next]

theorem bridge_decoder_32 (r : AirRow)
    (h_b0 : decoderLowBit0Zero r) (h_b1 : decoderLowBit1Zero r)
    (h_e1 : decoderExtraCol1Eq r)
    (h_b0_next : decoderLowBit0ZeroNext r) (h_b1_next : decoderLowBit1ZeroNext r)
    (h_e1_next : decoderExtraCol1EqNext r) :
    Constraints.Symbolic.Decoder.base[32]! (toSymbolicFrame r) =
      Subsystems.Decoder.haltAbsorbing.eval r := by
  have h_sym :
      Constraints.Symbolic.Decoder.base[32]! (toSymbolicFrame r) =
        r.isTransition * (decoderHaltSymSel r * (1 - decoderHaltNextSymSel r)) := by
    rw [Constraints.Symbolic.Decoder.base]
    rw [getElem!_pos (h := by native_decide)]
    change (fun f =>
      f.is_transition * (((f.colCurr 9 * f.colCurr 10) * (f.colCurr 11 * f.colCurr 29)) *
        (1 - ((f.colNext 9 * f.colNext 10) * (f.colNext 11 * f.colNext 29))))) (toSymbolicFrame r) =
      r.isTransition * (decoderHaltSymSel r * (1 - decoderHaltNextSymSel r))
    simp [decoderHaltSymSel, decoderHaltNextSymSel, toSymbolicFrame, MainWidth,
      SymbolicFrame.colCurr, SymbolicFrame.colNext]
  have h_can :
      Subsystems.Decoder.haltAbsorbing.eval r =
        r.isTransition * (Subsystems.Decoder.isHalt.eval r * (1 - Subsystems.Decoder.isHaltNext.eval r)) := by
    simp [Subsystems.Decoder.haltAbsorbing, Builder.whenTransition, Builder.gate,
      Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr, FExpr.eval,
      AirRow.boundary, Subsystems.Decoder.oneMinus]
  rw [h_sym, h_can, decoderHaltSel_eval r h_b0 h_b1 h_e1,
    decoderHaltNextSel_eval r h_b0_next h_b1_next h_e1_next]

theorem bridge_decoder_33 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[33]! (toSymbolicFrame r) =
      Subsystems.Decoder.groupCountDeltaBinary.eval r := by
  rw [Constraints.Symbolic.Decoder.base]
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => f.is_transition * ((f.colCurr 22 * (f.colCurr 23 - f.colNext 23)) *
      ((f.colCurr 23 - f.colNext 23) - 1))) (toSymbolicFrame r) =
    Subsystems.Decoder.groupCountDeltaBinary.eval r
  have h22 : 22 < MainWidth := by decide
  have h23 : 23 < MainWidth := by decide
  simp only [Subsystems.Decoder.groupCountDeltaBinary, Subsystems.Decoder.inSpan,
    Subsystems.Decoder.deltaGc, Subsystems.Decoder.groupCount, Subsystems.Decoder.groupCountNext,
    Subsystems.Decoder.inSpanCol, Subsystems.Decoder.groupCountCol, Subsystems.Decoder.decoderTraceOffset,
    toSymbolicFrame, FExpr.eval, Builder.whenTransition,
    Builder.assertZero, Builder.gate, BaseConstraint.eval, BaseConstraint.expr, AirRow.boundary,
    AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, SymbolicFrame.colNext, h22, h23]
  have hSp :
      (if h : True then r.curr ⟨22, h22⟩ else 0) =
        r.curr ⟨22, Subsystems.Decoder.inSpanCol._proof_1⟩ := by
    simp
  have hGc :
      (if h : True then r.curr ⟨23, h23⟩ else 0) =
        r.curr ⟨23, Subsystems.Decoder.groupCountCol._proof_1⟩ := by
    simp
  have hGcN :
      (if h : True then r.next ⟨23, h23⟩ else 0) =
        r.next ⟨23, Subsystems.Decoder.groupCountCol._proof_1⟩ := by
    simp
  rw [hSp, hGc, hGcN]
  ring

/- `base[34]` through `base[42]` mix `SPAN`/`RESPAN`/`PUSH`/`END` selectors into
group-count and op-index transitions. They inherit the same `e0`/`e1` refinement gap
as the earlier control-flow bridge theorems. -/

theorem bridge_decoder_34 (r : AirRow)
    (h_e0 : decoderExtraCol0Eq r) :
    Constraints.Symbolic.Decoder.base[34]! (toSymbolicFrame r) =
      Subsystems.Decoder.groupCountDecrementH0OrPush.eval r := by
  let deltaGc : Felt := r.curr ⟨23, by decide⟩ - r.next ⟨23, by decide⟩
  let h0 : Felt := r.curr ⟨14, by decide⟩
  have h_sym :
      Constraints.Symbolic.Decoder.base[34]! (toSymbolicFrame r) =
        r.isTransition * (((r.curr ⟨22, by decide⟩ * deltaGc) * (1 - decoderPushSymSel r)) * h0) := by
    rw [Constraints.Symbolic.Decoder.base]
    rw [getElem!_pos (h := by native_decide)]
    change (fun f =>
      f.is_transition * (((f.colCurr 22 * (f.colCurr 23 - f.colNext 23)) *
        (1 - (((f.colCurr 7 * f.colCurr 8) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)))) *
        f.colCurr 14)) (toSymbolicFrame r) =
      r.isTransition * (((r.curr ⟨22, by decide⟩ * deltaGc) * (1 - decoderPushSymSel r)) * h0)
    simp [deltaGc, h0, decoderPushSymSel, toSymbolicFrame, MainWidth,
      SymbolicFrame.colCurr, SymbolicFrame.colNext]
  have h_can :
      Subsystems.Decoder.groupCountDecrementH0OrPush.eval r =
        r.isTransition * (((r.curr ⟨22, by decide⟩ * deltaGc) *
          (1 - Subsystems.Decoder.isPush.eval r)) * h0) := by
    simp [deltaGc, h0, Subsystems.Decoder.groupCountDecrementH0OrPush, Builder.gate,
      Subsystems.Decoder.inSpan, Subsystems.Decoder.inSpanCol, Subsystems.Decoder.deltaGc,
      Subsystems.Decoder.groupCount, Subsystems.Decoder.groupCountNext, Subsystems.Decoder.groupCountCol,
      Subsystems.Decoder.decoderH0, Subsystems.Decoder.decoderH0Col,
      Subsystems.Decoder.decoderTraceOffset, Builder.whenTransition, Builder.assertZero,
      BaseConstraint.eval, BaseConstraint.expr, FExpr.eval, AirRow.boundary, AirRow.baseAt,
      AirRow.base, Subsystems.Decoder.oneMinus]
    air_bridge_pick_selector_eq
  rw [h_sym, h_can, decoderPushSel_eval r h_e0]

theorem bridge_decoder_35 (r : AirRow)
    (h_b0 : decoderLowBit0Zero r) (h_b1 : decoderLowBit1Zero r)
    (h_e0 : decoderExtraCol0Eq r) (h_e1 : decoderExtraCol1Eq r) :
    Constraints.Symbolic.Decoder.base[35]! (toSymbolicFrame r) =
      Subsystems.Decoder.groupCountSpanDecrement.eval r := by
  let deltaGc : Felt := r.curr ⟨23, by decide⟩ - r.next ⟨23, by decide⟩
  have h_sym :
      Constraints.Symbolic.Decoder.base[35]! (toSymbolicFrame r) =
        r.isTransition *
          (((decoderSpanSymSel r + decoderRespanSymSel r) + decoderPushSymSel r) * (deltaGc - 1)) := by
    rw [Constraints.Symbolic.Decoder.base]
    rw [getElem!_pos (h := by native_decide)]
    change (fun f =>
      f.is_transition * (((((((1 - f.colCurr 7) * f.colCurr 8) * f.colCurr 9) * ((1 - f.colCurr 10) * f.colCurr 28)) +
          (((1 - f.colCurr 9) * f.colCurr 10) * (f.colCurr 11 * f.colCurr 29))) +
        (((f.colCurr 7 * f.colCurr 8) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28))) *
        ((f.colCurr 23 - f.colNext 23) - 1))) (toSymbolicFrame r) =
      r.isTransition *
        (((decoderSpanSymSel r + decoderRespanSymSel r) + decoderPushSymSel r) * (deltaGc - 1))
    simp [deltaGc, decoderSpanSymSel, decoderRespanSymSel, decoderPushSymSel,
      toSymbolicFrame, MainWidth, SymbolicFrame.colCurr, SymbolicFrame.colNext]
  have h_can :
      Subsystems.Decoder.groupCountSpanDecrement.eval r =
        r.isTransition *
          (((Subsystems.Decoder.isSpan.eval r + Subsystems.Decoder.isRespan.eval r) +
            Subsystems.Decoder.isPush.eval r) * (deltaGc - 1)) := by
    simp [deltaGc, Subsystems.Decoder.groupCountSpanDecrement, Builder.gate, Subsystems.Decoder.deltaGc,
      Subsystems.Decoder.groupCount, Subsystems.Decoder.groupCountNext, Subsystems.Decoder.groupCountCol,
      Subsystems.Decoder.decoderTraceOffset, Builder.whenTransition, Builder.assertZero,
      BaseConstraint.eval, BaseConstraint.expr, FExpr.eval, AirRow.boundary, AirRow.baseAt,
      AirRow.base]
    air_bridge_pick_selector_eq
  rw [h_sym, h_can, decoderSpanSel_eval r h_e0, decoderRespanSel_eval r h_b0 h_b1 h_e1,
    decoderPushSel_eval r h_e0]

theorem bridge_decoder_36 (r : AirRow)
    (h_b0_next : decoderLowBit0ZeroNext r) (h_b1_next : decoderLowBit1ZeroNext r)
    (h_e1_next : decoderExtraCol1EqNext r) :
    Constraints.Symbolic.Decoder.base[36]! (toSymbolicFrame r) =
      Subsystems.Decoder.groupCountHoldBeforeEndOrRespan.eval r := by
  let deltaGc : Felt := r.curr ⟨23, by decide⟩ - r.next ⟨23, by decide⟩
  have h_sym :
      Constraints.Symbolic.Decoder.base[36]! (toSymbolicFrame r) =
        r.isTransition * (deltaGc * (decoderEndNextSymSel r + decoderRespanNextSymSel r)) := by
    rw [Constraints.Symbolic.Decoder.base]
    rw [getElem!_pos (h := by native_decide)]
    change (fun f =>
      f.is_transition * ((f.colCurr 23 - f.colNext 23) *
        ((((1 - f.colNext 9) * (1 - f.colNext 10)) * (f.colNext 11 * f.colNext 29)) +
          (((1 - f.colNext 9) * f.colNext 10) * (f.colNext 11 * f.colNext 29))))) (toSymbolicFrame r) =
      r.isTransition * (deltaGc * (decoderEndNextSymSel r + decoderRespanNextSymSel r))
    simp [deltaGc, decoderEndNextSymSel, decoderRespanNextSymSel, toSymbolicFrame, MainWidth,
      SymbolicFrame.colCurr, SymbolicFrame.colNext]
  have h_can :
      Subsystems.Decoder.groupCountHoldBeforeEndOrRespan.eval r =
        r.isTransition * (deltaGc *
          (Subsystems.Decoder.isEndNext.eval r + Subsystems.Decoder.isRespanNext.eval r)) := by
    simp [deltaGc, Subsystems.Decoder.groupCountHoldBeforeEndOrRespan, Builder.gate, Subsystems.Decoder.deltaGc,
      Subsystems.Decoder.groupCount, Subsystems.Decoder.groupCountNext, Subsystems.Decoder.groupCountCol,
      Subsystems.Decoder.decoderTraceOffset, Builder.whenTransition, Builder.assertZero,
      BaseConstraint.eval, BaseConstraint.expr, FExpr.eval, AirRow.boundary, AirRow.baseAt,
      AirRow.base]
  rw [h_sym, h_can, decoderEndOrRespanNextSel_eval r h_b0_next h_b1_next h_e1_next]

theorem bridge_decoder_37 (r : AirRow)
    (h_b0 : decoderLowBit0Zero r) (h_b1 : decoderLowBit1Zero r)
    (h_e1 : decoderExtraCol1Eq r) :
    Constraints.Symbolic.Decoder.base[37]! (toSymbolicFrame r) =
      Subsystems.Decoder.groupCountZeroAtEnd.eval r := by
  let gc : Felt := r.curr ⟨23, by decide⟩
  have h_sym :
      Constraints.Symbolic.Decoder.base[37]! (toSymbolicFrame r) =
        decoderEndSymSel r * gc := by
    rw [Constraints.Symbolic.Decoder.base]
    rw [getElem!_pos (h := by native_decide)]
    change (fun f =>
      ((((1 - f.colCurr 9) * (1 - f.colCurr 10)) * (f.colCurr 11 * f.colCurr 29)) *
        f.colCurr 23)) (toSymbolicFrame r) =
      decoderEndSymSel r * gc
    simp [gc, decoderEndSymSel, toSymbolicFrame, MainWidth, SymbolicFrame.colCurr]
  have h_can :
      Subsystems.Decoder.groupCountZeroAtEnd.eval r =
        Subsystems.Decoder.isEnd.eval r * Subsystems.Decoder.groupCount.eval r := by
    simp [Subsystems.Decoder.groupCountZeroAtEnd, Builder.assertZero, BaseConstraint.eval,
      BaseConstraint.expr]
  rw [h_sym, h_can, decoderEndSel_eval r h_b0 h_b1 h_e1, decoderGroupCount_eval r]

theorem bridge_decoder_38 (r : AirRow)
    (h_b0 : decoderLowBit0Zero r) (h_b1 : decoderLowBit1Zero r)
    (h_e0 : decoderExtraCol0Eq r) (h_e1 : decoderExtraCol1Eq r) :
    Constraints.Symbolic.Decoder.base[38]! (toSymbolicFrame r) =
      Subsystems.Decoder.h0Shift.eval r := by
  let deltaGc : Felt := r.curr ⟨23, by decide⟩ - r.next ⟨23, by decide⟩
  let opNext : Felt :=
    r.next ⟨7, by decide⟩ +
      (r.next ⟨8, by decide⟩ * Felt.ofNat 2) +
      (r.next ⟨9, by decide⟩ * Felt.ofNat 4) +
      (r.next ⟨10, by decide⟩ * Felt.ofNat 8) +
      (r.next ⟨11, by decide⟩ * Felt.ofNat 16) +
      (r.next ⟨12, by decide⟩ * Felt.ofNat 32) +
      (r.next ⟨13, by decide⟩ * Felt.ofNat 64)
  have h_sym :
      Constraints.Symbolic.Decoder.base[38]! (toSymbolicFrame r) =
        r.isTransition *
          (((decoderSpanSymSel r + decoderRespanSymSel r) +
              (decoderPushSymSel r + ((r.curr ⟨22, by decide⟩ * r.next ⟨22, by decide⟩) * (1 - deltaGc)))) *
            (r.curr ⟨14, by decide⟩ - (r.next ⟨14, by decide⟩ * Felt.ofNat 128 + opNext))) := by
    rw [Constraints.Symbolic.Decoder.base]
    rw [getElem!_pos (h := by native_decide)]
    change
      ((fun f =>
          f.is_transition *
            ((((((((1 - f.colCurr 7) * f.colCurr 8) * f.colCurr 9) * ((1 - f.colCurr 10) * f.colCurr 28)) +
                  (((1 - f.colCurr 9) * f.colCurr 10) * (f.colCurr 11 * f.colCurr 29))) +
                (((f.colCurr 7 * f.colCurr 8) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28))) +
              ((f.colCurr 22 * f.colNext 22) * (1 - (f.colCurr 23 - f.colNext 23)))) *
              ((f.colCurr 14 - (f.colNext 14 * Felt.ofNat 128)) -
                ((((((f.colNext 7 + (f.colNext 8 * Felt.ofNat 2)) + (f.colNext 9 * Felt.ofNat 4)) +
                    (f.colNext 10 * Felt.ofNat 8)) +
                  (f.colNext 11 * Felt.ofNat 16)) +
                (f.colNext 12 * Felt.ofNat 32)) +
                  (f.colNext 13 * Felt.ofNat 64))))
        ) (toSymbolicFrame r)) =
      r.isTransition *
        (((decoderSpanSymSel r + decoderRespanSymSel r) +
            (decoderPushSymSel r + ((r.curr ⟨22, by decide⟩ * r.next ⟨22, by decide⟩) * (1 - deltaGc)))) *
          (r.curr ⟨14, by decide⟩ - (r.next ⟨14, by decide⟩ * Felt.ofNat 128 + opNext)))
    simp [deltaGc, opNext, decoderSpanSymSel, decoderRespanSymSel, decoderPushSymSel,
      toSymbolicFrame, MainWidth, SymbolicFrame.colCurr, SymbolicFrame.colNext]
    ring_nf
    simp
  have h_can :
      Subsystems.Decoder.h0Shift.eval r =
        r.isTransition *
          ((Subsystems.Decoder.spanOrRespan.eval r +
              (Subsystems.Decoder.isPush.eval r + Subsystems.Decoder.fSgc.eval r)) *
            (r.curr ⟨14, by decide⟩ -
              (r.next ⟨14, by decide⟩ * Felt.ofNat 128 + Subsystems.Decoder.opNext.eval r))) := by
    simp [Subsystems.Decoder.h0Shift, Builder.gate, Subsystems.Decoder.decoderH0, Subsystems.Decoder.decoderH0Next,
      Subsystems.Decoder.decoderH0Col, Subsystems.Decoder.decoderTraceOffset, Builder.whenTransition,
      Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr, FExpr.eval, AirRow.boundary,
      AirRow.baseAt, AirRow.base]
    left
    left
    left
    rfl
  rw [h_sym, h_can, decoderSpanOrRespanSel_eval r h_b0 h_b1 h_e0 h_e1,
    decoderPushSel_eval r h_e0, decoderFSgc_eval r, decoderOpNext_eval r]

theorem bridge_decoder_39 (r : AirRow)
    (h_b0_next : decoderLowBit0ZeroNext r) (h_b1_next : decoderLowBit1ZeroNext r)
    (h_e1_next : decoderExtraCol1EqNext r) :
    Constraints.Symbolic.Decoder.base[39]! (toSymbolicFrame r) =
      Subsystems.Decoder.h0ZeroBeforeEndOrRespan.eval r := by
  let h0 : Felt := r.curr ⟨14, by decide⟩
  have h_sym :
      Constraints.Symbolic.Decoder.base[39]! (toSymbolicFrame r) =
        r.isTransition *
          ((r.curr ⟨22, by decide⟩ * (decoderEndNextSymSel r + decoderRespanNextSymSel r)) * h0) := by
    rw [Constraints.Symbolic.Decoder.base]
    rw [getElem!_pos (h := by native_decide)]
    change (fun f =>
      f.is_transition * ((f.colCurr 22 *
        ((((1 - f.colNext 9) * (1 - f.colNext 10)) * (f.colNext 11 * f.colNext 29)) +
          (((1 - f.colNext 9) * f.colNext 10) * (f.colNext 11 * f.colNext 29)))) *
        f.colCurr 14)) (toSymbolicFrame r) =
      r.isTransition *
        ((r.curr ⟨22, by decide⟩ * (decoderEndNextSymSel r + decoderRespanNextSymSel r)) * h0)
    simp [h0, decoderEndNextSymSel, decoderRespanNextSymSel, toSymbolicFrame, MainWidth,
      SymbolicFrame.colCurr, SymbolicFrame.colNext]
  have h_can :
      Subsystems.Decoder.h0ZeroBeforeEndOrRespan.eval r =
        r.isTransition *
          ((r.curr ⟨22, by decide⟩ *
            (Subsystems.Decoder.isEndNext.eval r + Subsystems.Decoder.isRespanNext.eval r)) * h0) := by
    simp [h0, Subsystems.Decoder.h0ZeroBeforeEndOrRespan, Builder.gate, Subsystems.Decoder.sp,
      Subsystems.Decoder.inSpan, Subsystems.Decoder.inSpanCol, Subsystems.Decoder.decoderH0,
      Subsystems.Decoder.decoderH0Col, Subsystems.Decoder.decoderTraceOffset, Builder.whenTransition,
      Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr, FExpr.eval, AirRow.boundary,
      AirRow.baseAt, AirRow.base]
    air_bridge_pick_selector_eq
  rw [h_sym, h_can, decoderEndOrRespanNextSel_eval r h_b0_next h_b1_next h_e1_next]

theorem bridge_decoder_40 (r : AirRow)
    (h_b0 : decoderLowBit0Zero r) (h_b1 : decoderLowBit1Zero r)
    (h_e0 : decoderExtraCol0Eq r) (h_e1 : decoderExtraCol1Eq r) :
    Constraints.Symbolic.Decoder.base[40]! (toSymbolicFrame r) =
      Subsystems.Decoder.opIndexSpanRespanReset.eval r := by
  have h_sym :
      Constraints.Symbolic.Decoder.base[40]! (toSymbolicFrame r) =
        r.isTransition * ((decoderSpanSymSel r + decoderRespanSymSel r) * r.next ⟨24, by decide⟩) := by
    rw [Constraints.Symbolic.Decoder.base]
    rw [getElem!_pos (h := by native_decide)]
    change (fun f =>
      f.is_transition * ((((((1 - f.colCurr 7) * f.colCurr 8) * f.colCurr 9) * ((1 - f.colCurr 10) * f.colCurr 28)) +
        (((1 - f.colCurr 9) * f.colCurr 10) * (f.colCurr 11 * f.colCurr 29))) * f.colNext 24))
      (toSymbolicFrame r) =
      r.isTransition * ((decoderSpanSymSel r + decoderRespanSymSel r) * r.next ⟨24, by decide⟩)
    simp [decoderSpanSymSel, decoderRespanSymSel, toSymbolicFrame, MainWidth,
      SymbolicFrame.colCurr, SymbolicFrame.colNext]
  have h_can :
      Subsystems.Decoder.opIndexSpanRespanReset.eval r =
        r.isTransition * (Subsystems.Decoder.spanOrRespan.eval r * r.next ⟨24, by decide⟩) := by
    simp [Subsystems.Decoder.opIndexSpanRespanReset, Builder.gate, Subsystems.Decoder.oxNext, Subsystems.Decoder.opIndexCol,
      Subsystems.Decoder.decoderTraceOffset, Builder.whenTransition, Builder.assertZero,
      BaseConstraint.eval, BaseConstraint.expr, FExpr.eval, AirRow.boundary, AirRow.baseAt, AirRow.base]
  rw [h_sym, h_can, decoderSpanOrRespanSel_eval r h_b0 h_b1 h_e0 h_e1]

theorem bridge_decoder_41 (r : AirRow)
    (h_e0 : decoderExtraCol0Eq r) :
    Constraints.Symbolic.Decoder.base[41]! (toSymbolicFrame r) =
      Subsystems.Decoder.opIndexNewGroupReset.eval r := by
  have h_sym :
      Constraints.Symbolic.Decoder.base[41]! (toSymbolicFrame r) =
        r.isTransition *
          ((r.curr ⟨22, by decide⟩ *
            ((r.curr ⟨23, by decide⟩ - r.next ⟨23, by decide⟩) - decoderPushSymSel r)) *
            r.next ⟨24, by decide⟩) := by
    rw [Constraints.Symbolic.Decoder.base]
    rw [getElem!_pos (h := by native_decide)]
    change (fun f =>
      f.is_transition * ((f.colCurr 22 * ((f.colCurr 23 - f.colNext 23) -
        (((f.colCurr 7 * f.colCurr 8) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28)))) *
        f.colNext 24)) (toSymbolicFrame r) =
      r.isTransition *
        ((r.curr ⟨22, by decide⟩ *
          ((r.curr ⟨23, by decide⟩ - r.next ⟨23, by decide⟩) - decoderPushSymSel r)) *
          r.next ⟨24, by decide⟩)
    simp [decoderPushSymSel, toSymbolicFrame, MainWidth, SymbolicFrame.colCurr, SymbolicFrame.colNext]
  have h_can :
      Subsystems.Decoder.opIndexNewGroupReset.eval r =
        r.isTransition *
          ((r.curr ⟨22, by decide⟩ * Subsystems.Decoder.newGroup.eval r) * r.next ⟨24, by decide⟩) := by
    simp [Subsystems.Decoder.opIndexNewGroupReset, Builder.gate, Subsystems.Decoder.sp, Subsystems.Decoder.inSpan,
      Subsystems.Decoder.inSpanCol, Subsystems.Decoder.oxNext, Subsystems.Decoder.opIndexCol,
      Subsystems.Decoder.decoderTraceOffset, Builder.whenTransition, Builder.assertZero,
      BaseConstraint.eval, BaseConstraint.expr, FExpr.eval, AirRow.boundary, AirRow.baseAt, AirRow.base]
    air_bridge_pick_selector_eq
  rw [h_sym, h_can, decoderNewGroup_eval r h_e0]

theorem bridge_decoder_42 (r : AirRow)
    (h_e0 : decoderExtraCol0Eq r) :
    Constraints.Symbolic.Decoder.base[42]! (toSymbolicFrame r) =
      Subsystems.Decoder.opIndexIncrement.eval r := by
  let deltaGc : Felt := r.curr ⟨23, by decide⟩ - r.next ⟨23, by decide⟩
  have h_sym :
      Constraints.Symbolic.Decoder.base[42]! (toSymbolicFrame r) =
        r.isTransition *
          (((r.curr ⟨22, by decide⟩ * r.next ⟨22, by decide⟩) *
            (1 - (deltaGc - decoderPushSymSel r))) *
            ((r.next ⟨24, by decide⟩ - r.curr ⟨24, by decide⟩) - 1)) := by
    rw [Constraints.Symbolic.Decoder.base]
    rw [getElem!_pos (h := by native_decide)]
    change (fun f =>
      f.is_transition * (((f.colCurr 22 * f.colNext 22) *
        (1 - ((f.colCurr 23 - f.colNext 23) -
          (((f.colCurr 7 * f.colCurr 8) * (1 - f.colCurr 9)) * (f.colCurr 10 * f.colCurr 28))))) *
        ((f.colNext 24 - f.colCurr 24) - 1))) (toSymbolicFrame r) =
      r.isTransition *
        (((r.curr ⟨22, by decide⟩ * r.next ⟨22, by decide⟩) *
          (1 - (deltaGc - decoderPushSymSel r))) *
          ((r.next ⟨24, by decide⟩ - r.curr ⟨24, by decide⟩) - 1))
    simp [deltaGc, decoderPushSymSel, toSymbolicFrame, MainWidth,
      SymbolicFrame.colCurr, SymbolicFrame.colNext]
  have h_can :
      Subsystems.Decoder.opIndexIncrement.eval r =
        r.isTransition *
          (((r.curr ⟨22, by decide⟩ * r.next ⟨22, by decide⟩) *
            (1 - Subsystems.Decoder.newGroup.eval r)) *
            ((r.next ⟨24, by decide⟩ - r.curr ⟨24, by decide⟩) - 1)) := by
    simp [Subsystems.Decoder.opIndexIncrement, Builder.gate, Subsystems.Decoder.sp, Subsystems.Decoder.spNext,
      Subsystems.Decoder.inSpan, Subsystems.Decoder.inSpanNext, Subsystems.Decoder.inSpanCol,
      Subsystems.Decoder.ox, Subsystems.Decoder.oxNext, Subsystems.Decoder.opIndex, Subsystems.Decoder.opIndexCol,
      Subsystems.Decoder.decoderTraceOffset, Builder.whenTransition, Builder.assertZero,
      BaseConstraint.eval, BaseConstraint.expr, FExpr.eval, AirRow.boundary, AirRow.baseAt,
      AirRow.base, Subsystems.Decoder.oneMinus]
    air_bridge_pick_selector_eq
  rw [h_sym, h_can, decoderNewGroup_eval r h_e0]

theorem bridge_decoder_43 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[43]! (toSymbolicFrame r) =
      Subsystems.Decoder.opIndexRange.eval r := by
  rw [Constraints.Symbolic.Decoder.base]
  rw [getElem!_pos (h := by native_decide)]
  rw [decoderOpIndexRange_eval r]
  change (fun f =>
    ((((((((f.colCurr 24 * (f.colCurr 24 - 1)) * (f.colCurr 24 - Felt.ofNat 2)) *
          (f.colCurr 24 - Felt.ofNat 3)) *
        (f.colCurr 24 - Felt.ofNat 4)) *
      (f.colCurr 24 - Felt.ofNat 5)) *
        (f.colCurr 24 - Felt.ofNat 6)) *
      (f.colCurr 24 - Felt.ofNat 7)) *
        (f.colCurr 24 - Felt.ofNat 8))) (toSymbolicFrame r) =
    r.curr ⟨24, by decide⟩ *
      ((r.curr ⟨24, by decide⟩ - 1) *
        ((r.curr ⟨24, by decide⟩ - Felt.ofNat 2) *
          ((r.curr ⟨24, by decide⟩ - Felt.ofNat 3) *
            ((r.curr ⟨24, by decide⟩ - Felt.ofNat 4) *
              ((r.curr ⟨24, by decide⟩ - Felt.ofNat 5) *
                ((r.curr ⟨24, by decide⟩ - Felt.ofNat 6) *
                  ((r.curr ⟨24, by decide⟩ - Felt.ofNat 7) *
                    (r.curr ⟨24, by decide⟩ - Felt.ofNat 8))))))))
  simp [toSymbolicFrame, MainWidth, SymbolicFrame.colCurr]
  ac_rfl

/- `base[44]` and `base[45]` compare the compressed `SPAN`/`RESPAN` selectors
against the batch-flag encoding, so they stay as documented gaps for now. -/

theorem bridge_decoder_44 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[44]! (toSymbolicFrame r) =
      Subsystems.Decoder.batchFlagSpanSum.eval r := by
  sorry

theorem bridge_decoder_45 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[45]! (toSymbolicFrame r) =
      Subsystems.Decoder.batchFlagZeroWhenNotSpan.eval r := by
  sorry

theorem bridge_decoder_46 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[46]! (toSymbolicFrame r) =
      Subsystems.Decoder.batchFlagH4Zero.eval r := by
  rw [Constraints.Symbolic.Decoder.base]
  rw [getElem!_pos (h := by native_decide)]
  change (fun f =>
      ((((((1 - f.colCurr 25) * f.colCurr 26) * f.colCurr 27) +
          (((1 - f.colCurr 25) * (1 - f.colCurr 26)) * f.colCurr 27)) +
        (((1 - f.colCurr 25) * f.colCurr 26) * (1 - f.colCurr 27))) * f.h 2))
      (toSymbolicFrame r) = Subsystems.Decoder.batchFlagH4Zero.eval r
  have h18 : 18 < MainWidth := by decide
  have h25 : 25 < MainWidth := by decide
  have h26 : 26 < MainWidth := by decide
  have h27 : 27 < MainWidth := by decide
  simp only [Subsystems.Decoder.batchFlagH4Zero, Subsystems.Decoder.smallBatch,
    Subsystems.Decoder.fG1, Subsystems.Decoder.fG2, Subsystems.Decoder.fG4,
    Subsystems.Decoder.batchFlag0, Subsystems.Decoder.batchFlag1, Subsystems.Decoder.batchFlag2,
    Subsystems.Decoder.decoderH4, Subsystems.Decoder.oneMinus, Subsystems.Decoder.batchFlag0Col,
    Subsystems.Decoder.batchFlag1Col, Subsystems.Decoder.batchFlag2Col, Subsystems.Decoder.decoderH4Col,
    Subsystems.Decoder.decoderTraceOffset, toSymbolicFrame, FExpr.eval, Builder.gate,
    Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr, AirRow.baseAt, AirRow.base,
    SymbolicFrame.colCurr, SymbolicFrame.h, h18, h25, h26, h27]
  ring_nf
  simp

theorem bridge_decoder_47 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[47]! (toSymbolicFrame r) =
      Subsystems.Decoder.batchFlagH5Zero.eval r := by
  rw [Constraints.Symbolic.Decoder.base]
  rw [getElem!_pos (h := by native_decide)]
  change (fun f =>
      ((((((1 - f.colCurr 25) * f.colCurr 26) * f.colCurr 27) +
          (((1 - f.colCurr 25) * (1 - f.colCurr 26)) * f.colCurr 27)) +
        (((1 - f.colCurr 25) * f.colCurr 26) * (1 - f.colCurr 27))) * f.h 3))
      (toSymbolicFrame r) = Subsystems.Decoder.batchFlagH5Zero.eval r
  have h19 : 19 < MainWidth := by decide
  have h25 : 25 < MainWidth := by decide
  have h26 : 26 < MainWidth := by decide
  have h27 : 27 < MainWidth := by decide
  simp only [Subsystems.Decoder.batchFlagH5Zero, Subsystems.Decoder.smallBatch,
    Subsystems.Decoder.fG1, Subsystems.Decoder.fG2, Subsystems.Decoder.fG4,
    Subsystems.Decoder.batchFlag0, Subsystems.Decoder.batchFlag1, Subsystems.Decoder.batchFlag2,
    Subsystems.Decoder.decoderH5, Subsystems.Decoder.oneMinus, Subsystems.Decoder.batchFlag0Col,
    Subsystems.Decoder.batchFlag1Col, Subsystems.Decoder.batchFlag2Col, Subsystems.Decoder.decoderH5Col,
    Subsystems.Decoder.decoderTraceOffset, toSymbolicFrame, FExpr.eval, Builder.gate,
    Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr, AirRow.baseAt, AirRow.base,
    SymbolicFrame.colCurr, SymbolicFrame.h, h19, h25, h26, h27]
  ring_nf
  simp

theorem bridge_decoder_48 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[48]! (toSymbolicFrame r) =
      Subsystems.Decoder.batchFlagH6Zero.eval r := by
  rw [Constraints.Symbolic.Decoder.base]
  rw [getElem!_pos (h := by native_decide)]
  change (fun f =>
      ((((((1 - f.colCurr 25) * f.colCurr 26) * f.colCurr 27) +
          (((1 - f.colCurr 25) * (1 - f.colCurr 26)) * f.colCurr 27)) +
        (((1 - f.colCurr 25) * f.colCurr 26) * (1 - f.colCurr 27))) * f.h 4))
      (toSymbolicFrame r) = Subsystems.Decoder.batchFlagH6Zero.eval r
  have h20 : 20 < MainWidth := by decide
  have h25 : 25 < MainWidth := by decide
  have h26 : 26 < MainWidth := by decide
  have h27 : 27 < MainWidth := by decide
  simp only [Subsystems.Decoder.batchFlagH6Zero, Subsystems.Decoder.smallBatch,
    Subsystems.Decoder.fG1, Subsystems.Decoder.fG2, Subsystems.Decoder.fG4,
    Subsystems.Decoder.batchFlag0, Subsystems.Decoder.batchFlag1, Subsystems.Decoder.batchFlag2,
    Subsystems.Decoder.decoderH6, Subsystems.Decoder.oneMinus, Subsystems.Decoder.batchFlag0Col,
    Subsystems.Decoder.batchFlag1Col, Subsystems.Decoder.batchFlag2Col, Subsystems.Decoder.decoderH6Col,
    Subsystems.Decoder.decoderTraceOffset, toSymbolicFrame, FExpr.eval, Builder.gate,
    Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr, AirRow.baseAt, AirRow.base,
    SymbolicFrame.colCurr, SymbolicFrame.h, h20, h25, h26, h27]
  ring_nf
  simp

theorem bridge_decoder_49 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[49]! (toSymbolicFrame r) =
      Subsystems.Decoder.batchFlagH7Zero.eval r := by
  rw [Constraints.Symbolic.Decoder.base]
  rw [getElem!_pos (h := by native_decide)]
  change (fun f =>
      ((((((1 - f.colCurr 25) * f.colCurr 26) * f.colCurr 27) +
          (((1 - f.colCurr 25) * (1 - f.colCurr 26)) * f.colCurr 27)) +
        (((1 - f.colCurr 25) * f.colCurr 26) * (1 - f.colCurr 27))) * f.h 5))
      (toSymbolicFrame r) = Subsystems.Decoder.batchFlagH7Zero.eval r
  have h21 : 21 < MainWidth := by decide
  have h25 : 25 < MainWidth := by decide
  have h26 : 26 < MainWidth := by decide
  have h27 : 27 < MainWidth := by decide
  simp only [Subsystems.Decoder.batchFlagH7Zero, Subsystems.Decoder.smallBatch,
    Subsystems.Decoder.fG1, Subsystems.Decoder.fG2, Subsystems.Decoder.fG4,
    Subsystems.Decoder.batchFlag0, Subsystems.Decoder.batchFlag1, Subsystems.Decoder.batchFlag2,
    Subsystems.Decoder.decoderH7, Subsystems.Decoder.oneMinus, Subsystems.Decoder.batchFlag0Col,
    Subsystems.Decoder.batchFlag1Col, Subsystems.Decoder.batchFlag2Col, Subsystems.Decoder.decoderH7Col,
    Subsystems.Decoder.decoderTraceOffset, toSymbolicFrame, FExpr.eval, Builder.gate,
    Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr, AirRow.baseAt, AirRow.base,
    SymbolicFrame.colCurr, SymbolicFrame.h, h21, h25, h26, h27]
  ring_nf
  simp

theorem bridge_decoder_50 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[50]! (toSymbolicFrame r) =
      Subsystems.Decoder.batchFlagH2Zero.eval r := by
  rw [Constraints.Symbolic.Decoder.base]
  rw [getElem!_pos (h := by native_decide)]
  change (fun f =>
      (((((1 - f.colCurr 25) * f.colCurr 26) * f.colCurr 27) +
          (((1 - f.colCurr 25) * (1 - f.colCurr 26)) * f.colCurr 27)) * f.h 0))
      (toSymbolicFrame r) = Subsystems.Decoder.batchFlagH2Zero.eval r
  have h16 : 16 < MainWidth := by decide
  have h25 : 25 < MainWidth := by decide
  have h26 : 26 < MainWidth := by decide
  have h27 : 27 < MainWidth := by decide
  simp only [Subsystems.Decoder.batchFlagH2Zero, Subsystems.Decoder.tinyBatch,
    Subsystems.Decoder.fG1, Subsystems.Decoder.fG2, Subsystems.Decoder.batchFlag0,
    Subsystems.Decoder.batchFlag1, Subsystems.Decoder.batchFlag2, Subsystems.Decoder.decoderH2,
    Subsystems.Decoder.oneMinus, Subsystems.Decoder.batchFlag0Col, Subsystems.Decoder.batchFlag1Col,
    Subsystems.Decoder.batchFlag2Col, Subsystems.Decoder.decoderH2Col, Subsystems.Decoder.decoderTraceOffset,
    toSymbolicFrame, FExpr.eval, Builder.gate, Builder.assertZero, BaseConstraint.eval,
    BaseConstraint.expr, AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, SymbolicFrame.h,
    h16, h25, h26, h27]
  ring_nf
  simp

theorem bridge_decoder_51 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[51]! (toSymbolicFrame r) =
      Subsystems.Decoder.batchFlagH3Zero.eval r := by
  rw [Constraints.Symbolic.Decoder.base]
  rw [getElem!_pos (h := by native_decide)]
  change (fun f =>
      (((((1 - f.colCurr 25) * f.colCurr 26) * f.colCurr 27) +
          (((1 - f.colCurr 25) * (1 - f.colCurr 26)) * f.colCurr 27)) * f.h 1))
      (toSymbolicFrame r) = Subsystems.Decoder.batchFlagH3Zero.eval r
  have h17 : 17 < MainWidth := by decide
  have h25 : 25 < MainWidth := by decide
  have h26 : 26 < MainWidth := by decide
  have h27 : 27 < MainWidth := by decide
  simp only [Subsystems.Decoder.batchFlagH3Zero, Subsystems.Decoder.tinyBatch,
    Subsystems.Decoder.fG1, Subsystems.Decoder.fG2, Subsystems.Decoder.batchFlag0,
    Subsystems.Decoder.batchFlag1, Subsystems.Decoder.batchFlag2, Subsystems.Decoder.decoderH3,
    Subsystems.Decoder.oneMinus, Subsystems.Decoder.batchFlag0Col, Subsystems.Decoder.batchFlag1Col,
    Subsystems.Decoder.batchFlag2Col, Subsystems.Decoder.decoderH3Col, Subsystems.Decoder.decoderTraceOffset,
    toSymbolicFrame, FExpr.eval, Builder.gate, Builder.assertZero, BaseConstraint.eval,
    BaseConstraint.expr, AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, SymbolicFrame.h,
    h17, h25, h26, h27]
  ring_nf
  simp

theorem bridge_decoder_52 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[52]! (toSymbolicFrame r) =
      Subsystems.Decoder.batchFlagH1Zero.eval r := by
  rw [Constraints.Symbolic.Decoder.base]
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => ((((1 - f.colCurr 25) * f.colCurr 26) * f.colCurr 27) * f.colCurr 15))
      (toSymbolicFrame r) = Subsystems.Decoder.batchFlagH1Zero.eval r
  have h15 : 15 < MainWidth := by decide
  have h25 : 25 < MainWidth := by decide
  have h26 : 26 < MainWidth := by decide
  have h27 : 27 < MainWidth := by decide
  simp only [Subsystems.Decoder.batchFlagH1Zero, Subsystems.Decoder.fG1,
    Subsystems.Decoder.batchFlag0, Subsystems.Decoder.batchFlag1, Subsystems.Decoder.batchFlag2,
    Subsystems.Decoder.decoderH1, Subsystems.Decoder.oneMinus, Subsystems.Decoder.batchFlag0Col,
    Subsystems.Decoder.batchFlag1Col, Subsystems.Decoder.batchFlag2Col, Subsystems.Decoder.decoderH1Col,
    Subsystems.Decoder.decoderTraceOffset, toSymbolicFrame, FExpr.eval, Builder.gate,
    Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr, AirRow.baseAt, AirRow.base,
    SymbolicFrame.colCurr, h15, h25, h26, h27]
  ring_nf
  simp

theorem bridge_decoder_53 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[53]! (toSymbolicFrame r) =
      Subsystems.Decoder.blockAddrHoldInSpan.eval r := by
  rw [Constraints.Symbolic.Decoder.base]
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => f.is_transition * (f.colCurr 22 * (f.colNext 6 - f.colCurr 6)))
      (toSymbolicFrame r) = Subsystems.Decoder.blockAddrHoldInSpan.eval r
  have h6 : 6 < MainWidth := by decide
  have h22 : 22 < MainWidth := by decide
  simp only [Subsystems.Decoder.blockAddrHoldInSpan, Subsystems.Decoder.sp, Subsystems.Decoder.inSpan,
    Subsystems.Decoder.addrNext, Subsystems.Decoder.addr, Subsystems.Decoder.inSpanCol,
    Subsystems.Decoder.addrCol, Subsystems.Decoder.decoderTraceOffset, toSymbolicFrame,
    FExpr.eval, Builder.whenTransition, Builder.gate, Builder.assertZero, BaseConstraint.eval,
    BaseConstraint.expr, AirRow.boundary, AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr,
    SymbolicFrame.colNext, h6, h22]
  have hCurr :
      (if h : True then r.curr ⟨22, h22⟩ else 0) =
        r.curr ⟨22, Subsystems.Decoder.inSpanCol._proof_1⟩ := by
    simp
  have hAddr :
      (if h : True then r.curr ⟨6, h6⟩ else 0) =
        r.curr ⟨6, Subsystems.Decoder.addrCol._proof_1⟩ := by
    simp
  have hAddrN :
      (if h : True then r.next ⟨6, h6⟩ else 0) =
        r.next ⟨6, Subsystems.Decoder.addrCol._proof_1⟩ := by
    simp
  rw [hCurr, hAddr, hAddrN]

/- `base[54]` and `base[55]` use `RESPAN`/`HALT` selectors through `e1`, and
`base[56]` is the global control-flow complement that aggregates the same compressed
selectors. All three therefore need extra refinement facts before the bridge closes. -/

theorem bridge_decoder_54 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[54]! (toSymbolicFrame r) =
      Subsystems.Decoder.blockAddrRespanIncrement.eval r := by
  sorry

theorem bridge_decoder_55 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[55]! (toSymbolicFrame r) =
      Subsystems.Decoder.blockAddrHaltZero.eval r := by
  sorry

theorem bridge_decoder_56 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[56]! (toSymbolicFrame r) =
      Subsystems.Decoder.spComplementControlFlow.eval r := by
  sorry

end MidenLean.AIR.Semantics.Refinement.SymbolicToCanonical
