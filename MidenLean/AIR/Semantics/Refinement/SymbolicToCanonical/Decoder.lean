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

theorem bridge_decoder_2 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[2]! (toSymbolicFrame r) =
      Subsystems.Decoder.inSpanAfterSpan.eval r := by
  sorry

theorem bridge_decoder_3 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[3]! (toSymbolicFrame r) =
      Subsystems.Decoder.inSpanAfterRespan.eval r := by
  sorry

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

theorem bridge_decoder_19 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[19]! (toSymbolicFrame r) =
      Subsystems.Decoder.splitLoopS0Binary.eval r := by
  sorry

theorem bridge_decoder_20 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[20]! (toSymbolicFrame r) =
      Subsystems.Decoder.dynH4Zero.eval r := by
  sorry

theorem bridge_decoder_21 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[21]! (toSymbolicFrame r) =
      Subsystems.Decoder.dynH5Zero.eval r := by
  sorry

theorem bridge_decoder_22 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[22]! (toSymbolicFrame r) =
      Subsystems.Decoder.dynH6Zero.eval r := by
  sorry

theorem bridge_decoder_23 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[23]! (toSymbolicFrame r) =
      Subsystems.Decoder.dynH7Zero.eval r := by
  sorry

theorem bridge_decoder_24 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[24]! (toSymbolicFrame r) =
      Subsystems.Decoder.repeatS0One.eval r := by
  sorry

theorem bridge_decoder_25 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[25]! (toSymbolicFrame r) =
      Subsystems.Decoder.repeatH4One.eval r := by
  sorry

theorem bridge_decoder_26 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[26]! (toSymbolicFrame r) =
      Subsystems.Decoder.endLoopS0Zero.eval r := by
  sorry

theorem bridge_decoder_27 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[27]! (toSymbolicFrame r) =
      Subsystems.Decoder.endRepeatCarryH0.eval r := by
  sorry

theorem bridge_decoder_28 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[28]! (toSymbolicFrame r) =
      Subsystems.Decoder.endRepeatCarryH1.eval r := by
  sorry

theorem bridge_decoder_29 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[29]! (toSymbolicFrame r) =
      Subsystems.Decoder.endRepeatCarryH2.eval r := by
  sorry

theorem bridge_decoder_30 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[30]! (toSymbolicFrame r) =
      Subsystems.Decoder.endRepeatCarryH3.eval r := by
  sorry

theorem bridge_decoder_31 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[31]! (toSymbolicFrame r) =
      Subsystems.Decoder.endRepeatCarryH4.eval r := by
  sorry

theorem bridge_decoder_32 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[32]! (toSymbolicFrame r) =
      Subsystems.Decoder.haltAbsorbing.eval r := by
  sorry

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

theorem bridge_decoder_34 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[34]! (toSymbolicFrame r) =
      Subsystems.Decoder.groupCountDecrementH0OrPush.eval r := by
  sorry

theorem bridge_decoder_35 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[35]! (toSymbolicFrame r) =
      Subsystems.Decoder.groupCountSpanDecrement.eval r := by
  sorry

theorem bridge_decoder_36 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[36]! (toSymbolicFrame r) =
      Subsystems.Decoder.groupCountHoldBeforeEndOrRespan.eval r := by
  sorry

theorem bridge_decoder_37 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[37]! (toSymbolicFrame r) =
      Subsystems.Decoder.groupCountZeroAtEnd.eval r := by
  sorry

theorem bridge_decoder_38 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[38]! (toSymbolicFrame r) =
      Subsystems.Decoder.h0Shift.eval r := by
  sorry

theorem bridge_decoder_39 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[39]! (toSymbolicFrame r) =
      Subsystems.Decoder.h0ZeroBeforeEndOrRespan.eval r := by
  sorry

theorem bridge_decoder_40 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[40]! (toSymbolicFrame r) =
      Subsystems.Decoder.opIndexSpanRespanReset.eval r := by
  sorry

theorem bridge_decoder_41 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[41]! (toSymbolicFrame r) =
      Subsystems.Decoder.opIndexNewGroupReset.eval r := by
  sorry

theorem bridge_decoder_42 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[42]! (toSymbolicFrame r) =
      Subsystems.Decoder.opIndexIncrement.eval r := by
  sorry

/- `base[43]` does not appear to suffer from the decoder `e0`/`e1` selector mismatch.
The remaining gap here is only a large associativity/normalization proof for the degree-8
`ox` range polynomial, so it is left as a documented `sorry` instead of burning the whole
heartbeat budget on a purely algebraic reshaping lemma. -/
theorem bridge_decoder_43 (r : AirRow) :
    Constraints.Symbolic.Decoder.base[43]! (toSymbolicFrame r) =
      Subsystems.Decoder.opIndexRange.eval r := by
  sorry

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
