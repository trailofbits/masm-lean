import MidenLean.AIR.Semantics.Tactics
import MidenLean.AIR.Semantics.Subsystems.ChipletSelectors
import MidenLean.AIR.Constraints.Symbolic.ChipletSelectors

set_option maxHeartbeats 8000000

namespace MidenLean.AIR.Semantics.Refinement.SymbolicToCanonical

open MidenLean
open MidenLean.AIR
open MidenLean.AIR.Semantics
open MidenLean.AIR.Semantics.Tactics
open MidenLean.AIR.Semantics.Builder

@[simp] theorem curr_chipletSelectors_s0Col_eq (r : AirRow) :
    r.curr Subsystems.ChipletSelectors.s0Col = r.curr 51 := rfl

@[simp] theorem next_chipletSelectors_s0Col_eq (r : AirRow) :
    r.next Subsystems.ChipletSelectors.s0Col = r.next 51 := rfl

@[simp] theorem curr_chipletSelectors_s1Col_eq (r : AirRow) :
    r.curr Subsystems.ChipletSelectors.s1Col = r.curr 52 := rfl

@[simp] theorem next_chipletSelectors_s1Col_eq (r : AirRow) :
    r.next Subsystems.ChipletSelectors.s1Col = r.next 52 := rfl

@[simp] theorem curr_chipletSelectors_s2Col_eq (r : AirRow) :
    r.curr Subsystems.ChipletSelectors.s2Col = r.curr 53 := rfl

@[simp] theorem next_chipletSelectors_s2Col_eq (r : AirRow) :
    r.next Subsystems.ChipletSelectors.s2Col = r.next 53 := rfl

@[simp] theorem curr_chipletSelectors_s3Col_eq (r : AirRow) :
    r.curr Subsystems.ChipletSelectors.s3Col = r.curr 54 := rfl

@[simp] theorem next_chipletSelectors_s3Col_eq (r : AirRow) :
    r.next Subsystems.ChipletSelectors.s3Col = r.next 54 := rfl

@[simp] theorem curr_chipletSelectors_s4Col_eq (r : AirRow) :
    r.curr Subsystems.ChipletSelectors.s4Col = r.curr 55 := rfl

@[simp] theorem next_chipletSelectors_s4Col_eq (r : AirRow) :
    r.next Subsystems.ChipletSelectors.s4Col = r.next 55 := rfl

theorem bridge_chiplet_selectors_0 (r : AirRow) :
    Constraints.Symbolic.ChipletSelectors.base[0]! (toSymbolicFrame r) =
      Subsystems.ChipletSelectors.s0Binary.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => f.colCurr 51 * (f.colCurr 51 - 1)) (toSymbolicFrame r) =
    Subsystems.ChipletSelectors.s0Binary.eval r
  have h51 : 51 < MainWidth := by decide
  simp only [Subsystems.ChipletSelectors.s0Binary, Subsystems.ChipletSelectors.s0,
    Subsystems.ChipletSelectors.s0Col, Subsystems.ChipletSelectors.chipletsOffset,
    toSymbolicFrame, FExpr.eval, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, h51]
  simp

theorem bridge_chiplet_selectors_1 (r : AirRow) :
    Constraints.Symbolic.ChipletSelectors.base[1]! (toSymbolicFrame r) =
      Subsystems.ChipletSelectors.s1Binary.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => f.colCurr 51 * (f.colCurr 52 * (f.colCurr 52 - 1))) (toSymbolicFrame r) =
    Subsystems.ChipletSelectors.s1Binary.eval r
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  simp only [Subsystems.ChipletSelectors.s1Binary, Subsystems.ChipletSelectors.s0,
    Subsystems.ChipletSelectors.s1, Subsystems.ChipletSelectors.s0Col,
    Subsystems.ChipletSelectors.s1Col, Subsystems.ChipletSelectors.chipletsOffset,
    toSymbolicFrame, FExpr.eval, Builder.gate, Builder.assertZero, BaseConstraint.eval,
    BaseConstraint.expr, AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, h51, h52]
  simp

theorem bridge_chiplet_selectors_2 (r : AirRow) :
    Constraints.Symbolic.ChipletSelectors.base[2]! (toSymbolicFrame r) =
      Subsystems.ChipletSelectors.s2Binary.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => f.colCurr 51 * (f.colCurr 52 * (f.colCurr 53 * (f.colCurr 53 - 1))))
      (toSymbolicFrame r) = Subsystems.ChipletSelectors.s2Binary.eval r
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  simp only [Subsystems.ChipletSelectors.s2Binary, Subsystems.ChipletSelectors.s01,
    Subsystems.ChipletSelectors.s0, Subsystems.ChipletSelectors.s1,
    Subsystems.ChipletSelectors.s2, Subsystems.ChipletSelectors.s0Col,
    Subsystems.ChipletSelectors.s1Col, Subsystems.ChipletSelectors.s2Col,
    Subsystems.ChipletSelectors.chipletsOffset, toSymbolicFrame, FExpr.eval, Builder.gate,
    Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr, AirRow.baseAt, AirRow.base,
    SymbolicFrame.colCurr, h51, h52, h53]
  simp; ring_nf

theorem bridge_chiplet_selectors_3 (r : AirRow) :
    Constraints.Symbolic.ChipletSelectors.base[3]! (toSymbolicFrame r) =
      Subsystems.ChipletSelectors.s3Binary.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f =>
      f.colCurr 51 * (f.colCurr 52 * (f.colCurr 53 * (f.colCurr 54 * (f.colCurr 54 - 1)))))
      (toSymbolicFrame r) = Subsystems.ChipletSelectors.s3Binary.eval r
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  have h54 : 54 < MainWidth := by decide
  simp only [Subsystems.ChipletSelectors.s3Binary, Subsystems.ChipletSelectors.s012,
    Subsystems.ChipletSelectors.s01, Subsystems.ChipletSelectors.s0,
    Subsystems.ChipletSelectors.s1, Subsystems.ChipletSelectors.s2,
    Subsystems.ChipletSelectors.s3, Subsystems.ChipletSelectors.s0Col,
    Subsystems.ChipletSelectors.s1Col, Subsystems.ChipletSelectors.s2Col,
    Subsystems.ChipletSelectors.s3Col, Subsystems.ChipletSelectors.chipletsOffset,
    toSymbolicFrame, FExpr.eval, Builder.gate, Builder.assertZero, BaseConstraint.eval,
    BaseConstraint.expr, AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr,
    h51, h52, h53, h54]
  simp; ring_nf

theorem bridge_chiplet_selectors_4 (r : AirRow) :
    Constraints.Symbolic.ChipletSelectors.base[4]! (toSymbolicFrame r) =
      Subsystems.ChipletSelectors.s4Binary.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f =>
      f.colCurr 51 * (f.colCurr 52 * (f.colCurr 53 * (f.colCurr 54 *
        (f.colCurr 55 * (f.colCurr 55 - 1)))))) (toSymbolicFrame r) =
    Subsystems.ChipletSelectors.s4Binary.eval r
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  have h54 : 54 < MainWidth := by decide
  have h55 : 55 < MainWidth := by decide
  simp only [Subsystems.ChipletSelectors.s4Binary, Subsystems.ChipletSelectors.s0123,
    Subsystems.ChipletSelectors.s012, Subsystems.ChipletSelectors.s01,
    Subsystems.ChipletSelectors.s0, Subsystems.ChipletSelectors.s1,
    Subsystems.ChipletSelectors.s2, Subsystems.ChipletSelectors.s3,
    Subsystems.ChipletSelectors.s4, Subsystems.ChipletSelectors.s0Col,
    Subsystems.ChipletSelectors.s1Col, Subsystems.ChipletSelectors.s2Col,
    Subsystems.ChipletSelectors.s3Col, Subsystems.ChipletSelectors.s4Col,
    Subsystems.ChipletSelectors.chipletsOffset, toSymbolicFrame, FExpr.eval, Builder.gate,
    Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr, AirRow.baseAt, AirRow.base,
    SymbolicFrame.colCurr, h51, h52, h53, h54, h55]
  simp; ring_nf

theorem bridge_chiplet_selectors_5 (r : AirRow) :
    Constraints.Symbolic.ChipletSelectors.base[5]! (toSymbolicFrame r) =
      Subsystems.ChipletSelectors.s0Stability.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => f.is_transition * (f.colCurr 51 * (f.colNext 51 - f.colCurr 51)))
      (toSymbolicFrame r) = Subsystems.ChipletSelectors.s0Stability.eval r
  have h51 : 51 < MainWidth := by decide
  simp only [Subsystems.ChipletSelectors.s0Stability, Subsystems.ChipletSelectors.s0Next,
    Subsystems.ChipletSelectors.s0, Subsystems.ChipletSelectors.s0Col,
    Subsystems.ChipletSelectors.chipletsOffset, toSymbolicFrame, FExpr.eval,
    Builder.whenTransition, Builder.gate, Builder.assertEq, Builder.assertZero,
    BaseConstraint.eval, BaseConstraint.expr, AirRow.boundary, AirRow.baseAt, AirRow.base,
    SymbolicFrame.colCurr, SymbolicFrame.colNext, h51]
  simp

theorem bridge_chiplet_selectors_6 (r : AirRow) :
    Constraints.Symbolic.ChipletSelectors.base[6]! (toSymbolicFrame r) =
      Subsystems.ChipletSelectors.s1Stability.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f =>
      f.is_transition * (f.colCurr 51 * (f.colCurr 52 * (f.colNext 52 - f.colCurr 52))))
      (toSymbolicFrame r) = Subsystems.ChipletSelectors.s1Stability.eval r
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  simp only [Subsystems.ChipletSelectors.s1Stability, Subsystems.ChipletSelectors.s01,
    Subsystems.ChipletSelectors.s1Next, Subsystems.ChipletSelectors.s0,
    Subsystems.ChipletSelectors.s1, Subsystems.ChipletSelectors.s0Col,
    Subsystems.ChipletSelectors.s1Col, Subsystems.ChipletSelectors.chipletsOffset,
    toSymbolicFrame, FExpr.eval, Builder.whenTransition, Builder.gate, Builder.assertEq,
    Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr, AirRow.boundary,
    AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, SymbolicFrame.colNext, h51, h52]
  simp; ring_nf; left; trivial

theorem bridge_chiplet_selectors_7 (r : AirRow) :
    Constraints.Symbolic.ChipletSelectors.base[7]! (toSymbolicFrame r) =
      Subsystems.ChipletSelectors.s2Stability.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f =>
      f.is_transition *
        (f.colCurr 51 * (f.colCurr 52 * (f.colCurr 53 * (f.colNext 53 - f.colCurr 53)))))
      (toSymbolicFrame r) = Subsystems.ChipletSelectors.s2Stability.eval r
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  simp only [Subsystems.ChipletSelectors.s2Stability, Subsystems.ChipletSelectors.s012,
    Subsystems.ChipletSelectors.s01, Subsystems.ChipletSelectors.s2Next,
    Subsystems.ChipletSelectors.s0, Subsystems.ChipletSelectors.s1,
    Subsystems.ChipletSelectors.s2, Subsystems.ChipletSelectors.s0Col,
    Subsystems.ChipletSelectors.s1Col, Subsystems.ChipletSelectors.s2Col,
    Subsystems.ChipletSelectors.chipletsOffset, toSymbolicFrame, FExpr.eval,
    Builder.whenTransition, Builder.gate, Builder.assertEq, Builder.assertZero,
    BaseConstraint.eval, BaseConstraint.expr, AirRow.boundary, AirRow.baseAt, AirRow.base,
    SymbolicFrame.colCurr, SymbolicFrame.colNext, h51, h52, h53]
  simp; ring_nf; left; trivial

theorem bridge_chiplet_selectors_8 (r : AirRow) :
    Constraints.Symbolic.ChipletSelectors.base[8]! (toSymbolicFrame r) =
      Subsystems.ChipletSelectors.s3Stability.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f =>
      f.is_transition * (f.colCurr 51 *
        (f.colCurr 52 * (f.colCurr 53 * (f.colCurr 54 * (f.colNext 54 - f.colCurr 54))))))
      (toSymbolicFrame r) = Subsystems.ChipletSelectors.s3Stability.eval r
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  have h54 : 54 < MainWidth := by decide
  simp only [Subsystems.ChipletSelectors.s3Stability, Subsystems.ChipletSelectors.s0123,
    Subsystems.ChipletSelectors.s012, Subsystems.ChipletSelectors.s01,
    Subsystems.ChipletSelectors.s3Next, Subsystems.ChipletSelectors.s0,
    Subsystems.ChipletSelectors.s1, Subsystems.ChipletSelectors.s2,
    Subsystems.ChipletSelectors.s3, Subsystems.ChipletSelectors.s0Col,
    Subsystems.ChipletSelectors.s1Col, Subsystems.ChipletSelectors.s2Col,
    Subsystems.ChipletSelectors.s3Col, Subsystems.ChipletSelectors.chipletsOffset,
    toSymbolicFrame, FExpr.eval, Builder.whenTransition, Builder.gate, Builder.assertEq,
    Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr, AirRow.boundary,
    AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, SymbolicFrame.colNext,
    h51, h52, h53, h54]
  simp; ring_nf; left; trivial

theorem bridge_chiplet_selectors_9 (r : AirRow) :
    Constraints.Symbolic.ChipletSelectors.base[9]! (toSymbolicFrame r) =
      Subsystems.ChipletSelectors.s4Stability.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f =>
      f.is_transition * (f.colCurr 51 * (f.colCurr 52 *
        (f.colCurr 53 * (f.colCurr 54 * (f.colCurr 55 * (f.colNext 55 - f.colCurr 55)))))))
      (toSymbolicFrame r) = Subsystems.ChipletSelectors.s4Stability.eval r
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  have h54 : 54 < MainWidth := by decide
  have h55 : 55 < MainWidth := by decide
  simp only [Subsystems.ChipletSelectors.s4Stability, Subsystems.ChipletSelectors.s01234,
    Subsystems.ChipletSelectors.s0123, Subsystems.ChipletSelectors.s012,
    Subsystems.ChipletSelectors.s01, Subsystems.ChipletSelectors.s4Next,
    Subsystems.ChipletSelectors.s0, Subsystems.ChipletSelectors.s1,
    Subsystems.ChipletSelectors.s2, Subsystems.ChipletSelectors.s3,
    Subsystems.ChipletSelectors.s4, Subsystems.ChipletSelectors.s0Col,
    Subsystems.ChipletSelectors.s1Col, Subsystems.ChipletSelectors.s2Col,
    Subsystems.ChipletSelectors.s3Col, Subsystems.ChipletSelectors.s4Col,
    Subsystems.ChipletSelectors.chipletsOffset, toSymbolicFrame, FExpr.eval,
    Builder.whenTransition, Builder.gate, Builder.assertEq, Builder.assertZero,
    BaseConstraint.eval, BaseConstraint.expr, AirRow.boundary, AirRow.baseAt, AirRow.base,
    SymbolicFrame.colCurr, SymbolicFrame.colNext, h51, h52, h53, h54, h55]
  simp; ring_nf; left; trivial

end MidenLean.AIR.Semantics.Refinement.SymbolicToCanonical
