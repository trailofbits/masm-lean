import MidenLean.AIR.Semantics.Tactics
import MidenLean.AIR.Semantics.Subsystems.Range
import MidenLean.AIR.Constraints.Symbolic.Range

set_option maxHeartbeats 16000000

namespace MidenLean.AIR.Semantics.Refinement.SymbolicToCanonical

open MidenLean
open MidenLean.AIR
open MidenLean.AIR.Semantics
open MidenLean.AIR.Semantics.Tactics
open MidenLean.AIR.Semantics.Builder

theorem bridge_range_0 (r : AirRow) :
    Constraints.Symbolic.Range.base[0]! (toSymbolicFrame r) =
      Subsystems.Range.vFirst.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => f.is_first_row * f.colCurr 50) (toSymbolicFrame r) =
    Subsystems.Range.vFirst.eval r
  have h50 : 50 < MainWidth := by decide
  simp only [Subsystems.Range.vFirst, Subsystems.Range.rangeV, Subsystems.Range.rangeVCol,
    toSymbolicFrame, FExpr.eval, Builder.gate, Builder.assertEq, Builder.assertZero,
    BaseConstraint.eval, BaseConstraint.expr, AirRow.boundary, AirRow.baseAt, AirRow.base,
    SymbolicFrame.colCurr, h50]
  have hCurr :
      (r.isFirst * if h : True then r.curr ⟨50, h50⟩ else 0) =
        r.isFirst * r.curr ⟨50, Subsystems.Range.rangeVCol._proof_1⟩ := by
    simp
  rw [hCurr]
  ring

theorem bridge_range_1 (r : AirRow) :
    Constraints.Symbolic.Range.base[1]! (toSymbolicFrame r) =
      Subsystems.Range.vLast.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => f.is_last_row * (f.colCurr 50 - 65535)) (toSymbolicFrame r) =
    Subsystems.Range.vLast.eval r
  have h50 : 50 < MainWidth := by decide
  simp only [Subsystems.Range.vLast, Subsystems.Range.rangeV, Subsystems.Range.rangeVCol,
    toSymbolicFrame, FExpr.eval, Builder.gate, Builder.assertEq, Builder.assertZero,
    BaseConstraint.eval, BaseConstraint.expr, AirRow.boundary, AirRow.baseAt, AirRow.base,
    SymbolicFrame.colCurr, h50]
  have hCurr :
      (r.isLast * ((if h : True then r.curr ⟨50, h50⟩ else 0) - 65535)) =
        r.isLast * (r.curr ⟨50, Subsystems.Range.rangeVCol._proof_1⟩ - 65535) := by
    simp
  rw [hCurr]

theorem bridge_range_2 (r : AirRow) :
    Constraints.Symbolic.Range.base[2]! (toSymbolicFrame r) =
      Subsystems.Range.vTransition.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => f.is_transition * (((((((((f.colNext 50 - f.colCurr 50) *
      ((f.colNext 50 - f.colCurr 50) - 1)) *
      ((f.colNext 50 - f.colCurr 50) - 3)) *
      ((f.colNext 50 - f.colCurr 50) - 9)) *
      ((f.colNext 50 - f.colCurr 50) - 27)) *
      ((f.colNext 50 - f.colCurr 50) - 81)) *
      ((f.colNext 50 - f.colCurr 50) - 243)) *
      ((f.colNext 50 - f.colCurr 50) - 729)) *
      ((f.colNext 50 - f.colCurr 50) - 2187))) (toSymbolicFrame r) =
    Subsystems.Range.vTransition.eval r
  have h50 : 50 < MainWidth := by decide
  simp only [Subsystems.Range.vTransition, Subsystems.Range.changeV, Subsystems.Range.rangeV,
    Subsystems.Range.rangeVNext, Subsystems.Range.rangeVCol, toSymbolicFrame, FExpr.eval,
    Builder.whenTransition, Builder.gate, Builder.assertZero, BaseConstraint.eval,
    BaseConstraint.expr, AirRow.boundary, AirRow.baseAt, AirRow.base,
    SymbolicFrame.colCurr, SymbolicFrame.colNext, h50]
  have hCurr :
      (if h : True then r.curr ⟨50, h50⟩ else 0) =
        r.curr ⟨50, Subsystems.Range.rangeVCol._proof_1⟩ := by
    simp
  have hNext :
      (if h : True then r.next ⟨50, h50⟩ else 0) =
        r.next ⟨50, Subsystems.Range.rangeVCol._proof_1⟩ := by
    simp
  rw [hCurr, hNext]
  ac_rfl

end MidenLean.AIR.Semantics.Refinement.SymbolicToCanonical
