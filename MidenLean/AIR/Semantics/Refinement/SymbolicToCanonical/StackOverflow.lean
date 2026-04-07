import MidenLean.AIR.Semantics.Tactics
import MidenLean.AIR.Semantics.Subsystems.StackOverflow
import MidenLean.AIR.Constraints.Symbolic.StackOverflow

set_option maxHeartbeats 32000000

namespace MidenLean.AIR.Semantics.Refinement.SymbolicToCanonical

open MidenLean
open MidenLean.AIR
open MidenLean.AIR.Semantics
open MidenLean.AIR.Semantics.Tactics
open MidenLean.AIR.Semantics.Builder

@[simp] theorem felt_ofNat_sixteen_eq : (Felt.ofNat 16 : Felt) = 16 := rfl

@[simp] theorem curr_stackOverflow_clkCol_eq (r : AirRow) :
    r.curr Subsystems.StackOverflow.clkCol = r.curr 0 := rfl

@[simp] theorem curr_stackOverflow_opBit0Col_eq (r : AirRow) :
    r.curr Subsystems.StackOverflow.opBit0Col = r.curr 7 := rfl

@[simp] theorem curr_stackOverflow_opBit1Col_eq (r : AirRow) :
    r.curr Subsystems.StackOverflow.opBit1Col = r.curr 8 := rfl

@[simp] theorem curr_stackOverflow_opBit2Col_eq (r : AirRow) :
    r.curr Subsystems.StackOverflow.opBit2Col = r.curr 9 := rfl

@[simp] theorem curr_stackOverflow_opBit3Col_eq (r : AirRow) :
    r.curr Subsystems.StackOverflow.opBit3Col = r.curr 10 := rfl

@[simp] theorem curr_stackOverflow_opBit4Col_eq (r : AirRow) :
    r.curr Subsystems.StackOverflow.opBit4Col = r.curr 11 := rfl

@[simp] theorem curr_stackOverflow_opBit5Col_eq (r : AirRow) :
    r.curr Subsystems.StackOverflow.opBit5Col = r.curr 12 := rfl

@[simp] theorem curr_stackOverflow_opBit6Col_eq (r : AirRow) :
    r.curr Subsystems.StackOverflow.opBit6Col = r.curr 13 := rfl

@[simp] theorem curr_stackOverflow_s15Col_eq (r : AirRow) :
    r.curr Subsystems.StackOverflow.s15Col = r.curr 45 := rfl

@[simp] theorem next_stackOverflow_s15Col_eq (r : AirRow) :
    r.next Subsystems.StackOverflow.s15Col = r.next 45 := rfl

@[simp] theorem curr_stackOverflow_stackDepthCol_eq (r : AirRow) :
    r.curr Subsystems.StackOverflow.stackDepthCol = r.curr 46 := rfl

@[simp] theorem next_stackOverflow_stackDepthCol_eq (r : AirRow) :
    r.next Subsystems.StackOverflow.stackDepthCol = r.next 46 := rfl

@[simp] theorem curr_stackOverflow_overflowAddrCol_eq (r : AirRow) :
    r.curr Subsystems.StackOverflow.overflowAddrCol = r.curr 47 := rfl

@[simp] theorem next_stackOverflow_overflowAddrCol_eq (r : AirRow) :
    r.next Subsystems.StackOverflow.overflowAddrCol = r.next 47 := rfl

@[simp] theorem curr_stackOverflow_overflowHelperCol_eq (r : AirRow) :
    r.curr Subsystems.StackOverflow.overflowHelperCol = r.curr 48 := rfl

@[simp] theorem next_stackOverflow_overflowHelperCol_eq (r : AirRow) :
    r.next Subsystems.StackOverflow.overflowHelperCol = r.next 48 := rfl

theorem bridge_stack_overflow_0 (r : AirRow) :
    Constraints.Symbolic.StackOverflow.base[0]! (toSymbolicFrame r) =
      Subsystems.StackOverflow.stackDepthFirst.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => f.is_first_row * (f.b0 - Felt.ofNat 16)) (toSymbolicFrame r) =
    Subsystems.StackOverflow.stackDepthFirst.eval r
  have h46 : 46 < MainWidth := by decide
  simp only [Subsystems.StackOverflow.stackDepthFirst, Subsystems.StackOverflow.stackDepth,
    Subsystems.StackOverflow.stackDepthCol, toSymbolicFrame, FExpr.eval, Builder.gate,
    Builder.assertEq, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.boundary, AirRow.baseAt, AirRow.base, SymbolicFrame.b0, h46]
  have hCurr :
      r.isFirst * ((if h : True then r.curr ⟨46, h46⟩ else 0) - Felt.ofNat 16) =
        r.isFirst * (r.curr ⟨46, Subsystems.StackOverflow.stackDepthCol._proof_1⟩ - 16) := by
    simp
  exact hCurr

theorem bridge_stack_overflow_1 (r : AirRow) :
    Constraints.Symbolic.StackOverflow.base[1]! (toSymbolicFrame r) =
      Subsystems.StackOverflow.stackDepthLast.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => f.is_last_row * (f.b0 - Felt.ofNat 16)) (toSymbolicFrame r) =
    Subsystems.StackOverflow.stackDepthLast.eval r
  have h46 : 46 < MainWidth := by decide
  simp only [Subsystems.StackOverflow.stackDepthLast, Subsystems.StackOverflow.stackDepth,
    Subsystems.StackOverflow.stackDepthCol, toSymbolicFrame, FExpr.eval, Builder.gate,
    Builder.assertEq, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.boundary, AirRow.baseAt, AirRow.base, SymbolicFrame.b0, h46]
  have hCurr :
      r.isLast * ((if h : True then r.curr ⟨46, h46⟩ else 0) - Felt.ofNat 16) =
        r.isLast * (r.curr ⟨46, Subsystems.StackOverflow.stackDepthCol._proof_1⟩ - 16) := by
    simp
  exact hCurr

theorem bridge_stack_overflow_2 (r : AirRow) :
    Constraints.Symbolic.StackOverflow.base[2]! (toSymbolicFrame r) =
      Subsystems.StackOverflow.overflowAddrFirst.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => f.is_first_row * f.b1) (toSymbolicFrame r) =
    Subsystems.StackOverflow.overflowAddrFirst.eval r
  have h47 : 47 < MainWidth := by decide
  simp only [Subsystems.StackOverflow.overflowAddrFirst, Subsystems.StackOverflow.overflowAddr,
    Subsystems.StackOverflow.overflowAddrCol, toSymbolicFrame, FExpr.eval, Builder.gate,
    Builder.assertEq, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.boundary, AirRow.baseAt, AirRow.base, SymbolicFrame.b1, h47]
  have hCurr :
      r.isFirst * (if h : True then r.curr ⟨47, h47⟩ else 0) =
        r.isFirst * (r.curr ⟨47, Subsystems.StackOverflow.overflowAddrCol._proof_1⟩ - 0) := by
    simp
  exact hCurr

theorem bridge_stack_overflow_3 (r : AirRow) :
    Constraints.Symbolic.StackOverflow.base[3]! (toSymbolicFrame r) =
      Subsystems.StackOverflow.overflowAddrLast.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => f.is_last_row * f.b1) (toSymbolicFrame r) =
    Subsystems.StackOverflow.overflowAddrLast.eval r
  have h47 : 47 < MainWidth := by decide
  simp only [Subsystems.StackOverflow.overflowAddrLast, Subsystems.StackOverflow.overflowAddr,
    Subsystems.StackOverflow.overflowAddrCol, toSymbolicFrame, FExpr.eval, Builder.gate,
    Builder.assertEq, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.boundary, AirRow.baseAt, AirRow.base, SymbolicFrame.b1, h47]
  have hCurr :
      r.isLast * (if h : True then r.curr ⟨47, h47⟩ else 0) =
        r.isLast * (r.curr ⟨47, Subsystems.StackOverflow.overflowAddrCol._proof_1⟩ - 0) := by
    simp
  exact hCurr

theorem bridge_stack_overflow_4 (r : AirRow) :
    Constraints.Symbolic.StackOverflow.base[4]! (toSymbolicFrame r) =
      Subsystems.StackOverflow.stackDepthTransition.eval r := by
  /-
  The extracted symbolic depth-transition polynomial still uses the full Rust
  aggregate masks over the decoder helper columns (`col 28`, `col 29`, `h 3`,
  `h 4`, `h 5`). The current canonical `StackOverflow.stackDepthTransition`
  instead factors through the temporary proxies
  `Subsystems.StackOverflow.leftShift = prefix010` and
  `Subsystems.StackOverflow.rightShift = prefix011`, as documented in
  `MidenLean/AIR/Semantics/Subsystems/StackOverflow.lean`.
  Until the exact op-flag bridge is imported into the canonical model, this
  is not a direct symbolic-to-canonical identity.
  -/
  sorry

theorem bridge_stack_overflow_5 (r : AirRow) :
    Constraints.Symbolic.StackOverflow.base[5]! (toSymbolicFrame r) =
      Subsystems.StackOverflow.overflowFlag.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => (1 - ((f.b0 - Felt.ofNat 16) * f.h0_overflow)) * (f.b0 - Felt.ofNat 16))
      (toSymbolicFrame r) = Subsystems.StackOverflow.overflowFlag.eval r
  have h46 : 46 < MainWidth := by decide
  have h48 : 48 < MainWidth := by decide
  simp only [Subsystems.StackOverflow.overflowFlag, Subsystems.StackOverflow.overflow,
    Subsystems.StackOverflow.stackDepth, Subsystems.StackOverflow.stackDepthCol,
    Subsystems.StackOverflow.overflowHelper, Subsystems.StackOverflow.overflowHelperCol,
    toSymbolicFrame, FExpr.eval, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.baseAt, AirRow.base, SymbolicFrame.b0, SymbolicFrame.h0_overflow, h46, h48]
  have hDepth :
      (if h : True then r.curr ⟨46, h46⟩ else 0) =
        r.curr ⟨46, Subsystems.StackOverflow.stackDepthCol._proof_1⟩ := by
    simp
  have hHelper :
      (if h : True then r.curr ⟨48, h48⟩ else 0) =
        r.curr ⟨48, Subsystems.StackOverflow.overflowHelperCol._proof_1⟩ := by
    simp
  rw [hDepth, hHelper]
  simp [felt_ofNat_sixteen_eq]

theorem bridge_stack_overflow_6 (r : AirRow) :
    Constraints.Symbolic.StackOverflow.base[6]! (toSymbolicFrame r) =
      Subsystems.StackOverflow.overflowAddrTransition.eval r := by
  /-
  Symbolic constraint `base[6]` is gated by the extracted full `right_shift`
  aggregate. The current canonical `overflowAddrTransition` only uses the
  proxy selector `Subsystems.StackOverflow.rightShift = prefix011`, so the two
  polynomials do not presently match by definitional unfolding.
  -/
  sorry

theorem bridge_stack_overflow_7 (r : AirRow) :
    Constraints.Symbolic.StackOverflow.base[7]! (toSymbolicFrame r) =
      Subsystems.StackOverflow.zeroInsertTransition.eval r := by
  /-
  Symbolic constraint `base[7]` is gated by the extracted full `left_shift`
  aggregate. The current canonical `zeroInsertTransition` only uses the proxy
  selector `Subsystems.StackOverflow.leftShift = prefix010`, so this bridge is
  blocked until the canonical model carries the exact shift aggregate.
  -/
  sorry

end MidenLean.AIR.Semantics.Refinement.SymbolicToCanonical
