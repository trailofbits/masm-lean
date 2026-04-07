import MidenLean.AIR.Semantics.Tactics
import MidenLean.AIR.Semantics.Subsystems.StackOps
import MidenLean.AIR.Constraints.Symbolic.StackOps

set_option maxHeartbeats 32000000

namespace MidenLean.AIR.Semantics.Refinement.SymbolicToCanonical

open MidenLean
open MidenLean.AIR
open MidenLean.AIR.Semantics
open MidenLean.AIR.Semantics.Tactics
open MidenLean.AIR.Semantics.Builder

private theorem h0 : 0 < MainWidth := by decide
private theorem h7 : 7 < MainWidth := by decide
private theorem h8 : 8 < MainWidth := by decide
private theorem h9 : 9 < MainWidth := by decide
private theorem h10 : 10 < MainWidth := by decide
private theorem h11 : 11 < MainWidth := by decide
private theorem h12 : 12 < MainWidth := by decide
private theorem h13 : 13 < MainWidth := by decide
private theorem h30 : 30 < MainWidth := by decide
private theorem h31 : 31 < MainWidth := by decide
private theorem h32 : 32 < MainWidth := by decide
private theorem h33 : 33 < MainWidth := by decide
private theorem h34 : 34 < MainWidth := by decide
private theorem h35 : 35 < MainWidth := by decide
private theorem h36 : 36 < MainWidth := by decide
private theorem h37 : 37 < MainWidth := by decide
private theorem h38 : 38 < MainWidth := by decide
private theorem h39 : 39 < MainWidth := by decide
private theorem h40 : 40 < MainWidth := by decide
private theorem h41 : 41 < MainWidth := by decide
private theorem h42 : 42 < MainWidth := by decide
private theorem h43 : 43 < MainWidth := by decide
private theorem h44 : 44 < MainWidth := by decide
private theorem h45 : 45 < MainWidth := by decide

private theorem curr_main_col_eq (r : AirRow) {i : Nat}
    (hi : i < MainWidth) {hj : i < MainWidth} :
    (if _h : True then r.curr ⟨i, hi⟩ else 0) = r.curr ⟨i, hj⟩ := by
  simp

private theorem next_main_col_eq (r : AirRow) {i : Nat}
    (hi : i < MainWidth) {hj : i < MainWidth} :
    (if _h : True then r.next ⟨i, hi⟩ else 0) = r.next ⟨i, hj⟩ := by
  simp

private theorem curr_stack_col_eq (r : AirRow) {k : Nat}
    (hk : 30 + k < MainWidth) {hj : 30 + k < MainWidth} :
    (if _h : 30 + k < MainWidth then r.curr ⟨30 + k, _h⟩ else 0) =
      r.curr ⟨30 + k, hj⟩ := by
  simp [hk]

private theorem next_stack_col_eq (r : AirRow) {k : Nat}
    (hk : 30 + k < MainWidth) {hj : 30 + k < MainWidth} :
    (if _h : 30 + k < MainWidth then r.next ⟨30 + k, _h⟩ else 0) =
      r.next ⟨30 + k, hj⟩ := by
  simp [hk]

theorem bridge_stack_ops_0 (r : AirRow) :
    Constraints.Symbolic.StackOps.base[0]! (toSymbolicFrame r) =
      Subsystems.StackOps.pad.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => f.is_transition * ((((((f.colCurr 12 * f.colCurr 11) *
      ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * (1 - f.colCurr 9)) *
      (1 - f.colCurr 8)) * (1 - f.colCurr 7)) * f.s' 0)) (toSymbolicFrame r) =
    Subsystems.StackOps.pad.eval r
  have h7 : 7 < MainWidth := by decide
  have h8 : 8 < MainWidth := by decide
  have h9 : 9 < MainWidth := by decide
  have h10 : 10 < MainWidth := by decide
  have h11 : 11 < MainWidth := by decide
  have h12 : 12 < MainWidth := by decide
  have h13 : 13 < MainWidth := by decide
  have h30 : 30 < MainWidth := by decide
  simp only [Subsystems.StackOps.pad, Subsystems.StackOps.isPad,
    Subsystems.StackOps.notOpBit0, Subsystems.StackOps.notOpBit1,
    Subsystems.StackOps.notOpBit2, Subsystems.StackOps.notOpBit3,
    Subsystems.StackOps.notOpBit6, Subsystems.StackOps.opBit0,
    Subsystems.StackOps.opBit1, Subsystems.StackOps.opBit2,
    Subsystems.StackOps.opBit3, Subsystems.StackOps.opBit4,
    Subsystems.StackOps.opBit5, Subsystems.StackOps.opBit6,
    Subsystems.StackOps.opBit0Col, Subsystems.StackOps.opBit1Col,
    Subsystems.StackOps.opBit2Col, Subsystems.StackOps.opBit3Col,
    Subsystems.StackOps.opBit4Col, Subsystems.StackOps.opBit5Col,
    Subsystems.StackOps.opBit6Col,
    Subsystems.StackOps.s0Next, Subsystems.StackOps.s0Col,
    toSymbolicFrame, FExpr.eval, Builder.whenTransition, Builder.gate,
    Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr, AirRow.boundary,
    AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, SymbolicFrame.s',
    h7, h8, h9, h10, h11, h12, h13, h30]
  have hOp0 :
      (if h : True then r.curr ⟨7, h7⟩ else 0) =
        r.curr ⟨7, Subsystems.StackOps.opBit0Col._proof_1⟩ := by
    simp
  have hOp1 :
      (if h : True then r.curr ⟨8, h8⟩ else 0) =
        r.curr ⟨8, Subsystems.StackOps.opBit1Col._proof_1⟩ := by
    simp
  have hOp2 :
      (if h : True then r.curr ⟨9, h9⟩ else 0) =
        r.curr ⟨9, Subsystems.StackOps.opBit2Col._proof_1⟩ := by
    simp
  have hOp3 :
      (if h : True then r.curr ⟨10, h10⟩ else 0) =
        r.curr ⟨10, Subsystems.StackOps.opBit3Col._proof_1⟩ := by
    simp
  have hOp4 :
      (if h : True then r.curr ⟨11, h11⟩ else 0) =
        r.curr ⟨11, Subsystems.StackOps.opBit4Col._proof_1⟩ := by
    simp
  have hOp5 :
      (if h : True then r.curr ⟨12, h12⟩ else 0) =
        r.curr ⟨12, Subsystems.StackOps.opBit5Col._proof_1⟩ := by
    simp
  have hOp6 :
      (if h : True then r.curr ⟨13, h13⟩ else 0) =
        r.curr ⟨13, Subsystems.StackOps.opBit6Col._proof_1⟩ := by
    simp
  have hNext :
      (if h : True then r.next ⟨30, h30⟩ else 0) =
        r.next ⟨30, Subsystems.StackOps.s0Col._proof_1⟩ := by
    simp
  rw [hOp0, hOp1, hOp2, hOp3, hOp4, hOp5, hOp6, hNext]
  ring

theorem bridge_stack_ops_1 (r : AirRow) :
    Constraints.Symbolic.StackOps.base[1]! (toSymbolicFrame r) =
      Subsystems.StackOps.dup0.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => f.is_transition * ((((((f.colCurr 12 * f.colCurr 11) *
      ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * (1 - f.colCurr 9)) *
      (1 - f.colCurr 8)) * f.colCurr 7) * (f.s' 0 - f.s 0))) (toSymbolicFrame r) =
    Subsystems.StackOps.dup0.eval r
  simp only [Subsystems.StackOps.dup0, Subsystems.StackOps.isDup0,
    Subsystems.StackOps.notOpBit1, Subsystems.StackOps.notOpBit2,
    Subsystems.StackOps.notOpBit3, Subsystems.StackOps.notOpBit6,
    Subsystems.StackOps.opBit0, Subsystems.StackOps.opBit1,
    Subsystems.StackOps.opBit2, Subsystems.StackOps.opBit3,
    Subsystems.StackOps.opBit4, Subsystems.StackOps.opBit5,
    Subsystems.StackOps.opBit6, Subsystems.StackOps.opBit0Col,
    Subsystems.StackOps.opBit1Col, Subsystems.StackOps.opBit2Col,
    Subsystems.StackOps.opBit3Col, Subsystems.StackOps.opBit4Col,
    Subsystems.StackOps.opBit5Col, Subsystems.StackOps.opBit6Col,
    Subsystems.StackOps.s0Next, Subsystems.StackOps.s0, Subsystems.StackOps.s0Col,
    toSymbolicFrame, FExpr.eval, Builder.whenTransition, Builder.gate,
    Builder.assertEq, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.boundary, AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr,
    SymbolicFrame.s, SymbolicFrame.s', h7, h8, h9, h10, h11, h12, h13]
  rw [curr_main_col_eq (r := r) (i := 7) h7
        (hj := Subsystems.StackOps.opBit0Col._proof_1),
      curr_main_col_eq (r := r) (i := 8) h8
        (hj := Subsystems.StackOps.opBit1Col._proof_1),
      curr_main_col_eq (r := r) (i := 9) h9
        (hj := Subsystems.StackOps.opBit2Col._proof_1),
      curr_main_col_eq (r := r) (i := 10) h10
        (hj := Subsystems.StackOps.opBit3Col._proof_1),
      curr_main_col_eq (r := r) (i := 11) h11
        (hj := Subsystems.StackOps.opBit4Col._proof_1),
      curr_main_col_eq (r := r) (i := 12) h12
        (hj := Subsystems.StackOps.opBit5Col._proof_1),
      curr_main_col_eq (r := r) (i := 13) h13
        (hj := Subsystems.StackOps.opBit6Col._proof_1),
      curr_stack_col_eq (r := r) (k := 0) h30
        (hj := by simpa using Subsystems.StackOps.s0Col._proof_1),
      next_stack_col_eq (r := r) (k := 0) h30
        (hj := by simpa using Subsystems.StackOps.s0Col._proof_1)]
  ring

theorem bridge_stack_ops_2 (r : AirRow) :
    Constraints.Symbolic.StackOps.base[2]! (toSymbolicFrame r) =
      Subsystems.StackOps.dup1.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => f.is_transition * ((((((f.colCurr 12 * f.colCurr 11) *
      ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * (1 - f.colCurr 9)) *
      f.colCurr 8) * (1 - f.colCurr 7)) * (f.s' 0 - f.s 1))) (toSymbolicFrame r) =
    Subsystems.StackOps.dup1.eval r
  simp only [Subsystems.StackOps.dup1, Subsystems.StackOps.isDup1,
    Subsystems.StackOps.notOpBit0, Subsystems.StackOps.notOpBit2,
    Subsystems.StackOps.notOpBit3, Subsystems.StackOps.notOpBit6,
    Subsystems.StackOps.opBit0, Subsystems.StackOps.opBit1,
    Subsystems.StackOps.opBit2, Subsystems.StackOps.opBit3,
    Subsystems.StackOps.opBit4, Subsystems.StackOps.opBit5,
    Subsystems.StackOps.opBit6, Subsystems.StackOps.opBit0Col,
    Subsystems.StackOps.opBit1Col, Subsystems.StackOps.opBit2Col,
    Subsystems.StackOps.opBit3Col, Subsystems.StackOps.opBit4Col,
    Subsystems.StackOps.opBit5Col, Subsystems.StackOps.opBit6Col,
    Subsystems.StackOps.s0Next, Subsystems.StackOps.s1,
    Subsystems.StackOps.s0Col, Subsystems.StackOps.s1Col,
    toSymbolicFrame, FExpr.eval, Builder.whenTransition, Builder.gate,
    Builder.assertEq, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.boundary, AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr,
    SymbolicFrame.s, SymbolicFrame.s', h7, h8, h9, h10, h11, h12, h13]
  rw [curr_main_col_eq (r := r) (i := 7) h7
        (hj := Subsystems.StackOps.opBit0Col._proof_1),
      curr_main_col_eq (r := r) (i := 8) h8
        (hj := Subsystems.StackOps.opBit1Col._proof_1),
      curr_main_col_eq (r := r) (i := 9) h9
        (hj := Subsystems.StackOps.opBit2Col._proof_1),
      curr_main_col_eq (r := r) (i := 10) h10
        (hj := Subsystems.StackOps.opBit3Col._proof_1),
      curr_main_col_eq (r := r) (i := 11) h11
        (hj := Subsystems.StackOps.opBit4Col._proof_1),
      curr_main_col_eq (r := r) (i := 12) h12
        (hj := Subsystems.StackOps.opBit5Col._proof_1),
      curr_main_col_eq (r := r) (i := 13) h13
        (hj := Subsystems.StackOps.opBit6Col._proof_1),
      curr_stack_col_eq (r := r) (k := 1) h31
        (hj := by simpa using Subsystems.StackOps.s1Col._proof_1),
      next_stack_col_eq (r := r) (k := 0) h30
        (hj := by simpa using Subsystems.StackOps.s0Col._proof_1)]
  ring

theorem bridge_stack_ops_3 (r : AirRow) :
    Constraints.Symbolic.StackOps.base[3]! (toSymbolicFrame r) =
      Subsystems.StackOps.dup2.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => f.is_transition * ((((((f.colCurr 12 * f.colCurr 11) *
      ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * (1 - f.colCurr 9)) *
      f.colCurr 8) * f.colCurr 7) * (f.s' 0 - f.s 2))) (toSymbolicFrame r) =
    Subsystems.StackOps.dup2.eval r
  simp only [Subsystems.StackOps.dup2, Subsystems.StackOps.isDup2,
    Subsystems.StackOps.notOpBit2, Subsystems.StackOps.notOpBit3,
    Subsystems.StackOps.notOpBit6, Subsystems.StackOps.opBit0,
    Subsystems.StackOps.opBit1, Subsystems.StackOps.opBit2,
    Subsystems.StackOps.opBit3, Subsystems.StackOps.opBit4,
    Subsystems.StackOps.opBit5, Subsystems.StackOps.opBit6,
    Subsystems.StackOps.opBit0Col, Subsystems.StackOps.opBit1Col,
    Subsystems.StackOps.opBit2Col, Subsystems.StackOps.opBit3Col,
    Subsystems.StackOps.opBit4Col, Subsystems.StackOps.opBit5Col,
    Subsystems.StackOps.opBit6Col, Subsystems.StackOps.s0Next,
    Subsystems.StackOps.s2, Subsystems.StackOps.s0Col, Subsystems.StackOps.s2Col,
    toSymbolicFrame, FExpr.eval, Builder.whenTransition, Builder.gate,
    Builder.assertEq, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.boundary, AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr,
    SymbolicFrame.s, SymbolicFrame.s', h7, h8, h9, h10, h11, h12, h13]
  rw [curr_main_col_eq (r := r) (i := 7) h7
        (hj := Subsystems.StackOps.opBit0Col._proof_1),
      curr_main_col_eq (r := r) (i := 8) h8
        (hj := Subsystems.StackOps.opBit1Col._proof_1),
      curr_main_col_eq (r := r) (i := 9) h9
        (hj := Subsystems.StackOps.opBit2Col._proof_1),
      curr_main_col_eq (r := r) (i := 10) h10
        (hj := Subsystems.StackOps.opBit3Col._proof_1),
      curr_main_col_eq (r := r) (i := 11) h11
        (hj := Subsystems.StackOps.opBit4Col._proof_1),
      curr_main_col_eq (r := r) (i := 12) h12
        (hj := Subsystems.StackOps.opBit5Col._proof_1),
      curr_main_col_eq (r := r) (i := 13) h13
        (hj := Subsystems.StackOps.opBit6Col._proof_1),
      curr_stack_col_eq (r := r) (k := 2) h32
        (hj := by simpa using Subsystems.StackOps.s2Col._proof_1),
      next_stack_col_eq (r := r) (k := 0) h30
        (hj := by simpa using Subsystems.StackOps.s0Col._proof_1)]
  ring

theorem bridge_stack_ops_4 (r : AirRow) :
    Constraints.Symbolic.StackOps.base[4]! (toSymbolicFrame r) =
      Subsystems.StackOps.dup3.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => f.is_transition * ((((((f.colCurr 12 * f.colCurr 11) *
      ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * f.colCurr 9) *
      (1 - f.colCurr 8)) * (1 - f.colCurr 7)) * (f.s' 0 - f.s 3)))
      (toSymbolicFrame r) =
    Subsystems.StackOps.dup3.eval r
  simp only [Subsystems.StackOps.dup3, Subsystems.StackOps.isDup3,
    Subsystems.StackOps.notOpBit0, Subsystems.StackOps.notOpBit1,
    Subsystems.StackOps.notOpBit3, Subsystems.StackOps.notOpBit6,
    Subsystems.StackOps.opBit0, Subsystems.StackOps.opBit1,
    Subsystems.StackOps.opBit2, Subsystems.StackOps.opBit3,
    Subsystems.StackOps.opBit4, Subsystems.StackOps.opBit5,
    Subsystems.StackOps.opBit6, Subsystems.StackOps.opBit0Col,
    Subsystems.StackOps.opBit1Col, Subsystems.StackOps.opBit2Col,
    Subsystems.StackOps.opBit3Col, Subsystems.StackOps.opBit4Col,
    Subsystems.StackOps.opBit5Col, Subsystems.StackOps.opBit6Col,
    Subsystems.StackOps.s0Next, Subsystems.StackOps.s3,
    Subsystems.StackOps.s0Col, Subsystems.StackOps.s3Col,
    toSymbolicFrame, FExpr.eval, Builder.whenTransition, Builder.gate,
    Builder.assertEq, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.boundary, AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr,
    SymbolicFrame.s, SymbolicFrame.s', h7, h8, h9, h10, h11, h12, h13]
  rw [curr_main_col_eq (r := r) (i := 7) h7
        (hj := Subsystems.StackOps.opBit0Col._proof_1),
      curr_main_col_eq (r := r) (i := 8) h8
        (hj := Subsystems.StackOps.opBit1Col._proof_1),
      curr_main_col_eq (r := r) (i := 9) h9
        (hj := Subsystems.StackOps.opBit2Col._proof_1),
      curr_main_col_eq (r := r) (i := 10) h10
        (hj := Subsystems.StackOps.opBit3Col._proof_1),
      curr_main_col_eq (r := r) (i := 11) h11
        (hj := Subsystems.StackOps.opBit4Col._proof_1),
      curr_main_col_eq (r := r) (i := 12) h12
        (hj := Subsystems.StackOps.opBit5Col._proof_1),
      curr_main_col_eq (r := r) (i := 13) h13
        (hj := Subsystems.StackOps.opBit6Col._proof_1),
      curr_stack_col_eq (r := r) (k := 3) h33
        (hj := by simpa using Subsystems.StackOps.s3Col._proof_1),
      next_stack_col_eq (r := r) (k := 0) h30
        (hj := by simpa using Subsystems.StackOps.s0Col._proof_1)]
  ring

theorem bridge_stack_ops_5 (r : AirRow) :
    Constraints.Symbolic.StackOps.base[5]! (toSymbolicFrame r) =
      Subsystems.StackOps.dup4.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => f.is_transition * ((((((f.colCurr 12 * f.colCurr 11) *
      ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * f.colCurr 9) *
      (1 - f.colCurr 8)) * f.colCurr 7) * (f.s' 0 - f.s 4)))
      (toSymbolicFrame r) =
    Subsystems.StackOps.dup4.eval r
  simp only [Subsystems.StackOps.dup4, Subsystems.StackOps.isDup4,
    Subsystems.StackOps.notOpBit1, Subsystems.StackOps.notOpBit3,
    Subsystems.StackOps.notOpBit6, Subsystems.StackOps.opBit0,
    Subsystems.StackOps.opBit1, Subsystems.StackOps.opBit2,
    Subsystems.StackOps.opBit3, Subsystems.StackOps.opBit4,
    Subsystems.StackOps.opBit5, Subsystems.StackOps.opBit6,
    Subsystems.StackOps.opBit0Col, Subsystems.StackOps.opBit1Col,
    Subsystems.StackOps.opBit2Col, Subsystems.StackOps.opBit3Col,
    Subsystems.StackOps.opBit4Col, Subsystems.StackOps.opBit5Col,
    Subsystems.StackOps.opBit6Col, Subsystems.StackOps.s0Next,
    Subsystems.StackOps.s4, Subsystems.StackOps.s0Col, Subsystems.StackOps.s4Col,
    toSymbolicFrame, FExpr.eval, Builder.whenTransition, Builder.gate,
    Builder.assertEq, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.boundary, AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr,
    SymbolicFrame.s, SymbolicFrame.s', h7, h8, h9, h10, h11, h12, h13]
  rw [curr_main_col_eq (r := r) (i := 7) h7
        (hj := Subsystems.StackOps.opBit0Col._proof_1),
      curr_main_col_eq (r := r) (i := 8) h8
        (hj := Subsystems.StackOps.opBit1Col._proof_1),
      curr_main_col_eq (r := r) (i := 9) h9
        (hj := Subsystems.StackOps.opBit2Col._proof_1),
      curr_main_col_eq (r := r) (i := 10) h10
        (hj := Subsystems.StackOps.opBit3Col._proof_1),
      curr_main_col_eq (r := r) (i := 11) h11
        (hj := Subsystems.StackOps.opBit4Col._proof_1),
      curr_main_col_eq (r := r) (i := 12) h12
        (hj := Subsystems.StackOps.opBit5Col._proof_1),
      curr_main_col_eq (r := r) (i := 13) h13
        (hj := Subsystems.StackOps.opBit6Col._proof_1),
      curr_stack_col_eq (r := r) (k := 4) h34
        (hj := by simpa using Subsystems.StackOps.s4Col._proof_1),
      next_stack_col_eq (r := r) (k := 0) h30
        (hj := by simpa using Subsystems.StackOps.s0Col._proof_1)]
  ring

theorem bridge_stack_ops_6 (r : AirRow) :
    Constraints.Symbolic.StackOps.base[6]! (toSymbolicFrame r) =
      Subsystems.StackOps.dup5.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => f.is_transition * ((((((f.colCurr 12 * f.colCurr 11) *
      ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * f.colCurr 9) *
      f.colCurr 8) * (1 - f.colCurr 7)) * (f.s' 0 - f.s 5)))
      (toSymbolicFrame r) =
    Subsystems.StackOps.dup5.eval r
  simp only [Subsystems.StackOps.dup5, Subsystems.StackOps.isDup5,
    Subsystems.StackOps.notOpBit0, Subsystems.StackOps.notOpBit3,
    Subsystems.StackOps.notOpBit6, Subsystems.StackOps.opBit0,
    Subsystems.StackOps.opBit1, Subsystems.StackOps.opBit2,
    Subsystems.StackOps.opBit3, Subsystems.StackOps.opBit4,
    Subsystems.StackOps.opBit5, Subsystems.StackOps.opBit6,
    Subsystems.StackOps.opBit0Col, Subsystems.StackOps.opBit1Col,
    Subsystems.StackOps.opBit2Col, Subsystems.StackOps.opBit3Col,
    Subsystems.StackOps.opBit4Col, Subsystems.StackOps.opBit5Col,
    Subsystems.StackOps.opBit6Col, Subsystems.StackOps.s0Next,
    Subsystems.StackOps.s5, Subsystems.StackOps.s0Col, Subsystems.StackOps.s5Col,
    toSymbolicFrame, FExpr.eval, Builder.whenTransition, Builder.gate,
    Builder.assertEq, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.boundary, AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr,
    SymbolicFrame.s, SymbolicFrame.s', h7, h8, h9, h10, h11, h12, h13]
  rw [curr_main_col_eq (r := r) (i := 7) h7
        (hj := Subsystems.StackOps.opBit0Col._proof_1),
      curr_main_col_eq (r := r) (i := 8) h8
        (hj := Subsystems.StackOps.opBit1Col._proof_1),
      curr_main_col_eq (r := r) (i := 9) h9
        (hj := Subsystems.StackOps.opBit2Col._proof_1),
      curr_main_col_eq (r := r) (i := 10) h10
        (hj := Subsystems.StackOps.opBit3Col._proof_1),
      curr_main_col_eq (r := r) (i := 11) h11
        (hj := Subsystems.StackOps.opBit4Col._proof_1),
      curr_main_col_eq (r := r) (i := 12) h12
        (hj := Subsystems.StackOps.opBit5Col._proof_1),
      curr_main_col_eq (r := r) (i := 13) h13
        (hj := Subsystems.StackOps.opBit6Col._proof_1),
      curr_stack_col_eq (r := r) (k := 5) h35
        (hj := by simpa using Subsystems.StackOps.s5Col._proof_1),
      next_stack_col_eq (r := r) (k := 0) h30
        (hj := by simpa using Subsystems.StackOps.s0Col._proof_1)]
  ring

theorem bridge_stack_ops_7 (r : AirRow) :
    Constraints.Symbolic.StackOps.base[7]! (toSymbolicFrame r) =
      Subsystems.StackOps.dup6.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => f.is_transition * ((((((f.colCurr 12 * f.colCurr 11) *
      ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * f.colCurr 9) *
      f.colCurr 8) * f.colCurr 7) * (f.s' 0 - f.s 6))) (toSymbolicFrame r) =
    Subsystems.StackOps.dup6.eval r
  simp only [Subsystems.StackOps.dup6, Subsystems.StackOps.isDup6,
    Subsystems.StackOps.notOpBit3, Subsystems.StackOps.notOpBit6,
    Subsystems.StackOps.opBit0, Subsystems.StackOps.opBit1,
    Subsystems.StackOps.opBit2, Subsystems.StackOps.opBit3,
    Subsystems.StackOps.opBit4, Subsystems.StackOps.opBit5,
    Subsystems.StackOps.opBit6, Subsystems.StackOps.opBit0Col,
    Subsystems.StackOps.opBit1Col, Subsystems.StackOps.opBit2Col,
    Subsystems.StackOps.opBit3Col, Subsystems.StackOps.opBit4Col,
    Subsystems.StackOps.opBit5Col, Subsystems.StackOps.opBit6Col,
    Subsystems.StackOps.s0Next, Subsystems.StackOps.s6,
    Subsystems.StackOps.s0Col, Subsystems.StackOps.s6Col,
    toSymbolicFrame, FExpr.eval, Builder.whenTransition, Builder.gate,
    Builder.assertEq, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.boundary, AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr,
    SymbolicFrame.s, SymbolicFrame.s', h7, h8, h9, h10, h11, h12, h13]
  rw [curr_main_col_eq (r := r) (i := 7) h7
        (hj := Subsystems.StackOps.opBit0Col._proof_1),
      curr_main_col_eq (r := r) (i := 8) h8
        (hj := Subsystems.StackOps.opBit1Col._proof_1),
      curr_main_col_eq (r := r) (i := 9) h9
        (hj := Subsystems.StackOps.opBit2Col._proof_1),
      curr_main_col_eq (r := r) (i := 10) h10
        (hj := Subsystems.StackOps.opBit3Col._proof_1),
      curr_main_col_eq (r := r) (i := 11) h11
        (hj := Subsystems.StackOps.opBit4Col._proof_1),
      curr_main_col_eq (r := r) (i := 12) h12
        (hj := Subsystems.StackOps.opBit5Col._proof_1),
      curr_main_col_eq (r := r) (i := 13) h13
        (hj := Subsystems.StackOps.opBit6Col._proof_1),
      curr_stack_col_eq (r := r) (k := 6) h36
        (hj := by simpa using Subsystems.StackOps.s6Col._proof_1),
      next_stack_col_eq (r := r) (k := 0) h30
        (hj := by simpa using Subsystems.StackOps.s0Col._proof_1)]
  ring

theorem bridge_stack_ops_8 (r : AirRow) :
    Constraints.Symbolic.StackOps.base[8]! (toSymbolicFrame r) =
      Subsystems.StackOps.dup7.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => f.is_transition * ((((((f.colCurr 12 * f.colCurr 11) *
      ((1 - f.colCurr 13) * f.colCurr 10)) * (1 - f.colCurr 9)) *
      (1 - f.colCurr 8)) * (1 - f.colCurr 7)) * (f.s' 0 - f.s 7)))
      (toSymbolicFrame r) =
    Subsystems.StackOps.dup7.eval r
  simp only [Subsystems.StackOps.dup7, Subsystems.StackOps.isDup7,
    Subsystems.StackOps.notOpBit0, Subsystems.StackOps.notOpBit1,
    Subsystems.StackOps.notOpBit2, Subsystems.StackOps.notOpBit6,
    Subsystems.StackOps.opBit0, Subsystems.StackOps.opBit1,
    Subsystems.StackOps.opBit2, Subsystems.StackOps.opBit3,
    Subsystems.StackOps.opBit4, Subsystems.StackOps.opBit5,
    Subsystems.StackOps.opBit6, Subsystems.StackOps.opBit0Col,
    Subsystems.StackOps.opBit1Col, Subsystems.StackOps.opBit2Col,
    Subsystems.StackOps.opBit3Col, Subsystems.StackOps.opBit4Col,
    Subsystems.StackOps.opBit5Col, Subsystems.StackOps.opBit6Col,
    Subsystems.StackOps.s0Next, Subsystems.StackOps.s7,
    Subsystems.StackOps.s0Col, Subsystems.StackOps.s7Col,
    toSymbolicFrame, FExpr.eval, Builder.whenTransition, Builder.gate,
    Builder.assertEq, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.boundary, AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr,
    SymbolicFrame.s, SymbolicFrame.s', h7, h8, h9, h10, h11, h12, h13]
  rw [curr_main_col_eq (r := r) (i := 7) h7
        (hj := Subsystems.StackOps.opBit0Col._proof_1),
      curr_main_col_eq (r := r) (i := 8) h8
        (hj := Subsystems.StackOps.opBit1Col._proof_1),
      curr_main_col_eq (r := r) (i := 9) h9
        (hj := Subsystems.StackOps.opBit2Col._proof_1),
      curr_main_col_eq (r := r) (i := 10) h10
        (hj := Subsystems.StackOps.opBit3Col._proof_1),
      curr_main_col_eq (r := r) (i := 11) h11
        (hj := Subsystems.StackOps.opBit4Col._proof_1),
      curr_main_col_eq (r := r) (i := 12) h12
        (hj := Subsystems.StackOps.opBit5Col._proof_1),
      curr_main_col_eq (r := r) (i := 13) h13
        (hj := Subsystems.StackOps.opBit6Col._proof_1),
      curr_stack_col_eq (r := r) (k := 7) h37
        (hj := by simpa using Subsystems.StackOps.s7Col._proof_1),
      next_stack_col_eq (r := r) (k := 0) h30
        (hj := by simpa using Subsystems.StackOps.s0Col._proof_1)]
  ring

/- `base[9]` carries selector `011_1001` with body `s9`, but canonical `dup9`
uses selector `011_1010`. The current symbolic and canonical files are not
definitionally aligned here. -/
theorem bridge_stack_ops_9 (r : AirRow) :
    Constraints.Symbolic.StackOps.base[9]! (toSymbolicFrame r) =
      Subsystems.StackOps.dup9.eval r := by
  sorry

/- `base[10]` carries selector `011_1010` with body `s11`, but canonical
`dup11` uses selector `011_1100`. The current symbolic and canonical files are
not definitionally aligned here. -/
theorem bridge_stack_ops_10 (r : AirRow) :
    Constraints.Symbolic.StackOps.base[10]! (toSymbolicFrame r) =
      Subsystems.StackOps.dup11.eval r := by
  sorry

/- `base[11]` carries selector `011_1011` with body `s13`, but canonical
`dup13` uses selector `011_1110`. The current symbolic and canonical files are
not definitionally aligned here. -/
theorem bridge_stack_ops_11 (r : AirRow) :
    Constraints.Symbolic.StackOps.base[11]! (toSymbolicFrame r) =
      Subsystems.StackOps.dup13.eval r := by
  sorry

/- `base[12]` carries selector `011_1100` with body `s15`, but canonical
`dup15` uses selector `011_1001`. The current symbolic and canonical files are
not definitionally aligned here. -/
theorem bridge_stack_ops_12 (r : AirRow) :
    Constraints.Symbolic.StackOps.base[12]! (toSymbolicFrame r) =
      Subsystems.StackOps.dup15.eval r := by
  sorry

/- `base[13]` carries selector `011_1111` with body `clk`, but canonical
`clk` uses selector `011_1011`. The current symbolic and canonical files are
not definitionally aligned here. -/
theorem bridge_stack_ops_13 (r : AirRow) :
    Constraints.Symbolic.StackOps.base[13]! (toSymbolicFrame r) =
      Subsystems.StackOps.clk.eval r := by
  sorry

theorem bridge_stack_ops_14 (r : AirRow) :
    Constraints.Symbolic.StackOps.base[14]! (toSymbolicFrame r) =
      Subsystems.StackOps.swap0.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => f.is_transition * (((((((1 - f.colCurr 12) * (1 - f.colCurr 11)) *
      ((1 - f.colCurr 13) * f.colCurr 10)) * (1 - f.colCurr 9)) *
      (1 - f.colCurr 8)) * (1 - f.colCurr 7)) * (f.s' 0 - f.s 1)))
      (toSymbolicFrame r) =
    Subsystems.StackOps.swap0.eval r
  simp only [Subsystems.StackOps.swap0, Subsystems.StackOps.isSwap,
    Subsystems.StackOps.notOpBit0, Subsystems.StackOps.notOpBit1,
    Subsystems.StackOps.notOpBit2, Subsystems.StackOps.notOpBit4,
    Subsystems.StackOps.notOpBit5, Subsystems.StackOps.notOpBit6,
    Subsystems.StackOps.opBit0, Subsystems.StackOps.opBit1,
    Subsystems.StackOps.opBit2, Subsystems.StackOps.opBit3,
    Subsystems.StackOps.opBit4, Subsystems.StackOps.opBit5,
    Subsystems.StackOps.opBit6, Subsystems.StackOps.opBit0Col,
    Subsystems.StackOps.opBit1Col, Subsystems.StackOps.opBit2Col,
    Subsystems.StackOps.opBit3Col, Subsystems.StackOps.opBit4Col,
    Subsystems.StackOps.opBit5Col, Subsystems.StackOps.opBit6Col,
    Subsystems.StackOps.s0Next, Subsystems.StackOps.s1,
    Subsystems.StackOps.s0Col, Subsystems.StackOps.s1Col,
    toSymbolicFrame, FExpr.eval, Builder.whenTransition, Builder.gate,
    Builder.assertEq, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.boundary, AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr,
    SymbolicFrame.s, SymbolicFrame.s', h7, h8, h9, h10, h11, h12, h13]
  rw [curr_main_col_eq (r := r) (i := 7) h7
        (hj := Subsystems.StackOps.opBit0Col._proof_1),
      curr_main_col_eq (r := r) (i := 8) h8
        (hj := Subsystems.StackOps.opBit1Col._proof_1),
      curr_main_col_eq (r := r) (i := 9) h9
        (hj := Subsystems.StackOps.opBit2Col._proof_1),
      curr_main_col_eq (r := r) (i := 10) h10
        (hj := Subsystems.StackOps.opBit3Col._proof_1),
      curr_main_col_eq (r := r) (i := 11) h11
        (hj := Subsystems.StackOps.opBit4Col._proof_1),
      curr_main_col_eq (r := r) (i := 12) h12
        (hj := Subsystems.StackOps.opBit5Col._proof_1),
      curr_main_col_eq (r := r) (i := 13) h13
        (hj := Subsystems.StackOps.opBit6Col._proof_1),
      curr_stack_col_eq (r := r) (k := 1) h31
        (hj := by simpa using Subsystems.StackOps.s1Col._proof_1),
      next_stack_col_eq (r := r) (k := 0) h30
        (hj := by simpa using Subsystems.StackOps.s0Col._proof_1)]
  ring

theorem bridge_stack_ops_15 (r : AirRow) :
    Constraints.Symbolic.StackOps.base[15]! (toSymbolicFrame r) =
      Subsystems.StackOps.swap1.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => f.is_transition * (((((((1 - f.colCurr 12) * (1 - f.colCurr 11)) *
      ((1 - f.colCurr 13) * f.colCurr 10)) * (1 - f.colCurr 9)) *
      (1 - f.colCurr 8)) * (1 - f.colCurr 7)) * (f.s' 1 - f.s 0)))
      (toSymbolicFrame r) =
    Subsystems.StackOps.swap1.eval r
  simp only [Subsystems.StackOps.swap1, Subsystems.StackOps.isSwap,
    Subsystems.StackOps.notOpBit0, Subsystems.StackOps.notOpBit1,
    Subsystems.StackOps.notOpBit2, Subsystems.StackOps.notOpBit4,
    Subsystems.StackOps.notOpBit5, Subsystems.StackOps.notOpBit6,
    Subsystems.StackOps.opBit0, Subsystems.StackOps.opBit1,
    Subsystems.StackOps.opBit2, Subsystems.StackOps.opBit3,
    Subsystems.StackOps.opBit4, Subsystems.StackOps.opBit5,
    Subsystems.StackOps.opBit6, Subsystems.StackOps.opBit0Col,
    Subsystems.StackOps.opBit1Col, Subsystems.StackOps.opBit2Col,
    Subsystems.StackOps.opBit3Col, Subsystems.StackOps.opBit4Col,
    Subsystems.StackOps.opBit5Col, Subsystems.StackOps.opBit6Col,
    Subsystems.StackOps.s0, Subsystems.StackOps.s1Next,
    Subsystems.StackOps.s0Col, Subsystems.StackOps.s1Col,
    toSymbolicFrame, FExpr.eval, Builder.whenTransition, Builder.gate,
    Builder.assertEq, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.boundary, AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr,
    SymbolicFrame.s, SymbolicFrame.s', h7, h8, h9, h10, h11, h12, h13]
  rw [curr_main_col_eq (r := r) (i := 7) h7
        (hj := Subsystems.StackOps.opBit0Col._proof_1),
      curr_main_col_eq (r := r) (i := 8) h8
        (hj := Subsystems.StackOps.opBit1Col._proof_1),
      curr_main_col_eq (r := r) (i := 9) h9
        (hj := Subsystems.StackOps.opBit2Col._proof_1),
      curr_main_col_eq (r := r) (i := 10) h10
        (hj := Subsystems.StackOps.opBit3Col._proof_1),
      curr_main_col_eq (r := r) (i := 11) h11
        (hj := Subsystems.StackOps.opBit4Col._proof_1),
      curr_main_col_eq (r := r) (i := 12) h12
        (hj := Subsystems.StackOps.opBit5Col._proof_1),
      curr_main_col_eq (r := r) (i := 13) h13
        (hj := Subsystems.StackOps.opBit6Col._proof_1),
      curr_stack_col_eq (r := r) (k := 0) h30
        (hj := by simpa using Subsystems.StackOps.s0Col._proof_1),
      next_stack_col_eq (r := r) (k := 1) h31
        (hj := by simpa using Subsystems.StackOps.s1Col._proof_1)]
  ring

theorem bridge_stack_ops_16 (r : AirRow) :
    Constraints.Symbolic.StackOps.base[16]! (toSymbolicFrame r) =
      Subsystems.StackOps.movup2.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => f.is_transition * (((((((1 - f.colCurr 12) * (1 - f.colCurr 11)) *
      ((1 - f.colCurr 13) * f.colCurr 10)) * (1 - f.colCurr 9)) * f.colCurr 8) *
      (1 - f.colCurr 7)) * (f.s' 0 - f.s 2))) (toSymbolicFrame r) =
    Subsystems.StackOps.movup2.eval r
  simp only [Subsystems.StackOps.movup2, Subsystems.StackOps.isMovup2,
    Subsystems.StackOps.notOpBit0, Subsystems.StackOps.notOpBit2,
    Subsystems.StackOps.notOpBit4, Subsystems.StackOps.notOpBit5,
    Subsystems.StackOps.notOpBit6, Subsystems.StackOps.opBit0,
    Subsystems.StackOps.opBit1, Subsystems.StackOps.opBit2,
    Subsystems.StackOps.opBit3, Subsystems.StackOps.opBit4,
    Subsystems.StackOps.opBit5, Subsystems.StackOps.opBit6,
    Subsystems.StackOps.opBit0Col, Subsystems.StackOps.opBit1Col,
    Subsystems.StackOps.opBit2Col, Subsystems.StackOps.opBit3Col,
    Subsystems.StackOps.opBit4Col, Subsystems.StackOps.opBit5Col,
    Subsystems.StackOps.opBit6Col, Subsystems.StackOps.s0Next,
    Subsystems.StackOps.s2, Subsystems.StackOps.s0Col, Subsystems.StackOps.s2Col,
    toSymbolicFrame, FExpr.eval, Builder.whenTransition, Builder.gate,
    Builder.assertEq, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.boundary, AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr,
    SymbolicFrame.s, SymbolicFrame.s', h7, h8, h9, h10, h11, h12, h13]
  rw [curr_main_col_eq (r := r) (i := 7) h7
        (hj := Subsystems.StackOps.opBit0Col._proof_1),
      curr_main_col_eq (r := r) (i := 8) h8
        (hj := Subsystems.StackOps.opBit1Col._proof_1),
      curr_main_col_eq (r := r) (i := 9) h9
        (hj := Subsystems.StackOps.opBit2Col._proof_1),
      curr_main_col_eq (r := r) (i := 10) h10
        (hj := Subsystems.StackOps.opBit3Col._proof_1),
      curr_main_col_eq (r := r) (i := 11) h11
        (hj := Subsystems.StackOps.opBit4Col._proof_1),
      curr_main_col_eq (r := r) (i := 12) h12
        (hj := Subsystems.StackOps.opBit5Col._proof_1),
      curr_main_col_eq (r := r) (i := 13) h13
        (hj := Subsystems.StackOps.opBit6Col._proof_1),
      curr_stack_col_eq (r := r) (k := 2) h32
        (hj := by simpa using Subsystems.StackOps.s2Col._proof_1),
      next_stack_col_eq (r := r) (k := 0) h30
        (hj := by simpa using Subsystems.StackOps.s0Col._proof_1)]
  ring

theorem bridge_stack_ops_17 (r : AirRow) :
    Constraints.Symbolic.StackOps.base[17]! (toSymbolicFrame r) =
      Subsystems.StackOps.movup3.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => f.is_transition * (((((((1 - f.colCurr 12) * (1 - f.colCurr 11)) *
      ((1 - f.colCurr 13) * f.colCurr 10)) * f.colCurr 9) * (1 - f.colCurr 8)) *
      (1 - f.colCurr 7)) * (f.s' 0 - f.s 3))) (toSymbolicFrame r) =
    Subsystems.StackOps.movup3.eval r
  simp only [Subsystems.StackOps.movup3, Subsystems.StackOps.isMovup3,
    Subsystems.StackOps.notOpBit0, Subsystems.StackOps.notOpBit1,
    Subsystems.StackOps.notOpBit4, Subsystems.StackOps.notOpBit5,
    Subsystems.StackOps.notOpBit6, Subsystems.StackOps.opBit0,
    Subsystems.StackOps.opBit1, Subsystems.StackOps.opBit2,
    Subsystems.StackOps.opBit3, Subsystems.StackOps.opBit4,
    Subsystems.StackOps.opBit5, Subsystems.StackOps.opBit6,
    Subsystems.StackOps.opBit0Col, Subsystems.StackOps.opBit1Col,
    Subsystems.StackOps.opBit2Col, Subsystems.StackOps.opBit3Col,
    Subsystems.StackOps.opBit4Col, Subsystems.StackOps.opBit5Col,
    Subsystems.StackOps.opBit6Col, Subsystems.StackOps.s0Next,
    Subsystems.StackOps.s3, Subsystems.StackOps.s0Col, Subsystems.StackOps.s3Col,
    toSymbolicFrame, FExpr.eval, Builder.whenTransition, Builder.gate,
    Builder.assertEq, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.boundary, AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr,
    SymbolicFrame.s, SymbolicFrame.s', h7, h8, h9, h10, h11, h12, h13]
  rw [curr_main_col_eq (r := r) (i := 7) h7
        (hj := Subsystems.StackOps.opBit0Col._proof_1),
      curr_main_col_eq (r := r) (i := 8) h8
        (hj := Subsystems.StackOps.opBit1Col._proof_1),
      curr_main_col_eq (r := r) (i := 9) h9
        (hj := Subsystems.StackOps.opBit2Col._proof_1),
      curr_main_col_eq (r := r) (i := 10) h10
        (hj := Subsystems.StackOps.opBit3Col._proof_1),
      curr_main_col_eq (r := r) (i := 11) h11
        (hj := Subsystems.StackOps.opBit4Col._proof_1),
      curr_main_col_eq (r := r) (i := 12) h12
        (hj := Subsystems.StackOps.opBit5Col._proof_1),
      curr_main_col_eq (r := r) (i := 13) h13
        (hj := Subsystems.StackOps.opBit6Col._proof_1),
      curr_stack_col_eq (r := r) (k := 3) h33
        (hj := by simpa using Subsystems.StackOps.s3Col._proof_1),
      next_stack_col_eq (r := r) (k := 0) h30
        (hj := by simpa using Subsystems.StackOps.s0Col._proof_1)]
  ring

theorem bridge_stack_ops_18 (r : AirRow) :
    Constraints.Symbolic.StackOps.base[18]! (toSymbolicFrame r) =
      Subsystems.StackOps.movup4.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) *
      ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * (1 - f.colCurr 9)) *
      (1 - f.colCurr 8)) * (1 - f.colCurr 7)) * (f.s' 0 - f.s 4)))
      (toSymbolicFrame r) =
    Subsystems.StackOps.movup4.eval r
  simp only [Subsystems.StackOps.movup4, Subsystems.StackOps.isMovup4,
    Subsystems.StackOps.notOpBit0, Subsystems.StackOps.notOpBit1,
    Subsystems.StackOps.notOpBit2, Subsystems.StackOps.notOpBit3,
    Subsystems.StackOps.notOpBit5, Subsystems.StackOps.notOpBit6,
    Subsystems.StackOps.opBit0, Subsystems.StackOps.opBit1,
    Subsystems.StackOps.opBit2, Subsystems.StackOps.opBit3,
    Subsystems.StackOps.opBit4, Subsystems.StackOps.opBit5,
    Subsystems.StackOps.opBit6, Subsystems.StackOps.opBit0Col,
    Subsystems.StackOps.opBit1Col, Subsystems.StackOps.opBit2Col,
    Subsystems.StackOps.opBit3Col, Subsystems.StackOps.opBit4Col,
    Subsystems.StackOps.opBit5Col, Subsystems.StackOps.opBit6Col,
    Subsystems.StackOps.s0Next, Subsystems.StackOps.s4,
    Subsystems.StackOps.s0Col, Subsystems.StackOps.s4Col,
    toSymbolicFrame, FExpr.eval, Builder.whenTransition, Builder.gate,
    Builder.assertEq, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.boundary, AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr,
    SymbolicFrame.s, SymbolicFrame.s', h7, h8, h9, h10, h11, h12, h13]
  rw [curr_main_col_eq (r := r) (i := 7) h7
        (hj := Subsystems.StackOps.opBit0Col._proof_1),
      curr_main_col_eq (r := r) (i := 8) h8
        (hj := Subsystems.StackOps.opBit1Col._proof_1),
      curr_main_col_eq (r := r) (i := 9) h9
        (hj := Subsystems.StackOps.opBit2Col._proof_1),
      curr_main_col_eq (r := r) (i := 10) h10
        (hj := Subsystems.StackOps.opBit3Col._proof_1),
      curr_main_col_eq (r := r) (i := 11) h11
        (hj := Subsystems.StackOps.opBit4Col._proof_1),
      curr_main_col_eq (r := r) (i := 12) h12
        (hj := Subsystems.StackOps.opBit5Col._proof_1),
      curr_main_col_eq (r := r) (i := 13) h13
        (hj := Subsystems.StackOps.opBit6Col._proof_1),
      curr_stack_col_eq (r := r) (k := 4) h34
        (hj := by simpa using Subsystems.StackOps.s4Col._proof_1),
      next_stack_col_eq (r := r) (k := 0) h30
        (hj := by simpa using Subsystems.StackOps.s0Col._proof_1)]
  ring

theorem bridge_stack_ops_19 (r : AirRow) :
    Constraints.Symbolic.StackOps.base[19]! (toSymbolicFrame r) =
      Subsystems.StackOps.movup5.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => f.is_transition * (((((((1 - f.colCurr 12) * f.colCurr 11) *
      ((1 - f.colCurr 13) * (1 - f.colCurr 10))) * (1 - f.colCurr 9)) *
      f.colCurr 8) * (1 - f.colCurr 7)) * (f.s' 0 - f.s 5)))
      (toSymbolicFrame r) =
    Subsystems.StackOps.movup5.eval r
  simp only [Subsystems.StackOps.movup5, Subsystems.StackOps.isMovup5,
    Subsystems.StackOps.notOpBit0, Subsystems.StackOps.notOpBit2,
    Subsystems.StackOps.notOpBit3, Subsystems.StackOps.notOpBit5,
    Subsystems.StackOps.notOpBit6, Subsystems.StackOps.opBit0,
    Subsystems.StackOps.opBit1, Subsystems.StackOps.opBit2,
    Subsystems.StackOps.opBit3, Subsystems.StackOps.opBit4,
    Subsystems.StackOps.opBit5, Subsystems.StackOps.opBit6,
    Subsystems.StackOps.opBit0Col, Subsystems.StackOps.opBit1Col,
    Subsystems.StackOps.opBit2Col, Subsystems.StackOps.opBit3Col,
    Subsystems.StackOps.opBit4Col, Subsystems.StackOps.opBit5Col,
    Subsystems.StackOps.opBit6Col, Subsystems.StackOps.s0Next,
    Subsystems.StackOps.s5, Subsystems.StackOps.s0Col, Subsystems.StackOps.s5Col,
    toSymbolicFrame, FExpr.eval, Builder.whenTransition, Builder.gate,
    Builder.assertEq, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.boundary, AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr,
    SymbolicFrame.s, SymbolicFrame.s', h7, h8, h9, h10, h11, h12, h13]
  rw [curr_main_col_eq (r := r) (i := 7) h7
        (hj := Subsystems.StackOps.opBit0Col._proof_1),
      curr_main_col_eq (r := r) (i := 8) h8
        (hj := Subsystems.StackOps.opBit1Col._proof_1),
      curr_main_col_eq (r := r) (i := 9) h9
        (hj := Subsystems.StackOps.opBit2Col._proof_1),
      curr_main_col_eq (r := r) (i := 10) h10
        (hj := Subsystems.StackOps.opBit3Col._proof_1),
      curr_main_col_eq (r := r) (i := 11) h11
        (hj := Subsystems.StackOps.opBit4Col._proof_1),
      curr_main_col_eq (r := r) (i := 12) h12
        (hj := Subsystems.StackOps.opBit5Col._proof_1),
      curr_main_col_eq (r := r) (i := 13) h13
        (hj := Subsystems.StackOps.opBit6Col._proof_1),
      curr_stack_col_eq (r := r) (k := 5) h35
        (hj := by simpa using Subsystems.StackOps.s5Col._proof_1),
      next_stack_col_eq (r := r) (k := 0) h30
        (hj := by simpa using Subsystems.StackOps.s0Col._proof_1)]
  ring

end MidenLean.AIR.Semantics.Refinement.SymbolicToCanonical
