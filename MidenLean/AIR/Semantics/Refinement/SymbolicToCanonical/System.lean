import MidenLean.AIR.Semantics.Tactics
import MidenLean.AIR.Semantics.Subsystems.System
import MidenLean.AIR.Constraints.Symbolic.System

set_option maxHeartbeats 16000000

namespace MidenLean.AIR.Semantics.Refinement.SymbolicToCanonical

open MidenLean
open MidenLean.AIR
open MidenLean.AIR.Semantics
open MidenLean.AIR.Semantics.Tactics
open MidenLean.AIR.Semantics.Builder

private def systemLowBit0Zero (r : AirRow) : Prop :=
  r.curr ⟨7, by decide⟩ = 0

private def systemLowBit1Zero (r : AirRow) : Prop :=
  r.curr ⟨8, by decide⟩ = 0

private def systemExtraCol0Eq (r : AirRow) : Prop :=
  r.curr ⟨28, by decide⟩ =
    r.curr ⟨13, by decide⟩ * (1 - r.curr ⟨12, by decide⟩) * r.curr ⟨11, by decide⟩

private def systemExtraCol1Eq (r : AirRow) : Prop :=
  r.curr ⟨29, by decide⟩ =
    r.curr ⟨13, by decide⟩ * r.curr ⟨12, by decide⟩

theorem bridge_system_0 (r : AirRow) :
    Constraints.Symbolic.System.base[0]! (toSymbolicFrame r) =
      Subsystems.System.clkFirst.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => f.is_first_row * f.clk) (toSymbolicFrame r) =
    Subsystems.System.clkFirst.eval r
  simp [Subsystems.System.clkFirst, Subsystems.System.clk, Subsystems.System.clkCol,
    toSymbolicFrame, FExpr.eval, Builder.gate, Builder.assertEq, Builder.assertZero,
    BaseConstraint.eval, BaseConstraint.expr, AirRow.boundary, AirRow.baseAt, AirRow.base,
    SymbolicFrame.clk]

theorem bridge_system_1 (r : AirRow) :
    Constraints.Symbolic.System.base[1]! (toSymbolicFrame r) =
      Subsystems.System.clkTransition.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => f.is_transition * (f.clk' - (f.clk + 1))) (toSymbolicFrame r) =
    Subsystems.System.clkTransition.eval r
  simp [Subsystems.System.clkTransition, Subsystems.System.clkNext, Subsystems.System.clk,
    Subsystems.System.clkCol, toSymbolicFrame, FExpr.eval, Builder.whenTransition,
    Builder.gate, Builder.assertEq, Builder.assertZero, BaseConstraint.eval,
    BaseConstraint.expr, AirRow.boundary, AirRow.baseAt, AirRow.base, SymbolicFrame.clk,
    SymbolicFrame.clk']

private def weakBridgeCounterexampleCurr (i : MainCol) : Felt :=
  match i.1 with
  | 7 => 1
  | 9 => 1
  | 10 => 1
  | 12 => 1
  | 13 => 1
  | 29 => 1
  | _ => 0

private def weakBridgeCounterexampleNext (i : MainCol) : Felt :=
  match i.1 with
  | 1 => 5
  | _ => 0

private def weakBridgeCounterexample : AirRow :=
  { curr := weakBridgeCounterexampleCurr
    next := weakBridgeCounterexampleNext
    isTransition := 1 }

private theorem weakBridgeCounterexample_e0 :
    systemExtraCol0Eq weakBridgeCounterexample := by
  unfold systemExtraCol0Eq weakBridgeCounterexample
  simp [weakBridgeCounterexampleCurr]

private theorem weakBridgeCounterexample_e1 :
    systemExtraCol1Eq weakBridgeCounterexample := by
  unfold systemExtraCol1Eq weakBridgeCounterexample
  simp [weakBridgeCounterexampleCurr]

private theorem weakBridgeCounterexample_symbolic :
    Constraints.Symbolic.System.base[2]! (toSymbolicFrame weakBridgeCounterexample) = 4 := by
  native_decide

private theorem weakBridgeCounterexample_canonical :
    Subsystems.System.ctxCallDyncall.eval weakBridgeCounterexample = 0 := by
  native_decide

/--
The extracted symbolic `System.base[2]` constraint cannot be bridged to the
canonical `ctxCallDyncall` constraint from the extra-column equalities alone.

The missing assumptions are the low-bit facts `b0 = 0` and `b1 = 0` for the
`CALL`/`SYSCALL`/`END` selectors: the canonical subsystem includes the factors
`(1 - b1) * (1 - b0)`, while the symbolic constraint does not.
-/
theorem not_bridge_system_2_under_extra_cols_only :
    ¬ ∀ (r : AirRow),
        systemExtraCol0Eq r →
        systemExtraCol1Eq r →
        Constraints.Symbolic.System.base[2]! (toSymbolicFrame r) =
          Subsystems.System.ctxCallDyncall.eval r := by
  intro h
  specialize h weakBridgeCounterexample
    weakBridgeCounterexample_e0
    weakBridgeCounterexample_e1
  have h40 : (4 : Felt) = 0 := by
    simpa [weakBridgeCounterexample_symbolic, weakBridgeCounterexample_canonical] using h
  have hne : (4 : Felt) ≠ 0 := by
    native_decide
  exact hne h40

private theorem systemBridgeHypotheses
    (r : AirRow)
    (h_b0 : systemLowBit0Zero r) (h_b1 : systemLowBit1Zero r)
    (h_e0 : systemExtraCol0Eq r) (h_e1 : systemExtraCol1Eq r) :
    r.curr 7 = 0 ∧
      r.curr 8 = 0 ∧
      r.curr 28 = r.curr 13 * (1 - r.curr 12) * r.curr 11 ∧
      r.curr 29 = r.curr 13 * r.curr 12 := by
  constructor
  · simpa [systemLowBit0Zero] using h_b0
  constructor
  · simpa [systemLowBit1Zero] using h_b1
  constructor
  · simpa [systemExtraCol0Eq] using h_e0
  · simpa [systemExtraCol1Eq] using h_e1

private def systemCallDyncallSymSel (r : AirRow) : Felt :=
  r.curr 9 * r.curr 10 * ((1 - r.curr 11) * r.curr 29) +
    (1 - r.curr 7) * (1 - r.curr 8) * r.curr 9 * (r.curr 10 * r.curr 28)

private def systemCallDyncallCanSel (r : AirRow) : Felt :=
  r.curr 13 * (r.curr 12 * ((1 - r.curr 11) *
    (r.curr 10 * (r.curr 9 * ((1 - r.curr 8) * (1 - r.curr 7)))))) +
    r.curr 13 * ((1 - r.curr 12) * (r.curr 11 *
      (r.curr 10 * (r.curr 9 * ((1 - r.curr 8) * (1 - r.curr 7))))))

private def systemSyscallSymSel (r : AirRow) : Felt :=
  (1 - r.curr 9) * r.curr 10 * ((1 - r.curr 11) * r.curr 29)

private def systemSyscallCanSel (r : AirRow) : Felt :=
  r.curr 13 * (r.curr 12 * ((1 - r.curr 11) *
    (r.curr 10 * ((1 - r.curr 9) * ((1 - r.curr 8) * (1 - r.curr 7))))))

private theorem systemCallDyncallFlag_eval (r : AirRow) :
    Subsystems.System.callDyncallFlag.eval r = systemCallDyncallCanSel r := by
  simp [systemCallDyncallCanSel, Subsystems.System.callDyncallFlag, Subsystems.System.isCall,
    Subsystems.System.isDyncall, Subsystems.System.opBit0, Subsystems.System.opBit1,
    Subsystems.System.opBit2, Subsystems.System.opBit3, Subsystems.System.opBit4,
    Subsystems.System.opBit5, Subsystems.System.opBit6, Subsystems.System.notOpBit0,
    Subsystems.System.notOpBit1, Subsystems.System.notOpBit4, Subsystems.System.notOpBit5,
    Subsystems.System.opBit0Col, Subsystems.System.opBit1Col, Subsystems.System.opBit2Col,
    Subsystems.System.opBit3Col, Subsystems.System.opBit4Col, Subsystems.System.opBit5Col,
    Subsystems.System.opBit6Col, FExpr.eval, AirRow.baseAt, AirRow.base]

private theorem systemSyscallFlag_eval (r : AirRow) :
    Subsystems.System.isSyscall.eval r = systemSyscallCanSel r := by
  simp [systemSyscallCanSel, Subsystems.System.isSyscall, Subsystems.System.opBit0,
    Subsystems.System.opBit1, Subsystems.System.opBit2, Subsystems.System.opBit3,
    Subsystems.System.opBit4, Subsystems.System.opBit5, Subsystems.System.opBit6,
    Subsystems.System.notOpBit0, Subsystems.System.notOpBit1, Subsystems.System.notOpBit2,
    Subsystems.System.notOpBit4, Subsystems.System.opBit0Col, Subsystems.System.opBit1Col,
    Subsystems.System.opBit2Col, Subsystems.System.opBit3Col, Subsystems.System.opBit4Col,
    Subsystems.System.opBit5Col, Subsystems.System.opBit6Col, FExpr.eval, AirRow.baseAt,
    AirRow.base]

private def systemEndSymSel (r : AirRow) : Felt :=
  (1 - r.curr 9) * (1 - r.curr 10) * (r.curr 11 * r.curr 29)

private def systemEndCanSel (r : AirRow) : Felt :=
  r.curr 13 * (r.curr 12 * (r.curr 11 *
    ((1 - r.curr 10) * ((1 - r.curr 9) * ((1 - r.curr 8) * (1 - r.curr 7))))))

private def systemDefaultSymSel (r : AirRow) : Felt :=
  1 - (systemCallDyncallSymSel r + systemSyscallSymSel r + systemEndSymSel r)

private def systemDefaultCanSel (r : AirRow) : Felt :=
  1 - (systemCallDyncallCanSel r + systemSyscallCanSel r + systemEndCanSel r)

private def systemPreserveSymSel (r : AirRow) : Felt :=
  1 - (systemCallDyncallSymSel r + systemEndSymSel r)

private def systemPreserveCanSel (r : AirRow) : Felt :=
  1 - (systemCallDyncallCanSel r + systemEndCanSel r)

private theorem systemEndFlag_eval (r : AirRow) :
    Subsystems.System.isEnd.eval r = systemEndCanSel r := by
  simp [systemEndCanSel, Subsystems.System.isEnd, Subsystems.System.opBit0,
    Subsystems.System.opBit1, Subsystems.System.opBit2, Subsystems.System.opBit3,
    Subsystems.System.opBit4, Subsystems.System.opBit5, Subsystems.System.opBit6,
    Subsystems.System.notOpBit0, Subsystems.System.notOpBit1, Subsystems.System.notOpBit2,
    Subsystems.System.notOpBit3, Subsystems.System.opBit0Col, Subsystems.System.opBit1Col,
    Subsystems.System.opBit2Col, Subsystems.System.opBit3Col, Subsystems.System.opBit4Col,
    Subsystems.System.opBit5Col, Subsystems.System.opBit6Col, FExpr.eval, AirRow.baseAt,
    AirRow.base]

private theorem systemDefaultFlag_eval (r : AirRow) :
    Subsystems.System.defaultCtxFlag.eval r = systemDefaultCanSel r := by
  simp [systemDefaultCanSel, systemCallDyncallCanSel, systemSyscallCanSel, systemEndCanSel,
    Subsystems.System.defaultCtxFlag, Subsystems.System.changeCtxFlag,
    Subsystems.System.isCall, Subsystems.System.isSyscall,
    Subsystems.System.isDyncall, Subsystems.System.isEnd, Subsystems.System.opBit0,
    Subsystems.System.opBit1, Subsystems.System.opBit2, Subsystems.System.opBit3,
    Subsystems.System.opBit4, Subsystems.System.opBit5, Subsystems.System.opBit6,
    Subsystems.System.notOpBit0, Subsystems.System.notOpBit1, Subsystems.System.notOpBit2,
    Subsystems.System.notOpBit3, Subsystems.System.notOpBit4, Subsystems.System.notOpBit5,
    Subsystems.System.opBit0Col, Subsystems.System.opBit1Col, Subsystems.System.opBit2Col,
    Subsystems.System.opBit3Col, Subsystems.System.opBit4Col, Subsystems.System.opBit5Col,
    Subsystems.System.opBit6Col, FExpr.eval, AirRow.baseAt, AirRow.base]
  ring_nf

private theorem systemLoadFlag_eval (r : AirRow) :
    Subsystems.System.loadFlag.eval r = systemCallDyncallCanSel r := by
  simpa [Subsystems.System.loadFlag] using systemCallDyncallFlag_eval r

private theorem systemPreserveFlag_eval (r : AirRow) :
    Subsystems.System.preserveFlag.eval r = systemPreserveCanSel r := by
  simp [systemPreserveCanSel, systemCallDyncallCanSel, systemEndCanSel,
    Subsystems.System.preserveFlag, Subsystems.System.loadFlag, Subsystems.System.callDyncallFlag,
    Subsystems.System.isCall, Subsystems.System.isDyncall, Subsystems.System.isEnd,
    Subsystems.System.opBit0, Subsystems.System.opBit1, Subsystems.System.opBit2,
    Subsystems.System.opBit3, Subsystems.System.opBit4, Subsystems.System.opBit5,
    Subsystems.System.opBit6, Subsystems.System.notOpBit0, Subsystems.System.notOpBit1,
    Subsystems.System.notOpBit2, Subsystems.System.notOpBit3, Subsystems.System.notOpBit4,
    Subsystems.System.notOpBit5, Subsystems.System.opBit0Col, Subsystems.System.opBit1Col,
    Subsystems.System.opBit2Col, Subsystems.System.opBit3Col, Subsystems.System.opBit4Col,
    Subsystems.System.opBit5Col, Subsystems.System.opBit6Col, FExpr.eval, AirRow.baseAt,
    AirRow.base]

theorem bridge_system_2 (r : AirRow)
    (h_b0 : systemLowBit0Zero r) (h_b1 : systemLowBit1Zero r)
    (h_e0 : systemExtraCol0Eq r) (h_e1 : systemExtraCol1Eq r) :
    Constraints.Symbolic.System.base[2]! (toSymbolicFrame r) =
      Subsystems.System.ctxCallDyncall.eval r := by
  rcases systemBridgeHypotheses r h_b0 h_b1 h_e0 h_e1 with ⟨h_b0', h_b1', h_e0', h_e1'⟩
  let delta := r.next 1 - (r.curr 0 + 1)
  have h_sym :
      Constraints.Symbolic.System.base[2]! (toSymbolicFrame r) =
        r.isTransition * (systemCallDyncallSymSel r * delta) := by
    rw [getElem!_pos (h := by native_decide)]
    change (fun f =>
      f.is_transition *
        ((((f.colCurr 9 * f.colCurr 10) * ((1 - f.colCurr 11) * f.colCurr 29)) +
            ((((1 - f.colCurr 7) * (1 - f.colCurr 8)) * f.colCurr 9) *
              (f.colCurr 10 * f.colCurr 28))) *
          (f.ctx' - (f.clk + 1)))) (toSymbolicFrame r) =
      r.isTransition * (systemCallDyncallSymSel r * delta)
    simp [systemCallDyncallSymSel, delta, toSymbolicFrame, MainWidth,
      SymbolicFrame.colCurr, SymbolicFrame.ctx', SymbolicFrame.clk]
  have h_can :
      Subsystems.System.ctxCallDyncall.eval r =
        r.isTransition * (systemCallDyncallCanSel r * delta) := by
    simpa [Subsystems.System.ctxCallDyncall, Subsystems.System.ctxNext, Subsystems.System.ctxCol,
      Subsystems.System.clk, Subsystems.System.clkCol, Builder.whenTransition, Builder.gate,
      Builder.assertEq, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr, FExpr.eval,
      AirRow.boundary, AirRow.baseAt, AirRow.base, delta] using
      congrArg (fun x => r.isTransition * (x * delta)) (systemCallDyncallFlag_eval r)
  rw [h_sym, h_can]
  simp [delta, systemCallDyncallSymSel, systemCallDyncallCanSel,
    h_b0', h_b1', h_e0', h_e1']
  left
  left
  ring_nf

theorem bridge_system_3 (r : AirRow)
    (h_b0 : systemLowBit0Zero r) (h_b1 : systemLowBit1Zero r)
    (h_e0 : systemExtraCol0Eq r) (h_e1 : systemExtraCol1Eq r) :
    Constraints.Symbolic.System.base[3]! (toSymbolicFrame r) =
      Subsystems.System.ctxSyscall.eval r := by
  rcases systemBridgeHypotheses r h_b0 h_b1 h_e0 h_e1 with ⟨h_b0', h_b1', _, h_e1'⟩
  let delta := r.next 1
  have h_sym :
      Constraints.Symbolic.System.base[3]! (toSymbolicFrame r) =
        r.isTransition * (systemSyscallSymSel r * delta) := by
    rw [getElem!_pos (h := by native_decide)]
    change (fun f =>
      f.is_transition *
        ((((1 - f.colCurr 9) * f.colCurr 10) * ((1 - f.colCurr 11) * f.colCurr 29)) *
          f.ctx')) (toSymbolicFrame r) =
      r.isTransition * (systemSyscallSymSel r * delta)
    simp [systemSyscallSymSel, delta, toSymbolicFrame, MainWidth,
      SymbolicFrame.colCurr, SymbolicFrame.ctx']
  have h_can :
      Subsystems.System.ctxSyscall.eval r =
        r.isTransition * (systemSyscallCanSel r * delta) := by
    simpa [Subsystems.System.ctxSyscall, Subsystems.System.ctxNext, Subsystems.System.ctxCol,
      Builder.whenTransition, Builder.gate, Builder.assertEq, Builder.assertZero,
      BaseConstraint.eval, BaseConstraint.expr, FExpr.eval, AirRow.boundary, AirRow.baseAt,
      AirRow.base, delta] using
      congrArg (fun x => r.isTransition * (x * delta)) (systemSyscallFlag_eval r)
  rw [h_sym, h_can]
  simp [delta, systemSyscallSymSel, systemSyscallCanSel, h_b0', h_b1', h_e1']
  left
  left
  ring_nf

theorem bridge_system_4 (r : AirRow)
    (h_b0 : systemLowBit0Zero r) (h_b1 : systemLowBit1Zero r)
    (h_e0 : systemExtraCol0Eq r) (h_e1 : systemExtraCol1Eq r) :
    Constraints.Symbolic.System.base[4]! (toSymbolicFrame r) =
      Subsystems.System.ctxDefault.eval r := by
  rcases systemBridgeHypotheses r h_b0 h_b1 h_e0 h_e1 with ⟨h_b0', h_b1', h_e0', h_e1'⟩
  let delta := r.next 1 - r.curr 1
  have h_sym :
      Constraints.Symbolic.System.base[4]! (toSymbolicFrame r) =
        r.isTransition * (systemDefaultSymSel r * delta) := by
    rw [getElem!_pos (h := by native_decide)]
    change (fun f =>
      f.is_transition *
        ((1 - (((((f.colCurr 9 * f.colCurr 10) * ((1 - f.colCurr 11) * f.colCurr 29)) +
            (((1 - f.colCurr 9) * f.colCurr 10) * ((1 - f.colCurr 11) * f.colCurr 29))) +
            ((((1 - f.colCurr 7) * (1 - f.colCurr 8)) * f.colCurr 9) *
              (f.colCurr 10 * f.colCurr 28))) +
            (((1 - f.colCurr 9) * (1 - f.colCurr 10)) * (f.colCurr 11 * f.colCurr 29)))) *
          (f.ctx' - f.ctx))) (toSymbolicFrame r) =
      r.isTransition * (systemDefaultSymSel r * delta)
    simp [systemDefaultSymSel, systemCallDyncallSymSel, systemSyscallSymSel, systemEndSymSel,
      delta, toSymbolicFrame, MainWidth, SymbolicFrame.colCurr, SymbolicFrame.ctx',
      SymbolicFrame.ctx]
    left
    left
    ac_rfl
  have h_can :
      Subsystems.System.ctxDefault.eval r =
        r.isTransition * (systemDefaultCanSel r * delta) := by
    simpa [Subsystems.System.ctxDefault, Subsystems.System.ctxNext, Subsystems.System.ctx,
      Subsystems.System.ctxCol, Builder.whenTransition, Builder.gate, Builder.assertEq,
      Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr, FExpr.eval,
      AirRow.boundary, AirRow.baseAt, AirRow.base, delta] using
      congrArg (fun x => r.isTransition * (x * delta)) (systemDefaultFlag_eval r)
  rw [h_sym, h_can]
  simp [delta, systemDefaultSymSel, systemDefaultCanSel, systemCallDyncallSymSel,
    systemCallDyncallCanSel, systemSyscallSymSel, systemSyscallCanSel, systemEndSymSel,
    systemEndCanSel, h_b0', h_b1', h_e0', h_e1']
  left
  left
  ac_rfl

theorem bridge_system_5 (r : AirRow)
    (h_b0 : systemLowBit0Zero r) (h_b1 : systemLowBit1Zero r)
    (h_e0 : systemExtraCol0Eq r) (h_e1 : systemExtraCol1Eq r) :
    Constraints.Symbolic.System.base[5]! (toSymbolicFrame r) =
      Subsystems.System.fnHash0Load.eval r := by
  rcases systemBridgeHypotheses r h_b0 h_b1 h_e0 h_e1 with ⟨h_b0', h_b1', h_e0', h_e1'⟩
  let delta := r.next 2 - r.curr 14
  have h_sym :
      Constraints.Symbolic.System.base[5]! (toSymbolicFrame r) =
        r.isTransition * (systemCallDyncallSymSel r * delta) := by
    rw [getElem!_pos (h := by native_decide)]
    change (fun f =>
      f.is_transition *
        ((((f.colCurr 9 * f.colCurr 10) * ((1 - f.colCurr 11) * f.colCurr 29)) +
            ((((1 - f.colCurr 7) * (1 - f.colCurr 8)) * f.colCurr 9) *
              (f.colCurr 10 * f.colCurr 28))) *
          (f.colNext 2 - f.colCurr 14))) (toSymbolicFrame r) =
      r.isTransition * (systemCallDyncallSymSel r * delta)
    simp [systemCallDyncallSymSel, delta, toSymbolicFrame, MainWidth,
      SymbolicFrame.colCurr, SymbolicFrame.colNext]
  have h_can :
      Subsystems.System.fnHash0Load.eval r =
        r.isTransition * (systemCallDyncallCanSel r * delta) := by
    change r.isTransition * (Subsystems.System.loadFlag.eval r * delta) =
      r.isTransition * (systemCallDyncallCanSel r * delta)
    rw [systemLoadFlag_eval]
  rw [h_sym, h_can]
  simp [delta, systemCallDyncallSymSel, systemCallDyncallCanSel,
    h_b0', h_b1', h_e0', h_e1']
  left
  left
  ring_nf

theorem bridge_system_6 (r : AirRow)
    (h_b0 : systemLowBit0Zero r) (h_b1 : systemLowBit1Zero r)
    (h_e0 : systemExtraCol0Eq r) (h_e1 : systemExtraCol1Eq r) :
    Constraints.Symbolic.System.base[6]! (toSymbolicFrame r) =
      Subsystems.System.fnHash1Load.eval r := by
  rcases systemBridgeHypotheses r h_b0 h_b1 h_e0 h_e1 with ⟨h_b0', h_b1', h_e0', h_e1'⟩
  let delta := r.next 3 - r.curr 15
  have h_sym :
      Constraints.Symbolic.System.base[6]! (toSymbolicFrame r) =
        r.isTransition * (systemCallDyncallSymSel r * delta) := by
    rw [getElem!_pos (h := by native_decide)]
    change (fun f =>
      f.is_transition *
        ((((f.colCurr 9 * f.colCurr 10) * ((1 - f.colCurr 11) * f.colCurr 29)) +
            ((((1 - f.colCurr 7) * (1 - f.colCurr 8)) * f.colCurr 9) *
              (f.colCurr 10 * f.colCurr 28))) *
          (f.colNext 3 - f.colCurr 15))) (toSymbolicFrame r) =
      r.isTransition * (systemCallDyncallSymSel r * delta)
    simp [systemCallDyncallSymSel, delta, toSymbolicFrame, MainWidth,
      SymbolicFrame.colCurr, SymbolicFrame.colNext]
  have h_can :
      Subsystems.System.fnHash1Load.eval r =
        r.isTransition * (systemCallDyncallCanSel r * delta) := by
    change r.isTransition * (Subsystems.System.loadFlag.eval r * delta) =
      r.isTransition * (systemCallDyncallCanSel r * delta)
    rw [systemLoadFlag_eval]
  rw [h_sym, h_can]
  simp [delta, systemCallDyncallSymSel, systemCallDyncallCanSel,
    h_b0', h_b1', h_e0', h_e1']
  left
  left
  ring_nf

theorem bridge_system_7 (r : AirRow)
    (h_b0 : systemLowBit0Zero r) (h_b1 : systemLowBit1Zero r)
    (h_e0 : systemExtraCol0Eq r) (h_e1 : systemExtraCol1Eq r) :
    Constraints.Symbolic.System.base[7]! (toSymbolicFrame r) =
      Subsystems.System.fnHash2Load.eval r := by
  rcases systemBridgeHypotheses r h_b0 h_b1 h_e0 h_e1 with ⟨h_b0', h_b1', h_e0', h_e1'⟩
  let delta := r.next 4 - r.curr 16
  have h_sym :
      Constraints.Symbolic.System.base[7]! (toSymbolicFrame r) =
        r.isTransition * (systemCallDyncallSymSel r * delta) := by
    rw [getElem!_pos (h := by native_decide)]
    change (fun f =>
      f.is_transition *
        ((((f.colCurr 9 * f.colCurr 10) * ((1 - f.colCurr 11) * f.colCurr 29)) +
            ((((1 - f.colCurr 7) * (1 - f.colCurr 8)) * f.colCurr 9) *
              (f.colCurr 10 * f.colCurr 28))) *
          (f.colNext 4 - f.h 0))) (toSymbolicFrame r) =
      r.isTransition * (systemCallDyncallSymSel r * delta)
    simp [systemCallDyncallSymSel, delta, toSymbolicFrame, MainWidth,
      SymbolicFrame.colCurr, SymbolicFrame.colNext, SymbolicFrame.h]
  have h_can :
      Subsystems.System.fnHash2Load.eval r =
        r.isTransition * (systemCallDyncallCanSel r * delta) := by
    change r.isTransition * (Subsystems.System.loadFlag.eval r * delta) =
      r.isTransition * (systemCallDyncallCanSel r * delta)
    rw [systemLoadFlag_eval]
  rw [h_sym, h_can]
  simp [delta, systemCallDyncallSymSel, systemCallDyncallCanSel,
    h_b0', h_b1', h_e0', h_e1']
  left
  left
  ring_nf

theorem bridge_system_8 (r : AirRow)
    (h_b0 : systemLowBit0Zero r) (h_b1 : systemLowBit1Zero r)
    (h_e0 : systemExtraCol0Eq r) (h_e1 : systemExtraCol1Eq r) :
    Constraints.Symbolic.System.base[8]! (toSymbolicFrame r) =
      Subsystems.System.fnHash3Load.eval r := by
  rcases systemBridgeHypotheses r h_b0 h_b1 h_e0 h_e1 with ⟨h_b0', h_b1', h_e0', h_e1'⟩
  let delta := r.next 5 - r.curr 17
  have h_sym :
      Constraints.Symbolic.System.base[8]! (toSymbolicFrame r) =
        r.isTransition * (systemCallDyncallSymSel r * delta) := by
    rw [getElem!_pos (h := by native_decide)]
    change (fun f =>
      f.is_transition *
        ((((f.colCurr 9 * f.colCurr 10) * ((1 - f.colCurr 11) * f.colCurr 29)) +
            ((((1 - f.colCurr 7) * (1 - f.colCurr 8)) * f.colCurr 9) *
              (f.colCurr 10 * f.colCurr 28))) *
          (f.colNext 5 - f.h 1))) (toSymbolicFrame r) =
      r.isTransition * (systemCallDyncallSymSel r * delta)
    simp [systemCallDyncallSymSel, delta, toSymbolicFrame, MainWidth,
      SymbolicFrame.colCurr, SymbolicFrame.colNext, SymbolicFrame.h]
  have h_can :
      Subsystems.System.fnHash3Load.eval r =
        r.isTransition * (systemCallDyncallCanSel r * delta) := by
    change r.isTransition * (Subsystems.System.loadFlag.eval r * delta) =
      r.isTransition * (systemCallDyncallCanSel r * delta)
    rw [systemLoadFlag_eval]
  rw [h_sym, h_can]
  simp [delta, systemCallDyncallSymSel, systemCallDyncallCanSel,
    h_b0', h_b1', h_e0', h_e1']
  left
  left
  ring_nf

theorem bridge_system_9 (r : AirRow)
    (h_b0 : systemLowBit0Zero r) (h_b1 : systemLowBit1Zero r)
    (h_e0 : systemExtraCol0Eq r) (h_e1 : systemExtraCol1Eq r) :
    Constraints.Symbolic.System.base[9]! (toSymbolicFrame r) =
      Subsystems.System.fnHash0Preserve.eval r := by
  rcases systemBridgeHypotheses r h_b0 h_b1 h_e0 h_e1 with ⟨h_b0', h_b1', h_e0', h_e1'⟩
  let delta := r.next 2 - r.curr 2
  have h_sym :
      Constraints.Symbolic.System.base[9]! (toSymbolicFrame r) =
        r.isTransition * (systemPreserveSymSel r * delta) := by
    rw [getElem!_pos (h := by native_decide)]
    change (fun f =>
      f.is_transition *
        ((1 - ((((f.colCurr 9 * f.colCurr 10) * ((1 - f.colCurr 11) * f.colCurr 29)) +
            ((((1 - f.colCurr 7) * (1 - f.colCurr 8)) * f.colCurr 9) *
              (f.colCurr 10 * f.colCurr 28))) +
            (((1 - f.colCurr 9) * (1 - f.colCurr 10)) * (f.colCurr 11 * f.colCurr 29)))) *
          (f.colNext 2 - f.colCurr 2))) (toSymbolicFrame r) =
      r.isTransition * (systemPreserveSymSel r * delta)
    simp [systemPreserveSymSel, systemCallDyncallSymSel, systemEndSymSel, delta,
      toSymbolicFrame, MainWidth, SymbolicFrame.colCurr, SymbolicFrame.colNext]
  have h_can :
      Subsystems.System.fnHash0Preserve.eval r =
        r.isTransition * (systemPreserveCanSel r * delta) := by
    change r.isTransition * (Subsystems.System.preserveFlag.eval r * delta) =
      r.isTransition * (systemPreserveCanSel r * delta)
    rw [systemPreserveFlag_eval]
  rw [h_sym, h_can]
  simp [delta, systemPreserveSymSel, systemPreserveCanSel, systemCallDyncallSymSel,
    systemCallDyncallCanSel, systemEndSymSel, systemEndCanSel, h_b0', h_b1', h_e0', h_e1']
  left
  left
  ring_nf

theorem bridge_system_10 (r : AirRow)
    (h_b0 : systemLowBit0Zero r) (h_b1 : systemLowBit1Zero r)
    (h_e0 : systemExtraCol0Eq r) (h_e1 : systemExtraCol1Eq r) :
    Constraints.Symbolic.System.base[10]! (toSymbolicFrame r) =
      Subsystems.System.fnHash1Preserve.eval r := by
  rcases systemBridgeHypotheses r h_b0 h_b1 h_e0 h_e1 with ⟨h_b0', h_b1', h_e0', h_e1'⟩
  let delta := r.next 3 - r.curr 3
  have h_sym :
      Constraints.Symbolic.System.base[10]! (toSymbolicFrame r) =
        r.isTransition * (systemPreserveSymSel r * delta) := by
    rw [getElem!_pos (h := by native_decide)]
    change (fun f =>
      f.is_transition *
        ((1 - ((((f.colCurr 9 * f.colCurr 10) * ((1 - f.colCurr 11) * f.colCurr 29)) +
            ((((1 - f.colCurr 7) * (1 - f.colCurr 8)) * f.colCurr 9) *
              (f.colCurr 10 * f.colCurr 28))) +
            (((1 - f.colCurr 9) * (1 - f.colCurr 10)) * (f.colCurr 11 * f.colCurr 29)))) *
          (f.colNext 3 - f.colCurr 3))) (toSymbolicFrame r) =
      r.isTransition * (systemPreserveSymSel r * delta)
    simp [systemPreserveSymSel, systemCallDyncallSymSel, systemEndSymSel, delta,
      toSymbolicFrame, MainWidth, SymbolicFrame.colCurr, SymbolicFrame.colNext]
  have h_can :
      Subsystems.System.fnHash1Preserve.eval r =
        r.isTransition * (systemPreserveCanSel r * delta) := by
    change r.isTransition * (Subsystems.System.preserveFlag.eval r * delta) =
      r.isTransition * (systemPreserveCanSel r * delta)
    rw [systemPreserveFlag_eval]
  rw [h_sym, h_can]
  simp [delta, systemPreserveSymSel, systemPreserveCanSel, systemCallDyncallSymSel,
    systemCallDyncallCanSel, systemEndSymSel, systemEndCanSel, h_b0', h_b1', h_e0', h_e1']
  left
  left
  ring_nf

theorem bridge_system_11 (r : AirRow)
    (h_b0 : systemLowBit0Zero r) (h_b1 : systemLowBit1Zero r)
    (h_e0 : systemExtraCol0Eq r) (h_e1 : systemExtraCol1Eq r) :
    Constraints.Symbolic.System.base[11]! (toSymbolicFrame r) =
      Subsystems.System.fnHash2Preserve.eval r := by
  rcases systemBridgeHypotheses r h_b0 h_b1 h_e0 h_e1 with ⟨h_b0', h_b1', h_e0', h_e1'⟩
  let delta := r.next 4 - r.curr 4
  have h_sym :
      Constraints.Symbolic.System.base[11]! (toSymbolicFrame r) =
        r.isTransition * (systemPreserveSymSel r * delta) := by
    rw [getElem!_pos (h := by native_decide)]
    change (fun f =>
      f.is_transition *
        ((1 - ((((f.colCurr 9 * f.colCurr 10) * ((1 - f.colCurr 11) * f.colCurr 29)) +
            ((((1 - f.colCurr 7) * (1 - f.colCurr 8)) * f.colCurr 9) *
              (f.colCurr 10 * f.colCurr 28))) +
            (((1 - f.colCurr 9) * (1 - f.colCurr 10)) * (f.colCurr 11 * f.colCurr 29)))) *
          (f.colNext 4 - f.colCurr 4))) (toSymbolicFrame r) =
      r.isTransition * (systemPreserveSymSel r * delta)
    simp [systemPreserveSymSel, systemCallDyncallSymSel, systemEndSymSel, delta,
      toSymbolicFrame, MainWidth, SymbolicFrame.colCurr, SymbolicFrame.colNext]
  have h_can :
      Subsystems.System.fnHash2Preserve.eval r =
        r.isTransition * (systemPreserveCanSel r * delta) := by
    change r.isTransition * (Subsystems.System.preserveFlag.eval r * delta) =
      r.isTransition * (systemPreserveCanSel r * delta)
    rw [systemPreserveFlag_eval]
  rw [h_sym, h_can]
  simp [delta, systemPreserveSymSel, systemPreserveCanSel, systemCallDyncallSymSel,
    systemCallDyncallCanSel, systemEndSymSel, systemEndCanSel, h_b0', h_b1', h_e0', h_e1']
  left
  left
  ring_nf

theorem bridge_system_12 (r : AirRow)
    (h_b0 : systemLowBit0Zero r) (h_b1 : systemLowBit1Zero r)
    (h_e0 : systemExtraCol0Eq r) (h_e1 : systemExtraCol1Eq r) :
    Constraints.Symbolic.System.base[12]! (toSymbolicFrame r) =
      Subsystems.System.fnHash3Preserve.eval r := by
  rcases systemBridgeHypotheses r h_b0 h_b1 h_e0 h_e1 with ⟨h_b0', h_b1', h_e0', h_e1'⟩
  let delta := r.next 5 - r.curr 5
  have h_sym :
      Constraints.Symbolic.System.base[12]! (toSymbolicFrame r) =
        r.isTransition * (systemPreserveSymSel r * delta) := by
    rw [getElem!_pos (h := by native_decide)]
    change (fun f =>
      f.is_transition *
        ((1 - ((((f.colCurr 9 * f.colCurr 10) * ((1 - f.colCurr 11) * f.colCurr 29)) +
            ((((1 - f.colCurr 7) * (1 - f.colCurr 8)) * f.colCurr 9) *
              (f.colCurr 10 * f.colCurr 28))) +
            (((1 - f.colCurr 9) * (1 - f.colCurr 10)) * (f.colCurr 11 * f.colCurr 29)))) *
          (f.colNext 5 - f.colCurr 5))) (toSymbolicFrame r) =
      r.isTransition * (systemPreserveSymSel r * delta)
    simp [systemPreserveSymSel, systemCallDyncallSymSel, systemEndSymSel, delta,
      toSymbolicFrame, MainWidth, SymbolicFrame.colCurr, SymbolicFrame.colNext]
  have h_can :
      Subsystems.System.fnHash3Preserve.eval r =
        r.isTransition * (systemPreserveCanSel r * delta) := by
    change r.isTransition * (Subsystems.System.preserveFlag.eval r * delta) =
      r.isTransition * (systemPreserveCanSel r * delta)
    rw [systemPreserveFlag_eval]
  rw [h_sym, h_can]
  simp [delta, systemPreserveSymSel, systemPreserveCanSel, systemCallDyncallSymSel,
    systemCallDyncallCanSel, systemEndSymSel, systemEndCanSel, h_b0', h_b1', h_e0', h_e1']
  left
  left
  ring_nf

end MidenLean.AIR.Semantics.Refinement.SymbolicToCanonical
