import MidenLean.AIR.Semantics.Tactics
import MidenLean.AIR.Semantics.Subsystems.ChipletKernelRom
import MidenLean.AIR.Constraints.Symbolic.ChipletKernelRom

set_option maxHeartbeats 16000000

namespace MidenLean.AIR.Semantics.Refinement.SymbolicToCanonical

open MidenLean
open MidenLean.AIR
open MidenLean.AIR.Semantics
open MidenLean.AIR.Semantics.Tactics
open MidenLean.AIR.Semantics.Builder

@[simp] theorem curr_chipletKernelRom_sfirstCol_eq (r : AirRow) :
    r.curr Subsystems.ChipletKernelRom.sfirstCol = r.curr 56 := rfl

@[simp] theorem next_chipletKernelRom_sfirstCol_eq (r : AirRow) :
    r.next Subsystems.ChipletKernelRom.sfirstCol = r.next 56 := rfl

@[simp] theorem curr_chipletKernelRom_digestCol0_eq (r : AirRow) :
    r.curr (Subsystems.ChipletKernelRom.digestCol ⟨0, by decide⟩) = r.curr 57 := by
  apply congrArg r.curr
  apply Fin.ext
  native_decide

@[simp] theorem next_chipletKernelRom_digestCol0_eq (r : AirRow) :
    r.next (Subsystems.ChipletKernelRom.digestCol ⟨0, by decide⟩) = r.next 57 := by
  apply congrArg r.next
  apply Fin.ext
  native_decide

@[simp] theorem curr_chipletKernelRom_digestCol1_eq (r : AirRow) :
    r.curr (Subsystems.ChipletKernelRom.digestCol ⟨1, by decide⟩) = r.curr 58 := by
  apply congrArg r.curr
  apply Fin.ext
  native_decide

@[simp] theorem next_chipletKernelRom_digestCol1_eq (r : AirRow) :
    r.next (Subsystems.ChipletKernelRom.digestCol ⟨1, by decide⟩) = r.next 58 := by
  apply congrArg r.next
  apply Fin.ext
  native_decide

@[simp] theorem curr_chipletKernelRom_digestCol2_eq (r : AirRow) :
    r.curr (Subsystems.ChipletKernelRom.digestCol ⟨2, by decide⟩) = r.curr 59 := by
  apply congrArg r.curr
  apply Fin.ext
  native_decide

@[simp] theorem next_chipletKernelRom_digestCol2_eq (r : AirRow) :
    r.next (Subsystems.ChipletKernelRom.digestCol ⟨2, by decide⟩) = r.next 59 := by
  apply congrArg r.next
  apply Fin.ext
  native_decide

@[simp] theorem curr_chipletKernelRom_digestCol3_eq (r : AirRow) :
    r.curr (Subsystems.ChipletKernelRom.digestCol ⟨3, by decide⟩) = r.curr 60 := by
  apply congrArg r.curr
  apply Fin.ext
  native_decide

@[simp] theorem next_chipletKernelRom_digestCol3_eq (r : AirRow) :
    r.next (Subsystems.ChipletKernelRom.digestCol ⟨3, by decide⟩) = r.next 60 := by
  apply congrArg r.next
  apply Fin.ext
  native_decide

theorem bridge_chiplet_kernel_rom_0 (r : AirRow) :
    Constraints.Symbolic.ChipletKernelRom.base[0]! (toSymbolicFrame r) =
      Subsystems.ChipletKernelRom.sfirstBinary.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f =>
      ((((((f.colCurr 51 * f.colCurr 52) * f.colCurr 53) * f.colCurr 54) *
          (1 - f.colCurr 55)) * f.colCurr 56) * (f.colCurr 56 - 1)))
      (toSymbolicFrame r) = Subsystems.ChipletKernelRom.sfirstBinary.eval r
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  have h54 : 54 < MainWidth := by decide
  have h55 : 55 < MainWidth := by decide
  have h56 : 56 < MainWidth := by decide
  simp only [Subsystems.ChipletKernelRom.sfirstBinary, Subsystems.ChipletKernelRom.integrityZero,
    Subsystems.ChipletKernelRom.kernelRomFlag, Subsystems.ChipletKernelRom.sfirst,
    Subsystems.ChipletKernelRom.one, Subsystems.ChipletKernelRom.sfirstCol,
    Subsystems.ChipletKernelRom.kernelRomTraceOffset, Subsystems.ChipletKernelRom.chipletsOffset,
    Subsystems.ChipletSelectors.kernelRomChipletFlag, Subsystems.ChipletSelectors.s0123,
    Subsystems.ChipletSelectors.s012, Subsystems.ChipletSelectors.s01,
    Subsystems.ChipletSelectors.notS4, Subsystems.ChipletSelectors.s0,
    Subsystems.ChipletSelectors.s1, Subsystems.ChipletSelectors.s2,
    Subsystems.ChipletSelectors.s3, Subsystems.ChipletSelectors.s4,
    Subsystems.ChipletSelectors.s0Col, Subsystems.ChipletSelectors.s1Col,
    Subsystems.ChipletSelectors.s2Col, Subsystems.ChipletSelectors.s3Col,
    Subsystems.ChipletSelectors.s4Col, Subsystems.ChipletSelectors.chipletsOffset,
    toSymbolicFrame, FExpr.eval, Builder.gate, Builder.assertZero, BaseConstraint.eval,
    BaseConstraint.expr, AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr,
    h51, h52, h53, h54, h55, h56]
  simp
  ring_nf

theorem bridge_chiplet_kernel_rom_1 (r : AirRow) :
    Constraints.Symbolic.ChipletKernelRom.base[1]! (toSymbolicFrame r) =
      (Subsystems.ChipletKernelRom.digestContiguity ⟨0, by decide⟩).eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f =>
      f.is_transition * ((((((f.colCurr 51 * f.colCurr 52) * f.colCurr 53) *
          f.colCurr 54) * (1 - f.colCurr 55)) *
        ((1 - f.colNext 55) * (1 - f.colNext 56))) * (f.colNext 57 - f.colCurr 57)))
      (toSymbolicFrame r) = (Subsystems.ChipletKernelRom.digestContiguity ⟨0, by decide⟩).eval r
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  have h54 : 54 < MainWidth := by decide
  have h55 : 55 < MainWidth := by decide
  have h56 : 56 < MainWidth := by decide
  have h57 : 57 < MainWidth := by decide
  simp only [Subsystems.ChipletKernelRom.digestContiguity, Subsystems.ChipletKernelRom.transitionEq,
    Subsystems.ChipletKernelRom.contiguityGate, Subsystems.ChipletKernelRom.kernelRomFlag,
    Subsystems.ChipletKernelRom.oneMinus, Subsystems.ChipletKernelRom.one,
    Subsystems.ChipletKernelRom.s4Next, Subsystems.ChipletKernelRom.sfirstNext,
    Subsystems.ChipletKernelRom.digestNext, Subsystems.ChipletKernelRom.digest,
    next_chipletKernelRom_sfirstCol_eq, curr_chipletKernelRom_digestCol0_eq,
    next_chipletKernelRom_digestCol0_eq, Subsystems.ChipletSelectors.kernelRomChipletFlag,
    Subsystems.ChipletSelectors.s0123, Subsystems.ChipletSelectors.s012,
    Subsystems.ChipletSelectors.s01, Subsystems.ChipletSelectors.notS4,
    Subsystems.ChipletSelectors.s4Next, Subsystems.ChipletSelectors.s0,
    Subsystems.ChipletSelectors.s1, Subsystems.ChipletSelectors.s2,
    Subsystems.ChipletSelectors.s3, Subsystems.ChipletSelectors.s4,
    Subsystems.ChipletSelectors.s0Col, Subsystems.ChipletSelectors.s1Col,
    Subsystems.ChipletSelectors.s2Col, Subsystems.ChipletSelectors.s3Col,
    Subsystems.ChipletSelectors.s4Col, Subsystems.ChipletSelectors.chipletsOffset,
    toSymbolicFrame, FExpr.eval, Builder.whenTransition, Builder.gate,
    Builder.assertEq, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.boundary, AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr,
    SymbolicFrame.colNext, h51, h52, h53, h54, h55, h56, h57]
  simp
  ring_nf
  left
  trivial

theorem bridge_chiplet_kernel_rom_2 (r : AirRow) :
    Constraints.Symbolic.ChipletKernelRom.base[2]! (toSymbolicFrame r) =
      (Subsystems.ChipletKernelRom.digestContiguity ⟨1, by decide⟩).eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f =>
      f.is_transition * ((((((f.colCurr 51 * f.colCurr 52) * f.colCurr 53) *
          f.colCurr 54) * (1 - f.colCurr 55)) *
        ((1 - f.colNext 55) * (1 - f.colNext 56))) * (f.colNext 58 - f.colCurr 58)))
      (toSymbolicFrame r) = (Subsystems.ChipletKernelRom.digestContiguity ⟨1, by decide⟩).eval r
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  have h54 : 54 < MainWidth := by decide
  have h55 : 55 < MainWidth := by decide
  have h56 : 56 < MainWidth := by decide
  have h58 : 58 < MainWidth := by decide
  simp only [Subsystems.ChipletKernelRom.digestContiguity, Subsystems.ChipletKernelRom.transitionEq,
    Subsystems.ChipletKernelRom.contiguityGate, Subsystems.ChipletKernelRom.kernelRomFlag,
    Subsystems.ChipletKernelRom.oneMinus, Subsystems.ChipletKernelRom.one,
    Subsystems.ChipletKernelRom.s4Next, Subsystems.ChipletKernelRom.sfirstNext,
    Subsystems.ChipletKernelRom.digestNext, Subsystems.ChipletKernelRom.digest,
    next_chipletKernelRom_sfirstCol_eq, curr_chipletKernelRom_digestCol1_eq,
    next_chipletKernelRom_digestCol1_eq, Subsystems.ChipletSelectors.kernelRomChipletFlag,
    Subsystems.ChipletSelectors.s0123, Subsystems.ChipletSelectors.s012,
    Subsystems.ChipletSelectors.s01, Subsystems.ChipletSelectors.notS4,
    Subsystems.ChipletSelectors.s4Next, Subsystems.ChipletSelectors.s0,
    Subsystems.ChipletSelectors.s1, Subsystems.ChipletSelectors.s2,
    Subsystems.ChipletSelectors.s3, Subsystems.ChipletSelectors.s4,
    Subsystems.ChipletSelectors.s0Col, Subsystems.ChipletSelectors.s1Col,
    Subsystems.ChipletSelectors.s2Col, Subsystems.ChipletSelectors.s3Col,
    Subsystems.ChipletSelectors.s4Col, Subsystems.ChipletSelectors.chipletsOffset,
    toSymbolicFrame, FExpr.eval, Builder.whenTransition, Builder.gate,
    Builder.assertEq, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.boundary, AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr,
    SymbolicFrame.colNext, h51, h52, h53, h54, h55, h56, h58]
  simp
  ring_nf
  left
  trivial

theorem bridge_chiplet_kernel_rom_3 (r : AirRow) :
    Constraints.Symbolic.ChipletKernelRom.base[3]! (toSymbolicFrame r) =
      (Subsystems.ChipletKernelRom.digestContiguity ⟨2, by decide⟩).eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f =>
      f.is_transition * ((((((f.colCurr 51 * f.colCurr 52) * f.colCurr 53) *
          f.colCurr 54) * (1 - f.colCurr 55)) *
        ((1 - f.colNext 55) * (1 - f.colNext 56))) * (f.colNext 59 - f.colCurr 59)))
      (toSymbolicFrame r) = (Subsystems.ChipletKernelRom.digestContiguity ⟨2, by decide⟩).eval r
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  have h54 : 54 < MainWidth := by decide
  have h55 : 55 < MainWidth := by decide
  have h56 : 56 < MainWidth := by decide
  have h59 : 59 < MainWidth := by decide
  simp only [Subsystems.ChipletKernelRom.digestContiguity, Subsystems.ChipletKernelRom.transitionEq,
    Subsystems.ChipletKernelRom.contiguityGate, Subsystems.ChipletKernelRom.kernelRomFlag,
    Subsystems.ChipletKernelRom.oneMinus, Subsystems.ChipletKernelRom.one,
    Subsystems.ChipletKernelRom.s4Next, Subsystems.ChipletKernelRom.sfirstNext,
    Subsystems.ChipletKernelRom.digestNext, Subsystems.ChipletKernelRom.digest,
    next_chipletKernelRom_sfirstCol_eq, curr_chipletKernelRom_digestCol2_eq,
    next_chipletKernelRom_digestCol2_eq, Subsystems.ChipletSelectors.kernelRomChipletFlag,
    Subsystems.ChipletSelectors.s0123, Subsystems.ChipletSelectors.s012,
    Subsystems.ChipletSelectors.s01, Subsystems.ChipletSelectors.notS4,
    Subsystems.ChipletSelectors.s4Next, Subsystems.ChipletSelectors.s0,
    Subsystems.ChipletSelectors.s1, Subsystems.ChipletSelectors.s2,
    Subsystems.ChipletSelectors.s3, Subsystems.ChipletSelectors.s4,
    Subsystems.ChipletSelectors.s0Col, Subsystems.ChipletSelectors.s1Col,
    Subsystems.ChipletSelectors.s2Col, Subsystems.ChipletSelectors.s3Col,
    Subsystems.ChipletSelectors.s4Col, Subsystems.ChipletSelectors.chipletsOffset,
    toSymbolicFrame, FExpr.eval, Builder.whenTransition, Builder.gate,
    Builder.assertEq, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.boundary, AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr,
    SymbolicFrame.colNext, h51, h52, h53, h54, h55, h56, h59]
  simp
  ring_nf
  left
  trivial

theorem bridge_chiplet_kernel_rom_4 (r : AirRow) :
    Constraints.Symbolic.ChipletKernelRom.base[4]! (toSymbolicFrame r) =
      (Subsystems.ChipletKernelRom.digestContiguity ⟨3, by decide⟩).eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f =>
      f.is_transition * ((((((f.colCurr 51 * f.colCurr 52) * f.colCurr 53) *
          f.colCurr 54) * (1 - f.colCurr 55)) *
        ((1 - f.colNext 55) * (1 - f.colNext 56))) * (f.colNext 60 - f.colCurr 60)))
      (toSymbolicFrame r) = (Subsystems.ChipletKernelRom.digestContiguity ⟨3, by decide⟩).eval r
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  have h54 : 54 < MainWidth := by decide
  have h55 : 55 < MainWidth := by decide
  have h56 : 56 < MainWidth := by decide
  have h60 : 60 < MainWidth := by decide
  simp only [Subsystems.ChipletKernelRom.digestContiguity, Subsystems.ChipletKernelRom.transitionEq,
    Subsystems.ChipletKernelRom.contiguityGate, Subsystems.ChipletKernelRom.kernelRomFlag,
    Subsystems.ChipletKernelRom.oneMinus, Subsystems.ChipletKernelRom.one,
    Subsystems.ChipletKernelRom.s4Next, Subsystems.ChipletKernelRom.sfirstNext,
    Subsystems.ChipletKernelRom.digestNext, Subsystems.ChipletKernelRom.digest,
    next_chipletKernelRom_sfirstCol_eq, curr_chipletKernelRom_digestCol3_eq,
    next_chipletKernelRom_digestCol3_eq, Subsystems.ChipletSelectors.kernelRomChipletFlag,
    Subsystems.ChipletSelectors.s0123, Subsystems.ChipletSelectors.s012,
    Subsystems.ChipletSelectors.s01, Subsystems.ChipletSelectors.notS4,
    Subsystems.ChipletSelectors.s4Next, Subsystems.ChipletSelectors.s0,
    Subsystems.ChipletSelectors.s1, Subsystems.ChipletSelectors.s2,
    Subsystems.ChipletSelectors.s3, Subsystems.ChipletSelectors.s4,
    Subsystems.ChipletSelectors.s0Col, Subsystems.ChipletSelectors.s1Col,
    Subsystems.ChipletSelectors.s2Col, Subsystems.ChipletSelectors.s3Col,
    Subsystems.ChipletSelectors.s4Col, Subsystems.ChipletSelectors.chipletsOffset,
    toSymbolicFrame, FExpr.eval, Builder.whenTransition, Builder.gate,
    Builder.assertEq, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.boundary, AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr,
    SymbolicFrame.colNext, h51, h52, h53, h54, h55, h56, h60]
  simp
  ring_nf
  left
  trivial

theorem bridge_chiplet_kernel_rom_5 (r : AirRow) :
    Constraints.Symbolic.ChipletKernelRom.base[5]! (toSymbolicFrame r) =
      Subsystems.ChipletKernelRom.firstRowStart.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f =>
      f.is_transition * (((((f.colCurr 51 * f.colCurr 52) * f.colCurr 53) *
          (1 - f.colCurr 54)) * (f.colNext 54 * (1 - f.colNext 55))) *
        (f.colNext 56 - 1)))
      (toSymbolicFrame r) = Subsystems.ChipletKernelRom.firstRowStart.eval r
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  have h54 : 54 < MainWidth := by decide
  have h55 : 55 < MainWidth := by decide
  have h56 : 56 < MainWidth := by decide
  simp only [Subsystems.ChipletKernelRom.firstRowStart, Subsystems.ChipletKernelRom.transitionEq,
    Subsystems.ChipletKernelRom.flagNextRowFirstKernelRom, Subsystems.ChipletKernelRom.aceFlag,
    Subsystems.ChipletKernelRom.kernelRomNext, Subsystems.ChipletKernelRom.oneMinus,
    Subsystems.ChipletKernelRom.one, Subsystems.ChipletKernelRom.s3Next,
    Subsystems.ChipletKernelRom.s4Next, Subsystems.ChipletKernelRom.sfirstNext,
    next_chipletKernelRom_sfirstCol_eq, Subsystems.ChipletSelectors.aceChipletFlag,
    Subsystems.ChipletSelectors.s012, Subsystems.ChipletSelectors.s01,
    Subsystems.ChipletSelectors.notS3, Subsystems.ChipletSelectors.s3Next,
    Subsystems.ChipletSelectors.s4Next, Subsystems.ChipletSelectors.s0,
    Subsystems.ChipletSelectors.s1, Subsystems.ChipletSelectors.s2,
    Subsystems.ChipletSelectors.s3, Subsystems.ChipletSelectors.s0Col,
    Subsystems.ChipletSelectors.s1Col, Subsystems.ChipletSelectors.s2Col,
    Subsystems.ChipletSelectors.s3Col, Subsystems.ChipletSelectors.s4Col,
    Subsystems.ChipletSelectors.chipletsOffset, toSymbolicFrame, FExpr.eval,
    Builder.whenTransition, Builder.gate, Builder.assertEq, Builder.assertZero,
    BaseConstraint.eval, BaseConstraint.expr, AirRow.boundary, AirRow.baseAt, AirRow.base,
    SymbolicFrame.colCurr, SymbolicFrame.colNext, h51, h52, h53, h54, h55, h56]
  simp
  ring_nf
  left
  left
  exact next_chipletKernelRom_sfirstCol_eq r

end MidenLean.AIR.Semantics.Refinement.SymbolicToCanonical
