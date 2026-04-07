import MidenLean.AIR.Semantics.Tactics
import MidenLean.AIR.Semantics.Subsystems.ChipletBitwise
import MidenLean.AIR.Constraints.Symbolic.ChipletBitwise

set_option maxHeartbeats 16000000

namespace MidenLean.AIR.Semantics.Refinement.SymbolicToCanonical

open MidenLean
open MidenLean.AIR
open MidenLean.AIR.Semantics
open MidenLean.AIR.Semantics.Tactics
open MidenLean.AIR.Semantics.Builder

private abbrev bit0 : Subsystems.ChipletBitwise.BitIndex := ⟨0, by decide⟩
private abbrev bit1 : Subsystems.ChipletBitwise.BitIndex := ⟨1, by decide⟩
private abbrev bit2 : Subsystems.ChipletBitwise.BitIndex := ⟨2, by decide⟩
private abbrev bit3 : Subsystems.ChipletBitwise.BitIndex := ⟨3, by decide⟩

@[simp] theorem curr_51_any_eq (r : AirRow) (h : 51 < MainWidth) :
    r.curr ⟨51, h⟩ = r.curr 51 := rfl

@[simp] theorem curr_52_any_eq (r : AirRow) (h : 52 < MainWidth) :
    r.curr ⟨52, h⟩ = r.curr 52 := rfl

@[simp] theorem curr_53_any_eq (r : AirRow) (h : 53 < MainWidth) :
    r.curr ⟨53, h⟩ = r.curr 53 := rfl

@[simp] theorem next_53_any_eq (r : AirRow) (h : 53 < MainWidth) :
    r.next ⟨53, h⟩ = r.next 53 := rfl

@[simp] theorem curr_54_any_eq (r : AirRow) (h : 54 < MainWidth) :
    r.curr ⟨54, h⟩ = r.curr 54 := rfl

@[simp] theorem curr_55_any_eq (r : AirRow) (h : 55 < MainWidth) :
    r.curr ⟨55, h⟩ = r.curr 55 := rfl

@[simp] theorem curr_56_any_eq (r : AirRow) (h : 56 < MainWidth) :
    r.curr ⟨56, h⟩ = r.curr 56 := rfl

@[simp] theorem curr_57_any_eq (r : AirRow) (h : 57 < MainWidth) :
    r.curr ⟨57, h⟩ = r.curr 57 := rfl

@[simp] theorem curr_58_any_eq (r : AirRow) (h : 58 < MainWidth) :
    r.curr ⟨58, h⟩ = r.curr 58 := rfl

@[simp] theorem curr_59_any_eq (r : AirRow) (h : 59 < MainWidth) :
    r.curr ⟨59, h⟩ = r.curr 59 := rfl

@[simp] theorem curr_60_any_eq (r : AirRow) (h : 60 < MainWidth) :
    r.curr ⟨60, h⟩ = r.curr 60 := rfl

@[simp] theorem curr_61_any_eq (r : AirRow) (h : 61 < MainWidth) :
    r.curr ⟨61, h⟩ = r.curr 61 := rfl

@[simp] theorem curr_62_any_eq (r : AirRow) (h : 62 < MainWidth) :
    r.curr ⟨62, h⟩ = r.curr 62 := rfl

@[simp] theorem curr_63_any_eq (r : AirRow) (h : 63 < MainWidth) :
    r.curr ⟨63, h⟩ = r.curr 63 := rfl

@[simp] theorem curr_64_any_eq (r : AirRow) (h : 64 < MainWidth) :
    r.curr ⟨64, h⟩ = r.curr 64 := rfl

@[simp] theorem next_64_any_eq (r : AirRow) (h : 64 < MainWidth) :
    r.next ⟨64, h⟩ = r.next 64 := rfl

@[simp] theorem curr_65_any_eq (r : AirRow) (h : 65 < MainWidth) :
    r.curr ⟨65, h⟩ = r.curr 65 := rfl

@[simp] theorem next_54_any_eq (r : AirRow) (h : 54 < MainWidth) :
    r.next ⟨54, h⟩ = r.next 54 := rfl

@[simp] theorem next_55_any_eq (r : AirRow) (h : 55 < MainWidth) :
    r.next ⟨55, h⟩ = r.next 55 := rfl

@[simp] theorem next_56_any_eq (r : AirRow) (h : 56 < MainWidth) :
    r.next ⟨56, h⟩ = r.next 56 := rfl

@[simp] theorem next_57_any_eq (r : AirRow) (h : 57 < MainWidth) :
    r.next ⟨57, h⟩ = r.next 57 := rfl

@[simp] theorem next_58_any_eq (r : AirRow) (h : 58 < MainWidth) :
    r.next ⟨58, h⟩ = r.next 58 := rfl

@[simp] theorem next_59_any_eq (r : AirRow) (h : 59 < MainWidth) :
    r.next ⟨59, h⟩ = r.next 59 := rfl

@[simp] theorem next_60_any_eq (r : AirRow) (h : 60 < MainWidth) :
    r.next ⟨60, h⟩ = r.next 60 := rfl

@[simp] theorem next_61_any_eq (r : AirRow) (h : 61 < MainWidth) :
    r.next ⟨61, h⟩ = r.next 61 := rfl

@[simp] theorem next_62_any_eq (r : AirRow) (h : 62 < MainWidth) :
    r.next ⟨62, h⟩ = r.next 62 := rfl

@[simp] theorem next_63_any_eq (r : AirRow) (h : 63 < MainWidth) :
    r.next ⟨63, h⟩ = r.next 63 := rfl

@[simp] theorem periodic_18_any_eq (g : AirGlobals) (h : 18 < PeriodicWidth) :
    g.periodic ⟨18, h⟩ = g.periodic 18 := rfl

@[simp] theorem periodic_19_any_eq (g : AirGlobals) (h : 19 < PeriodicWidth) :
    g.periodic ⟨19, h⟩ = g.periodic 19 := rfl

@[simp] theorem toSymbolicFrame_colCurr_51_eq (r : AirRow) :
    (toSymbolicFrame r).colCurr 51 = r.curr 51 := by
  have h51 : 51 < MainWidth := by decide
  simp [SymbolicFrame.colCurr, toSymbolicFrame, h51]

@[simp] theorem toSymbolicFrame_colCurr_52_eq (r : AirRow) :
    (toSymbolicFrame r).colCurr 52 = r.curr 52 := by
  have h52 : 52 < MainWidth := by decide
  simp [SymbolicFrame.colCurr, toSymbolicFrame, h52]

@[simp] theorem toSymbolicFrame_colCurr_53_eq (r : AirRow) :
    (toSymbolicFrame r).colCurr 53 = r.curr 53 := by
  have h53 : 53 < MainWidth := by decide
  simp [SymbolicFrame.colCurr, toSymbolicFrame, h53]

@[simp] theorem toSymbolicFrame_colCurr_54_eq (r : AirRow) :
    (toSymbolicFrame r).colCurr 54 = r.curr 54 := by
  have h54 : 54 < MainWidth := by decide
  simp [SymbolicFrame.colCurr, toSymbolicFrame, h54]

@[simp] theorem toSymbolicFrame_colCurr_55_eq (r : AirRow) :
    (toSymbolicFrame r).colCurr 55 = r.curr 55 := by
  have h55 : 55 < MainWidth := by decide
  simp [SymbolicFrame.colCurr, toSymbolicFrame, h55]

@[simp] theorem toSymbolicFrame_colCurr_56_eq (r : AirRow) :
    (toSymbolicFrame r).colCurr 56 = r.curr 56 := by
  have h56 : 56 < MainWidth := by decide
  simp [SymbolicFrame.colCurr, toSymbolicFrame, h56]

@[simp] theorem toSymbolicFrame_colCurr_57_eq (r : AirRow) :
    (toSymbolicFrame r).colCurr 57 = r.curr 57 := by
  have h57 : 57 < MainWidth := by decide
  simp [SymbolicFrame.colCurr, toSymbolicFrame, h57]

@[simp] theorem toSymbolicFrame_colCurr_58_eq (r : AirRow) :
    (toSymbolicFrame r).colCurr 58 = r.curr 58 := by
  have h58 : 58 < MainWidth := by decide
  simp [SymbolicFrame.colCurr, toSymbolicFrame, h58]

@[simp] theorem toSymbolicFrame_colCurr_59_eq (r : AirRow) :
    (toSymbolicFrame r).colCurr 59 = r.curr 59 := by
  have h59 : 59 < MainWidth := by decide
  simp [SymbolicFrame.colCurr, toSymbolicFrame, h59]

@[simp] theorem toSymbolicFrame_colCurr_60_eq (r : AirRow) :
    (toSymbolicFrame r).colCurr 60 = r.curr 60 := by
  have h60 : 60 < MainWidth := by decide
  simp [SymbolicFrame.colCurr, toSymbolicFrame, h60]

@[simp] theorem toSymbolicFrame_colCurr_61_eq (r : AirRow) :
    (toSymbolicFrame r).colCurr 61 = r.curr 61 := by
  have h61 : 61 < MainWidth := by decide
  simp [SymbolicFrame.colCurr, toSymbolicFrame, h61]

@[simp] theorem toSymbolicFrame_colCurr_62_eq (r : AirRow) :
    (toSymbolicFrame r).colCurr 62 = r.curr 62 := by
  have h62 : 62 < MainWidth := by decide
  simp [SymbolicFrame.colCurr, toSymbolicFrame, h62]

@[simp] theorem toSymbolicFrame_colCurr_63_eq (r : AirRow) :
    (toSymbolicFrame r).colCurr 63 = r.curr 63 := by
  have h63 : 63 < MainWidth := by decide
  simp [SymbolicFrame.colCurr, toSymbolicFrame, h63]

@[simp] theorem toSymbolicFrame_colCurr_64_eq (r : AirRow) :
    (toSymbolicFrame r).colCurr 64 = r.curr 64 := by
  have h64 : 64 < MainWidth := by decide
  simp [SymbolicFrame.colCurr, toSymbolicFrame, h64]

@[simp] theorem toSymbolicFrame_colCurr_65_eq (r : AirRow) :
    (toSymbolicFrame r).colCurr 65 = r.curr 65 := by
  have h65 : 65 < MainWidth := by decide
  simp [SymbolicFrame.colCurr, toSymbolicFrame, h65]

@[simp] theorem toSymbolicFrame_colNext_53_eq (r : AirRow) :
    (toSymbolicFrame r).colNext 53 = r.next 53 := by
  have h53 : 53 < MainWidth := by decide
  simp [SymbolicFrame.colNext, toSymbolicFrame, h53]

@[simp] theorem toSymbolicFrame_colNext_54_eq (r : AirRow) :
    (toSymbolicFrame r).colNext 54 = r.next 54 := by
  have h54 : 54 < MainWidth := by decide
  simp [SymbolicFrame.colNext, toSymbolicFrame, h54]

@[simp] theorem toSymbolicFrame_colNext_55_eq (r : AirRow) :
    (toSymbolicFrame r).colNext 55 = r.next 55 := by
  have h55 : 55 < MainWidth := by decide
  simp [SymbolicFrame.colNext, toSymbolicFrame, h55]

@[simp] theorem toSymbolicFrame_colNext_56_eq (r : AirRow) :
    (toSymbolicFrame r).colNext 56 = r.next 56 := by
  have h56 : 56 < MainWidth := by decide
  simp [SymbolicFrame.colNext, toSymbolicFrame, h56]

@[simp] theorem toSymbolicFrame_colNext_57_eq (r : AirRow) :
    (toSymbolicFrame r).colNext 57 = r.next 57 := by
  have h57 : 57 < MainWidth := by decide
  simp [SymbolicFrame.colNext, toSymbolicFrame, h57]

@[simp] theorem toSymbolicFrame_colNext_58_eq (r : AirRow) :
    (toSymbolicFrame r).colNext 58 = r.next 58 := by
  have h58 : 58 < MainWidth := by decide
  simp [SymbolicFrame.colNext, toSymbolicFrame, h58]

@[simp] theorem toSymbolicFrame_colNext_59_eq (r : AirRow) :
    (toSymbolicFrame r).colNext 59 = r.next 59 := by
  have h59 : 59 < MainWidth := by decide
  simp [SymbolicFrame.colNext, toSymbolicFrame, h59]

@[simp] theorem toSymbolicFrame_colNext_60_eq (r : AirRow) :
    (toSymbolicFrame r).colNext 60 = r.next 60 := by
  have h60 : 60 < MainWidth := by decide
  simp [SymbolicFrame.colNext, toSymbolicFrame, h60]

@[simp] theorem toSymbolicFrame_colNext_61_eq (r : AirRow) :
    (toSymbolicFrame r).colNext 61 = r.next 61 := by
  have h61 : 61 < MainWidth := by decide
  simp [SymbolicFrame.colNext, toSymbolicFrame, h61]

@[simp] theorem toSymbolicFrame_colNext_62_eq (r : AirRow) :
    (toSymbolicFrame r).colNext 62 = r.next 62 := by
  have h62 : 62 < MainWidth := by decide
  simp [SymbolicFrame.colNext, toSymbolicFrame, h62]

@[simp] theorem toSymbolicFrame_colNext_63_eq (r : AirRow) :
    (toSymbolicFrame r).colNext 63 = r.next 63 := by
  have h63 : 63 < MainWidth := by decide
  simp [SymbolicFrame.colNext, toSymbolicFrame, h63]

@[simp] theorem toSymbolicFrame_colNext_64_eq (r : AirRow) :
    (toSymbolicFrame r).colNext 64 = r.next 64 := by
  have h64 : 64 < MainWidth := by decide
  simp [SymbolicFrame.colNext, toSymbolicFrame, h64]

@[simp] theorem toSymbolicFrame_periodic_18_eq (r : AirRow) :
    (toSymbolicFrame r).periodic 18 = r.globals.periodic 18 := by
  have h18 : 18 < PeriodicWidth := by decide
  simp [toSymbolicFrame, h18]

@[simp] theorem toSymbolicFrame_periodic_19_eq (r : AirRow) :
    (toSymbolicFrame r).periodic 19 = r.globals.periodic 19 := by
  have h19 : 19 < PeriodicWidth := by decide
  simp [toSymbolicFrame, h19]

@[simp] theorem curr_chipletSelectors_s0Col_eq (r : AirRow) :
    r.curr Subsystems.ChipletSelectors.s0Col = r.curr 51 := rfl

@[simp] theorem next_chipletSelectors_s0Col_eq (r : AirRow) :
    r.next Subsystems.ChipletSelectors.s0Col = r.next 51 := rfl

@[simp] theorem curr_chipletSelectors_s1Col_eq (r : AirRow) :
    r.curr Subsystems.ChipletSelectors.s1Col = r.curr 52 := rfl

@[simp] theorem next_chipletSelectors_s1Col_eq (r : AirRow) :
    r.next Subsystems.ChipletSelectors.s1Col = r.next 52 := rfl

@[simp] theorem curr_chipletBitwise_opFlagCol_eq (r : AirRow) :
    r.curr Subsystems.ChipletBitwise.opFlagCol = r.curr 53 := rfl

@[simp] theorem next_chipletBitwise_opFlagCol_eq (r : AirRow) :
    r.next Subsystems.ChipletBitwise.opFlagCol = r.next 53 := rfl

@[simp] theorem curr_chipletBitwise_aCol_eq (r : AirRow) :
    r.curr Subsystems.ChipletBitwise.aCol = r.curr 54 := rfl

@[simp] theorem next_chipletBitwise_aCol_eq (r : AirRow) :
    r.next Subsystems.ChipletBitwise.aCol = r.next 54 := rfl

@[simp] theorem curr_chipletBitwise_bCol_eq (r : AirRow) :
    r.curr Subsystems.ChipletBitwise.bCol = r.curr 55 := rfl

@[simp] theorem next_chipletBitwise_bCol_eq (r : AirRow) :
    r.next Subsystems.ChipletBitwise.bCol = r.next 55 := rfl

@[simp] theorem curr_chipletBitwise_aBit0Col_eq (r : AirRow) :
    r.curr (Subsystems.ChipletBitwise.aBitCol bit0) = r.curr 56 := rfl

@[simp] theorem next_chipletBitwise_aBit0Col_eq (r : AirRow) :
    r.next (Subsystems.ChipletBitwise.aBitCol bit0) = r.next 56 := rfl

@[simp] theorem curr_chipletBitwise_aBit1Col_eq (r : AirRow) :
    r.curr (Subsystems.ChipletBitwise.aBitCol bit1) = r.curr 57 := rfl

@[simp] theorem next_chipletBitwise_aBit1Col_eq (r : AirRow) :
    r.next (Subsystems.ChipletBitwise.aBitCol bit1) = r.next 57 := rfl

@[simp] theorem curr_chipletBitwise_aBit2Col_eq (r : AirRow) :
    r.curr (Subsystems.ChipletBitwise.aBitCol bit2) = r.curr 58 := rfl

@[simp] theorem next_chipletBitwise_aBit2Col_eq (r : AirRow) :
    r.next (Subsystems.ChipletBitwise.aBitCol bit2) = r.next 58 := rfl

@[simp] theorem curr_chipletBitwise_aBit3Col_eq (r : AirRow) :
    r.curr (Subsystems.ChipletBitwise.aBitCol bit3) = r.curr 59 := rfl

@[simp] theorem next_chipletBitwise_aBit3Col_eq (r : AirRow) :
    r.next (Subsystems.ChipletBitwise.aBitCol bit3) = r.next 59 := rfl

@[simp] theorem curr_chipletBitwise_aBitCol0_num_eq (r : AirRow) :
    r.curr (Subsystems.ChipletBitwise.aBitCol 0) = r.curr 56 := by
  apply congrArg r.curr
  apply Fin.ext
  native_decide

@[simp] theorem next_chipletBitwise_aBitCol0_num_eq (r : AirRow) :
    r.next (Subsystems.ChipletBitwise.aBitCol 0) = r.next 56 := by
  apply congrArg r.next
  apply Fin.ext
  native_decide

@[simp] theorem curr_chipletBitwise_aBitCol1_num_eq (r : AirRow) :
    r.curr (Subsystems.ChipletBitwise.aBitCol 1) = r.curr 57 := by
  apply congrArg r.curr
  apply Fin.ext
  native_decide

@[simp] theorem next_chipletBitwise_aBitCol1_num_eq (r : AirRow) :
    r.next (Subsystems.ChipletBitwise.aBitCol 1) = r.next 57 := by
  apply congrArg r.next
  apply Fin.ext
  native_decide

@[simp] theorem curr_chipletBitwise_aBitCol2_num_eq (r : AirRow) :
    r.curr (Subsystems.ChipletBitwise.aBitCol 2) = r.curr 58 := by
  apply congrArg r.curr
  apply Fin.ext
  native_decide

@[simp] theorem next_chipletBitwise_aBitCol2_num_eq (r : AirRow) :
    r.next (Subsystems.ChipletBitwise.aBitCol 2) = r.next 58 := by
  apply congrArg r.next
  apply Fin.ext
  native_decide

@[simp] theorem curr_chipletBitwise_aBitCol3_num_eq (r : AirRow) :
    r.curr (Subsystems.ChipletBitwise.aBitCol 3) = r.curr 59 := by
  apply congrArg r.curr
  apply Fin.ext
  native_decide

@[simp] theorem next_chipletBitwise_aBitCol3_num_eq (r : AirRow) :
    r.next (Subsystems.ChipletBitwise.aBitCol 3) = r.next 59 := by
  apply congrArg r.next
  apply Fin.ext
  native_decide

@[simp] theorem curr_chipletBitwise_bBit0Col_eq (r : AirRow) :
    r.curr (Subsystems.ChipletBitwise.bBitCol bit0) = r.curr 60 := rfl

@[simp] theorem next_chipletBitwise_bBit0Col_eq (r : AirRow) :
    r.next (Subsystems.ChipletBitwise.bBitCol bit0) = r.next 60 := rfl

@[simp] theorem curr_chipletBitwise_bBit1Col_eq (r : AirRow) :
    r.curr (Subsystems.ChipletBitwise.bBitCol bit1) = r.curr 61 := rfl

@[simp] theorem next_chipletBitwise_bBit1Col_eq (r : AirRow) :
    r.next (Subsystems.ChipletBitwise.bBitCol bit1) = r.next 61 := rfl

@[simp] theorem curr_chipletBitwise_bBit2Col_eq (r : AirRow) :
    r.curr (Subsystems.ChipletBitwise.bBitCol bit2) = r.curr 62 := rfl

@[simp] theorem next_chipletBitwise_bBit2Col_eq (r : AirRow) :
    r.next (Subsystems.ChipletBitwise.bBitCol bit2) = r.next 62 := rfl

@[simp] theorem curr_chipletBitwise_bBit3Col_eq (r : AirRow) :
    r.curr (Subsystems.ChipletBitwise.bBitCol bit3) = r.curr 63 := rfl

@[simp] theorem next_chipletBitwise_bBit3Col_eq (r : AirRow) :
    r.next (Subsystems.ChipletBitwise.bBitCol bit3) = r.next 63 := rfl

@[simp] theorem curr_chipletBitwise_bBitCol0_num_eq (r : AirRow) :
    r.curr (Subsystems.ChipletBitwise.bBitCol 0) = r.curr 60 := by
  apply congrArg r.curr
  apply Fin.ext
  native_decide

@[simp] theorem next_chipletBitwise_bBitCol0_num_eq (r : AirRow) :
    r.next (Subsystems.ChipletBitwise.bBitCol 0) = r.next 60 := by
  apply congrArg r.next
  apply Fin.ext
  native_decide

@[simp] theorem curr_chipletBitwise_bBitCol1_num_eq (r : AirRow) :
    r.curr (Subsystems.ChipletBitwise.bBitCol 1) = r.curr 61 := by
  apply congrArg r.curr
  apply Fin.ext
  native_decide

@[simp] theorem next_chipletBitwise_bBitCol1_num_eq (r : AirRow) :
    r.next (Subsystems.ChipletBitwise.bBitCol 1) = r.next 61 := by
  apply congrArg r.next
  apply Fin.ext
  native_decide

@[simp] theorem curr_chipletBitwise_bBitCol2_num_eq (r : AirRow) :
    r.curr (Subsystems.ChipletBitwise.bBitCol 2) = r.curr 62 := by
  apply congrArg r.curr
  apply Fin.ext
  native_decide

@[simp] theorem next_chipletBitwise_bBitCol2_num_eq (r : AirRow) :
    r.next (Subsystems.ChipletBitwise.bBitCol 2) = r.next 62 := by
  apply congrArg r.next
  apply Fin.ext
  native_decide

@[simp] theorem curr_chipletBitwise_bBitCol3_num_eq (r : AirRow) :
    r.curr (Subsystems.ChipletBitwise.bBitCol 3) = r.curr 63 := by
  apply congrArg r.curr
  apply Fin.ext
  native_decide

@[simp] theorem next_chipletBitwise_bBitCol3_num_eq (r : AirRow) :
    r.next (Subsystems.ChipletBitwise.bBitCol 3) = r.next 63 := by
  apply congrArg r.next
  apply Fin.ext
  native_decide

@[simp] theorem curr_chipletBitwise_prevOutputCol_eq (r : AirRow) :
    r.curr Subsystems.ChipletBitwise.prevOutputCol = r.curr 64 := rfl

@[simp] theorem next_chipletBitwise_prevOutputCol_eq (r : AirRow) :
    r.next Subsystems.ChipletBitwise.prevOutputCol = r.next 64 := rfl

@[simp] theorem curr_chipletBitwise_outputCol_eq (r : AirRow) :
    r.curr Subsystems.ChipletBitwise.outputCol = r.curr 65 := rfl

@[simp] theorem periodic_chipletBitwise_pBitwiseKFirst_eq (r : AirRow) :
    r.periodic Subsystems.ChipletBitwise.pBitwiseKFirst = r.globals.periodic 18 := rfl

@[simp] theorem periodic_chipletBitwise_pBitwiseKTransition_eq (r : AirRow) :
    r.periodic Subsystems.ChipletBitwise.pBitwiseKTransition = r.globals.periodic 19 := rfl

@[simp] theorem eval_chipletSelectors_notS1 (r : AirRow) :
    Subsystems.ChipletSelectors.notS1.eval r = 1 - r.curr 52 := by
  have h52 : 52 < MainWidth := by decide
  simp [Subsystems.ChipletSelectors.notS1, Subsystems.ChipletSelectors.s1,
    FExpr.eval, AirRow.baseAt, AirRow.base, h52]

@[simp] theorem eval_chipletBitwise_bitwiseFlag (r : AirRow) :
    Subsystems.ChipletBitwise.bitwiseFlag.eval r = r.curr 51 * (1 - r.curr 52) := by
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  simp [Subsystems.ChipletBitwise.bitwiseFlag, Subsystems.ChipletSelectors.bitwiseChipletFlag,
    Subsystems.ChipletSelectors.s0, Subsystems.ChipletSelectors.notS1,
    Subsystems.ChipletSelectors.s1, FExpr.eval, AirRow.baseAt, AirRow.base, h51, h52]

@[simp] theorem eval_chipletBitwise_gateFirst (r : AirRow) :
    Subsystems.ChipletBitwise.gateFirst.eval r =
      r.globals.periodic 18 * (r.curr 51 * (1 - r.curr 52)) := by
  have h18 : 18 < PeriodicWidth := by decide
  simp [Subsystems.ChipletBitwise.gateFirst, Subsystems.ChipletBitwise.kFirst, FExpr.eval,
    AirRow.periodicAt, AirRow.periodic, h18]

@[simp] theorem eval_chipletBitwise_gateTransition (r : AirRow) :
    Subsystems.ChipletBitwise.gateTransition.eval r =
      r.globals.periodic 19 * (r.curr 51 * (1 - r.curr 52)) := by
  have h19 : 19 < PeriodicWidth := by decide
  simp [Subsystems.ChipletBitwise.gateTransition, Subsystems.ChipletBitwise.kTransition,
    FExpr.eval, AirRow.periodicAt, AirRow.periodic, h19]

theorem bridge_chiplet_bitwise_0 (r : AirRow) :
    Constraints.Symbolic.ChipletBitwise.base[0]! (toSymbolicFrame r) =
      Subsystems.ChipletBitwise.opFlagBinary.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  simp only [Constraints.Symbolic.ChipletBitwise.base,
    List.getElem_cons_zero, List.getElem_cons_succ,
    toSymbolicFrame_colCurr_51_eq, toSymbolicFrame_colCurr_52_eq,
    toSymbolicFrame_colCurr_53_eq,
    Subsystems.ChipletBitwise.opFlagBinary, Subsystems.ChipletBitwise.integrityZero,
    Subsystems.ChipletBitwise.opFlag, Subsystems.ChipletBitwise.one,
    curr_chipletSelectors_s0Col_eq, curr_chipletSelectors_s1Col_eq,
    curr_chipletBitwise_opFlagCol_eq, FExpr.eval, Builder.gate, Builder.assertZero,
    BaseConstraint.eval, BaseConstraint.expr, AirRow.baseAt, AirRow.base,
    eval_chipletBitwise_bitwiseFlag]
  ring_nf

theorem bridge_chiplet_bitwise_1_neg (r : AirRow) (h_transition : r.isTransition = 1) :
    Constraints.Symbolic.ChipletBitwise.base[1]! (toSymbolicFrame r) =
      -Subsystems.ChipletBitwise.opFlagStability.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  simp only [Constraints.Symbolic.ChipletBitwise.base,
    List.getElem_cons_zero, List.getElem_cons_succ,
    toSymbolicFrame_periodic_19_eq, toSymbolicFrame_colCurr_51_eq,
    toSymbolicFrame_colCurr_52_eq, toSymbolicFrame_colCurr_53_eq,
    toSymbolicFrame_colNext_53_eq,
    Subsystems.ChipletBitwise.opFlagStability, Subsystems.ChipletBitwise.transitionEq,
    Subsystems.ChipletBitwise.opFlagNext, Subsystems.ChipletBitwise.opFlag,
    curr_chipletBitwise_opFlagCol_eq, next_chipletBitwise_opFlagCol_eq,
    periodic_chipletBitwise_pBitwiseKTransition_eq, FExpr.eval,
    Builder.whenTransition, Builder.gate,
    Builder.assertEq, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.boundaryAt, AirRow.boundary, AirRow.baseAt, AirRow.base,
    eval_chipletBitwise_gateTransition,
    h_transition]
  ring_nf

private def chipletBitwiseStabilityCounterexample : AirRow := {
  curr := fun j =>
    match j.val with
    | 51 => 1
    | 52 => 0
    | 53 => 1
    | _ => 0
  next := fun j =>
    match j.val with
    | 53 => 0
    | _ => 0
  globals := {
    periodic := fun j =>
      match j.val with
      | 19 => 1
      | _ => 0
  }
  isTransition := 1
}

theorem bridge_chiplet_bitwise_1_counterexample :
    Constraints.Symbolic.ChipletBitwise.base[1]!
        (toSymbolicFrame chipletBitwiseStabilityCounterexample) ≠
      Subsystems.ChipletBitwise.opFlagStability.eval chipletBitwiseStabilityCounterexample := by
  native_decide

theorem bridge_chiplet_bitwise_2 (r : AirRow) :
    Constraints.Symbolic.ChipletBitwise.base[2]! (toSymbolicFrame r) =
      (Subsystems.ChipletBitwise.aBitBinary bit0).eval r := by
  rw [getElem!_pos (h := by native_decide)]
  simp only [Constraints.Symbolic.ChipletBitwise.base,
    List.getElem_cons_zero, List.getElem_cons_succ,
    toSymbolicFrame_colCurr_51_eq, toSymbolicFrame_colCurr_52_eq,
    toSymbolicFrame_colCurr_56_eq,
    Subsystems.ChipletBitwise.aBitBinary, Subsystems.ChipletBitwise.integrityZero,
    Subsystems.ChipletBitwise.aBit, Subsystems.ChipletBitwise.one,
    curr_chipletBitwise_aBit0Col_eq,
    FExpr.eval, Builder.gate, Builder.assertZero, BaseConstraint.eval,
    BaseConstraint.expr, AirRow.baseAt, AirRow.base, eval_chipletBitwise_bitwiseFlag]
  ring_nf

theorem bridge_chiplet_bitwise_3 (r : AirRow) :
    Constraints.Symbolic.ChipletBitwise.base[3]! (toSymbolicFrame r) =
      (Subsystems.ChipletBitwise.aBitBinary bit1).eval r := by
  rw [getElem!_pos (h := by native_decide)]
  simp only [Constraints.Symbolic.ChipletBitwise.base,
    List.getElem_cons_zero, List.getElem_cons_succ,
    toSymbolicFrame_colCurr_51_eq, toSymbolicFrame_colCurr_52_eq,
    toSymbolicFrame_colCurr_57_eq,
    Subsystems.ChipletBitwise.aBitBinary, Subsystems.ChipletBitwise.integrityZero,
    Subsystems.ChipletBitwise.aBit, Subsystems.ChipletBitwise.one,
    curr_chipletBitwise_aBit1Col_eq,
    FExpr.eval, Builder.gate, Builder.assertZero, BaseConstraint.eval,
    BaseConstraint.expr, AirRow.baseAt, AirRow.base, eval_chipletBitwise_bitwiseFlag]
  ring_nf

theorem bridge_chiplet_bitwise_4 (r : AirRow) :
    Constraints.Symbolic.ChipletBitwise.base[4]! (toSymbolicFrame r) =
      (Subsystems.ChipletBitwise.aBitBinary bit2).eval r := by
  rw [getElem!_pos (h := by native_decide)]
  simp only [Constraints.Symbolic.ChipletBitwise.base,
    List.getElem_cons_zero, List.getElem_cons_succ,
    toSymbolicFrame_colCurr_51_eq, toSymbolicFrame_colCurr_52_eq,
    toSymbolicFrame_colCurr_58_eq,
    Subsystems.ChipletBitwise.aBitBinary, Subsystems.ChipletBitwise.integrityZero,
    Subsystems.ChipletBitwise.aBit, Subsystems.ChipletBitwise.one,
    curr_chipletBitwise_aBit2Col_eq,
    FExpr.eval, Builder.gate, Builder.assertZero, BaseConstraint.eval,
    BaseConstraint.expr, AirRow.baseAt, AirRow.base, eval_chipletBitwise_bitwiseFlag]
  ring_nf

theorem bridge_chiplet_bitwise_5 (r : AirRow) :
    Constraints.Symbolic.ChipletBitwise.base[5]! (toSymbolicFrame r) =
      (Subsystems.ChipletBitwise.aBitBinary bit3).eval r := by
  rw [getElem!_pos (h := by native_decide)]
  simp only [Constraints.Symbolic.ChipletBitwise.base,
    List.getElem_cons_zero, List.getElem_cons_succ,
    toSymbolicFrame_colCurr_51_eq, toSymbolicFrame_colCurr_52_eq,
    toSymbolicFrame_colCurr_59_eq,
    Subsystems.ChipletBitwise.aBitBinary, Subsystems.ChipletBitwise.integrityZero,
    Subsystems.ChipletBitwise.aBit, Subsystems.ChipletBitwise.one,
    curr_chipletBitwise_aBit3Col_eq,
    FExpr.eval, Builder.gate, Builder.assertZero, BaseConstraint.eval,
    BaseConstraint.expr, AirRow.baseAt, AirRow.base, eval_chipletBitwise_bitwiseFlag]
  ring_nf

theorem bridge_chiplet_bitwise_6 (r : AirRow) :
    Constraints.Symbolic.ChipletBitwise.base[6]! (toSymbolicFrame r) =
      (Subsystems.ChipletBitwise.bBitBinary bit0).eval r := by
  rw [getElem!_pos (h := by native_decide)]
  simp only [Constraints.Symbolic.ChipletBitwise.base,
    List.getElem_cons_zero, List.getElem_cons_succ,
    toSymbolicFrame_colCurr_51_eq, toSymbolicFrame_colCurr_52_eq,
    toSymbolicFrame_colCurr_60_eq,
    Subsystems.ChipletBitwise.bBitBinary, Subsystems.ChipletBitwise.integrityZero,
    Subsystems.ChipletBitwise.bBit, Subsystems.ChipletBitwise.one,
    curr_chipletBitwise_bBit0Col_eq,
    FExpr.eval, Builder.gate, Builder.assertZero, BaseConstraint.eval,
    BaseConstraint.expr, AirRow.baseAt, AirRow.base, eval_chipletBitwise_bitwiseFlag]
  ring_nf

theorem bridge_chiplet_bitwise_7 (r : AirRow) :
    Constraints.Symbolic.ChipletBitwise.base[7]! (toSymbolicFrame r) =
      (Subsystems.ChipletBitwise.bBitBinary bit1).eval r := by
  rw [getElem!_pos (h := by native_decide)]
  simp only [Constraints.Symbolic.ChipletBitwise.base,
    List.getElem_cons_zero, List.getElem_cons_succ,
    toSymbolicFrame_colCurr_51_eq, toSymbolicFrame_colCurr_52_eq,
    toSymbolicFrame_colCurr_61_eq,
    Subsystems.ChipletBitwise.bBitBinary, Subsystems.ChipletBitwise.integrityZero,
    Subsystems.ChipletBitwise.bBit, Subsystems.ChipletBitwise.one,
    curr_chipletBitwise_bBit1Col_eq,
    FExpr.eval, Builder.gate, Builder.assertZero, BaseConstraint.eval,
    BaseConstraint.expr, AirRow.baseAt, AirRow.base, eval_chipletBitwise_bitwiseFlag]
  ring_nf

theorem bridge_chiplet_bitwise_8 (r : AirRow) :
    Constraints.Symbolic.ChipletBitwise.base[8]! (toSymbolicFrame r) =
      (Subsystems.ChipletBitwise.bBitBinary bit2).eval r := by
  rw [getElem!_pos (h := by native_decide)]
  simp only [Constraints.Symbolic.ChipletBitwise.base,
    List.getElem_cons_zero, List.getElem_cons_succ,
    toSymbolicFrame_colCurr_51_eq, toSymbolicFrame_colCurr_52_eq,
    toSymbolicFrame_colCurr_62_eq,
    Subsystems.ChipletBitwise.bBitBinary, Subsystems.ChipletBitwise.integrityZero,
    Subsystems.ChipletBitwise.bBit, Subsystems.ChipletBitwise.one,
    curr_chipletBitwise_bBit2Col_eq,
    FExpr.eval, Builder.gate, Builder.assertZero, BaseConstraint.eval,
    BaseConstraint.expr, AirRow.baseAt, AirRow.base, eval_chipletBitwise_bitwiseFlag]
  ring_nf

theorem bridge_chiplet_bitwise_9 (r : AirRow) :
    Constraints.Symbolic.ChipletBitwise.base[9]! (toSymbolicFrame r) =
      (Subsystems.ChipletBitwise.bBitBinary bit3).eval r := by
  rw [getElem!_pos (h := by native_decide)]
  simp only [Constraints.Symbolic.ChipletBitwise.base,
    List.getElem_cons_zero, List.getElem_cons_succ,
    toSymbolicFrame_colCurr_51_eq, toSymbolicFrame_colCurr_52_eq,
    toSymbolicFrame_colCurr_63_eq,
    Subsystems.ChipletBitwise.bBitBinary, Subsystems.ChipletBitwise.integrityZero,
    Subsystems.ChipletBitwise.bBit, Subsystems.ChipletBitwise.one,
    curr_chipletBitwise_bBit3Col_eq,
    FExpr.eval, Builder.gate, Builder.assertZero, BaseConstraint.eval,
    BaseConstraint.expr, AirRow.baseAt, AirRow.base, eval_chipletBitwise_bitwiseFlag]
  ring_nf

theorem bridge_chiplet_bitwise_10 (r : AirRow) :
    Constraints.Symbolic.ChipletBitwise.base[10]! (toSymbolicFrame r) =
      Subsystems.ChipletBitwise.firstRowA.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  simp only [Constraints.Symbolic.ChipletBitwise.base,
    List.getElem_cons_zero, List.getElem_cons_succ,
    toSymbolicFrame_periodic_18_eq, toSymbolicFrame_colCurr_51_eq,
    toSymbolicFrame_colCurr_52_eq, toSymbolicFrame_colCurr_54_eq,
    toSymbolicFrame_colCurr_56_eq, toSymbolicFrame_colCurr_57_eq,
    toSymbolicFrame_colCurr_58_eq, toSymbolicFrame_colCurr_59_eq,
    Subsystems.ChipletBitwise.firstRowA, Subsystems.ChipletBitwise.integrityEq,
    Subsystems.ChipletBitwise.a, Subsystems.ChipletBitwise.aggregateBits,
    Subsystems.ChipletBitwise.aBit, Subsystems.ChipletBitwise.double,
    curr_chipletBitwise_aCol_eq, curr_chipletBitwise_aBitCol0_num_eq,
    curr_chipletBitwise_aBitCol1_num_eq, curr_chipletBitwise_aBitCol2_num_eq,
    curr_chipletBitwise_aBitCol3_num_eq, FExpr.eval, Builder.gate,
    Builder.assertEq, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.baseAt, AirRow.base, eval_chipletBitwise_gateFirst]

theorem bridge_chiplet_bitwise_11 (r : AirRow) :
    Constraints.Symbolic.ChipletBitwise.base[11]! (toSymbolicFrame r) =
      Subsystems.ChipletBitwise.firstRowB.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  simp only [Constraints.Symbolic.ChipletBitwise.base,
    List.getElem_cons_zero, List.getElem_cons_succ,
    toSymbolicFrame_periodic_18_eq, toSymbolicFrame_colCurr_51_eq,
    toSymbolicFrame_colCurr_52_eq, toSymbolicFrame_colCurr_55_eq,
    toSymbolicFrame_colCurr_60_eq, toSymbolicFrame_colCurr_61_eq,
    toSymbolicFrame_colCurr_62_eq, toSymbolicFrame_colCurr_63_eq,
    Subsystems.ChipletBitwise.firstRowB, Subsystems.ChipletBitwise.integrityEq,
    Subsystems.ChipletBitwise.b, Subsystems.ChipletBitwise.aggregateBits,
    Subsystems.ChipletBitwise.bBit, Subsystems.ChipletBitwise.double,
    curr_chipletBitwise_bCol_eq, curr_chipletBitwise_bBitCol0_num_eq,
    curr_chipletBitwise_bBitCol1_num_eq, curr_chipletBitwise_bBitCol2_num_eq,
    curr_chipletBitwise_bBitCol3_num_eq, FExpr.eval, Builder.gate,
    Builder.assertEq, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.baseAt, AirRow.base, eval_chipletBitwise_gateFirst]

theorem bridge_chiplet_bitwise_12 (r : AirRow) :
    Constraints.Symbolic.ChipletBitwise.base[12]! (toSymbolicFrame r) =
      Subsystems.ChipletBitwise.firstRowPrevOutput.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  simp only [Constraints.Symbolic.ChipletBitwise.base,
    List.getElem_cons_zero, List.getElem_cons_succ,
    toSymbolicFrame_periodic_18_eq, toSymbolicFrame_colCurr_51_eq,
    toSymbolicFrame_colCurr_52_eq, toSymbolicFrame_colCurr_64_eq,
    Subsystems.ChipletBitwise.firstRowPrevOutput, Subsystems.ChipletBitwise.prevOutput,
    curr_chipletBitwise_prevOutputCol_eq, FExpr.eval, Builder.gate, Builder.assertZero,
    BaseConstraint.eval, BaseConstraint.expr, AirRow.baseAt, AirRow.base,
    eval_chipletBitwise_gateFirst]

theorem bridge_chiplet_bitwise_13 (r : AirRow) (h_transition : r.isTransition = 1) :
    Constraints.Symbolic.ChipletBitwise.base[13]! (toSymbolicFrame r) =
      Subsystems.ChipletBitwise.inputTransitionA.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  simp only [Constraints.Symbolic.ChipletBitwise.base,
    List.getElem_cons_zero, List.getElem_cons_succ,
    toSymbolicFrame_periodic_19_eq, toSymbolicFrame_colCurr_51_eq,
    toSymbolicFrame_colCurr_52_eq, toSymbolicFrame_colCurr_54_eq,
    toSymbolicFrame_colNext_54_eq, toSymbolicFrame_colNext_56_eq,
    toSymbolicFrame_colNext_57_eq, toSymbolicFrame_colNext_58_eq,
    toSymbolicFrame_colNext_59_eq,
    Subsystems.ChipletBitwise.inputTransitionA, Subsystems.ChipletBitwise.transitionEq,
    Subsystems.ChipletBitwise.aNext, Subsystems.ChipletBitwise.a,
    Subsystems.ChipletBitwise.sixteen, Subsystems.ChipletBitwise.aggregateBits,
    Subsystems.ChipletBitwise.aBitNext, Subsystems.ChipletBitwise.double,
    curr_chipletBitwise_aCol_eq, next_chipletBitwise_aCol_eq,
    next_chipletBitwise_aBitCol0_num_eq, next_chipletBitwise_aBitCol1_num_eq,
    next_chipletBitwise_aBitCol2_num_eq, next_chipletBitwise_aBitCol3_num_eq,
    FExpr.eval, Builder.whenTransition, Builder.gate,
    Builder.assertEq, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.boundaryAt, AirRow.boundary, AirRow.baseAt, AirRow.base,
    eval_chipletBitwise_gateTransition,
    h_transition]
  rw [show (Felt.ofNat 16 : Felt) = 16 by rfl]
  ring_nf

theorem bridge_chiplet_bitwise_14 (r : AirRow) (h_transition : r.isTransition = 1) :
    Constraints.Symbolic.ChipletBitwise.base[14]! (toSymbolicFrame r) =
      Subsystems.ChipletBitwise.inputTransitionB.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  simp only [Constraints.Symbolic.ChipletBitwise.base,
    List.getElem_cons_zero, List.getElem_cons_succ,
    toSymbolicFrame_periodic_19_eq, toSymbolicFrame_colCurr_51_eq,
    toSymbolicFrame_colCurr_52_eq, toSymbolicFrame_colCurr_55_eq,
    toSymbolicFrame_colNext_55_eq, toSymbolicFrame_colNext_60_eq,
    toSymbolicFrame_colNext_61_eq, toSymbolicFrame_colNext_62_eq,
    toSymbolicFrame_colNext_63_eq,
    Subsystems.ChipletBitwise.inputTransitionB, Subsystems.ChipletBitwise.transitionEq,
    Subsystems.ChipletBitwise.bNext, Subsystems.ChipletBitwise.b,
    Subsystems.ChipletBitwise.sixteen, Subsystems.ChipletBitwise.aggregateBits,
    Subsystems.ChipletBitwise.bBitNext, Subsystems.ChipletBitwise.double,
    curr_chipletBitwise_bCol_eq, next_chipletBitwise_bCol_eq,
    next_chipletBitwise_bBitCol0_num_eq, next_chipletBitwise_bBitCol1_num_eq,
    next_chipletBitwise_bBitCol2_num_eq, next_chipletBitwise_bBitCol3_num_eq,
    FExpr.eval, Builder.whenTransition, Builder.gate,
    Builder.assertEq, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.boundaryAt, AirRow.boundary, AirRow.baseAt, AirRow.base,
    eval_chipletBitwise_gateTransition,
    h_transition]
  rw [show (Felt.ofNat 16 : Felt) = 16 by rfl]
  ring_nf

theorem bridge_chiplet_bitwise_15 (r : AirRow) (h_transition : r.isTransition = 1) :
    Constraints.Symbolic.ChipletBitwise.base[15]! (toSymbolicFrame r) =
      Subsystems.ChipletBitwise.outputPrevTransition.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  simp only [Constraints.Symbolic.ChipletBitwise.base,
    List.getElem_cons_zero, List.getElem_cons_succ,
    toSymbolicFrame_periodic_19_eq, toSymbolicFrame_colCurr_51_eq,
    toSymbolicFrame_colCurr_52_eq, toSymbolicFrame_colCurr_65_eq,
    toSymbolicFrame_colNext_64_eq,
    Subsystems.ChipletBitwise.outputPrevTransition, Subsystems.ChipletBitwise.transitionEq,
    Subsystems.ChipletBitwise.prevOutputNext, Subsystems.ChipletBitwise.output,
    next_chipletBitwise_prevOutputCol_eq, curr_chipletBitwise_outputCol_eq,
    FExpr.eval, Builder.whenTransition, Builder.gate,
    Builder.assertEq, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.boundaryAt, AirRow.boundary, AirRow.baseAt, AirRow.base,
    eval_chipletBitwise_gateTransition,
    h_transition]
  simpa

theorem bridge_chiplet_bitwise_16 (r : AirRow) :
    Constraints.Symbolic.ChipletBitwise.base[16]! (toSymbolicFrame r) =
      Subsystems.ChipletBitwise.outputAggregation.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  simp only [Constraints.Symbolic.ChipletBitwise.base,
    List.getElem_cons_zero, List.getElem_cons_succ,
    toSymbolicFrame_colCurr_51_eq, toSymbolicFrame_colCurr_52_eq,
    toSymbolicFrame_colCurr_53_eq, toSymbolicFrame_colCurr_56_eq,
    toSymbolicFrame_colCurr_57_eq, toSymbolicFrame_colCurr_58_eq,
    toSymbolicFrame_colCurr_59_eq, toSymbolicFrame_colCurr_60_eq,
    toSymbolicFrame_colCurr_61_eq, toSymbolicFrame_colCurr_62_eq,
    toSymbolicFrame_colCurr_63_eq, toSymbolicFrame_colCurr_64_eq,
    toSymbolicFrame_colCurr_65_eq,
    Subsystems.ChipletBitwise.outputAggregation, Subsystems.ChipletBitwise.integrityEq,
    Subsystems.ChipletBitwise.output, Subsystems.ChipletBitwise.expectedOutput,
    Subsystems.ChipletBitwise.prevOutput,
    Subsystems.ChipletBitwise.sixteen, Subsystems.ChipletBitwise.nibbleAnd,
    Subsystems.ChipletBitwise.nibbleXor, Subsystems.ChipletBitwise.opFlag,
    curr_chipletBitwise_opFlagCol_eq, Subsystems.ChipletBitwise.aBit,
    Subsystems.ChipletBitwise.aBitsOffset, Subsystems.ChipletBitwise.bBit,
    Subsystems.ChipletBitwise.bBitsOffset, Subsystems.ChipletBitwise.double,
    curr_chipletBitwise_outputCol_eq, curr_chipletBitwise_prevOutputCol_eq,
    curr_chipletBitwise_aBitCol0_num_eq, curr_chipletBitwise_aBitCol1_num_eq,
    curr_chipletBitwise_aBitCol2_num_eq, curr_chipletBitwise_aBitCol3_num_eq,
    curr_chipletBitwise_bBitCol0_num_eq, curr_chipletBitwise_bBitCol1_num_eq,
    curr_chipletBitwise_bBitCol2_num_eq, curr_chipletBitwise_bBitCol3_num_eq,
    FExpr.eval, Builder.gate, Builder.assertEq, Builder.assertZero,
    BaseConstraint.eval, BaseConstraint.expr, AirRow.baseAt, AirRow.base,
    eval_chipletBitwise_bitwiseFlag]
  rw [show (Felt.ofNat 16 : Felt) = 16 by rfl]
  ring_nf

end MidenLean.AIR.Semantics.Refinement.SymbolicToCanonical
