import MidenLean.AIR.Semantics.Tactics
import MidenLean.AIR.Semantics.Subsystems.ChipletHasher
import MidenLean.AIR.Constraints.Symbolic.ChipletHasher

set_option maxHeartbeats 32000000

namespace MidenLean.AIR.Semantics.Refinement.SymbolicToCanonical

open MidenLean
open MidenLean.AIR
open MidenLean.AIR.Semantics
open MidenLean.AIR.Semantics.Tactics
open MidenLean.AIR.Semantics.Builder
open Lean Parser Tactic

private abbrev lane0 : Subsystems.ChipletHasher.LaneIndex := ⟨0, by decide⟩
private abbrev lane1 : Subsystems.ChipletHasher.LaneIndex := ⟨1, by decide⟩
private abbrev lane2 : Subsystems.ChipletHasher.LaneIndex := ⟨2, by decide⟩
private abbrev lane3 : Subsystems.ChipletHasher.LaneIndex := ⟨3, by decide⟩
private abbrev lane4 : Subsystems.ChipletHasher.LaneIndex := ⟨4, by decide⟩
private abbrev lane5 : Subsystems.ChipletHasher.LaneIndex := ⟨5, by decide⟩
private abbrev lane6 : Subsystems.ChipletHasher.LaneIndex := ⟨6, by decide⟩
private abbrev lane7 : Subsystems.ChipletHasher.LaneIndex := ⟨7, by decide⟩
private abbrev lane8 : Subsystems.ChipletHasher.LaneIndex := ⟨8, by decide⟩
private abbrev lane9 : Subsystems.ChipletHasher.LaneIndex := ⟨9, by decide⟩
private abbrev lane10 : Subsystems.ChipletHasher.LaneIndex := ⟨10, by decide⟩
private abbrev lane11 : Subsystems.ChipletHasher.LaneIndex := ⟨11, by decide⟩

private abbrev word0 : Subsystems.ChipletHasher.WordIndex := ⟨0, by decide⟩
private abbrev word1 : Subsystems.ChipletHasher.WordIndex := ⟨1, by decide⟩
private abbrev word2 : Subsystems.ChipletHasher.WordIndex := ⟨2, by decide⟩
private abbrev word3 : Subsystems.ChipletHasher.WordIndex := ⟨3, by decide⟩

@[simp] theorem curr_chipletSelectors_s0Col_eq (r : AirRow) :
    r.curr Subsystems.ChipletSelectors.s0Col = r.curr 51 := rfl

@[simp] theorem next_chipletSelectors_s0Col_eq (r : AirRow) :
    r.next Subsystems.ChipletSelectors.s0Col = r.next 51 := rfl

@[simp] theorem curr_main_51_eq (r : AirRow) (h : 51 < MainWidth) :
    r.curr ⟨51, h⟩ = r.curr 51 := by
  apply congrArg r.curr
  apply Fin.ext
  rfl

@[simp] theorem curr_main_52_eq (r : AirRow) (h : 52 < MainWidth) :
    r.curr ⟨52, h⟩ = r.curr 52 := by
  apply congrArg r.curr
  apply Fin.ext
  rfl

@[simp] theorem curr_main_53_eq (r : AirRow) (h : 53 < MainWidth) :
    r.curr ⟨53, h⟩ = r.curr 53 := by
  apply congrArg r.curr
  apply Fin.ext
  rfl

@[simp] theorem curr_main_54_eq (r : AirRow) (h : 54 < MainWidth) :
    r.curr ⟨54, h⟩ = r.curr 54 := by
  apply congrArg r.curr
  apply Fin.ext
  rfl

@[simp] theorem next_main_51_eq (r : AirRow) (h : 51 < MainWidth) :
    r.next ⟨51, h⟩ = r.next 51 := by
  apply congrArg r.next
  apply Fin.ext
  rfl

@[simp] theorem next_main_52_eq (r : AirRow) (h : 52 < MainWidth) :
    r.next ⟨52, h⟩ = r.next 52 := by
  apply congrArg r.next
  apply Fin.ext
  rfl

@[simp] theorem next_main_53_eq (r : AirRow) (h : 53 < MainWidth) :
    r.next ⟨53, h⟩ = r.next 53 := by
  apply congrArg r.next
  apply Fin.ext
  rfl

@[simp] theorem next_main_54_eq (r : AirRow) (h : 54 < MainWidth) :
    r.next ⟨54, h⟩ = r.next 54 := by
  apply congrArg r.next
  apply Fin.ext
  rfl

@[simp] theorem curr_chipletHasher_sel0Col_eq (r : AirRow) :
    r.curr Subsystems.ChipletHasher.sel0Col = r.curr 52 := rfl

@[simp] theorem next_chipletHasher_sel0Col_eq (r : AirRow) :
    r.next Subsystems.ChipletHasher.sel0Col = r.next 52 := rfl

@[simp] theorem curr_chipletHasher_sel1Col_eq (r : AirRow) :
    r.curr Subsystems.ChipletHasher.sel1Col = r.curr 53 := rfl

@[simp] theorem next_chipletHasher_sel1Col_eq (r : AirRow) :
    r.next Subsystems.ChipletHasher.sel1Col = r.next 53 := rfl

@[simp] theorem curr_chipletHasher_sel2Col_eq (r : AirRow) :
    r.curr Subsystems.ChipletHasher.sel2Col = r.curr 54 := rfl

@[simp] theorem next_chipletHasher_sel2Col_eq (r : AirRow) :
    r.next Subsystems.ChipletHasher.sel2Col = r.next 54 := rfl

@[simp] theorem periodic_chipletHasher_pCycleRow0_eq (r : AirRow) :
    r.periodic Subsystems.ChipletHasher.pCycleRow0 = r.globals.periodic 0 := rfl

@[simp] theorem periodic_chipletHasher_pCycleRow30_eq (r : AirRow) :
    r.periodic Subsystems.ChipletHasher.pCycleRow30 = r.globals.periodic 1 := rfl

@[simp] theorem periodic_chipletHasher_pCycleRow31_eq (r : AirRow) :
    r.periodic Subsystems.ChipletHasher.pCycleRow31 = r.globals.periodic 2 := rfl

@[simp] theorem eval_chipletSelectors_hasherChipletFlag (r : AirRow) :
    Subsystems.ChipletSelectors.hasherChipletFlag.eval r = 1 - r.curr 51 := by
  simp [Subsystems.ChipletSelectors.hasherChipletFlag, Subsystems.ChipletSelectors.notS0,
    Subsystems.ChipletSelectors.s0, FExpr.eval, AirRow.baseAt, AirRow.base]

@[simp] theorem eval_chipletHasher_hasherFlag (r : AirRow) :
    Subsystems.ChipletHasher.hasherFlag.eval r = 1 - r.curr 51 := by
  simp [Subsystems.ChipletHasher.hasherFlag]

@[simp] theorem curr_main_55_eq (r : AirRow) (h : 55 < MainWidth) :
    r.curr ⟨55, h⟩ = r.curr 55 := by
  apply congrArg r.curr
  apply Fin.ext
  rfl

@[simp] theorem curr_main_56_eq (r : AirRow) (h : 56 < MainWidth) :
    r.curr ⟨56, h⟩ = r.curr 56 := by
  apply congrArg r.curr
  apply Fin.ext
  rfl

@[simp] theorem curr_main_57_eq (r : AirRow) (h : 57 < MainWidth) :
    r.curr ⟨57, h⟩ = r.curr 57 := by
  apply congrArg r.curr
  apply Fin.ext
  rfl

@[simp] theorem curr_main_58_eq (r : AirRow) (h : 58 < MainWidth) :
    r.curr ⟨58, h⟩ = r.curr 58 := by
  apply congrArg r.curr
  apply Fin.ext
  rfl

@[simp] theorem curr_main_59_eq (r : AirRow) (h : 59 < MainWidth) :
    r.curr ⟨59, h⟩ = r.curr 59 := by
  apply congrArg r.curr
  apply Fin.ext
  rfl

@[simp] theorem curr_main_60_eq (r : AirRow) (h : 60 < MainWidth) :
    r.curr ⟨60, h⟩ = r.curr 60 := by
  apply congrArg r.curr
  apply Fin.ext
  rfl

@[simp] theorem curr_main_61_eq (r : AirRow) (h : 61 < MainWidth) :
    r.curr ⟨61, h⟩ = r.curr 61 := by
  apply congrArg r.curr
  apply Fin.ext
  rfl

@[simp] theorem curr_main_62_eq (r : AirRow) (h : 62 < MainWidth) :
    r.curr ⟨62, h⟩ = r.curr 62 := by
  apply congrArg r.curr
  apply Fin.ext
  rfl

@[simp] theorem curr_main_63_eq (r : AirRow) (h : 63 < MainWidth) :
    r.curr ⟨63, h⟩ = r.curr 63 := by
  apply congrArg r.curr
  apply Fin.ext
  rfl

@[simp] theorem curr_main_64_eq (r : AirRow) (h : 64 < MainWidth) :
    r.curr ⟨64, h⟩ = r.curr 64 := by
  apply congrArg r.curr
  apply Fin.ext
  rfl

@[simp] theorem curr_main_65_eq (r : AirRow) (h : 65 < MainWidth) :
    r.curr ⟨65, h⟩ = r.curr 65 := by
  apply congrArg r.curr
  apply Fin.ext
  rfl

@[simp] theorem curr_main_66_eq (r : AirRow) (h : 66 < MainWidth) :
    r.curr ⟨66, h⟩ = r.curr 66 := by
  apply congrArg r.curr
  apply Fin.ext
  rfl

@[simp] theorem curr_main_67_eq (r : AirRow) (h : 67 < MainWidth) :
    r.curr ⟨67, h⟩ = r.curr 67 := by
  apply congrArg r.curr
  apply Fin.ext
  rfl

@[simp] theorem next_main_55_eq (r : AirRow) (h : 55 < MainWidth) :
    r.next ⟨55, h⟩ = r.next 55 := by
  apply congrArg r.next
  apply Fin.ext
  rfl

@[simp] theorem next_main_56_eq (r : AirRow) (h : 56 < MainWidth) :
    r.next ⟨56, h⟩ = r.next 56 := by
  apply congrArg r.next
  apply Fin.ext
  rfl

@[simp] theorem next_main_57_eq (r : AirRow) (h : 57 < MainWidth) :
    r.next ⟨57, h⟩ = r.next 57 := by
  apply congrArg r.next
  apply Fin.ext
  rfl

@[simp] theorem next_main_58_eq (r : AirRow) (h : 58 < MainWidth) :
    r.next ⟨58, h⟩ = r.next 58 := by
  apply congrArg r.next
  apply Fin.ext
  rfl

@[simp] theorem next_main_59_eq (r : AirRow) (h : 59 < MainWidth) :
    r.next ⟨59, h⟩ = r.next 59 := by
  apply congrArg r.next
  apply Fin.ext
  rfl

@[simp] theorem next_main_60_eq (r : AirRow) (h : 60 < MainWidth) :
    r.next ⟨60, h⟩ = r.next 60 := by
  apply congrArg r.next
  apply Fin.ext
  rfl

@[simp] theorem next_main_61_eq (r : AirRow) (h : 61 < MainWidth) :
    r.next ⟨61, h⟩ = r.next 61 := by
  apply congrArg r.next
  apply Fin.ext
  rfl

@[simp] theorem next_main_62_eq (r : AirRow) (h : 62 < MainWidth) :
    r.next ⟨62, h⟩ = r.next 62 := by
  apply congrArg r.next
  apply Fin.ext
  rfl

@[simp] theorem next_main_63_eq (r : AirRow) (h : 63 < MainWidth) :
    r.next ⟨63, h⟩ = r.next 63 := by
  apply congrArg r.next
  apply Fin.ext
  rfl

@[simp] theorem next_main_64_eq (r : AirRow) (h : 64 < MainWidth) :
    r.next ⟨64, h⟩ = r.next 64 := by
  apply congrArg r.next
  apply Fin.ext
  rfl

@[simp] theorem next_main_65_eq (r : AirRow) (h : 65 < MainWidth) :
    r.next ⟨65, h⟩ = r.next 65 := by
  apply congrArg r.next
  apply Fin.ext
  rfl

@[simp] theorem next_main_66_eq (r : AirRow) (h : 66 < MainWidth) :
    r.next ⟨66, h⟩ = r.next 66 := by
  apply congrArg r.next
  apply Fin.ext
  rfl

@[simp] theorem next_main_67_eq (r : AirRow) (h : 67 < MainWidth) :
    r.next ⟨67, h⟩ = r.next 67 := by
  apply congrArg r.next
  apply Fin.ext
  rfl

@[simp] theorem toSymbolicFrame_colCurr_51_eq (r : AirRow) :
    (toSymbolicFrame r).colCurr 51 = r.curr 51 := by
  have h51 : 51 < MainWidth := by decide
  simp [SymbolicFrame.colCurr, toSymbolicFrame, h51]

@[simp] theorem toSymbolicFrame_colNext_51_eq (r : AirRow) :
    (toSymbolicFrame r).colNext 51 = r.next 51 := by
  have h51 : 51 < MainWidth := by decide
  simp [SymbolicFrame.colNext, toSymbolicFrame, h51]

@[simp] theorem toSymbolicFrame_colCurr_52_eq (r : AirRow) :
    (toSymbolicFrame r).colCurr 52 = r.curr 52 := by
  have h52 : 52 < MainWidth := by decide
  simp [SymbolicFrame.colCurr, toSymbolicFrame, h52]

@[simp] theorem toSymbolicFrame_colNext_52_eq (r : AirRow) :
    (toSymbolicFrame r).colNext 52 = r.next 52 := by
  have h52 : 52 < MainWidth := by decide
  simp [SymbolicFrame.colNext, toSymbolicFrame, h52]

@[simp] theorem toSymbolicFrame_colCurr_53_eq (r : AirRow) :
    (toSymbolicFrame r).colCurr 53 = r.curr 53 := by
  have h53 : 53 < MainWidth := by decide
  simp [SymbolicFrame.colCurr, toSymbolicFrame, h53]

@[simp] theorem toSymbolicFrame_colNext_53_eq (r : AirRow) :
    (toSymbolicFrame r).colNext 53 = r.next 53 := by
  have h53 : 53 < MainWidth := by decide
  simp [SymbolicFrame.colNext, toSymbolicFrame, h53]

@[simp] theorem toSymbolicFrame_colCurr_54_eq (r : AirRow) :
    (toSymbolicFrame r).colCurr 54 = r.curr 54 := by
  have h54 : 54 < MainWidth := by decide
  simp [SymbolicFrame.colCurr, toSymbolicFrame, h54]

@[simp] theorem toSymbolicFrame_colNext_54_eq (r : AirRow) :
    (toSymbolicFrame r).colNext 54 = r.next 54 := by
  have h54 : 54 < MainWidth := by decide
  simp [SymbolicFrame.colNext, toSymbolicFrame, h54]

@[simp] theorem toSymbolicFrame_colCurr_55_eq (r : AirRow) :
    (toSymbolicFrame r).colCurr 55 = r.curr 55 := by
  have h55 : 55 < MainWidth := by decide
  simp [SymbolicFrame.colCurr, toSymbolicFrame, h55]

@[simp] theorem toSymbolicFrame_colNext_55_eq (r : AirRow) :
    (toSymbolicFrame r).colNext 55 = r.next 55 := by
  have h55 : 55 < MainWidth := by decide
  simp [SymbolicFrame.colNext, toSymbolicFrame, h55]

@[simp] theorem toSymbolicFrame_colCurr_56_eq (r : AirRow) :
    (toSymbolicFrame r).colCurr 56 = r.curr 56 := by
  have h56 : 56 < MainWidth := by decide
  simp [SymbolicFrame.colCurr, toSymbolicFrame, h56]

@[simp] theorem toSymbolicFrame_colNext_56_eq (r : AirRow) :
    (toSymbolicFrame r).colNext 56 = r.next 56 := by
  have h56 : 56 < MainWidth := by decide
  simp [SymbolicFrame.colNext, toSymbolicFrame, h56]

@[simp] theorem toSymbolicFrame_colCurr_57_eq (r : AirRow) :
    (toSymbolicFrame r).colCurr 57 = r.curr 57 := by
  have h57 : 57 < MainWidth := by decide
  simp [SymbolicFrame.colCurr, toSymbolicFrame, h57]

@[simp] theorem toSymbolicFrame_colNext_57_eq (r : AirRow) :
    (toSymbolicFrame r).colNext 57 = r.next 57 := by
  have h57 : 57 < MainWidth := by decide
  simp [SymbolicFrame.colNext, toSymbolicFrame, h57]

@[simp] theorem toSymbolicFrame_colCurr_58_eq (r : AirRow) :
    (toSymbolicFrame r).colCurr 58 = r.curr 58 := by
  have h58 : 58 < MainWidth := by decide
  simp [SymbolicFrame.colCurr, toSymbolicFrame, h58]

@[simp] theorem toSymbolicFrame_colNext_58_eq (r : AirRow) :
    (toSymbolicFrame r).colNext 58 = r.next 58 := by
  have h58 : 58 < MainWidth := by decide
  simp [SymbolicFrame.colNext, toSymbolicFrame, h58]

@[simp] theorem toSymbolicFrame_colCurr_59_eq (r : AirRow) :
    (toSymbolicFrame r).colCurr 59 = r.curr 59 := by
  have h59 : 59 < MainWidth := by decide
  simp [SymbolicFrame.colCurr, toSymbolicFrame, h59]

@[simp] theorem toSymbolicFrame_colNext_59_eq (r : AirRow) :
    (toSymbolicFrame r).colNext 59 = r.next 59 := by
  have h59 : 59 < MainWidth := by decide
  simp [SymbolicFrame.colNext, toSymbolicFrame, h59]

@[simp] theorem toSymbolicFrame_colCurr_60_eq (r : AirRow) :
    (toSymbolicFrame r).colCurr 60 = r.curr 60 := by
  have h60 : 60 < MainWidth := by decide
  simp [SymbolicFrame.colCurr, toSymbolicFrame, h60]

@[simp] theorem toSymbolicFrame_colNext_60_eq (r : AirRow) :
    (toSymbolicFrame r).colNext 60 = r.next 60 := by
  have h60 : 60 < MainWidth := by decide
  simp [SymbolicFrame.colNext, toSymbolicFrame, h60]

@[simp] theorem toSymbolicFrame_colCurr_61_eq (r : AirRow) :
    (toSymbolicFrame r).colCurr 61 = r.curr 61 := by
  have h61 : 61 < MainWidth := by decide
  simp [SymbolicFrame.colCurr, toSymbolicFrame, h61]

@[simp] theorem toSymbolicFrame_colNext_61_eq (r : AirRow) :
    (toSymbolicFrame r).colNext 61 = r.next 61 := by
  have h61 : 61 < MainWidth := by decide
  simp [SymbolicFrame.colNext, toSymbolicFrame, h61]

@[simp] theorem toSymbolicFrame_colCurr_62_eq (r : AirRow) :
    (toSymbolicFrame r).colCurr 62 = r.curr 62 := by
  have h62 : 62 < MainWidth := by decide
  simp [SymbolicFrame.colCurr, toSymbolicFrame, h62]

@[simp] theorem toSymbolicFrame_colNext_62_eq (r : AirRow) :
    (toSymbolicFrame r).colNext 62 = r.next 62 := by
  have h62 : 62 < MainWidth := by decide
  simp [SymbolicFrame.colNext, toSymbolicFrame, h62]

@[simp] theorem toSymbolicFrame_colCurr_63_eq (r : AirRow) :
    (toSymbolicFrame r).colCurr 63 = r.curr 63 := by
  have h63 : 63 < MainWidth := by decide
  simp [SymbolicFrame.colCurr, toSymbolicFrame, h63]

@[simp] theorem toSymbolicFrame_colNext_63_eq (r : AirRow) :
    (toSymbolicFrame r).colNext 63 = r.next 63 := by
  have h63 : 63 < MainWidth := by decide
  simp [SymbolicFrame.colNext, toSymbolicFrame, h63]

@[simp] theorem toSymbolicFrame_colCurr_64_eq (r : AirRow) :
    (toSymbolicFrame r).colCurr 64 = r.curr 64 := by
  have h64 : 64 < MainWidth := by decide
  simp [SymbolicFrame.colCurr, toSymbolicFrame, h64]

@[simp] theorem toSymbolicFrame_colNext_64_eq (r : AirRow) :
    (toSymbolicFrame r).colNext 64 = r.next 64 := by
  have h64 : 64 < MainWidth := by decide
  simp [SymbolicFrame.colNext, toSymbolicFrame, h64]

@[simp] theorem toSymbolicFrame_colCurr_65_eq (r : AirRow) :
    (toSymbolicFrame r).colCurr 65 = r.curr 65 := by
  have h65 : 65 < MainWidth := by decide
  simp [SymbolicFrame.colCurr, toSymbolicFrame, h65]

@[simp] theorem toSymbolicFrame_colNext_65_eq (r : AirRow) :
    (toSymbolicFrame r).colNext 65 = r.next 65 := by
  have h65 : 65 < MainWidth := by decide
  simp [SymbolicFrame.colNext, toSymbolicFrame, h65]

@[simp] theorem toSymbolicFrame_colCurr_66_eq (r : AirRow) :
    (toSymbolicFrame r).colCurr 66 = r.curr 66 := by
  have h66 : 66 < MainWidth := by decide
  simp [SymbolicFrame.colCurr, toSymbolicFrame, h66]

@[simp] theorem toSymbolicFrame_colNext_66_eq (r : AirRow) :
    (toSymbolicFrame r).colNext 66 = r.next 66 := by
  have h66 : 66 < MainWidth := by decide
  simp [SymbolicFrame.colNext, toSymbolicFrame, h66]

@[simp] theorem toSymbolicFrame_colCurr_67_eq (r : AirRow) :
    (toSymbolicFrame r).colCurr 67 = r.curr 67 := by
  have h67 : 67 < MainWidth := by decide
  simp [SymbolicFrame.colCurr, toSymbolicFrame, h67]

@[simp] theorem toSymbolicFrame_colNext_67_eq (r : AirRow) :
    (toSymbolicFrame r).colNext 67 = r.next 67 := by
  have h67 : 67 < MainWidth := by decide
  simp [SymbolicFrame.colNext, toSymbolicFrame, h67]

@[simp] theorem globals_periodic_0_eq (g : AirGlobals) (h : 0 < PeriodicWidth) :
    g.periodic ⟨0, h⟩ = g.periodic 0 := by
  apply congrArg g.periodic
  apply Fin.ext
  rfl

@[simp] theorem globals_periodic_1_eq (g : AirGlobals) (h : 1 < PeriodicWidth) :
    g.periodic ⟨1, h⟩ = g.periodic 1 := by
  apply congrArg g.periodic
  apply Fin.ext
  rfl

@[simp] theorem globals_periodic_2_eq (g : AirGlobals) (h : 2 < PeriodicWidth) :
    g.periodic ⟨2, h⟩ = g.periodic 2 := by
  apply congrArg g.periodic
  apply Fin.ext
  rfl

@[simp] theorem globals_periodic_3_eq (g : AirGlobals) (h : 3 < PeriodicWidth) :
    g.periodic ⟨3, h⟩ = g.periodic 3 := by
  apply congrArg g.periodic
  apply Fin.ext
  rfl

@[simp] theorem globals_periodic_4_eq (g : AirGlobals) (h : 4 < PeriodicWidth) :
    g.periodic ⟨4, h⟩ = g.periodic 4 := by
  apply congrArg g.periodic
  apply Fin.ext
  rfl

@[simp] theorem globals_periodic_5_eq (g : AirGlobals) (h : 5 < PeriodicWidth) :
    g.periodic ⟨5, h⟩ = g.periodic 5 := by
  apply congrArg g.periodic
  apply Fin.ext
  rfl

@[simp] theorem globals_periodic_6_eq (g : AirGlobals) (h : 6 < PeriodicWidth) :
    g.periodic ⟨6, h⟩ = g.periodic 6 := by
  apply congrArg g.periodic
  apply Fin.ext
  rfl

@[simp] theorem globals_periodic_7_eq (g : AirGlobals) (h : 7 < PeriodicWidth) :
    g.periodic ⟨7, h⟩ = g.periodic 7 := by
  apply congrArg g.periodic
  apply Fin.ext
  rfl

@[simp] theorem globals_periodic_8_eq (g : AirGlobals) (h : 8 < PeriodicWidth) :
    g.periodic ⟨8, h⟩ = g.periodic 8 := by
  apply congrArg g.periodic
  apply Fin.ext
  rfl

@[simp] theorem globals_periodic_9_eq (g : AirGlobals) (h : 9 < PeriodicWidth) :
    g.periodic ⟨9, h⟩ = g.periodic 9 := by
  apply congrArg g.periodic
  apply Fin.ext
  rfl

@[simp] theorem globals_periodic_10_eq (g : AirGlobals) (h : 10 < PeriodicWidth) :
    g.periodic ⟨10, h⟩ = g.periodic 10 := by
  apply congrArg g.periodic
  apply Fin.ext
  rfl

@[simp] theorem globals_periodic_11_eq (g : AirGlobals) (h : 11 < PeriodicWidth) :
    g.periodic ⟨11, h⟩ = g.periodic 11 := by
  apply congrArg g.periodic
  apply Fin.ext
  rfl

@[simp] theorem globals_periodic_12_eq (g : AirGlobals) (h : 12 < PeriodicWidth) :
    g.periodic ⟨12, h⟩ = g.periodic 12 := by
  apply congrArg g.periodic
  apply Fin.ext
  rfl

@[simp] theorem globals_periodic_13_eq (g : AirGlobals) (h : 13 < PeriodicWidth) :
    g.periodic ⟨13, h⟩ = g.periodic 13 := by
  apply congrArg g.periodic
  apply Fin.ext
  rfl

@[simp] theorem globals_periodic_14_eq (g : AirGlobals) (h : 14 < PeriodicWidth) :
    g.periodic ⟨14, h⟩ = g.periodic 14 := by
  apply congrArg g.periodic
  apply Fin.ext
  rfl

@[simp] theorem globals_periodic_15_eq (g : AirGlobals) (h : 15 < PeriodicWidth) :
    g.periodic ⟨15, h⟩ = g.periodic 15 := by
  apply congrArg g.periodic
  apply Fin.ext
  rfl

@[simp] theorem globals_periodic_16_eq (g : AirGlobals) (h : 16 < PeriodicWidth) :
    g.periodic ⟨16, h⟩ = g.periodic 16 := by
  apply congrArg g.periodic
  apply Fin.ext
  rfl

@[simp] theorem globals_periodic_17_eq (g : AirGlobals) (h : 17 < PeriodicWidth) :
    g.periodic ⟨17, h⟩ = g.periodic 17 := by
  apply congrArg g.periodic
  apply Fin.ext
  rfl

@[simp] theorem toSymbolicFrame_periodic_0_eq (r : AirRow) :
    (toSymbolicFrame r).periodic 0 = r.globals.periodic 0 := by
  have h0 : 0 < PeriodicWidth := by decide
  simp [toSymbolicFrame, h0]

@[simp] theorem toSymbolicFrame_periodic_1_eq (r : AirRow) :
    (toSymbolicFrame r).periodic 1 = r.globals.periodic 1 := by
  have h1 : 1 < PeriodicWidth := by decide
  simp [toSymbolicFrame, h1]

@[simp] theorem toSymbolicFrame_periodic_2_eq (r : AirRow) :
    (toSymbolicFrame r).periodic 2 = r.globals.periodic 2 := by
  have h2 : 2 < PeriodicWidth := by decide
  simp [toSymbolicFrame, h2]

@[simp] theorem toSymbolicFrame_periodic_3_eq (r : AirRow) :
    (toSymbolicFrame r).periodic 3 = r.globals.periodic 3 := by
  have h3 : 3 < PeriodicWidth := by decide
  simp [toSymbolicFrame, h3]

@[simp] theorem toSymbolicFrame_periodic_4_eq (r : AirRow) :
    (toSymbolicFrame r).periodic 4 = r.globals.periodic 4 := by
  have h4 : 4 < PeriodicWidth := by decide
  simp [toSymbolicFrame, h4]

@[simp] theorem toSymbolicFrame_periodic_5_eq (r : AirRow) :
    (toSymbolicFrame r).periodic 5 = r.globals.periodic 5 := by
  have h5 : 5 < PeriodicWidth := by decide
  simp [toSymbolicFrame, h5]

@[simp] theorem toSymbolicFrame_periodic_6_eq (r : AirRow) :
    (toSymbolicFrame r).periodic 6 = r.globals.periodic 6 := by
  have h6 : 6 < PeriodicWidth := by decide
  simp [toSymbolicFrame, h6]

@[simp] theorem toSymbolicFrame_periodic_7_eq (r : AirRow) :
    (toSymbolicFrame r).periodic 7 = r.globals.periodic 7 := by
  have h7 : 7 < PeriodicWidth := by decide
  simp [toSymbolicFrame, h7]

@[simp] theorem toSymbolicFrame_periodic_8_eq (r : AirRow) :
    (toSymbolicFrame r).periodic 8 = r.globals.periodic 8 := by
  have h8 : 8 < PeriodicWidth := by decide
  simp [toSymbolicFrame, h8]

@[simp] theorem toSymbolicFrame_periodic_9_eq (r : AirRow) :
    (toSymbolicFrame r).periodic 9 = r.globals.periodic 9 := by
  have h9 : 9 < PeriodicWidth := by decide
  simp [toSymbolicFrame, h9]

@[simp] theorem toSymbolicFrame_periodic_10_eq (r : AirRow) :
    (toSymbolicFrame r).periodic 10 = r.globals.periodic 10 := by
  have h10 : 10 < PeriodicWidth := by decide
  simp [toSymbolicFrame, h10]

@[simp] theorem toSymbolicFrame_periodic_11_eq (r : AirRow) :
    (toSymbolicFrame r).periodic 11 = r.globals.periodic 11 := by
  have h11 : 11 < PeriodicWidth := by decide
  simp [toSymbolicFrame, h11]

@[simp] theorem toSymbolicFrame_periodic_12_eq (r : AirRow) :
    (toSymbolicFrame r).periodic 12 = r.globals.periodic 12 := by
  have h12 : 12 < PeriodicWidth := by decide
  simp [toSymbolicFrame, h12]

@[simp] theorem toSymbolicFrame_periodic_13_eq (r : AirRow) :
    (toSymbolicFrame r).periodic 13 = r.globals.periodic 13 := by
  have h13 : 13 < PeriodicWidth := by decide
  simp [toSymbolicFrame, h13]

@[simp] theorem toSymbolicFrame_periodic_14_eq (r : AirRow) :
    (toSymbolicFrame r).periodic 14 = r.globals.periodic 14 := by
  have h14 : 14 < PeriodicWidth := by decide
  simp [toSymbolicFrame, h14]

@[simp] theorem toSymbolicFrame_periodic_15_eq (r : AirRow) :
    (toSymbolicFrame r).periodic 15 = r.globals.periodic 15 := by
  have h15 : 15 < PeriodicWidth := by decide
  simp [toSymbolicFrame, h15]

@[simp] theorem toSymbolicFrame_periodic_16_eq (r : AirRow) :
    (toSymbolicFrame r).periodic 16 = r.globals.periodic 16 := by
  have h16 : 16 < PeriodicWidth := by decide
  simp [toSymbolicFrame, h16]

@[simp] theorem toSymbolicFrame_periodic_17_eq (r : AirRow) :
    (toSymbolicFrame r).periodic 17 = r.globals.periodic 17 := by
  have h17 : 17 < PeriodicWidth := by decide
  simp [toSymbolicFrame, h17]

@[simp] theorem curr_chipletHasher_stateCol0_eq (r : AirRow) :
    r.curr (Subsystems.ChipletHasher.stateCol lane0) = r.curr 55 := rfl

@[simp] theorem next_chipletHasher_stateCol0_eq (r : AirRow) :
    r.next (Subsystems.ChipletHasher.stateCol lane0) = r.next 55 := rfl

@[simp] theorem curr_chipletHasher_stateCol1_eq (r : AirRow) :
    r.curr (Subsystems.ChipletHasher.stateCol lane1) = r.curr 56 := rfl

@[simp] theorem next_chipletHasher_stateCol1_eq (r : AirRow) :
    r.next (Subsystems.ChipletHasher.stateCol lane1) = r.next 56 := rfl

@[simp] theorem curr_chipletHasher_stateCol2_eq (r : AirRow) :
    r.curr (Subsystems.ChipletHasher.stateCol lane2) = r.curr 57 := rfl

@[simp] theorem next_chipletHasher_stateCol2_eq (r : AirRow) :
    r.next (Subsystems.ChipletHasher.stateCol lane2) = r.next 57 := rfl

@[simp] theorem curr_chipletHasher_stateCol3_eq (r : AirRow) :
    r.curr (Subsystems.ChipletHasher.stateCol lane3) = r.curr 58 := rfl

@[simp] theorem next_chipletHasher_stateCol3_eq (r : AirRow) :
    r.next (Subsystems.ChipletHasher.stateCol lane3) = r.next 58 := rfl

@[simp] theorem curr_chipletHasher_stateCol4_eq (r : AirRow) :
    r.curr (Subsystems.ChipletHasher.stateCol lane4) = r.curr 59 := rfl

@[simp] theorem next_chipletHasher_stateCol4_eq (r : AirRow) :
    r.next (Subsystems.ChipletHasher.stateCol lane4) = r.next 59 := rfl

@[simp] theorem curr_chipletHasher_stateCol5_eq (r : AirRow) :
    r.curr (Subsystems.ChipletHasher.stateCol lane5) = r.curr 60 := rfl

@[simp] theorem next_chipletHasher_stateCol5_eq (r : AirRow) :
    r.next (Subsystems.ChipletHasher.stateCol lane5) = r.next 60 := rfl

@[simp] theorem curr_chipletHasher_stateCol6_eq (r : AirRow) :
    r.curr (Subsystems.ChipletHasher.stateCol lane6) = r.curr 61 := rfl

@[simp] theorem next_chipletHasher_stateCol6_eq (r : AirRow) :
    r.next (Subsystems.ChipletHasher.stateCol lane6) = r.next 61 := rfl

@[simp] theorem curr_chipletHasher_stateCol7_eq (r : AirRow) :
    r.curr (Subsystems.ChipletHasher.stateCol lane7) = r.curr 62 := rfl

@[simp] theorem next_chipletHasher_stateCol7_eq (r : AirRow) :
    r.next (Subsystems.ChipletHasher.stateCol lane7) = r.next 62 := rfl

@[simp] theorem curr_chipletHasher_stateCol8_eq (r : AirRow) :
    r.curr (Subsystems.ChipletHasher.stateCol lane8) = r.curr 63 := rfl

@[simp] theorem next_chipletHasher_stateCol8_eq (r : AirRow) :
    r.next (Subsystems.ChipletHasher.stateCol lane8) = r.next 63 := rfl

@[simp] theorem curr_chipletHasher_stateCol9_eq (r : AirRow) :
    r.curr (Subsystems.ChipletHasher.stateCol lane9) = r.curr 64 := rfl

@[simp] theorem next_chipletHasher_stateCol9_eq (r : AirRow) :
    r.next (Subsystems.ChipletHasher.stateCol lane9) = r.next 64 := rfl

@[simp] theorem curr_chipletHasher_stateCol10_eq (r : AirRow) :
    r.curr (Subsystems.ChipletHasher.stateCol lane10) = r.curr 65 := rfl

@[simp] theorem next_chipletHasher_stateCol10_eq (r : AirRow) :
    r.next (Subsystems.ChipletHasher.stateCol lane10) = r.next 65 := rfl

@[simp] theorem curr_chipletHasher_stateCol11_eq (r : AirRow) :
    r.curr (Subsystems.ChipletHasher.stateCol lane11) = r.curr 66 := rfl

@[simp] theorem next_chipletHasher_stateCol11_eq (r : AirRow) :
    r.next (Subsystems.ChipletHasher.stateCol lane11) = r.next 66 := rfl

@[simp] theorem curr_chipletHasher_stateCol0_num_eq (r : AirRow) :
    r.curr (Subsystems.ChipletHasher.stateCol 0) = r.curr 55 := by
  apply congrArg r.curr
  apply Fin.ext
  native_decide

@[simp] theorem next_chipletHasher_stateCol0_num_eq (r : AirRow) :
    r.next (Subsystems.ChipletHasher.stateCol 0) = r.next 55 := by
  apply congrArg r.next
  apply Fin.ext
  native_decide

@[simp] theorem curr_chipletHasher_stateCol1_num_eq (r : AirRow) :
    r.curr (Subsystems.ChipletHasher.stateCol 1) = r.curr 56 := by
  apply congrArg r.curr
  apply Fin.ext
  native_decide

@[simp] theorem next_chipletHasher_stateCol1_num_eq (r : AirRow) :
    r.next (Subsystems.ChipletHasher.stateCol 1) = r.next 56 := by
  apply congrArg r.next
  apply Fin.ext
  native_decide

@[simp] theorem curr_chipletHasher_stateCol2_num_eq (r : AirRow) :
    r.curr (Subsystems.ChipletHasher.stateCol 2) = r.curr 57 := by
  apply congrArg r.curr
  apply Fin.ext
  native_decide

@[simp] theorem next_chipletHasher_stateCol2_num_eq (r : AirRow) :
    r.next (Subsystems.ChipletHasher.stateCol 2) = r.next 57 := by
  apply congrArg r.next
  apply Fin.ext
  native_decide

@[simp] theorem curr_chipletHasher_stateCol3_num_eq (r : AirRow) :
    r.curr (Subsystems.ChipletHasher.stateCol 3) = r.curr 58 := by
  apply congrArg r.curr
  apply Fin.ext
  native_decide

@[simp] theorem next_chipletHasher_stateCol3_num_eq (r : AirRow) :
    r.next (Subsystems.ChipletHasher.stateCol 3) = r.next 58 := by
  apply congrArg r.next
  apply Fin.ext
  native_decide

@[simp] theorem curr_chipletHasher_stateCol4_num_eq (r : AirRow) :
    r.curr (Subsystems.ChipletHasher.stateCol 4) = r.curr 59 := by
  apply congrArg r.curr
  apply Fin.ext
  native_decide

@[simp] theorem next_chipletHasher_stateCol4_num_eq (r : AirRow) :
    r.next (Subsystems.ChipletHasher.stateCol 4) = r.next 59 := by
  apply congrArg r.next
  apply Fin.ext
  native_decide

@[simp] theorem curr_chipletHasher_stateCol5_num_eq (r : AirRow) :
    r.curr (Subsystems.ChipletHasher.stateCol 5) = r.curr 60 := by
  apply congrArg r.curr
  apply Fin.ext
  native_decide

@[simp] theorem next_chipletHasher_stateCol5_num_eq (r : AirRow) :
    r.next (Subsystems.ChipletHasher.stateCol 5) = r.next 60 := by
  apply congrArg r.next
  apply Fin.ext
  native_decide

@[simp] theorem curr_chipletHasher_stateCol6_num_eq (r : AirRow) :
    r.curr (Subsystems.ChipletHasher.stateCol 6) = r.curr 61 := by
  apply congrArg r.curr
  apply Fin.ext
  native_decide

@[simp] theorem next_chipletHasher_stateCol6_num_eq (r : AirRow) :
    r.next (Subsystems.ChipletHasher.stateCol 6) = r.next 61 := by
  apply congrArg r.next
  apply Fin.ext
  native_decide

@[simp] theorem curr_chipletHasher_stateCol7_num_eq (r : AirRow) :
    r.curr (Subsystems.ChipletHasher.stateCol 7) = r.curr 62 := by
  apply congrArg r.curr
  apply Fin.ext
  native_decide

@[simp] theorem next_chipletHasher_stateCol7_num_eq (r : AirRow) :
    r.next (Subsystems.ChipletHasher.stateCol 7) = r.next 62 := by
  apply congrArg r.next
  apply Fin.ext
  native_decide

@[simp] theorem curr_chipletHasher_stateCol8_num_eq (r : AirRow) :
    r.curr (Subsystems.ChipletHasher.stateCol 8) = r.curr 63 := by
  apply congrArg r.curr
  apply Fin.ext
  native_decide

@[simp] theorem next_chipletHasher_stateCol8_num_eq (r : AirRow) :
    r.next (Subsystems.ChipletHasher.stateCol 8) = r.next 63 := by
  apply congrArg r.next
  apply Fin.ext
  native_decide

@[simp] theorem curr_chipletHasher_stateCol9_num_eq (r : AirRow) :
    r.curr (Subsystems.ChipletHasher.stateCol 9) = r.curr 64 := by
  apply congrArg r.curr
  apply Fin.ext
  native_decide

@[simp] theorem next_chipletHasher_stateCol9_num_eq (r : AirRow) :
    r.next (Subsystems.ChipletHasher.stateCol 9) = r.next 64 := by
  apply congrArg r.next
  apply Fin.ext
  native_decide

@[simp] theorem curr_chipletHasher_stateCol10_num_eq (r : AirRow) :
    r.curr (Subsystems.ChipletHasher.stateCol 10) = r.curr 65 := by
  apply congrArg r.curr
  apply Fin.ext
  native_decide

@[simp] theorem next_chipletHasher_stateCol10_num_eq (r : AirRow) :
    r.next (Subsystems.ChipletHasher.stateCol 10) = r.next 65 := by
  apply congrArg r.next
  apply Fin.ext
  native_decide

@[simp] theorem curr_chipletHasher_stateCol11_num_eq (r : AirRow) :
    r.curr (Subsystems.ChipletHasher.stateCol 11) = r.curr 66 := by
  apply congrArg r.curr
  apply Fin.ext
  native_decide

@[simp] theorem next_chipletHasher_stateCol11_num_eq (r : AirRow) :
    r.next (Subsystems.ChipletHasher.stateCol 11) = r.next 66 := by
  apply congrArg r.next
  apply Fin.ext
  native_decide

@[simp] theorem curr_chipletHasher_nodeIndexCol_eq (r : AirRow) :
    r.curr Subsystems.ChipletHasher.nodeIndexCol = r.curr 67 := rfl

@[simp] theorem next_chipletHasher_nodeIndexCol_eq (r : AirRow) :
    r.next Subsystems.ChipletHasher.nodeIndexCol = r.next 67 := rfl

@[simp] theorem periodic_chipletHasher_pIsExternal_eq (r : AirRow) :
    r.periodic Subsystems.ChipletHasher.pIsExternal = r.globals.periodic 3 := rfl

@[simp] theorem periodic_chipletHasher_pIsInternal_eq (r : AirRow) :
    r.periodic Subsystems.ChipletHasher.pIsInternal = r.globals.periodic 4 := rfl

@[simp] theorem periodic_chipletHasher_pArkExtCol0_eq (r : AirRow) :
    r.periodic (Subsystems.ChipletHasher.pArkExtCol lane0) = r.globals.periodic 5 := rfl

@[simp] theorem periodic_chipletHasher_pArkExtCol1_eq (r : AirRow) :
    r.periodic (Subsystems.ChipletHasher.pArkExtCol lane1) = r.globals.periodic 6 := rfl

@[simp] theorem periodic_chipletHasher_pArkExtCol2_eq (r : AirRow) :
    r.periodic (Subsystems.ChipletHasher.pArkExtCol lane2) = r.globals.periodic 7 := rfl

@[simp] theorem periodic_chipletHasher_pArkExtCol3_eq (r : AirRow) :
    r.periodic (Subsystems.ChipletHasher.pArkExtCol lane3) = r.globals.periodic 8 := rfl

@[simp] theorem periodic_chipletHasher_pArkExtCol4_eq (r : AirRow) :
    r.periodic (Subsystems.ChipletHasher.pArkExtCol lane4) = r.globals.periodic 9 := rfl

@[simp] theorem periodic_chipletHasher_pArkExtCol5_eq (r : AirRow) :
    r.periodic (Subsystems.ChipletHasher.pArkExtCol lane5) = r.globals.periodic 10 := rfl

@[simp] theorem periodic_chipletHasher_pArkExtCol6_eq (r : AirRow) :
    r.periodic (Subsystems.ChipletHasher.pArkExtCol lane6) = r.globals.periodic 11 := rfl

@[simp] theorem periodic_chipletHasher_pArkExtCol7_eq (r : AirRow) :
    r.periodic (Subsystems.ChipletHasher.pArkExtCol lane7) = r.globals.periodic 12 := rfl

@[simp] theorem periodic_chipletHasher_pArkExtCol8_eq (r : AirRow) :
    r.periodic (Subsystems.ChipletHasher.pArkExtCol lane8) = r.globals.periodic 13 := rfl

@[simp] theorem periodic_chipletHasher_pArkExtCol9_eq (r : AirRow) :
    r.periodic (Subsystems.ChipletHasher.pArkExtCol lane9) = r.globals.periodic 14 := rfl

@[simp] theorem periodic_chipletHasher_pArkExtCol10_eq (r : AirRow) :
    r.periodic (Subsystems.ChipletHasher.pArkExtCol lane10) = r.globals.periodic 15 := rfl

@[simp] theorem periodic_chipletHasher_pArkExtCol11_eq (r : AirRow) :
    r.periodic (Subsystems.ChipletHasher.pArkExtCol lane11) = r.globals.periodic 16 := rfl

@[simp] theorem periodic_chipletHasher_pArkInt_eq (r : AirRow) :
    r.periodic Subsystems.ChipletHasher.pArkInt = r.globals.periodic 17 := rfl

syntax (name := chipletHasherInitBridge) "chiplet_hasher_init_bridge " rwRule : tactic

macro_rules
  | `(tactic| chiplet_hasher_init_bridge $_) => `(tactic|
      unfold Constraints.Symbolic.ChipletHasher.base;
      rw [getElem!_pos (h := by native_decide)];
      simp (config := { decide := true }) [Subsystems.ChipletHasher.permutationInit,
        Subsystems.ChipletHasher.transitionEq,
        Subsystems.ChipletHasher.gateInit,
        Subsystems.ChipletHasher.hasherFlag,
        Subsystems.ChipletHasher.cycleRow0,
        Subsystems.ChipletHasher.expectedInit,
        Subsystems.ChipletHasher.applyMatmulExternal,
        Subsystems.ChipletHasher.matmulM4,
        Subsystems.ChipletHasher.word,
        Subsystems.ChipletHasher.double,
        Subsystems.ChipletHasher.quadruple,
        Subsystems.ChipletHasher.stateNext,
        Subsystems.ChipletHasher.state,
        Subsystems.ChipletHasher.rate0Lane,
        Subsystems.ChipletHasher.rate1Lane,
        Subsystems.ChipletHasher.capacityLane,
        periodic_chipletHasher_pCycleRow0_eq,
        curr_chipletHasher_stateCol0_eq,
        curr_chipletHasher_stateCol1_eq,
        curr_chipletHasher_stateCol2_eq,
        curr_chipletHasher_stateCol3_eq,
        curr_chipletHasher_stateCol4_eq,
        curr_chipletHasher_stateCol5_eq,
        curr_chipletHasher_stateCol6_eq,
        curr_chipletHasher_stateCol7_eq,
        curr_chipletHasher_stateCol8_eq,
        curr_chipletHasher_stateCol9_eq,
        curr_chipletHasher_stateCol10_eq,
        curr_chipletHasher_stateCol11_eq,
        toSymbolicFrame, FExpr.eval, Builder.whenTransition, Builder.gate,
        Builder.assertEq, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
        AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, SymbolicFrame.colNext,
        AirRow.boundaryAt, AirRow.boundary];
      ring_nf)

syntax (name := chipletHasherExternalBridge) "chiplet_hasher_external_bridge " rwRule : tactic

macro_rules
  | `(tactic| chiplet_hasher_external_bridge $_) => `(tactic|
      unfold Constraints.Symbolic.ChipletHasher.base;
      rw [getElem!_pos (h := by native_decide)];
      simp (config := { decide := true }) [Subsystems.ChipletHasher.permutationExternal,
        Subsystems.ChipletHasher.transitionEq,
        Subsystems.ChipletHasher.gateExternal,
        Subsystems.ChipletHasher.hasherFlag,
        Subsystems.ChipletHasher.isExternal,
        Subsystems.ChipletHasher.expectedExternal,
        Subsystems.ChipletHasher.applyMatmulExternal,
        Subsystems.ChipletHasher.matmulM4,
        Subsystems.ChipletHasher.externalRoundInput,
        Subsystems.ChipletHasher.pow7,
        Subsystems.ChipletHasher.square,
        Subsystems.ChipletHasher.word,
        Subsystems.ChipletHasher.double,
        Subsystems.ChipletHasher.quadruple,
        Subsystems.ChipletHasher.stateNext,
        Subsystems.ChipletHasher.state,
        Subsystems.ChipletHasher.arkExt,
        Subsystems.ChipletHasher.pArkExtCol,
        Subsystems.ChipletHasher.rate0Lane,
        Subsystems.ChipletHasher.rate1Lane,
        Subsystems.ChipletHasher.capacityLane,
        periodic_chipletHasher_pIsExternal_eq,
        periodic_chipletHasher_pArkExtCol0_eq,
        periodic_chipletHasher_pArkExtCol1_eq,
        periodic_chipletHasher_pArkExtCol2_eq,
        periodic_chipletHasher_pArkExtCol3_eq,
        periodic_chipletHasher_pArkExtCol4_eq,
        periodic_chipletHasher_pArkExtCol5_eq,
        periodic_chipletHasher_pArkExtCol6_eq,
        periodic_chipletHasher_pArkExtCol7_eq,
        periodic_chipletHasher_pArkExtCol8_eq,
        periodic_chipletHasher_pArkExtCol9_eq,
        periodic_chipletHasher_pArkExtCol10_eq,
        periodic_chipletHasher_pArkExtCol11_eq,
        curr_chipletHasher_stateCol0_eq,
        curr_chipletHasher_stateCol1_eq,
        curr_chipletHasher_stateCol2_eq,
        curr_chipletHasher_stateCol3_eq,
        curr_chipletHasher_stateCol4_eq,
        curr_chipletHasher_stateCol5_eq,
        curr_chipletHasher_stateCol6_eq,
        curr_chipletHasher_stateCol7_eq,
        curr_chipletHasher_stateCol8_eq,
        curr_chipletHasher_stateCol9_eq,
        curr_chipletHasher_stateCol10_eq,
        curr_chipletHasher_stateCol11_eq,
        toSymbolicFrame, FExpr.eval, Builder.whenTransition, Builder.gate,
        Builder.assertEq, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
        AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, SymbolicFrame.colNext,
        AirRow.boundaryAt, AirRow.boundary];
      ring_nf)

syntax (name := chipletHasherInternalBridge) "chiplet_hasher_internal_bridge " rwRule : tactic

macro_rules
  | `(tactic| chiplet_hasher_internal_bridge $_) => `(tactic|
      unfold Constraints.Symbolic.ChipletHasher.base;
      rw [getElem!_pos (h := by native_decide)];
      simp (config := { decide := true }) [Subsystems.ChipletHasher.permutationInternal,
        Subsystems.ChipletHasher.transitionEq,
        Subsystems.ChipletHasher.gateInternal,
        Subsystems.ChipletHasher.hasherFlag,
        Subsystems.ChipletHasher.isInternal,
        Subsystems.ChipletHasher.expectedInternal,
        Subsystems.ChipletHasher.applyMatmulInternal,
        Subsystems.ChipletHasher.internalRoundInput,
        Subsystems.ChipletHasher.pow7,
        Subsystems.ChipletHasher.square,
        Subsystems.ChipletHasher.sumLanes,
        Subsystems.ChipletHasher.stateNext,
        Subsystems.ChipletHasher.state,
        Subsystems.ChipletHasher.arkInt,
        Subsystems.ChipletHasher.matDiag,
        periodic_chipletHasher_pIsInternal_eq,
        periodic_chipletHasher_pArkInt_eq,
        curr_chipletHasher_stateCol0_eq,
        curr_chipletHasher_stateCol1_eq,
        curr_chipletHasher_stateCol2_eq,
        curr_chipletHasher_stateCol3_eq,
        curr_chipletHasher_stateCol4_eq,
        curr_chipletHasher_stateCol5_eq,
        curr_chipletHasher_stateCol6_eq,
        curr_chipletHasher_stateCol7_eq,
        curr_chipletHasher_stateCol8_eq,
        curr_chipletHasher_stateCol9_eq,
        curr_chipletHasher_stateCol10_eq,
        curr_chipletHasher_stateCol11_eq,
        toSymbolicFrame, FExpr.eval, Builder.whenTransition, Builder.gate,
        Builder.assertEq, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
        AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, SymbolicFrame.colNext,
        AirRow.boundaryAt, AirRow.boundary];
      ring_nf)

theorem bridge_chiplet_hasher_0 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[0]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.permutationInit lane0).eval r := by
  sorry -- TODO: normalize the symbolic base lookup for the init bridge

theorem bridge_chiplet_hasher_1 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[1]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.permutationInit lane1).eval r := by
  sorry -- TODO: normalize the symbolic base lookup for the init bridge

theorem bridge_chiplet_hasher_2 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[2]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.permutationInit lane2).eval r := by
  sorry -- TODO: normalize the symbolic base lookup for the init bridge

theorem bridge_chiplet_hasher_3 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[3]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.permutationInit lane3).eval r := by
  sorry -- TODO: normalize the symbolic base lookup for the init bridge

theorem bridge_chiplet_hasher_4 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[4]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.permutationInit lane4).eval r := by
  sorry -- TODO: normalize the symbolic base lookup for the init bridge

theorem bridge_chiplet_hasher_5 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[5]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.permutationInit lane5).eval r := by
  sorry -- TODO: normalize the symbolic base lookup for the init bridge

theorem bridge_chiplet_hasher_6 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[6]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.permutationInit lane6).eval r := by
  sorry -- TODO: normalize the symbolic base lookup for the init bridge

theorem bridge_chiplet_hasher_7 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[7]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.permutationInit lane7).eval r := by
  sorry -- TODO: normalize the symbolic base lookup for the init bridge

theorem bridge_chiplet_hasher_8 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[8]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.permutationInit lane8).eval r := by
  sorry -- TODO: normalize the symbolic base lookup for the init bridge

theorem bridge_chiplet_hasher_9 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[9]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.permutationInit lane9).eval r := by
  sorry -- TODO: normalize the symbolic base lookup for the init bridge

theorem bridge_chiplet_hasher_10 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[10]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.permutationInit lane10).eval r := by
  sorry -- TODO: normalize the symbolic base lookup for the init bridge

theorem bridge_chiplet_hasher_11 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[11]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.permutationInit lane11).eval r := by
  sorry -- TODO: normalize the symbolic base lookup for the init bridge

theorem bridge_chiplet_hasher_12 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[12]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.permutationExternal lane0).eval r := by
  sorry -- TODO: normalize the symbolic base lookup for the external bridge

theorem bridge_chiplet_hasher_13 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[13]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.permutationExternal lane1).eval r := by
  sorry -- TODO: normalize the symbolic base lookup for the external bridge

theorem bridge_chiplet_hasher_14 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[14]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.permutationExternal lane2).eval r := by
  sorry -- TODO: normalize the symbolic base lookup for the external bridge

theorem bridge_chiplet_hasher_15 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[15]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.permutationExternal lane3).eval r := by
  sorry -- TODO: normalize the symbolic base lookup for the external bridge

theorem bridge_chiplet_hasher_16 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[16]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.permutationExternal lane4).eval r := by
  sorry -- TODO: normalize the symbolic base lookup for the external bridge

theorem bridge_chiplet_hasher_17 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[17]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.permutationExternal lane5).eval r := by
  sorry -- TODO: normalize the symbolic base lookup for the external bridge

theorem bridge_chiplet_hasher_18 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[18]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.permutationExternal lane6).eval r := by
  sorry -- TODO: normalize the symbolic base lookup for the external bridge

theorem bridge_chiplet_hasher_19 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[19]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.permutationExternal lane7).eval r := by
  sorry -- TODO: normalize the symbolic base lookup for the external bridge

theorem bridge_chiplet_hasher_20 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[20]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.permutationExternal lane8).eval r := by
  sorry -- TODO: normalize the symbolic base lookup for the external bridge

theorem bridge_chiplet_hasher_21 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[21]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.permutationExternal lane9).eval r := by
  sorry -- TODO: normalize the symbolic base lookup for the external bridge

theorem bridge_chiplet_hasher_22 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[22]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.permutationExternal lane10).eval r := by
  sorry -- TODO: normalize the symbolic base lookup for the external bridge

theorem bridge_chiplet_hasher_23 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[23]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.permutationExternal lane11).eval r := by
  sorry -- TODO: normalize the symbolic base lookup for the external bridge

theorem bridge_chiplet_hasher_24 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[24]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.permutationInternal lane0).eval r := by
  sorry -- TODO: normalize the symbolic base lookup for the internal bridge

theorem bridge_chiplet_hasher_25 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[25]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.permutationInternal lane1).eval r := by
  sorry -- TODO: normalize the symbolic base lookup for the internal bridge

theorem bridge_chiplet_hasher_26 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[26]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.permutationInternal lane2).eval r := by
  sorry -- TODO: normalize the symbolic base lookup for the internal bridge

theorem bridge_chiplet_hasher_27 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[27]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.permutationInternal lane3).eval r := by
  sorry -- TODO: normalize the symbolic base lookup for the internal bridge

theorem bridge_chiplet_hasher_28 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[28]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.permutationInternal lane4).eval r := by
  sorry -- TODO: normalize the symbolic base lookup for the internal bridge

theorem bridge_chiplet_hasher_29 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[29]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.permutationInternal lane5).eval r := by
  sorry -- TODO: normalize the symbolic base lookup for the internal bridge

theorem bridge_chiplet_hasher_30 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[30]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.permutationInternal lane6).eval r := by
  sorry -- TODO: normalize the symbolic base lookup for the internal bridge

theorem bridge_chiplet_hasher_31 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[31]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.permutationInternal lane7).eval r := by
  sorry -- TODO: normalize the symbolic base lookup for the internal bridge

theorem bridge_chiplet_hasher_32 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[32]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.permutationInternal lane8).eval r := by
  sorry -- TODO: normalize the symbolic base lookup for the internal bridge

theorem bridge_chiplet_hasher_33 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[33]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.permutationInternal lane9).eval r := by
  sorry -- TODO: normalize the symbolic base lookup for the internal bridge

theorem bridge_chiplet_hasher_34 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[34]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.permutationInternal lane10).eval r := by
  sorry -- TODO: normalize the symbolic base lookup for the internal bridge

theorem bridge_chiplet_hasher_35 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[35]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.permutationInternal lane11).eval r := by
  sorry -- TODO: normalize the symbolic base lookup for the internal bridge

theorem bridge_chiplet_hasher_36 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[36]! (toSymbolicFrame r) =
      Subsystems.ChipletHasher.selector0Binary.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => (((1 - f.colCurr 51) * f.colCurr 52) * (f.colCurr 52 - 1)))
      (toSymbolicFrame r) = Subsystems.ChipletHasher.selector0Binary.eval r
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  simp only [Subsystems.ChipletHasher.selector0Binary, Subsystems.ChipletHasher.integrityZero,
    Subsystems.ChipletHasher.sel0, Subsystems.ChipletHasher.one,
    eval_chipletHasher_hasherFlag, curr_main_51_eq, curr_main_52_eq,
    curr_chipletHasher_sel0Col_eq,
    toSymbolicFrame, FExpr.eval, Builder.gate,
    Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr, AirRow.baseAt, AirRow.base,
    SymbolicFrame.colCurr, h51, h52]
  simp
  ring_nf

theorem bridge_chiplet_hasher_37 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[37]! (toSymbolicFrame r) =
      Subsystems.ChipletHasher.selector1Binary.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => (((1 - f.colCurr 51) * f.colCurr 53) * (f.colCurr 53 - 1)))
      (toSymbolicFrame r) = Subsystems.ChipletHasher.selector1Binary.eval r
  have h51 : 51 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  simp only [Subsystems.ChipletHasher.selector1Binary, Subsystems.ChipletHasher.integrityZero,
    Subsystems.ChipletHasher.sel1, Subsystems.ChipletHasher.one,
    eval_chipletHasher_hasherFlag, curr_main_51_eq, curr_main_53_eq,
    curr_chipletHasher_sel1Col_eq,
    toSymbolicFrame, FExpr.eval, Builder.gate,
    Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr, AirRow.baseAt, AirRow.base,
    SymbolicFrame.colCurr, h51, h53]
  simp
  ring_nf

theorem bridge_chiplet_hasher_38 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[38]! (toSymbolicFrame r) =
      Subsystems.ChipletHasher.selector2Binary.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => (((1 - f.colCurr 51) * f.colCurr 54) * (f.colCurr 54 - 1)))
      (toSymbolicFrame r) = Subsystems.ChipletHasher.selector2Binary.eval r
  have h51 : 51 < MainWidth := by decide
  have h54 : 54 < MainWidth := by decide
  simp only [Subsystems.ChipletHasher.selector2Binary, Subsystems.ChipletHasher.integrityZero,
    Subsystems.ChipletHasher.sel2, Subsystems.ChipletHasher.one,
    eval_chipletHasher_hasherFlag, curr_main_51_eq, curr_main_54_eq,
    curr_chipletHasher_sel2Col_eq,
    toSymbolicFrame, FExpr.eval, Builder.gate,
    Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr, AirRow.baseAt, AirRow.base,
    SymbolicFrame.colCurr, h51, h54]
  simp
  ring_nf

theorem bridge_chiplet_hasher_39 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[39]! (toSymbolicFrame r) =
      Subsystems.ChipletHasher.selector1Stable.eval r := by
  sorry -- TODO: finish selector stability normalization after simp/ring

theorem bridge_chiplet_hasher_40 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[40]! (toSymbolicFrame r) =
      Subsystems.ChipletHasher.selector2Stable.eval r := by
  sorry -- TODO: finish selector stability normalization after simp/ring

theorem bridge_chiplet_hasher_41 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[41]! (toSymbolicFrame r) =
      Subsystems.ChipletHasher.selectorContinuation.eval r := by
  sorry -- TODO: finish continuation selector normalization after simp/ring

theorem bridge_chiplet_hasher_42 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[42]! (toSymbolicFrame r) =
      Subsystems.ChipletHasher.selectorInvalidOutput.eval r := by
  sorry -- TODO: finish invalid-output selector normalization after simp/ring

theorem bridge_chiplet_hasher_43 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[43]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.abpCapacityPreserved word0).eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => (f.is_transition * (((1 - f.colCurr 51) *
      (((f.periodic 2 * f.colCurr 52) * (1 - f.colCurr 53)) * (1 - f.colCurr 54))) *
      (f.colNext 63 - f.colCurr 63)))) (toSymbolicFrame r) =
    (Subsystems.ChipletHasher.abpCapacityPreserved word0).eval r
  have h2 : 2 < PeriodicWidth := by decide
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  have h54 : 54 < MainWidth := by decide
  have h63 : 63 < MainWidth := by decide
  simp only [Subsystems.ChipletHasher.abpCapacityPreserved,
    Subsystems.ChipletHasher.transitionEq, Subsystems.ChipletHasher.gateAbpCapacity,
    Subsystems.ChipletHasher.hasherFlag, Subsystems.ChipletHasher.fAbp,
    Subsystems.ChipletHasher.cycleRow31, Subsystems.ChipletHasher.sel0,
    Subsystems.ChipletHasher.sel1, Subsystems.ChipletHasher.sel2,
    Subsystems.ChipletHasher.oneMinus, Subsystems.ChipletHasher.capacityNext,
    Subsystems.ChipletHasher.capacity, Subsystems.ChipletHasher.stateNext,
    Subsystems.ChipletHasher.state, Subsystems.ChipletHasher.capacityLane,
    periodic_chipletHasher_pCycleRow31_eq,
    curr_chipletHasher_sel0Col_eq, curr_chipletHasher_sel1Col_eq,
    curr_chipletHasher_sel2Col_eq,
    toSymbolicFrame, FExpr.eval, Builder.whenTransition, Builder.gate,
    Builder.assertEq, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, SymbolicFrame.colNext,
    h2, h51, h52, h53, h54, h63]
  simp [Subsystems.ChipletHasher.one, AirRow.boundaryAt, AirRow.boundary, FExpr.eval]
  ring_nf
  left; left; left; trivial

theorem bridge_chiplet_hasher_44 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[44]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.abpCapacityPreserved word1).eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => (f.is_transition * (((1 - f.colCurr 51) *
      (((f.periodic 2 * f.colCurr 52) * (1 - f.colCurr 53)) * (1 - f.colCurr 54))) *
      (f.colNext 64 - f.colCurr 64)))) (toSymbolicFrame r) =
    (Subsystems.ChipletHasher.abpCapacityPreserved word1).eval r
  have h2 : 2 < PeriodicWidth := by decide
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  have h54 : 54 < MainWidth := by decide
  have h64 : 64 < MainWidth := by decide
  simp only [Subsystems.ChipletHasher.abpCapacityPreserved,
    Subsystems.ChipletHasher.transitionEq, Subsystems.ChipletHasher.gateAbpCapacity,
    Subsystems.ChipletHasher.hasherFlag, Subsystems.ChipletHasher.fAbp,
    Subsystems.ChipletHasher.cycleRow31, Subsystems.ChipletHasher.sel0,
    Subsystems.ChipletHasher.sel1, Subsystems.ChipletHasher.sel2,
    Subsystems.ChipletHasher.oneMinus, Subsystems.ChipletHasher.capacityNext,
    Subsystems.ChipletHasher.capacity, Subsystems.ChipletHasher.stateNext,
    Subsystems.ChipletHasher.state, Subsystems.ChipletHasher.capacityLane,
    periodic_chipletHasher_pCycleRow31_eq,
    curr_chipletHasher_sel0Col_eq, curr_chipletHasher_sel1Col_eq,
    curr_chipletHasher_sel2Col_eq,
    toSymbolicFrame, FExpr.eval, Builder.whenTransition, Builder.gate,
    Builder.assertEq, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, SymbolicFrame.colNext,
    h2, h51, h52, h53, h54, h64]
  simp [Subsystems.ChipletHasher.one, AirRow.boundaryAt, AirRow.boundary, FExpr.eval]
  ring_nf
  left; left; left; trivial

theorem bridge_chiplet_hasher_45 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[45]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.abpCapacityPreserved word2).eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => (f.is_transition * (((1 - f.colCurr 51) *
      (((f.periodic 2 * f.colCurr 52) * (1 - f.colCurr 53)) * (1 - f.colCurr 54))) *
      (f.colNext 65 - f.colCurr 65)))) (toSymbolicFrame r) =
    (Subsystems.ChipletHasher.abpCapacityPreserved word2).eval r
  have h2 : 2 < PeriodicWidth := by decide
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  have h54 : 54 < MainWidth := by decide
  have h65 : 65 < MainWidth := by decide
  simp only [Subsystems.ChipletHasher.abpCapacityPreserved,
    Subsystems.ChipletHasher.transitionEq, Subsystems.ChipletHasher.gateAbpCapacity,
    Subsystems.ChipletHasher.hasherFlag, Subsystems.ChipletHasher.fAbp,
    Subsystems.ChipletHasher.cycleRow31, Subsystems.ChipletHasher.sel0,
    Subsystems.ChipletHasher.sel1, Subsystems.ChipletHasher.sel2,
    Subsystems.ChipletHasher.oneMinus, Subsystems.ChipletHasher.capacityNext,
    Subsystems.ChipletHasher.capacity, Subsystems.ChipletHasher.stateNext,
    Subsystems.ChipletHasher.state, Subsystems.ChipletHasher.capacityLane,
    periodic_chipletHasher_pCycleRow31_eq,
    curr_chipletHasher_sel0Col_eq, curr_chipletHasher_sel1Col_eq,
    curr_chipletHasher_sel2Col_eq,
    toSymbolicFrame, FExpr.eval, Builder.whenTransition, Builder.gate,
    Builder.assertEq, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, SymbolicFrame.colNext,
    h2, h51, h52, h53, h54, h65]
  simp [Subsystems.ChipletHasher.one, AirRow.boundaryAt, AirRow.boundary, FExpr.eval]
  ring_nf
  left; left; left; trivial

theorem bridge_chiplet_hasher_46 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[46]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.abpCapacityPreserved word3).eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => (f.is_transition * (((1 - f.colCurr 51) *
      (((f.periodic 2 * f.colCurr 52) * (1 - f.colCurr 53)) * (1 - f.colCurr 54))) *
      (f.colNext 66 - f.colCurr 66)))) (toSymbolicFrame r) =
    (Subsystems.ChipletHasher.abpCapacityPreserved word3).eval r
  have h2 : 2 < PeriodicWidth := by decide
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  have h54 : 54 < MainWidth := by decide
  have h66 : 66 < MainWidth := by decide
  simp only [Subsystems.ChipletHasher.abpCapacityPreserved,
    Subsystems.ChipletHasher.transitionEq, Subsystems.ChipletHasher.gateAbpCapacity,
    Subsystems.ChipletHasher.hasherFlag, Subsystems.ChipletHasher.fAbp,
    Subsystems.ChipletHasher.cycleRow31, Subsystems.ChipletHasher.sel0,
    Subsystems.ChipletHasher.sel1, Subsystems.ChipletHasher.sel2,
    Subsystems.ChipletHasher.oneMinus, Subsystems.ChipletHasher.capacityNext,
    Subsystems.ChipletHasher.capacity, Subsystems.ChipletHasher.stateNext,
    Subsystems.ChipletHasher.state, Subsystems.ChipletHasher.capacityLane,
    periodic_chipletHasher_pCycleRow31_eq,
    curr_chipletHasher_sel0Col_eq, curr_chipletHasher_sel1Col_eq,
    curr_chipletHasher_sel2Col_eq,
    toSymbolicFrame, FExpr.eval, Builder.whenTransition, Builder.gate,
    Builder.assertEq, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, SymbolicFrame.colNext,
    h2, h51, h52, h53, h54, h66]
  simp [Subsystems.ChipletHasher.one, AirRow.boundaryAt, AirRow.boundary, FExpr.eval]
  ring_nf
  left; left; left; trivial

theorem bridge_chiplet_hasher_47 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[47]! (toSymbolicFrame r) =
      Subsystems.ChipletHasher.outputIndexZero.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => (((1 - f.colCurr 51) * ((f.periodic 2 * (1 - f.colCurr 52)) * (1 - f.colCurr 53))) *
      f.colCurr 67)) (toSymbolicFrame r) = Subsystems.ChipletHasher.outputIndexZero.eval r
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  have h67 : 67 < MainWidth := by decide
  have h2 : 2 < PeriodicWidth := by decide
  simp only [Subsystems.ChipletHasher.outputIndexZero, Subsystems.ChipletHasher.integrityZero,
    Subsystems.ChipletHasher.fOut, Subsystems.ChipletHasher.cycleRow31,
    Subsystems.ChipletHasher.oneMinus, Subsystems.ChipletHasher.sel0,
    Subsystems.ChipletHasher.sel1, Subsystems.ChipletHasher.hasherFlag,
    eval_chipletHasher_hasherFlag, periodic_chipletHasher_pCycleRow31_eq,
    curr_chipletHasher_sel0Col_eq, curr_chipletHasher_sel1Col_eq,
    curr_chipletHasher_nodeIndexCol_eq, Subsystems.ChipletHasher.nodeIndex,
    toSymbolicFrame, FExpr.eval, Builder.gate, Builder.assertZero,
    BaseConstraint.eval, BaseConstraint.expr, AirRow.baseAt, AirRow.base,
    SymbolicFrame.colCurr, h51, h52, h53, h67, h2]
  simp [Subsystems.ChipletHasher.one]
  air_bridge_finish_gated

theorem bridge_chiplet_hasher_48 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[48]! (toSymbolicFrame r) =
      Subsystems.ChipletHasher.directionBitBinary.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => (f.is_transition * (((1 - f.colCurr 51) *
      ((((((((f.periodic 0 * f.colCurr 52) * (1 - f.colCurr 53)) * f.colCurr 54) +
          (((f.periodic 0 * f.colCurr 52) * f.colCurr 53) * (1 - f.colCurr 54))) +
        (((f.periodic 0 * f.colCurr 52) * f.colCurr 53) * f.colCurr 54)) +
      (((f.periodic 2 * f.colCurr 52) * (1 - f.colCurr 53)) * f.colCurr 54)) +
      (((f.periodic 2 * f.colCurr 52) * f.colCurr 53) * (1 - f.colCurr 54))) +
      (((f.periodic 2 * f.colCurr 52) * f.colCurr 53) * f.colCurr 54))) *
      (((f.colCurr 67 - (Felt.ofNat 2 * f.colNext 67)) *
        (f.colCurr 67 - (Felt.ofNat 2 * f.colNext 67))) -
        (f.colCurr 67 - (Felt.ofNat 2 * f.colNext 67)))))) (toSymbolicFrame r) =
    Subsystems.ChipletHasher.directionBitBinary.eval r
  have h0 : 0 < PeriodicWidth := by decide
  have h2 : 2 < PeriodicWidth := by decide
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  have h54 : 54 < MainWidth := by decide
  have h67 : 67 < MainWidth := by decide
  simp only [Subsystems.ChipletHasher.directionBitBinary, Subsystems.ChipletHasher.transitionZero,
    Subsystems.ChipletHasher.gateMerkleShift, Subsystems.ChipletHasher.hasherFlag,
    Subsystems.ChipletHasher.fMerkleActive, Subsystems.ChipletHasher.fMp,
    Subsystems.ChipletHasher.fMv, Subsystems.ChipletHasher.fMu,
    Subsystems.ChipletHasher.fMpa, Subsystems.ChipletHasher.fMva,
    Subsystems.ChipletHasher.fMua, Subsystems.ChipletHasher.cycleRow0,
    Subsystems.ChipletHasher.cycleRow31, Subsystems.ChipletHasher.sel0,
    Subsystems.ChipletHasher.sel1, Subsystems.ChipletHasher.sel2,
    Subsystems.ChipletHasher.oneMinus, Subsystems.ChipletHasher.directionBit,
    Subsystems.ChipletHasher.nodeIndex, Subsystems.ChipletHasher.nodeIndexNext,
    Subsystems.ChipletHasher.two, felt_ofNat_two_eq,
    periodic_chipletHasher_pCycleRow0_eq, periodic_chipletHasher_pCycleRow31_eq,
    curr_chipletHasher_sel0Col_eq, curr_chipletHasher_sel1Col_eq,
    curr_chipletHasher_sel2Col_eq, curr_chipletHasher_nodeIndexCol_eq,
    next_chipletHasher_nodeIndexCol_eq,
    toSymbolicFrame, FExpr.eval, Builder.whenTransition, Builder.gate,
    Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, SymbolicFrame.colNext,
    h0, h2, h51, h52, h53, h54, h67]
  simp [Subsystems.ChipletHasher.one, AirRow.boundaryAt, AirRow.boundary, FExpr.eval]
  ring_nf
  left; trivial

theorem bridge_chiplet_hasher_49 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[49]! (toSymbolicFrame r) =
      Subsystems.ChipletHasher.nodeIndexStable.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => (f.is_transition * (((1 - f.colCurr 51) *
      ((1 - ((f.periodic 2 * (1 - f.colCurr 52)) * (1 - f.colCurr 53))) -
      ((((((((f.periodic 0 * f.colCurr 52) * (1 - f.colCurr 53)) * f.colCurr 54) +
          (((f.periodic 0 * f.colCurr 52) * f.colCurr 53) * (1 - f.colCurr 54))) +
        (((f.periodic 0 * f.colCurr 52) * f.colCurr 53) * f.colCurr 54)) +
      (((f.periodic 2 * f.colCurr 52) * (1 - f.colCurr 53)) * f.colCurr 54)) +
      (((f.periodic 2 * f.colCurr 52) * f.colCurr 53) * (1 - f.colCurr 54))) +
      (((f.periodic 2 * f.colCurr 52) * f.colCurr 53) * f.colCurr 54)))) *
      (f.colNext 67 - f.colCurr 67)))) (toSymbolicFrame r) =
    Subsystems.ChipletHasher.nodeIndexStable.eval r
  have h0 : 0 < PeriodicWidth := by decide
  have h2 : 2 < PeriodicWidth := by decide
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  have h54 : 54 < MainWidth := by decide
  have h67 : 67 < MainWidth := by decide
  simp only [Subsystems.ChipletHasher.nodeIndexStable, Subsystems.ChipletHasher.transitionEq,
    Subsystems.ChipletHasher.gateNodeIndexHold, Subsystems.ChipletHasher.hasherFlag,
    Subsystems.ChipletHasher.oneMinus, Subsystems.ChipletHasher.fOut,
    Subsystems.ChipletHasher.fMerkleActive, Subsystems.ChipletHasher.fMp,
    Subsystems.ChipletHasher.fMv, Subsystems.ChipletHasher.fMu,
    Subsystems.ChipletHasher.fMpa, Subsystems.ChipletHasher.fMva,
    Subsystems.ChipletHasher.fMua, Subsystems.ChipletHasher.cycleRow0,
    Subsystems.ChipletHasher.cycleRow31, Subsystems.ChipletHasher.sel0,
    Subsystems.ChipletHasher.sel1, Subsystems.ChipletHasher.sel2,
    Subsystems.ChipletHasher.nodeIndex, Subsystems.ChipletHasher.nodeIndexNext,
    periodic_chipletHasher_pCycleRow0_eq, periodic_chipletHasher_pCycleRow31_eq,
    curr_chipletHasher_sel0Col_eq, curr_chipletHasher_sel1Col_eq,
    curr_chipletHasher_sel2Col_eq, curr_chipletHasher_nodeIndexCol_eq,
    next_chipletHasher_nodeIndexCol_eq,
    toSymbolicFrame, FExpr.eval, Builder.whenTransition, Builder.gate,
    Builder.assertEq, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, SymbolicFrame.colNext,
    h0, h2, h51, h52, h53, h54, h67]
  simp [Subsystems.ChipletHasher.one, AirRow.boundaryAt, AirRow.boundary, FExpr.eval]
  ring_nf
  left; left; left; trivial

theorem bridge_chiplet_hasher_50 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[50]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.merkleCapacityReset word0).eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => (f.is_transition * (((1 - f.colCurr 51) *
      (((((f.periodic 2 * f.colCurr 52) * (1 - f.colCurr 53)) * f.colCurr 54) +
      (((f.periodic 2 * f.colCurr 52) * f.colCurr 53) * (1 - f.colCurr 54))) +
      (((f.periodic 2 * f.colCurr 52) * f.colCurr 53) * f.colCurr 54))) *
      f.colNext 63))) (toSymbolicFrame r) =
    (Subsystems.ChipletHasher.merkleCapacityReset word0).eval r
  have h2 : 2 < PeriodicWidth := by decide
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  have h54 : 54 < MainWidth := by decide
  have h63 : 63 < MainWidth := by decide
  simp only [Subsystems.ChipletHasher.merkleCapacityReset, Subsystems.ChipletHasher.transitionZero,
    Subsystems.ChipletHasher.gateMerkleAbsorb, Subsystems.ChipletHasher.hasherFlag,
    Subsystems.ChipletHasher.fMerkleAbsorb, Subsystems.ChipletHasher.fMpa,
    Subsystems.ChipletHasher.fMva, Subsystems.ChipletHasher.fMua,
    Subsystems.ChipletHasher.cycleRow31, Subsystems.ChipletHasher.sel0,
    Subsystems.ChipletHasher.sel1, Subsystems.ChipletHasher.sel2,
    Subsystems.ChipletHasher.oneMinus, Subsystems.ChipletHasher.capacityNext,
    Subsystems.ChipletHasher.stateNext, Subsystems.ChipletHasher.capacityLane,
    periodic_chipletHasher_pCycleRow31_eq, curr_chipletHasher_sel0Col_eq,
    curr_chipletHasher_sel1Col_eq, curr_chipletHasher_sel2Col_eq,
    toSymbolicFrame, FExpr.eval, Builder.whenTransition, Builder.gate,
    Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, SymbolicFrame.colNext,
    h2, h51, h52, h53, h54, h63]
  simp [Subsystems.ChipletHasher.one, AirRow.boundaryAt, AirRow.boundary, FExpr.eval]
  ring_nf
  left; left; left; trivial

theorem bridge_chiplet_hasher_51 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[51]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.merkleCapacityReset word1).eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => (f.is_transition * (((1 - f.colCurr 51) *
      (((((f.periodic 2 * f.colCurr 52) * (1 - f.colCurr 53)) * f.colCurr 54) +
      (((f.periodic 2 * f.colCurr 52) * f.colCurr 53) * (1 - f.colCurr 54))) +
      (((f.periodic 2 * f.colCurr 52) * f.colCurr 53) * f.colCurr 54))) *
      f.colNext 64))) (toSymbolicFrame r) =
    (Subsystems.ChipletHasher.merkleCapacityReset word1).eval r
  have h2 : 2 < PeriodicWidth := by decide
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  have h54 : 54 < MainWidth := by decide
  have h64 : 64 < MainWidth := by decide
  simp only [Subsystems.ChipletHasher.merkleCapacityReset, Subsystems.ChipletHasher.transitionZero,
    Subsystems.ChipletHasher.gateMerkleAbsorb, Subsystems.ChipletHasher.hasherFlag,
    Subsystems.ChipletHasher.fMerkleAbsorb, Subsystems.ChipletHasher.fMpa,
    Subsystems.ChipletHasher.fMva, Subsystems.ChipletHasher.fMua,
    Subsystems.ChipletHasher.cycleRow31, Subsystems.ChipletHasher.sel0,
    Subsystems.ChipletHasher.sel1, Subsystems.ChipletHasher.sel2,
    Subsystems.ChipletHasher.oneMinus, Subsystems.ChipletHasher.capacityNext,
    Subsystems.ChipletHasher.stateNext, Subsystems.ChipletHasher.capacityLane,
    periodic_chipletHasher_pCycleRow31_eq, curr_chipletHasher_sel0Col_eq,
    curr_chipletHasher_sel1Col_eq, curr_chipletHasher_sel2Col_eq,
    toSymbolicFrame, FExpr.eval, Builder.whenTransition, Builder.gate,
    Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, SymbolicFrame.colNext,
    h2, h51, h52, h53, h54, h64]
  simp [Subsystems.ChipletHasher.one, AirRow.boundaryAt, AirRow.boundary, FExpr.eval]
  ring_nf
  left; left; left; trivial

theorem bridge_chiplet_hasher_52 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[52]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.merkleCapacityReset word2).eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => (f.is_transition * (((1 - f.colCurr 51) *
      (((((f.periodic 2 * f.colCurr 52) * (1 - f.colCurr 53)) * f.colCurr 54) +
      (((f.periodic 2 * f.colCurr 52) * f.colCurr 53) * (1 - f.colCurr 54))) +
      (((f.periodic 2 * f.colCurr 52) * f.colCurr 53) * f.colCurr 54))) *
      f.colNext 65))) (toSymbolicFrame r) =
    (Subsystems.ChipletHasher.merkleCapacityReset word2).eval r
  have h2 : 2 < PeriodicWidth := by decide
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  have h54 : 54 < MainWidth := by decide
  have h65 : 65 < MainWidth := by decide
  simp only [Subsystems.ChipletHasher.merkleCapacityReset, Subsystems.ChipletHasher.transitionZero,
    Subsystems.ChipletHasher.gateMerkleAbsorb, Subsystems.ChipletHasher.hasherFlag,
    Subsystems.ChipletHasher.fMerkleAbsorb, Subsystems.ChipletHasher.fMpa,
    Subsystems.ChipletHasher.fMva, Subsystems.ChipletHasher.fMua,
    Subsystems.ChipletHasher.cycleRow31, Subsystems.ChipletHasher.sel0,
    Subsystems.ChipletHasher.sel1, Subsystems.ChipletHasher.sel2,
    Subsystems.ChipletHasher.oneMinus, Subsystems.ChipletHasher.capacityNext,
    Subsystems.ChipletHasher.stateNext, Subsystems.ChipletHasher.capacityLane,
    periodic_chipletHasher_pCycleRow31_eq, curr_chipletHasher_sel0Col_eq,
    curr_chipletHasher_sel1Col_eq, curr_chipletHasher_sel2Col_eq,
    toSymbolicFrame, FExpr.eval, Builder.whenTransition, Builder.gate,
    Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, SymbolicFrame.colNext,
    h2, h51, h52, h53, h54, h65]
  simp [Subsystems.ChipletHasher.one, AirRow.boundaryAt, AirRow.boundary, FExpr.eval]
  ring_nf
  left; left; left; trivial

theorem bridge_chiplet_hasher_53 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[53]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.merkleCapacityReset word3).eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => (f.is_transition * (((1 - f.colCurr 51) *
      (((((f.periodic 2 * f.colCurr 52) * (1 - f.colCurr 53)) * f.colCurr 54) +
      (((f.periodic 2 * f.colCurr 52) * f.colCurr 53) * (1 - f.colCurr 54))) +
      (((f.periodic 2 * f.colCurr 52) * f.colCurr 53) * f.colCurr 54))) *
      f.colNext 66))) (toSymbolicFrame r) =
    (Subsystems.ChipletHasher.merkleCapacityReset word3).eval r
  have h2 : 2 < PeriodicWidth := by decide
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  have h54 : 54 < MainWidth := by decide
  have h66 : 66 < MainWidth := by decide
  simp only [Subsystems.ChipletHasher.merkleCapacityReset, Subsystems.ChipletHasher.transitionZero,
    Subsystems.ChipletHasher.gateMerkleAbsorb, Subsystems.ChipletHasher.hasherFlag,
    Subsystems.ChipletHasher.fMerkleAbsorb, Subsystems.ChipletHasher.fMpa,
    Subsystems.ChipletHasher.fMva, Subsystems.ChipletHasher.fMua,
    Subsystems.ChipletHasher.cycleRow31, Subsystems.ChipletHasher.sel0,
    Subsystems.ChipletHasher.sel1, Subsystems.ChipletHasher.sel2,
    Subsystems.ChipletHasher.oneMinus, Subsystems.ChipletHasher.capacityNext,
    Subsystems.ChipletHasher.stateNext, Subsystems.ChipletHasher.capacityLane,
    periodic_chipletHasher_pCycleRow31_eq, curr_chipletHasher_sel0Col_eq,
    curr_chipletHasher_sel1Col_eq, curr_chipletHasher_sel2Col_eq,
    toSymbolicFrame, FExpr.eval, Builder.whenTransition, Builder.gate,
    Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, SymbolicFrame.colNext,
    h2, h51, h52, h53, h54, h66]
  simp [Subsystems.ChipletHasher.one, AirRow.boundaryAt, AirRow.boundary, FExpr.eval]
  ring_nf
  left; left; left; trivial

theorem bridge_chiplet_hasher_54 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[54]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.merkleDigestToRate0 word0).eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => (f.is_transition * (((1 - f.colCurr 51) *
      ((((((f.periodic 2 * f.colCurr 52) * (1 - f.colCurr 53)) * f.colCurr 54) +
      (((f.periodic 2 * f.colCurr 52) * f.colCurr 53) * (1 - f.colCurr 54))) +
      (((f.periodic 2 * f.colCurr 52) * f.colCurr 53) * f.colCurr 54)) *
      (1 - (f.colCurr 67 - (Felt.ofNat 2 * f.colNext 67))))) *
      (f.colNext 55 - f.colCurr 55)))) (toSymbolicFrame r) =
    (Subsystems.ChipletHasher.merkleDigestToRate0 word0).eval r
  have h2 : 2 < PeriodicWidth := by decide
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  have h54 : 54 < MainWidth := by decide
  have h55 : 55 < MainWidth := by decide
  have h67 : 67 < MainWidth := by decide
  simp only [Subsystems.ChipletHasher.merkleDigestToRate0, Subsystems.ChipletHasher.transitionEq,
    Subsystems.ChipletHasher.gateMerkleAbsorbLeft, Subsystems.ChipletHasher.hasherFlag,
    Subsystems.ChipletHasher.fMerkleAbsorb,
    Subsystems.ChipletHasher.fMpa, Subsystems.ChipletHasher.fMva, Subsystems.ChipletHasher.fMua,
    Subsystems.ChipletHasher.cycleRow31, Subsystems.ChipletHasher.sel0,
    Subsystems.ChipletHasher.sel1, Subsystems.ChipletHasher.sel2,
    Subsystems.ChipletHasher.oneMinus, Subsystems.ChipletHasher.directionBit,
    Subsystems.ChipletHasher.nodeIndex, Subsystems.ChipletHasher.nodeIndexNext,
    Subsystems.ChipletHasher.two, felt_ofNat_two_eq,
    Subsystems.ChipletHasher.rate0Next, Subsystems.ChipletHasher.digest,
    Subsystems.ChipletHasher.stateNext, Subsystems.ChipletHasher.state,
    Subsystems.ChipletHasher.rate0Lane,
    periodic_chipletHasher_pCycleRow31_eq, curr_chipletHasher_sel0Col_eq,
    curr_chipletHasher_sel1Col_eq, curr_chipletHasher_sel2Col_eq,
    curr_chipletHasher_nodeIndexCol_eq, next_chipletHasher_nodeIndexCol_eq,
    next_chipletHasher_stateCol0_eq, curr_chipletHasher_stateCol0_eq,
    toSymbolicFrame, FExpr.eval, Builder.whenTransition, Builder.gate,
    Builder.assertEq, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, SymbolicFrame.colNext,
    h2, h51, h52, h53, h54, h55, h67]
  simp [Subsystems.ChipletHasher.one, AirRow.boundaryAt, AirRow.boundary, FExpr.eval]
  ring_nf
  left; left; left; left; trivial

theorem bridge_chiplet_hasher_55 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[55]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.merkleDigestToRate0 word1).eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => (f.is_transition * (((1 - f.colCurr 51) *
      ((((((f.periodic 2 * f.colCurr 52) * (1 - f.colCurr 53)) * f.colCurr 54) +
      (((f.periodic 2 * f.colCurr 52) * f.colCurr 53) * (1 - f.colCurr 54))) +
      (((f.periodic 2 * f.colCurr 52) * f.colCurr 53) * f.colCurr 54)) *
      (1 - (f.colCurr 67 - (Felt.ofNat 2 * f.colNext 67))))) *
      (f.colNext 56 - f.colCurr 56)))) (toSymbolicFrame r) =
    (Subsystems.ChipletHasher.merkleDigestToRate0 word1).eval r
  have h2 : 2 < PeriodicWidth := by decide
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  have h54 : 54 < MainWidth := by decide
  have h56 : 56 < MainWidth := by decide
  have h67 : 67 < MainWidth := by decide
  simp only [Subsystems.ChipletHasher.merkleDigestToRate0, Subsystems.ChipletHasher.transitionEq,
    Subsystems.ChipletHasher.gateMerkleAbsorbLeft, Subsystems.ChipletHasher.hasherFlag,
    Subsystems.ChipletHasher.fMerkleAbsorb,
    Subsystems.ChipletHasher.fMpa, Subsystems.ChipletHasher.fMva, Subsystems.ChipletHasher.fMua,
    Subsystems.ChipletHasher.cycleRow31, Subsystems.ChipletHasher.sel0,
    Subsystems.ChipletHasher.sel1, Subsystems.ChipletHasher.sel2,
    Subsystems.ChipletHasher.oneMinus, Subsystems.ChipletHasher.directionBit,
    Subsystems.ChipletHasher.nodeIndex, Subsystems.ChipletHasher.nodeIndexNext,
    Subsystems.ChipletHasher.two, felt_ofNat_two_eq,
    Subsystems.ChipletHasher.rate0Next, Subsystems.ChipletHasher.digest,
    Subsystems.ChipletHasher.stateNext, Subsystems.ChipletHasher.state,
    Subsystems.ChipletHasher.rate0Lane,
    periodic_chipletHasher_pCycleRow31_eq, curr_chipletHasher_sel0Col_eq,
    curr_chipletHasher_sel1Col_eq, curr_chipletHasher_sel2Col_eq,
    curr_chipletHasher_nodeIndexCol_eq, next_chipletHasher_nodeIndexCol_eq,
    next_chipletHasher_stateCol1_eq, curr_chipletHasher_stateCol1_eq,
    toSymbolicFrame, FExpr.eval, Builder.whenTransition, Builder.gate,
    Builder.assertEq, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, SymbolicFrame.colNext,
    h2, h51, h52, h53, h54, h56, h67]
  simp [Subsystems.ChipletHasher.one, AirRow.boundaryAt, AirRow.boundary, FExpr.eval]
  ring_nf
  left; left; left; left; trivial

theorem bridge_chiplet_hasher_56 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[56]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.merkleDigestToRate0 word2).eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => (f.is_transition * (((1 - f.colCurr 51) *
      ((((((f.periodic 2 * f.colCurr 52) * (1 - f.colCurr 53)) * f.colCurr 54) +
      (((f.periodic 2 * f.colCurr 52) * f.colCurr 53) * (1 - f.colCurr 54))) +
      (((f.periodic 2 * f.colCurr 52) * f.colCurr 53) * f.colCurr 54)) *
      (1 - (f.colCurr 67 - (Felt.ofNat 2 * f.colNext 67))))) *
      (f.colNext 57 - f.colCurr 57)))) (toSymbolicFrame r) =
    (Subsystems.ChipletHasher.merkleDigestToRate0 word2).eval r
  have h2 : 2 < PeriodicWidth := by decide
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  have h54 : 54 < MainWidth := by decide
  have h57 : 57 < MainWidth := by decide
  have h67 : 67 < MainWidth := by decide
  simp only [Subsystems.ChipletHasher.merkleDigestToRate0, Subsystems.ChipletHasher.transitionEq,
    Subsystems.ChipletHasher.gateMerkleAbsorbLeft, Subsystems.ChipletHasher.hasherFlag,
    Subsystems.ChipletHasher.fMerkleAbsorb,
    Subsystems.ChipletHasher.fMpa, Subsystems.ChipletHasher.fMva, Subsystems.ChipletHasher.fMua,
    Subsystems.ChipletHasher.cycleRow31, Subsystems.ChipletHasher.sel0,
    Subsystems.ChipletHasher.sel1, Subsystems.ChipletHasher.sel2,
    Subsystems.ChipletHasher.oneMinus, Subsystems.ChipletHasher.directionBit,
    Subsystems.ChipletHasher.nodeIndex, Subsystems.ChipletHasher.nodeIndexNext,
    Subsystems.ChipletHasher.two, felt_ofNat_two_eq,
    Subsystems.ChipletHasher.rate0Next, Subsystems.ChipletHasher.digest,
    Subsystems.ChipletHasher.stateNext, Subsystems.ChipletHasher.state,
    Subsystems.ChipletHasher.rate0Lane,
    periodic_chipletHasher_pCycleRow31_eq, curr_chipletHasher_sel0Col_eq,
    curr_chipletHasher_sel1Col_eq, curr_chipletHasher_sel2Col_eq,
    curr_chipletHasher_nodeIndexCol_eq, next_chipletHasher_nodeIndexCol_eq,
    next_chipletHasher_stateCol2_eq, curr_chipletHasher_stateCol2_eq,
    toSymbolicFrame, FExpr.eval, Builder.whenTransition, Builder.gate,
    Builder.assertEq, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, SymbolicFrame.colNext,
    h2, h51, h52, h53, h54, h57, h67]
  simp [Subsystems.ChipletHasher.one, AirRow.boundaryAt, AirRow.boundary, FExpr.eval]
  ring_nf
  left; left; left; left; trivial

theorem bridge_chiplet_hasher_57 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[57]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.merkleDigestToRate0 word3).eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => (f.is_transition * (((1 - f.colCurr 51) *
      ((((((f.periodic 2 * f.colCurr 52) * (1 - f.colCurr 53)) * f.colCurr 54) +
      (((f.periodic 2 * f.colCurr 52) * f.colCurr 53) * (1 - f.colCurr 54))) +
      (((f.periodic 2 * f.colCurr 52) * f.colCurr 53) * f.colCurr 54)) *
      (1 - (f.colCurr 67 - (Felt.ofNat 2 * f.colNext 67))))) *
      (f.colNext 58 - f.colCurr 58)))) (toSymbolicFrame r) =
    (Subsystems.ChipletHasher.merkleDigestToRate0 word3).eval r
  have h2 : 2 < PeriodicWidth := by decide
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  have h54 : 54 < MainWidth := by decide
  have h58 : 58 < MainWidth := by decide
  have h67 : 67 < MainWidth := by decide
  simp only [Subsystems.ChipletHasher.merkleDigestToRate0, Subsystems.ChipletHasher.transitionEq,
    Subsystems.ChipletHasher.gateMerkleAbsorbLeft, Subsystems.ChipletHasher.hasherFlag,
    Subsystems.ChipletHasher.fMerkleAbsorb,
    Subsystems.ChipletHasher.fMpa, Subsystems.ChipletHasher.fMva, Subsystems.ChipletHasher.fMua,
    Subsystems.ChipletHasher.cycleRow31, Subsystems.ChipletHasher.sel0,
    Subsystems.ChipletHasher.sel1, Subsystems.ChipletHasher.sel2,
    Subsystems.ChipletHasher.oneMinus, Subsystems.ChipletHasher.directionBit,
    Subsystems.ChipletHasher.nodeIndex, Subsystems.ChipletHasher.nodeIndexNext,
    Subsystems.ChipletHasher.two, felt_ofNat_two_eq,
    Subsystems.ChipletHasher.rate0Next, Subsystems.ChipletHasher.digest,
    Subsystems.ChipletHasher.stateNext, Subsystems.ChipletHasher.state,
    Subsystems.ChipletHasher.rate0Lane,
    periodic_chipletHasher_pCycleRow31_eq, curr_chipletHasher_sel0Col_eq,
    curr_chipletHasher_sel1Col_eq, curr_chipletHasher_sel2Col_eq,
    curr_chipletHasher_nodeIndexCol_eq, next_chipletHasher_nodeIndexCol_eq,
    next_chipletHasher_stateCol3_eq, curr_chipletHasher_stateCol3_eq,
    toSymbolicFrame, FExpr.eval, Builder.whenTransition, Builder.gate,
    Builder.assertEq, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, SymbolicFrame.colNext,
    h2, h51, h52, h53, h54, h58, h67]
  simp [Subsystems.ChipletHasher.one, AirRow.boundaryAt, AirRow.boundary, FExpr.eval]
  ring_nf
  left; left; left; left; trivial

theorem bridge_chiplet_hasher_58 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[58]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.merkleDigestToRate1 word0).eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => (f.is_transition * (((1 - f.colCurr 51) *
      ((((((f.periodic 2 * f.colCurr 52) * (1 - f.colCurr 53)) * f.colCurr 54) +
      (((f.periodic 2 * f.colCurr 52) * f.colCurr 53) * (1 - f.colCurr 54))) +
      (((f.periodic 2 * f.colCurr 52) * f.colCurr 53) * f.colCurr 54)) *
      (f.colCurr 67 - (Felt.ofNat 2 * f.colNext 67)))) *
      (f.colNext 59 - f.colCurr 55)))) (toSymbolicFrame r) =
    (Subsystems.ChipletHasher.merkleDigestToRate1 word0).eval r
  have h2 : 2 < PeriodicWidth := by decide
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  have h54 : 54 < MainWidth := by decide
  have h55 : 55 < MainWidth := by decide
  have h59 : 59 < MainWidth := by decide
  have h67 : 67 < MainWidth := by decide
  simp only [Subsystems.ChipletHasher.merkleDigestToRate1, Subsystems.ChipletHasher.transitionEq,
    Subsystems.ChipletHasher.gateMerkleAbsorbRight, Subsystems.ChipletHasher.hasherFlag,
    Subsystems.ChipletHasher.fMerkleAbsorb,
    Subsystems.ChipletHasher.fMpa, Subsystems.ChipletHasher.fMva, Subsystems.ChipletHasher.fMua,
    Subsystems.ChipletHasher.cycleRow31, Subsystems.ChipletHasher.sel0,
    Subsystems.ChipletHasher.sel1, Subsystems.ChipletHasher.sel2,
    Subsystems.ChipletHasher.oneMinus, Subsystems.ChipletHasher.directionBit,
    Subsystems.ChipletHasher.nodeIndex, Subsystems.ChipletHasher.nodeIndexNext,
    Subsystems.ChipletHasher.two, felt_ofNat_two_eq,
    Subsystems.ChipletHasher.rate1Next, Subsystems.ChipletHasher.digest,
    Subsystems.ChipletHasher.stateNext, Subsystems.ChipletHasher.state,
    Subsystems.ChipletHasher.rate1Lane, Subsystems.ChipletHasher.rate0Lane,
    periodic_chipletHasher_pCycleRow31_eq, curr_chipletHasher_sel0Col_eq,
    curr_chipletHasher_sel1Col_eq, curr_chipletHasher_sel2Col_eq,
    curr_chipletHasher_nodeIndexCol_eq, next_chipletHasher_nodeIndexCol_eq,
    curr_chipletHasher_stateCol0_eq,
    toSymbolicFrame, FExpr.eval, Builder.whenTransition, Builder.gate,
    Builder.assertEq, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, SymbolicFrame.colNext,
    h2, h51, h52, h53, h54, h55, h59, h67]
  simp [Subsystems.ChipletHasher.one, AirRow.boundaryAt, AirRow.boundary, FExpr.eval]
  ring_nf
  left; left; left; left; trivial

theorem bridge_chiplet_hasher_59 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[59]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.merkleDigestToRate1 word1).eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => (f.is_transition * (((1 - f.colCurr 51) *
      ((((((f.periodic 2 * f.colCurr 52) * (1 - f.colCurr 53)) * f.colCurr 54) +
      (((f.periodic 2 * f.colCurr 52) * f.colCurr 53) * (1 - f.colCurr 54))) +
      (((f.periodic 2 * f.colCurr 52) * f.colCurr 53) * f.colCurr 54)) *
      (f.colCurr 67 - (Felt.ofNat 2 * f.colNext 67)))) *
      (f.colNext 60 - f.colCurr 56)))) (toSymbolicFrame r) =
    (Subsystems.ChipletHasher.merkleDigestToRate1 word1).eval r
  have h2 : 2 < PeriodicWidth := by decide
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  have h54 : 54 < MainWidth := by decide
  have h56 : 56 < MainWidth := by decide
  have h60 : 60 < MainWidth := by decide
  have h67 : 67 < MainWidth := by decide
  simp only [Subsystems.ChipletHasher.merkleDigestToRate1, Subsystems.ChipletHasher.transitionEq,
    Subsystems.ChipletHasher.gateMerkleAbsorbRight, Subsystems.ChipletHasher.hasherFlag,
    Subsystems.ChipletHasher.fMerkleAbsorb,
    Subsystems.ChipletHasher.fMpa, Subsystems.ChipletHasher.fMva, Subsystems.ChipletHasher.fMua,
    Subsystems.ChipletHasher.cycleRow31, Subsystems.ChipletHasher.sel0,
    Subsystems.ChipletHasher.sel1, Subsystems.ChipletHasher.sel2,
    Subsystems.ChipletHasher.oneMinus, Subsystems.ChipletHasher.directionBit,
    Subsystems.ChipletHasher.nodeIndex, Subsystems.ChipletHasher.nodeIndexNext,
    Subsystems.ChipletHasher.two, felt_ofNat_two_eq,
    Subsystems.ChipletHasher.rate1Next, Subsystems.ChipletHasher.digest,
    Subsystems.ChipletHasher.stateNext, Subsystems.ChipletHasher.state,
    Subsystems.ChipletHasher.rate1Lane, Subsystems.ChipletHasher.rate0Lane,
    periodic_chipletHasher_pCycleRow31_eq, curr_chipletHasher_sel0Col_eq,
    curr_chipletHasher_sel1Col_eq, curr_chipletHasher_sel2Col_eq,
    curr_chipletHasher_nodeIndexCol_eq, next_chipletHasher_nodeIndexCol_eq,
    curr_chipletHasher_stateCol1_eq,
    toSymbolicFrame, FExpr.eval, Builder.whenTransition, Builder.gate,
    Builder.assertEq, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, SymbolicFrame.colNext,
    h2, h51, h52, h53, h54, h56, h60, h67]
  simp [Subsystems.ChipletHasher.one, AirRow.boundaryAt, AirRow.boundary, FExpr.eval]
  ring_nf
  left; left; left; left; trivial

theorem bridge_chiplet_hasher_60 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[60]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.merkleDigestToRate1 word2).eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => (f.is_transition * (((1 - f.colCurr 51) *
      ((((((f.periodic 2 * f.colCurr 52) * (1 - f.colCurr 53)) * f.colCurr 54) +
      (((f.periodic 2 * f.colCurr 52) * f.colCurr 53) * (1 - f.colCurr 54))) +
      (((f.periodic 2 * f.colCurr 52) * f.colCurr 53) * f.colCurr 54)) *
      (f.colCurr 67 - (Felt.ofNat 2 * f.colNext 67)))) *
      (f.colNext 61 - f.colCurr 57)))) (toSymbolicFrame r) =
    (Subsystems.ChipletHasher.merkleDigestToRate1 word2).eval r
  have h2 : 2 < PeriodicWidth := by decide
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  have h54 : 54 < MainWidth := by decide
  have h57 : 57 < MainWidth := by decide
  have h61 : 61 < MainWidth := by decide
  have h67 : 67 < MainWidth := by decide
  simp only [Subsystems.ChipletHasher.merkleDigestToRate1, Subsystems.ChipletHasher.transitionEq,
    Subsystems.ChipletHasher.gateMerkleAbsorbRight, Subsystems.ChipletHasher.hasherFlag,
    Subsystems.ChipletHasher.fMerkleAbsorb,
    Subsystems.ChipletHasher.fMpa, Subsystems.ChipletHasher.fMva, Subsystems.ChipletHasher.fMua,
    Subsystems.ChipletHasher.cycleRow31, Subsystems.ChipletHasher.sel0,
    Subsystems.ChipletHasher.sel1, Subsystems.ChipletHasher.sel2,
    Subsystems.ChipletHasher.oneMinus, Subsystems.ChipletHasher.directionBit,
    Subsystems.ChipletHasher.nodeIndex, Subsystems.ChipletHasher.nodeIndexNext,
    Subsystems.ChipletHasher.two, felt_ofNat_two_eq,
    Subsystems.ChipletHasher.rate1Next, Subsystems.ChipletHasher.digest,
    Subsystems.ChipletHasher.stateNext, Subsystems.ChipletHasher.state,
    Subsystems.ChipletHasher.rate1Lane, Subsystems.ChipletHasher.rate0Lane,
    periodic_chipletHasher_pCycleRow31_eq, curr_chipletHasher_sel0Col_eq,
    curr_chipletHasher_sel1Col_eq, curr_chipletHasher_sel2Col_eq,
    curr_chipletHasher_nodeIndexCol_eq, next_chipletHasher_nodeIndexCol_eq,
    curr_chipletHasher_stateCol2_eq,
    toSymbolicFrame, FExpr.eval, Builder.whenTransition, Builder.gate,
    Builder.assertEq, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, SymbolicFrame.colNext,
    h2, h51, h52, h53, h54, h57, h61, h67]
  simp [Subsystems.ChipletHasher.one, AirRow.boundaryAt, AirRow.boundary, FExpr.eval]
  ring_nf
  left; left; left; left; trivial

theorem bridge_chiplet_hasher_61 (r : AirRow) :
    Constraints.Symbolic.ChipletHasher.base[61]! (toSymbolicFrame r) =
      (Subsystems.ChipletHasher.merkleDigestToRate1 word3).eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => (f.is_transition * (((1 - f.colCurr 51) *
      ((((((f.periodic 2 * f.colCurr 52) * (1 - f.colCurr 53)) * f.colCurr 54) +
      (((f.periodic 2 * f.colCurr 52) * f.colCurr 53) * (1 - f.colCurr 54))) +
      (((f.periodic 2 * f.colCurr 52) * f.colCurr 53) * f.colCurr 54)) *
      (f.colCurr 67 - (Felt.ofNat 2 * f.colNext 67)))) *
      (f.colNext 62 - f.colCurr 58)))) (toSymbolicFrame r) =
    (Subsystems.ChipletHasher.merkleDigestToRate1 word3).eval r
  have h2 : 2 < PeriodicWidth := by decide
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  have h54 : 54 < MainWidth := by decide
  have h58 : 58 < MainWidth := by decide
  have h62 : 62 < MainWidth := by decide
  have h67 : 67 < MainWidth := by decide
  simp only [Subsystems.ChipletHasher.merkleDigestToRate1, Subsystems.ChipletHasher.transitionEq,
    Subsystems.ChipletHasher.gateMerkleAbsorbRight, Subsystems.ChipletHasher.hasherFlag,
    Subsystems.ChipletHasher.fMerkleAbsorb,
    Subsystems.ChipletHasher.fMpa, Subsystems.ChipletHasher.fMva, Subsystems.ChipletHasher.fMua,
    Subsystems.ChipletHasher.cycleRow31, Subsystems.ChipletHasher.sel0,
    Subsystems.ChipletHasher.sel1, Subsystems.ChipletHasher.sel2,
    Subsystems.ChipletHasher.oneMinus, Subsystems.ChipletHasher.directionBit,
    Subsystems.ChipletHasher.nodeIndex, Subsystems.ChipletHasher.nodeIndexNext,
    Subsystems.ChipletHasher.two, felt_ofNat_two_eq,
    Subsystems.ChipletHasher.rate1Next, Subsystems.ChipletHasher.digest,
    Subsystems.ChipletHasher.stateNext, Subsystems.ChipletHasher.state,
    Subsystems.ChipletHasher.rate1Lane, Subsystems.ChipletHasher.rate0Lane,
    periodic_chipletHasher_pCycleRow31_eq, curr_chipletHasher_sel0Col_eq,
    curr_chipletHasher_sel1Col_eq, curr_chipletHasher_sel2Col_eq,
    curr_chipletHasher_nodeIndexCol_eq, next_chipletHasher_nodeIndexCol_eq,
    curr_chipletHasher_stateCol3_eq,
    toSymbolicFrame, FExpr.eval, Builder.whenTransition, Builder.gate,
    Builder.assertEq, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, SymbolicFrame.colNext,
    h2, h51, h52, h53, h54, h58, h62, h67]
  simp [Subsystems.ChipletHasher.one, AirRow.boundaryAt, AirRow.boundary, FExpr.eval]
  ring_nf
  left; left; left; left; trivial

end MidenLean.AIR.Semantics.Refinement.SymbolicToCanonical
