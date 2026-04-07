import MidenLean.AIR.Semantics.Tactics
import MidenLean.AIR.Semantics.Subsystems.ChipletMemory
import MidenLean.AIR.Constraints.Symbolic.ChipletMemory

set_option maxHeartbeats 16000000

namespace MidenLean.AIR.Semantics.Refinement.SymbolicToCanonical

open MidenLean
open MidenLean.AIR
open MidenLean.AIR.Semantics
open MidenLean.AIR.Semantics.Tactics
open MidenLean.AIR.Semantics.Builder

private abbrev value0 : Subsystems.ChipletMemory.ValueIndex := ⟨0, by decide⟩
private abbrev value1 : Subsystems.ChipletMemory.ValueIndex := ⟨1, by decide⟩
private abbrev value2 : Subsystems.ChipletMemory.ValueIndex := ⟨2, by decide⟩
private abbrev value3 : Subsystems.ChipletMemory.ValueIndex := ⟨3, by decide⟩

@[simp] theorem felt_ofNat_65536_eq : (Felt.ofNat 65536 : Felt) = 65536 := rfl

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

@[simp] theorem curr_main_51_eq (r : AirRow) (h : 51 < MainWidth) :
    r.curr ⟨51, h⟩ = r.curr 51 := by
  apply congrArg r.curr
  apply Fin.ext
  rfl

@[simp] theorem next_main_51_eq (r : AirRow) (h : 51 < MainWidth) :
    r.next ⟨51, h⟩ = r.next 51 := by
  apply congrArg r.next
  apply Fin.ext
  rfl

@[simp] theorem curr_main_52_eq (r : AirRow) (h : 52 < MainWidth) :
    r.curr ⟨52, h⟩ = r.curr 52 := by
  apply congrArg r.curr
  apply Fin.ext
  rfl

@[simp] theorem next_main_52_eq (r : AirRow) (h : 52 < MainWidth) :
    r.next ⟨52, h⟩ = r.next 52 := by
  apply congrArg r.next
  apply Fin.ext
  rfl

@[simp] theorem curr_main_53_eq (r : AirRow) (h : 53 < MainWidth) :
    r.curr ⟨53, h⟩ = r.curr 53 := by
  apply congrArg r.curr
  apply Fin.ext
  rfl

@[simp] theorem next_main_53_eq (r : AirRow) (h : 53 < MainWidth) :
    r.next ⟨53, h⟩ = r.next 53 := by
  apply congrArg r.next
  apply Fin.ext
  rfl

@[simp] theorem curr_main_54_eq (r : AirRow) (h : 54 < MainWidth) :
    r.curr ⟨54, h⟩ = r.curr 54 := by
  apply congrArg r.curr
  apply Fin.ext
  rfl

@[simp] theorem next_main_54_eq (r : AirRow) (h : 54 < MainWidth) :
    r.next ⟨54, h⟩ = r.next 54 := by
  apply congrArg r.next
  apply Fin.ext
  rfl

@[simp] theorem curr_main_55_eq (r : AirRow) (h : 55 < MainWidth) :
    r.curr ⟨55, h⟩ = r.curr 55 := by
  apply congrArg r.curr
  apply Fin.ext
  rfl

@[simp] theorem next_main_55_eq (r : AirRow) (h : 55 < MainWidth) :
    r.next ⟨55, h⟩ = r.next 55 := by
  apply congrArg r.next
  apply Fin.ext
  rfl

@[simp] theorem curr_main_56_eq (r : AirRow) (h : 56 < MainWidth) :
    r.curr ⟨56, h⟩ = r.curr 56 := by
  apply congrArg r.curr
  apply Fin.ext
  rfl

@[simp] theorem next_main_56_eq (r : AirRow) (h : 56 < MainWidth) :
    r.next ⟨56, h⟩ = r.next 56 := by
  apply congrArg r.next
  apply Fin.ext
  rfl

@[simp] theorem curr_main_57_eq (r : AirRow) (h : 57 < MainWidth) :
    r.curr ⟨57, h⟩ = r.curr 57 := by
  apply congrArg r.curr
  apply Fin.ext
  rfl

@[simp] theorem next_main_57_eq (r : AirRow) (h : 57 < MainWidth) :
    r.next ⟨57, h⟩ = r.next 57 := by
  apply congrArg r.next
  apply Fin.ext
  rfl

@[simp] theorem curr_main_58_eq (r : AirRow) (h : 58 < MainWidth) :
    r.curr ⟨58, h⟩ = r.curr 58 := by
  apply congrArg r.curr
  apply Fin.ext
  rfl

@[simp] theorem next_main_58_eq (r : AirRow) (h : 58 < MainWidth) :
    r.next ⟨58, h⟩ = r.next 58 := by
  apply congrArg r.next
  apply Fin.ext
  rfl

@[simp] theorem curr_main_59_eq (r : AirRow) (h : 59 < MainWidth) :
    r.curr ⟨59, h⟩ = r.curr 59 := by
  apply congrArg r.curr
  apply Fin.ext
  rfl

@[simp] theorem next_main_59_eq (r : AirRow) (h : 59 < MainWidth) :
    r.next ⟨59, h⟩ = r.next 59 := by
  apply congrArg r.next
  apply Fin.ext
  rfl

@[simp] theorem curr_main_60_eq (r : AirRow) (h : 60 < MainWidth) :
    r.curr ⟨60, h⟩ = r.curr 60 := by
  apply congrArg r.curr
  apply Fin.ext
  rfl

@[simp] theorem next_main_60_eq (r : AirRow) (h : 60 < MainWidth) :
    r.next ⟨60, h⟩ = r.next 60 := by
  apply congrArg r.next
  apply Fin.ext
  rfl

@[simp] theorem curr_main_61_eq (r : AirRow) (h : 61 < MainWidth) :
    r.curr ⟨61, h⟩ = r.curr 61 := by
  apply congrArg r.curr
  apply Fin.ext
  rfl

@[simp] theorem next_main_61_eq (r : AirRow) (h : 61 < MainWidth) :
    r.next ⟨61, h⟩ = r.next 61 := by
  apply congrArg r.next
  apply Fin.ext
  rfl

@[simp] theorem curr_main_62_eq (r : AirRow) (h : 62 < MainWidth) :
    r.curr ⟨62, h⟩ = r.curr 62 := by
  apply congrArg r.curr
  apply Fin.ext
  rfl

@[simp] theorem next_main_62_eq (r : AirRow) (h : 62 < MainWidth) :
    r.next ⟨62, h⟩ = r.next 62 := by
  apply congrArg r.next
  apply Fin.ext
  rfl

@[simp] theorem curr_main_63_eq (r : AirRow) (h : 63 < MainWidth) :
    r.curr ⟨63, h⟩ = r.curr 63 := by
  apply congrArg r.curr
  apply Fin.ext
  rfl

@[simp] theorem next_main_63_eq (r : AirRow) (h : 63 < MainWidth) :
    r.next ⟨63, h⟩ = r.next 63 := by
  apply congrArg r.next
  apply Fin.ext
  rfl

@[simp] theorem curr_main_64_eq (r : AirRow) (h : 64 < MainWidth) :
    r.curr ⟨64, h⟩ = r.curr 64 := by
  apply congrArg r.curr
  apply Fin.ext
  rfl

@[simp] theorem next_main_64_eq (r : AirRow) (h : 64 < MainWidth) :
    r.next ⟨64, h⟩ = r.next 64 := by
  apply congrArg r.next
  apply Fin.ext
  rfl

@[simp] theorem curr_main_65_eq (r : AirRow) (h : 65 < MainWidth) :
    r.curr ⟨65, h⟩ = r.curr 65 := by
  apply congrArg r.curr
  apply Fin.ext
  rfl

@[simp] theorem next_main_65_eq (r : AirRow) (h : 65 < MainWidth) :
    r.next ⟨65, h⟩ = r.next 65 := by
  apply congrArg r.next
  apply Fin.ext
  rfl

@[simp] theorem curr_main_66_eq (r : AirRow) (h : 66 < MainWidth) :
    r.curr ⟨66, h⟩ = r.curr 66 := by
  apply congrArg r.curr
  apply Fin.ext
  rfl

@[simp] theorem next_main_66_eq (r : AirRow) (h : 66 < MainWidth) :
    r.next ⟨66, h⟩ = r.next 66 := by
  apply congrArg r.next
  apply Fin.ext
  rfl

@[simp] theorem curr_main_67_eq (r : AirRow) (h : 67 < MainWidth) :
    r.curr ⟨67, h⟩ = r.curr 67 := by
  apply congrArg r.curr
  apply Fin.ext
  rfl

@[simp] theorem next_main_67_eq (r : AirRow) (h : 67 < MainWidth) :
    r.next ⟨67, h⟩ = r.next 67 := by
  apply congrArg r.next
  apply Fin.ext
  rfl

@[simp] theorem curr_main_68_eq (r : AirRow) (h : 68 < MainWidth) :
    r.curr ⟨68, h⟩ = r.curr 68 := by
  apply congrArg r.curr
  apply Fin.ext
  rfl

@[simp] theorem next_main_68_eq (r : AirRow) (h : 68 < MainWidth) :
    r.next ⟨68, h⟩ = r.next 68 := by
  apply congrArg r.next
  apply Fin.ext
  rfl

@[simp] theorem curr_chipletMemory_isReadCol_eq (r : AirRow) :
    r.curr Subsystems.ChipletMemory.isReadCol = r.curr 54 := rfl

@[simp] theorem next_chipletMemory_isReadCol_eq (r : AirRow) :
    r.next Subsystems.ChipletMemory.isReadCol = r.next 54 := rfl

@[simp] theorem curr_chipletMemory_isWordCol_eq (r : AirRow) :
    r.curr Subsystems.ChipletMemory.isWordCol = r.curr 55 := rfl

@[simp] theorem next_chipletMemory_isWordCol_eq (r : AirRow) :
    r.next Subsystems.ChipletMemory.isWordCol = r.next 55 := rfl

@[simp] theorem curr_chipletMemory_ctxCol_eq (r : AirRow) :
    r.curr Subsystems.ChipletMemory.ctxCol = r.curr 56 := rfl

@[simp] theorem next_chipletMemory_ctxCol_eq (r : AirRow) :
    r.next Subsystems.ChipletMemory.ctxCol = r.next 56 := rfl

@[simp] theorem curr_chipletMemory_wordAddrCol_eq (r : AirRow) :
    r.curr Subsystems.ChipletMemory.wordAddrCol = r.curr 57 := rfl

@[simp] theorem next_chipletMemory_wordAddrCol_eq (r : AirRow) :
    r.next Subsystems.ChipletMemory.wordAddrCol = r.next 57 := rfl

@[simp] theorem curr_chipletMemory_idx0Col_eq (r : AirRow) :
    r.curr Subsystems.ChipletMemory.idx0Col = r.curr 58 := rfl

@[simp] theorem next_chipletMemory_idx0Col_eq (r : AirRow) :
    r.next Subsystems.ChipletMemory.idx0Col = r.next 58 := rfl

@[simp] theorem curr_chipletMemory_idx1Col_eq (r : AirRow) :
    r.curr Subsystems.ChipletMemory.idx1Col = r.curr 59 := rfl

@[simp] theorem next_chipletMemory_idx1Col_eq (r : AirRow) :
    r.next Subsystems.ChipletMemory.idx1Col = r.next 59 := rfl

@[simp] theorem curr_chipletMemory_clkCol_eq (r : AirRow) :
    r.curr Subsystems.ChipletMemory.clkCol = r.curr 60 := rfl

@[simp] theorem next_chipletMemory_clkCol_eq (r : AirRow) :
    r.next Subsystems.ChipletMemory.clkCol = r.next 60 := rfl

@[simp] theorem curr_chipletMemory_valueCol_eq
    (r : AirRow) (i : Subsystems.ChipletMemory.ValueIndex) :
    r.curr (Subsystems.ChipletMemory.valueCol i) =
      r.curr ⟨Subsystems.ChipletMemory.memoryValueOffset + i.val, by
        have hlt :
            Subsystems.ChipletMemory.memoryValueOffset + i.val <
              Subsystems.ChipletMemory.memoryValueOffset + 4 :=
          Nat.add_lt_add_left i.is_lt Subsystems.ChipletMemory.memoryValueOffset
        exact lt_of_lt_of_le hlt (by decide)⟩ := by
  apply congrArg r.curr
  apply Fin.ext
  simp [Subsystems.ChipletMemory.valueCol, Subsystems.ChipletMemory.memoryValueOffset]

@[simp] theorem next_chipletMemory_valueCol_eq
    (r : AirRow) (i : Subsystems.ChipletMemory.ValueIndex) :
    r.next (Subsystems.ChipletMemory.valueCol i) =
      r.next ⟨Subsystems.ChipletMemory.memoryValueOffset + i.val, by
        have hlt :
            Subsystems.ChipletMemory.memoryValueOffset + i.val <
              Subsystems.ChipletMemory.memoryValueOffset + 4 :=
          Nat.add_lt_add_left i.is_lt Subsystems.ChipletMemory.memoryValueOffset
        exact lt_of_lt_of_le hlt (by decide)⟩ := by
  apply congrArg r.next
  apply Fin.ext
  simp [Subsystems.ChipletMemory.valueCol, Subsystems.ChipletMemory.memoryValueOffset]

@[simp] theorem curr_chipletMemory_valueCol0_eq (r : AirRow) :
    r.curr (Subsystems.ChipletMemory.valueCol value0) = r.curr 61 := by
  apply congrArg r.curr
  apply Fin.ext
  rfl

@[simp] theorem next_chipletMemory_valueCol0_eq (r : AirRow) :
    r.next (Subsystems.ChipletMemory.valueCol value0) = r.next 61 := by
  apply congrArg r.next
  apply Fin.ext
  rfl

@[simp] theorem curr_chipletMemory_valueCol1_eq (r : AirRow) :
    r.curr (Subsystems.ChipletMemory.valueCol value1) = r.curr 62 := by
  apply congrArg r.curr
  apply Fin.ext
  rfl

@[simp] theorem next_chipletMemory_valueCol1_eq (r : AirRow) :
    r.next (Subsystems.ChipletMemory.valueCol value1) = r.next 62 := by
  apply congrArg r.next
  apply Fin.ext
  rfl

@[simp] theorem curr_chipletMemory_valueCol2_eq (r : AirRow) :
    r.curr (Subsystems.ChipletMemory.valueCol value2) = r.curr 63 := by
  apply congrArg r.curr
  apply Fin.ext
  rfl

@[simp] theorem next_chipletMemory_valueCol2_eq (r : AirRow) :
    r.next (Subsystems.ChipletMemory.valueCol value2) = r.next 63 := by
  apply congrArg r.next
  apply Fin.ext
  rfl

@[simp] theorem curr_chipletMemory_valueCol3_eq (r : AirRow) :
    r.curr (Subsystems.ChipletMemory.valueCol value3) = r.curr 64 := by
  apply congrArg r.curr
  apply Fin.ext
  rfl

@[simp] theorem next_chipletMemory_valueCol3_eq (r : AirRow) :
    r.next (Subsystems.ChipletMemory.valueCol value3) = r.next 64 := by
  apply congrArg r.next
  apply Fin.ext
  rfl

@[simp] theorem curr_chipletMemory_d0Col_eq (r : AirRow) :
    r.curr Subsystems.ChipletMemory.d0Col = r.curr 65 := rfl

@[simp] theorem next_chipletMemory_d0Col_eq (r : AirRow) :
    r.next Subsystems.ChipletMemory.d0Col = r.next 65 := rfl

@[simp] theorem curr_chipletMemory_d1Col_eq (r : AirRow) :
    r.curr Subsystems.ChipletMemory.d1Col = r.curr 66 := rfl

@[simp] theorem next_chipletMemory_d1Col_eq (r : AirRow) :
    r.next Subsystems.ChipletMemory.d1Col = r.next 66 := rfl

@[simp] theorem curr_chipletMemory_dInvCol_eq (r : AirRow) :
    r.curr Subsystems.ChipletMemory.dInvCol = r.curr 67 := rfl

@[simp] theorem next_chipletMemory_dInvCol_eq (r : AirRow) :
    r.next Subsystems.ChipletMemory.dInvCol = r.next 67 := rfl

@[simp] theorem curr_chipletMemory_sameCtxWordFlagCol_eq (r : AirRow) :
    r.curr Subsystems.ChipletMemory.sameCtxWordFlagCol = r.curr 68 := rfl

@[simp] theorem next_chipletMemory_sameCtxWordFlagCol_eq (r : AirRow) :
    r.next Subsystems.ChipletMemory.sameCtxWordFlagCol = r.next 68 := rfl

theorem bridge_chiplet_memory_0 (r : AirRow) :
    Constraints.Symbolic.ChipletMemory.base[0]! (toSymbolicFrame r) =
      Subsystems.ChipletMemory.isReadBinary.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change
    (fun f =>
      ((((f.colCurr 51 * f.colCurr 52) * (1 - f.colCurr 53)) * f.colCurr 54) *
        (f.colCurr 54 - 1)))
      (toSymbolicFrame r) = Subsystems.ChipletMemory.isReadBinary.eval r
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  have h54 : 54 < MainWidth := by decide
  simp [Subsystems.ChipletMemory.isReadBinary, Subsystems.ChipletMemory.integrityZero,
    Subsystems.ChipletMemory.memoryFlag, Subsystems.ChipletMemory.isRead,
    Subsystems.ChipletMemory.one, Subsystems.ChipletMemory.isReadCol,
    Subsystems.ChipletSelectors.memoryChipletFlag, Subsystems.ChipletSelectors.s01,
    Subsystems.ChipletSelectors.notS2, Subsystems.ChipletSelectors.s0,
    Subsystems.ChipletSelectors.s1, Subsystems.ChipletSelectors.s2,
    Subsystems.ChipletSelectors.s0Col, Subsystems.ChipletSelectors.s1Col,
    Subsystems.ChipletSelectors.s2Col, Subsystems.ChipletSelectors.chipletsOffset,
    Subsystems.ChipletMemory.memoryTraceOffset, Subsystems.ChipletMemory.chipletsOffset,
    toSymbolicFrame, FExpr.eval, Builder.gate, Builder.assertZero,
    BaseConstraint.eval, BaseConstraint.expr, AirRow.baseAt, AirRow.base,
    SymbolicFrame.colCurr, h51, h52, h53, h54]
  ring

theorem bridge_chiplet_memory_1 (r : AirRow) :
    Constraints.Symbolic.ChipletMemory.base[1]! (toSymbolicFrame r) =
      Subsystems.ChipletMemory.isWordBinary.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change
    (fun f =>
      ((((f.colCurr 51 * f.colCurr 52) * (1 - f.colCurr 53)) * f.colCurr 55) *
        (f.colCurr 55 - 1)))
      (toSymbolicFrame r) = Subsystems.ChipletMemory.isWordBinary.eval r
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  have h55 : 55 < MainWidth := by decide
  simp [Subsystems.ChipletMemory.isWordBinary, Subsystems.ChipletMemory.integrityZero,
    Subsystems.ChipletMemory.memoryFlag, Subsystems.ChipletMemory.isWord,
    Subsystems.ChipletMemory.one, Subsystems.ChipletMemory.isWordCol,
    Subsystems.ChipletSelectors.memoryChipletFlag, Subsystems.ChipletSelectors.s01,
    Subsystems.ChipletSelectors.notS2, Subsystems.ChipletSelectors.s0,
    Subsystems.ChipletSelectors.s1, Subsystems.ChipletSelectors.s2,
    Subsystems.ChipletSelectors.s0Col, Subsystems.ChipletSelectors.s1Col,
    Subsystems.ChipletSelectors.s2Col, Subsystems.ChipletSelectors.chipletsOffset,
    Subsystems.ChipletMemory.memoryTraceOffset, Subsystems.ChipletMemory.chipletsOffset,
    toSymbolicFrame, FExpr.eval, Builder.gate, Builder.assertZero,
    BaseConstraint.eval, BaseConstraint.expr, AirRow.baseAt, AirRow.base,
    SymbolicFrame.colCurr, h51, h52, h53, h55]
  ring

theorem bridge_chiplet_memory_2 (r : AirRow) :
    Constraints.Symbolic.ChipletMemory.base[2]! (toSymbolicFrame r) =
      Subsystems.ChipletMemory.idx0Binary.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change
    (fun f =>
      ((((f.colCurr 51 * f.colCurr 52) * (1 - f.colCurr 53)) * f.colCurr 58) *
        (f.colCurr 58 - 1)))
      (toSymbolicFrame r) = Subsystems.ChipletMemory.idx0Binary.eval r
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  have h58 : 58 < MainWidth := by decide
  simp [Subsystems.ChipletMemory.idx0Binary, Subsystems.ChipletMemory.integrityZero,
    Subsystems.ChipletMemory.memoryFlag, Subsystems.ChipletMemory.idx0,
    Subsystems.ChipletMemory.one, Subsystems.ChipletMemory.idx0Col,
    Subsystems.ChipletSelectors.memoryChipletFlag, Subsystems.ChipletSelectors.s01,
    Subsystems.ChipletSelectors.notS2, Subsystems.ChipletSelectors.s0,
    Subsystems.ChipletSelectors.s1, Subsystems.ChipletSelectors.s2,
    Subsystems.ChipletSelectors.s0Col, Subsystems.ChipletSelectors.s1Col,
    Subsystems.ChipletSelectors.s2Col, Subsystems.ChipletSelectors.chipletsOffset,
    Subsystems.ChipletMemory.memoryTraceOffset, Subsystems.ChipletMemory.chipletsOffset,
    toSymbolicFrame, FExpr.eval, Builder.gate, Builder.assertZero,
    BaseConstraint.eval, BaseConstraint.expr, AirRow.baseAt, AirRow.base,
    SymbolicFrame.colCurr, h51, h52, h53, h58]
  ring

theorem bridge_chiplet_memory_3 (r : AirRow) :
    Constraints.Symbolic.ChipletMemory.base[3]! (toSymbolicFrame r) =
      Subsystems.ChipletMemory.idx1Binary.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change
    (fun f =>
      ((((f.colCurr 51 * f.colCurr 52) * (1 - f.colCurr 53)) * f.colCurr 59) *
        (f.colCurr 59 - 1)))
      (toSymbolicFrame r) = Subsystems.ChipletMemory.idx1Binary.eval r
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  have h59 : 59 < MainWidth := by decide
  simp [Subsystems.ChipletMemory.idx1Binary, Subsystems.ChipletMemory.integrityZero,
    Subsystems.ChipletMemory.memoryFlag, Subsystems.ChipletMemory.idx1,
    Subsystems.ChipletMemory.one, Subsystems.ChipletMemory.idx1Col,
    Subsystems.ChipletSelectors.memoryChipletFlag, Subsystems.ChipletSelectors.s01,
    Subsystems.ChipletSelectors.notS2, Subsystems.ChipletSelectors.s0,
    Subsystems.ChipletSelectors.s1, Subsystems.ChipletSelectors.s2,
    Subsystems.ChipletSelectors.s0Col, Subsystems.ChipletSelectors.s1Col,
    Subsystems.ChipletSelectors.s2Col, Subsystems.ChipletSelectors.chipletsOffset,
    Subsystems.ChipletMemory.memoryTraceOffset, Subsystems.ChipletMemory.chipletsOffset,
    toSymbolicFrame, FExpr.eval, Builder.gate, Builder.assertZero,
    BaseConstraint.eval, BaseConstraint.expr, AirRow.baseAt, AirRow.base,
    SymbolicFrame.colCurr, h51, h52, h53, h59]
  ring

theorem bridge_chiplet_memory_4 (r : AirRow) :
    Constraints.Symbolic.ChipletMemory.base[4]! (toSymbolicFrame r) =
      Subsystems.ChipletMemory.wordAccessIdx0Zero.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change
    (fun f =>
      ((((f.colCurr 51 * f.colCurr 52) * (1 - f.colCurr 53)) * f.colCurr 55) *
        f.colCurr 58))
      (toSymbolicFrame r) = Subsystems.ChipletMemory.wordAccessIdx0Zero.eval r
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  have h55 : 55 < MainWidth := by decide
  have h58 : 58 < MainWidth := by decide
  simp [Subsystems.ChipletMemory.wordAccessIdx0Zero, Subsystems.ChipletMemory.integrityZero,
    Subsystems.ChipletMemory.memoryFlag, Subsystems.ChipletMemory.isWord,
    Subsystems.ChipletMemory.idx0, Subsystems.ChipletMemory.isWordCol,
    Subsystems.ChipletMemory.idx0Col, Subsystems.ChipletSelectors.memoryChipletFlag,
    Subsystems.ChipletSelectors.s01, Subsystems.ChipletSelectors.notS2,
    Subsystems.ChipletSelectors.s0, Subsystems.ChipletSelectors.s1,
    Subsystems.ChipletSelectors.s2, Subsystems.ChipletSelectors.s0Col,
    Subsystems.ChipletSelectors.s1Col, Subsystems.ChipletSelectors.s2Col,
    Subsystems.ChipletSelectors.chipletsOffset, Subsystems.ChipletMemory.memoryTraceOffset,
    Subsystems.ChipletMemory.chipletsOffset, toSymbolicFrame, FExpr.eval,
    Builder.gate, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, h51, h52, h53, h55, h58]

theorem bridge_chiplet_memory_5 (r : AirRow) :
    Constraints.Symbolic.ChipletMemory.base[5]! (toSymbolicFrame r) =
      Subsystems.ChipletMemory.wordAccessIdx1Zero.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change
    (fun f =>
      ((((f.colCurr 51 * f.colCurr 52) * (1 - f.colCurr 53)) * f.colCurr 55) *
        f.colCurr 59))
      (toSymbolicFrame r) = Subsystems.ChipletMemory.wordAccessIdx1Zero.eval r
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  have h55 : 55 < MainWidth := by decide
  have h59 : 59 < MainWidth := by decide
  simp [Subsystems.ChipletMemory.wordAccessIdx1Zero, Subsystems.ChipletMemory.integrityZero,
    Subsystems.ChipletMemory.memoryFlag, Subsystems.ChipletMemory.isWord,
    Subsystems.ChipletMemory.idx1, Subsystems.ChipletMemory.isWordCol,
    Subsystems.ChipletMemory.idx1Col, Subsystems.ChipletSelectors.memoryChipletFlag,
    Subsystems.ChipletSelectors.s01, Subsystems.ChipletSelectors.notS2,
    Subsystems.ChipletSelectors.s0, Subsystems.ChipletSelectors.s1,
    Subsystems.ChipletSelectors.s2, Subsystems.ChipletSelectors.s0Col,
    Subsystems.ChipletSelectors.s1Col, Subsystems.ChipletSelectors.s2Col,
    Subsystems.ChipletSelectors.chipletsOffset, Subsystems.ChipletMemory.memoryTraceOffset,
    Subsystems.ChipletMemory.chipletsOffset, toSymbolicFrame, FExpr.eval,
    Builder.gate, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, h51, h52, h53, h55, h59]

theorem bridge_chiplet_memory_6 (r : AirRow) :
    Constraints.Symbolic.ChipletMemory.base[6]! (toSymbolicFrame r) =
      (Subsystems.ChipletMemory.firstRowValueZero value0).eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change
    (fun f =>
      (((f.is_transition * ((((1 - f.colCurr 52) * f.colCurr 51) * f.colNext 52) *
            (1 - f.colNext 53))) *
          (f.colNext 54 + (((1 - f.colNext 54) * (1 - f.colNext 55)) *
            (1 - ((1 - f.colNext 59) * (1 - f.colNext 58)))))) *
        f.colNext 61))
      (toSymbolicFrame r) = (Subsystems.ChipletMemory.firstRowValueZero value0).eval r
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  have h54 : 54 < MainWidth := by decide
  have h55 : 55 < MainWidth := by decide
  have h58 : 58 < MainWidth := by decide
  have h59 : 59 < MainWidth := by decide
  have h61 : 61 < MainWidth := by decide
  simp [Subsystems.ChipletMemory.firstRowValueZero, Subsystems.ChipletMemory.transitionZero,
    Subsystems.ChipletMemory.flagNextRowFirstMemory, Subsystems.ChipletMemory.nextValueConstraintFlag,
    Subsystems.ChipletMemory.valueConstraintFlag, Subsystems.ChipletMemory.oneMinus,
    Subsystems.ChipletMemory.one, Subsystems.ChipletMemory.isReadNext,
    Subsystems.ChipletMemory.isWordNext, Subsystems.ChipletMemory.idx0Next,
    Subsystems.ChipletMemory.idx1Next, Subsystems.ChipletMemory.valueNext,
    Subsystems.ChipletMemory.valueSelectionFlag, Subsystems.ChipletMemory.isReadCol,
    Subsystems.ChipletMemory.isWordCol, Subsystems.ChipletMemory.idx0Col,
    Subsystems.ChipletMemory.idx1Col, Subsystems.ChipletMemory.valueCol,
    Subsystems.ChipletMemory.memoryValueOffset, Subsystems.ChipletMemory.memoryTraceOffset,
    Subsystems.ChipletMemory.chipletsOffset, Subsystems.ChipletSelectors.s0,
    Subsystems.ChipletSelectors.s1, Subsystems.ChipletSelectors.s1Next,
    Subsystems.ChipletSelectors.s2Next, Subsystems.ChipletSelectors.s0Col,
    Subsystems.ChipletSelectors.s1Col, Subsystems.ChipletSelectors.s2Col,
    Subsystems.ChipletSelectors.chipletsOffset, toSymbolicFrame, FExpr.eval,
    Builder.whenTransition, Builder.gate, Builder.assertZero, BaseConstraint.eval,
    BaseConstraint.expr, AirRow.boundary, AirRow.baseAt, AirRow.base,
    SymbolicFrame.colCurr, SymbolicFrame.colNext, h51, h52, h53, h54, h55, h58, h59,
    h61]
  ring

theorem bridge_chiplet_memory_7 (r : AirRow) :
    Constraints.Symbolic.ChipletMemory.base[7]! (toSymbolicFrame r) =
      (Subsystems.ChipletMemory.firstRowValueZero value1).eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change
    (fun f =>
      (((f.is_transition * ((((1 - f.colCurr 52) * f.colCurr 51) * f.colNext 52) *
            (1 - f.colNext 53))) *
          (f.colNext 54 + (((1 - f.colNext 54) * (1 - f.colNext 55)) *
            (1 - ((1 - f.colNext 59) * f.colNext 58))))) *
        f.colNext 62))
      (toSymbolicFrame r) = (Subsystems.ChipletMemory.firstRowValueZero value1).eval r
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  have h54 : 54 < MainWidth := by decide
  have h55 : 55 < MainWidth := by decide
  have h58 : 58 < MainWidth := by decide
  have h59 : 59 < MainWidth := by decide
  have h62 : 62 < MainWidth := by decide
  simp [Subsystems.ChipletMemory.firstRowValueZero, Subsystems.ChipletMemory.transitionZero,
    Subsystems.ChipletMemory.flagNextRowFirstMemory, Subsystems.ChipletMemory.nextValueConstraintFlag,
    Subsystems.ChipletMemory.valueConstraintFlag, Subsystems.ChipletMemory.oneMinus,
    Subsystems.ChipletMemory.one, Subsystems.ChipletMemory.isReadNext,
    Subsystems.ChipletMemory.isWordNext, Subsystems.ChipletMemory.idx0Next,
    Subsystems.ChipletMemory.idx1Next, Subsystems.ChipletMemory.valueNext,
    Subsystems.ChipletMemory.valueSelectionFlag, Subsystems.ChipletMemory.isReadCol,
    Subsystems.ChipletMemory.isWordCol, Subsystems.ChipletMemory.idx0Col,
    Subsystems.ChipletMemory.idx1Col, Subsystems.ChipletMemory.valueCol,
    Subsystems.ChipletMemory.memoryValueOffset, Subsystems.ChipletMemory.memoryTraceOffset,
    Subsystems.ChipletMemory.chipletsOffset, Subsystems.ChipletSelectors.s0,
    Subsystems.ChipletSelectors.s1, Subsystems.ChipletSelectors.s1Next,
    Subsystems.ChipletSelectors.s2Next, Subsystems.ChipletSelectors.s0Col,
    Subsystems.ChipletSelectors.s1Col, Subsystems.ChipletSelectors.s2Col,
    Subsystems.ChipletSelectors.chipletsOffset, toSymbolicFrame, FExpr.eval,
    Builder.whenTransition, Builder.gate, Builder.assertZero, BaseConstraint.eval,
    BaseConstraint.expr, AirRow.boundary, AirRow.baseAt, AirRow.base,
    SymbolicFrame.colCurr, SymbolicFrame.colNext, h51, h52, h53, h54, h55, h58, h59,
    h62]
  ring

theorem bridge_chiplet_memory_8 (r : AirRow) :
    Constraints.Symbolic.ChipletMemory.base[8]! (toSymbolicFrame r) =
      (Subsystems.ChipletMemory.firstRowValueZero value2).eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change
    (fun f =>
      (((f.is_transition * ((((1 - f.colCurr 52) * f.colCurr 51) * f.colNext 52) *
            (1 - f.colNext 53))) *
          (f.colNext 54 + (((1 - f.colNext 54) * (1 - f.colNext 55)) *
            (1 - (f.colNext 59 * (1 - f.colNext 58)))))) *
        f.colNext 63))
      (toSymbolicFrame r) = (Subsystems.ChipletMemory.firstRowValueZero value2).eval r
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  have h54 : 54 < MainWidth := by decide
  have h55 : 55 < MainWidth := by decide
  have h58 : 58 < MainWidth := by decide
  have h59 : 59 < MainWidth := by decide
  have h63 : 63 < MainWidth := by decide
  simp [Subsystems.ChipletMemory.firstRowValueZero, Subsystems.ChipletMemory.transitionZero,
    Subsystems.ChipletMemory.flagNextRowFirstMemory, Subsystems.ChipletMemory.nextValueConstraintFlag,
    Subsystems.ChipletMemory.valueConstraintFlag, Subsystems.ChipletMemory.oneMinus,
    Subsystems.ChipletMemory.one, Subsystems.ChipletMemory.isReadNext,
    Subsystems.ChipletMemory.isWordNext, Subsystems.ChipletMemory.idx0Next,
    Subsystems.ChipletMemory.idx1Next, Subsystems.ChipletMemory.valueNext,
    Subsystems.ChipletMemory.valueSelectionFlag, Subsystems.ChipletMemory.isReadCol,
    Subsystems.ChipletMemory.isWordCol, Subsystems.ChipletMemory.idx0Col,
    Subsystems.ChipletMemory.idx1Col, Subsystems.ChipletMemory.valueCol,
    Subsystems.ChipletMemory.memoryValueOffset, Subsystems.ChipletMemory.memoryTraceOffset,
    Subsystems.ChipletMemory.chipletsOffset, Subsystems.ChipletSelectors.s0,
    Subsystems.ChipletSelectors.s1, Subsystems.ChipletSelectors.s1Next,
    Subsystems.ChipletSelectors.s2Next, Subsystems.ChipletSelectors.s0Col,
    Subsystems.ChipletSelectors.s1Col, Subsystems.ChipletSelectors.s2Col,
    Subsystems.ChipletSelectors.chipletsOffset, toSymbolicFrame, FExpr.eval,
    Builder.whenTransition, Builder.gate, Builder.assertZero, BaseConstraint.eval,
    BaseConstraint.expr, AirRow.boundary, AirRow.baseAt, AirRow.base,
    SymbolicFrame.colCurr, SymbolicFrame.colNext, h51, h52, h53, h54, h55, h58, h59,
    h63]
  ring

theorem bridge_chiplet_memory_9 (r : AirRow) :
    Constraints.Symbolic.ChipletMemory.base[9]! (toSymbolicFrame r) =
      (Subsystems.ChipletMemory.firstRowValueZero value3).eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change
    (fun f =>
      (((f.is_transition * ((((1 - f.colCurr 52) * f.colCurr 51) * f.colNext 52) *
            (1 - f.colNext 53))) *
          (f.colNext 54 + (((1 - f.colNext 54) * (1 - f.colNext 55)) *
            (1 - (f.colNext 59 * f.colNext 58))))) *
        f.colNext 64))
      (toSymbolicFrame r) = (Subsystems.ChipletMemory.firstRowValueZero value3).eval r
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  have h54 : 54 < MainWidth := by decide
  have h55 : 55 < MainWidth := by decide
  have h58 : 58 < MainWidth := by decide
  have h59 : 59 < MainWidth := by decide
  have h64 : 64 < MainWidth := by decide
  simp [Subsystems.ChipletMemory.firstRowValueZero, Subsystems.ChipletMemory.transitionZero,
    Subsystems.ChipletMemory.flagNextRowFirstMemory, Subsystems.ChipletMemory.nextValueConstraintFlag,
    Subsystems.ChipletMemory.valueConstraintFlag, Subsystems.ChipletMemory.oneMinus,
    Subsystems.ChipletMemory.one, Subsystems.ChipletMemory.isReadNext,
    Subsystems.ChipletMemory.isWordNext, Subsystems.ChipletMemory.idx0Next,
    Subsystems.ChipletMemory.idx1Next, Subsystems.ChipletMemory.valueNext,
    Subsystems.ChipletMemory.valueSelectionFlag, Subsystems.ChipletMemory.isReadCol,
    Subsystems.ChipletMemory.isWordCol, Subsystems.ChipletMemory.idx0Col,
    Subsystems.ChipletMemory.idx1Col, Subsystems.ChipletMemory.valueCol,
    Subsystems.ChipletMemory.memoryValueOffset, Subsystems.ChipletMemory.memoryTraceOffset,
    Subsystems.ChipletMemory.chipletsOffset, Subsystems.ChipletSelectors.s0,
    Subsystems.ChipletSelectors.s1, Subsystems.ChipletSelectors.s1Next,
    Subsystems.ChipletSelectors.s2Next, Subsystems.ChipletSelectors.s0Col,
    Subsystems.ChipletSelectors.s1Col, Subsystems.ChipletSelectors.s2Col,
    Subsystems.ChipletSelectors.chipletsOffset, toSymbolicFrame, FExpr.eval,
    Builder.whenTransition, Builder.gate, Builder.assertZero, BaseConstraint.eval,
    BaseConstraint.expr, AirRow.boundary, AirRow.baseAt, AirRow.base,
    SymbolicFrame.colCurr, SymbolicFrame.colNext, h51, h52, h53, h54, h55, h58, h59,
    h64]
  ring

theorem bridge_chiplet_memory_10 (r : AirRow) :
    Constraints.Symbolic.ChipletMemory.base[10]! (toSymbolicFrame r) =
      Subsystems.ChipletMemory.n0Binary.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change
    (fun f =>
      (((f.is_transition * ((f.colCurr 51 * f.colCurr 52) * (1 - f.colNext 53))) *
          ((f.colNext 56 - f.colCurr 56) * f.colNext 67)) *
        (((f.colNext 56 - f.colCurr 56) * f.colNext 67) - 1)))
      (toSymbolicFrame r) = Subsystems.ChipletMemory.n0Binary.eval r
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  have h56 : 56 < MainWidth := by decide
  have h67 : 67 < MainWidth := by decide
  simp [Subsystems.ChipletMemory.n0Binary, Subsystems.ChipletMemory.transitionZero,
    Subsystems.ChipletMemory.flagMemoryActiveNotLast, Subsystems.ChipletMemory.n0,
    Subsystems.ChipletMemory.ctxDelta, Subsystems.ChipletMemory.dInvNext,
    Subsystems.ChipletMemory.oneMinus, Subsystems.ChipletMemory.one,
    Subsystems.ChipletMemory.ctxNext, Subsystems.ChipletMemory.ctx,
    Subsystems.ChipletMemory.dInvCol, Subsystems.ChipletMemory.ctxCol,
    Subsystems.ChipletMemory.s0, Subsystems.ChipletMemory.s1,
    Subsystems.ChipletMemory.s2Next, Subsystems.ChipletSelectors.s0,
    Subsystems.ChipletSelectors.s1, Subsystems.ChipletSelectors.s2Next,
    Subsystems.ChipletSelectors.s0Col, Subsystems.ChipletSelectors.s1Col,
    Subsystems.ChipletSelectors.s2Col, Subsystems.ChipletSelectors.chipletsOffset,
    Subsystems.ChipletMemory.memoryTraceOffset, Subsystems.ChipletMemory.chipletsOffset,
    toSymbolicFrame, FExpr.eval, Builder.whenTransition, Builder.gate,
    Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr, AirRow.boundary,
    AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, SymbolicFrame.colNext,
    h51, h52, h53, h56, h67]
  ring

theorem bridge_chiplet_memory_11 (r : AirRow) :
    Constraints.Symbolic.ChipletMemory.base[11]! (toSymbolicFrame r) =
      Subsystems.ChipletMemory.ctxDeltaWhenNotN0.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change
    (fun f =>
      (((f.is_transition * ((f.colCurr 51 * f.colCurr 52) * (1 - f.colNext 53))) *
          (1 - ((f.colNext 56 - f.colCurr 56) * f.colNext 67))) *
        (f.colNext 56 - f.colCurr 56)))
      (toSymbolicFrame r) = Subsystems.ChipletMemory.ctxDeltaWhenNotN0.eval r
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  have h56 : 56 < MainWidth := by decide
  have h67 : 67 < MainWidth := by decide
  simp [Subsystems.ChipletMemory.ctxDeltaWhenNotN0, Subsystems.ChipletMemory.transitionZero,
    Subsystems.ChipletMemory.flagMemoryActiveNotLast, Subsystems.ChipletMemory.oneMinus,
    Subsystems.ChipletMemory.n0, Subsystems.ChipletMemory.ctxDelta,
    Subsystems.ChipletMemory.dInvNext, Subsystems.ChipletMemory.one,
    Subsystems.ChipletMemory.ctxNext, Subsystems.ChipletMemory.ctx,
    Subsystems.ChipletMemory.dInvCol, Subsystems.ChipletMemory.ctxCol,
    Subsystems.ChipletMemory.s0, Subsystems.ChipletMemory.s1,
    Subsystems.ChipletMemory.s2Next, Subsystems.ChipletSelectors.s0,
    Subsystems.ChipletSelectors.s1, Subsystems.ChipletSelectors.s2Next,
    Subsystems.ChipletSelectors.s0Col, Subsystems.ChipletSelectors.s1Col,
    Subsystems.ChipletSelectors.s2Col, Subsystems.ChipletSelectors.chipletsOffset,
    Subsystems.ChipletMemory.memoryTraceOffset, Subsystems.ChipletMemory.chipletsOffset,
    toSymbolicFrame, FExpr.eval, Builder.whenTransition, Builder.gate,
    Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr, AirRow.boundary,
    AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, SymbolicFrame.colNext,
    h51, h52, h53, h56, h67]
  ring

theorem bridge_chiplet_memory_12 (r : AirRow) :
    Constraints.Symbolic.ChipletMemory.base[12]! (toSymbolicFrame r) =
      Subsystems.ChipletMemory.n1BinaryWhenSameContext.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change
    (fun f =>
      ((((f.is_transition * ((f.colCurr 51 * f.colCurr 52) * (1 - f.colNext 53))) *
            (1 - ((f.colNext 56 - f.colCurr 56) * f.colNext 67))) *
          ((f.colNext 57 - f.colCurr 57) * f.colNext 67)) *
        (((f.colNext 57 - f.colCurr 57) * f.colNext 67) - 1)))
      (toSymbolicFrame r) = Subsystems.ChipletMemory.n1BinaryWhenSameContext.eval r
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  have h56 : 56 < MainWidth := by decide
  have h57 : 57 < MainWidth := by decide
  have h67 : 67 < MainWidth := by decide
  simp [Subsystems.ChipletMemory.n1BinaryWhenSameContext, Subsystems.ChipletMemory.transitionZero,
    Subsystems.ChipletMemory.flagMemoryActiveNotLast, Subsystems.ChipletMemory.oneMinus,
    Subsystems.ChipletMemory.n0, Subsystems.ChipletMemory.n1,
    Subsystems.ChipletMemory.ctxDelta, Subsystems.ChipletMemory.addrDelta,
    Subsystems.ChipletMemory.dInvNext, Subsystems.ChipletMemory.one,
    Subsystems.ChipletMemory.ctxNext, Subsystems.ChipletMemory.ctx,
    Subsystems.ChipletMemory.wordAddrNext, Subsystems.ChipletMemory.wordAddr,
    Subsystems.ChipletMemory.dInvCol, Subsystems.ChipletMemory.ctxCol,
    Subsystems.ChipletMemory.wordAddrCol, Subsystems.ChipletMemory.s0,
    Subsystems.ChipletMemory.s1, Subsystems.ChipletMemory.s2Next,
    Subsystems.ChipletSelectors.s0, Subsystems.ChipletSelectors.s1,
    Subsystems.ChipletSelectors.s2Next, Subsystems.ChipletSelectors.s0Col,
    Subsystems.ChipletSelectors.s1Col, Subsystems.ChipletSelectors.s2Col,
    Subsystems.ChipletSelectors.chipletsOffset, Subsystems.ChipletMemory.memoryTraceOffset,
    Subsystems.ChipletMemory.chipletsOffset, toSymbolicFrame, FExpr.eval,
    Builder.whenTransition, Builder.gate, Builder.assertZero, BaseConstraint.eval,
    BaseConstraint.expr, AirRow.boundary, AirRow.baseAt, AirRow.base,
    SymbolicFrame.colCurr, SymbolicFrame.colNext, h51, h52, h53, h56, h57, h67]
  ring

theorem bridge_chiplet_memory_13 (r : AirRow) :
    Constraints.Symbolic.ChipletMemory.base[13]! (toSymbolicFrame r) =
      Subsystems.ChipletMemory.addrDeltaWhenSameContextAndWord.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change
    (fun f =>
      ((((f.is_transition * ((f.colCurr 51 * f.colCurr 52) * (1 - f.colNext 53))) *
            (1 - ((f.colNext 56 - f.colCurr 56) * f.colNext 67))) *
          (1 - ((f.colNext 57 - f.colCurr 57) * f.colNext 67))) *
        (f.colNext 57 - f.colCurr 57)))
      (toSymbolicFrame r) = Subsystems.ChipletMemory.addrDeltaWhenSameContextAndWord.eval r
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  have h56 : 56 < MainWidth := by decide
  have h57 : 57 < MainWidth := by decide
  have h67 : 67 < MainWidth := by decide
  simp [Subsystems.ChipletMemory.addrDeltaWhenSameContextAndWord,
    Subsystems.ChipletMemory.transitionZero, Subsystems.ChipletMemory.flagMemoryActiveNotLast,
    Subsystems.ChipletMemory.oneMinus, Subsystems.ChipletMemory.n0,
    Subsystems.ChipletMemory.n1, Subsystems.ChipletMemory.ctxDelta,
    Subsystems.ChipletMemory.addrDelta, Subsystems.ChipletMemory.dInvNext,
    Subsystems.ChipletMemory.one, Subsystems.ChipletMemory.ctxNext,
    Subsystems.ChipletMemory.ctx, Subsystems.ChipletMemory.wordAddrNext,
    Subsystems.ChipletMemory.wordAddr, Subsystems.ChipletMemory.dInvCol,
    Subsystems.ChipletMemory.ctxCol, Subsystems.ChipletMemory.wordAddrCol,
    Subsystems.ChipletMemory.s0, Subsystems.ChipletMemory.s1,
    Subsystems.ChipletMemory.s2Next, Subsystems.ChipletSelectors.s0,
    Subsystems.ChipletSelectors.s1, Subsystems.ChipletSelectors.s2Next,
    Subsystems.ChipletSelectors.s0Col, Subsystems.ChipletSelectors.s1Col,
    Subsystems.ChipletSelectors.s2Col, Subsystems.ChipletSelectors.chipletsOffset,
    Subsystems.ChipletMemory.memoryTraceOffset, Subsystems.ChipletMemory.chipletsOffset,
    toSymbolicFrame, FExpr.eval, Builder.whenTransition, Builder.gate,
    Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr, AirRow.boundary,
    AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, SymbolicFrame.colNext,
    h51, h52, h53, h56, h57, h67]
  ring

theorem bridge_chiplet_memory_14 (r : AirRow) :
    Constraints.Symbolic.ChipletMemory.base[14]! (toSymbolicFrame r) =
      Subsystems.ChipletMemory.deltaDecomposition.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change
    (fun f =>
      ((f.is_transition * ((f.colCurr 51 * f.colCurr 52) * (1 - f.colNext 53))) *
        (((((f.colNext 56 - f.colCurr 56) * f.colNext 67) * (f.colNext 56 - f.colCurr 56)) +
              ((1 - ((f.colNext 56 - f.colCurr 56) * f.colNext 67)) *
                ((((f.colNext 57 - f.colCurr 57) * f.colNext 67) * (f.colNext 57 - f.colCurr 57)) +
                  ((1 - ((f.colNext 57 - f.colCurr 57) * f.colNext 67)) *
                    (f.colNext 60 - f.colCurr 60))))) -
          ((f.colNext 66 * Felt.ofNat 65536) + f.colNext 65))))
      (toSymbolicFrame r) = Subsystems.ChipletMemory.deltaDecomposition.eval r
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  have h56 : 56 < MainWidth := by decide
  have h57 : 57 < MainWidth := by decide
  have h60 : 60 < MainWidth := by decide
  have h65 : 65 < MainWidth := by decide
  have h66 : 66 < MainWidth := by decide
  have h67 : 67 < MainWidth := by decide
  simp [Subsystems.ChipletMemory.deltaDecomposition, Subsystems.ChipletMemory.transitionEq,
    Subsystems.ChipletMemory.flagMemoryActiveNotLast, Subsystems.ChipletMemory.computedDelta,
    Subsystems.ChipletMemory.deltaFromLimbsNext, Subsystems.ChipletMemory.n0,
    Subsystems.ChipletMemory.n1, Subsystems.ChipletMemory.ctxDelta,
    Subsystems.ChipletMemory.addrDelta, Subsystems.ChipletMemory.clkDelta,
    Subsystems.ChipletMemory.dInvNext, Subsystems.ChipletMemory.d0Next,
    Subsystems.ChipletMemory.d1Next, Subsystems.ChipletMemory.twoPow16,
    Subsystems.ChipletMemory.oneMinus, Subsystems.ChipletMemory.one,
    Subsystems.ChipletMemory.ctxNext, Subsystems.ChipletMemory.ctx,
    Subsystems.ChipletMemory.wordAddrNext, Subsystems.ChipletMemory.wordAddr,
    Subsystems.ChipletMemory.clkNext, Subsystems.ChipletMemory.clk,
    Subsystems.ChipletMemory.s0, Subsystems.ChipletMemory.s1,
    Subsystems.ChipletMemory.s2Next, Subsystems.ChipletSelectors.s0,
    Subsystems.ChipletSelectors.s1, Subsystems.ChipletSelectors.s2Next,
    curr_chipletSelectors_s0Col_eq, curr_chipletSelectors_s1Col_eq,
    next_chipletSelectors_s2Col_eq, curr_chipletMemory_ctxCol_eq,
    next_chipletMemory_ctxCol_eq, curr_chipletMemory_wordAddrCol_eq,
    next_chipletMemory_wordAddrCol_eq, curr_chipletMemory_clkCol_eq,
    next_chipletMemory_clkCol_eq, next_chipletMemory_d0Col_eq,
    next_chipletMemory_d1Col_eq, next_chipletMemory_dInvCol_eq,
    felt_ofNat_65536_eq, toSymbolicFrame, FExpr.eval, Builder.whenTransition,
    Builder.gate, Builder.assertEq, Builder.assertZero, BaseConstraint.eval,
    BaseConstraint.expr, AirRow.boundary, AirRow.baseAt, AirRow.base,
    SymbolicFrame.colCurr, SymbolicFrame.colNext, h51, h52, h53, h56, h57, h60,
    h65, h66, h67]
  ring

theorem bridge_chiplet_memory_15 (r : AirRow) :
    Constraints.Symbolic.ChipletMemory.base[15]! (toSymbolicFrame r) =
      Subsystems.ChipletMemory.sameCtxWordFlagUpdate.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change
    (fun f =>
      ((f.is_transition * ((f.colCurr 51 * f.colCurr 52) * (1 - f.colNext 53))) *
        (f.colNext 68 -
          ((1 - ((f.colNext 56 - f.colCurr 56) * f.colNext 67)) *
            (1 - ((f.colNext 57 - f.colCurr 57) * f.colNext 67))))))
      (toSymbolicFrame r) = Subsystems.ChipletMemory.sameCtxWordFlagUpdate.eval r
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  have h56 : 56 < MainWidth := by decide
  have h57 : 57 < MainWidth := by decide
  have h67 : 67 < MainWidth := by decide
  have h68 : 68 < MainWidth := by decide
  simp [Subsystems.ChipletMemory.sameCtxWordFlagUpdate, Subsystems.ChipletMemory.transitionEq,
    Subsystems.ChipletMemory.flagMemoryActiveNotLast, Subsystems.ChipletMemory.sameCtxWordFlagNext,
    Subsystems.ChipletMemory.sameCtxWordFlagExpected, Subsystems.ChipletMemory.n0,
    Subsystems.ChipletMemory.n1, Subsystems.ChipletMemory.ctxDelta,
    Subsystems.ChipletMemory.addrDelta, Subsystems.ChipletMemory.dInvNext,
    Subsystems.ChipletMemory.oneMinus, Subsystems.ChipletMemory.one,
    Subsystems.ChipletMemory.ctxNext, Subsystems.ChipletMemory.ctx,
    Subsystems.ChipletMemory.wordAddrNext, Subsystems.ChipletMemory.wordAddr,
    Subsystems.ChipletMemory.s0, Subsystems.ChipletMemory.s1,
    Subsystems.ChipletMemory.s2Next, Subsystems.ChipletSelectors.s0,
    Subsystems.ChipletSelectors.s1, Subsystems.ChipletSelectors.s2Next,
    curr_chipletSelectors_s0Col_eq, curr_chipletSelectors_s1Col_eq,
    next_chipletSelectors_s2Col_eq, next_chipletMemory_sameCtxWordFlagCol_eq,
    next_chipletMemory_dInvCol_eq, curr_chipletMemory_ctxCol_eq,
    next_chipletMemory_ctxCol_eq, curr_chipletMemory_wordAddrCol_eq,
    next_chipletMemory_wordAddrCol_eq, toSymbolicFrame, FExpr.eval,
    Builder.whenTransition, Builder.gate, Builder.assertEq, Builder.assertZero,
    BaseConstraint.eval, BaseConstraint.expr, AirRow.boundary, AirRow.baseAt,
    AirRow.base, SymbolicFrame.colCurr, SymbolicFrame.colNext, h51, h52, h53,
    h56, h57, h67, h68]
  ring

theorem bridge_chiplet_memory_16 (r : AirRow) :
    Constraints.Symbolic.ChipletMemory.base[16]! (toSymbolicFrame r) =
      Subsystems.ChipletMemory.sameCtxWordReadonly.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change
    (fun f =>
      ((((f.is_transition * ((f.colCurr 51 * f.colCurr 52) * (1 - f.colNext 53))) *
            f.colNext 68) *
          (1 - ((f.colNext 60 - f.colCurr 60) * f.colNext 67))) *
        ((1 - f.colCurr 54) + (1 - f.colNext 54))))
      (toSymbolicFrame r) = Subsystems.ChipletMemory.sameCtxWordReadonly.eval r
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  have h54 : 54 < MainWidth := by decide
  have h60 : 60 < MainWidth := by decide
  have h67 : 67 < MainWidth := by decide
  have h68 : 68 < MainWidth := by decide
  simp [Subsystems.ChipletMemory.sameCtxWordReadonly, Subsystems.ChipletMemory.transitionZero,
    Subsystems.ChipletMemory.flagMemoryActiveNotLast, Subsystems.ChipletMemory.sameCtxWordFlagNext,
    Subsystems.ChipletMemory.clkNoChange, Subsystems.ChipletMemory.anyWrite,
    Subsystems.ChipletMemory.isWrite, Subsystems.ChipletMemory.isWriteNext,
    Subsystems.ChipletMemory.isRead, Subsystems.ChipletMemory.isReadNext,
    Subsystems.ChipletMemory.clkDelta, Subsystems.ChipletMemory.dInvNext,
    Subsystems.ChipletMemory.oneMinus, Subsystems.ChipletMemory.one,
    Subsystems.ChipletMemory.clkNext, Subsystems.ChipletMemory.clk,
    Subsystems.ChipletMemory.s0, Subsystems.ChipletMemory.s1,
    Subsystems.ChipletMemory.s2Next, Subsystems.ChipletSelectors.s0,
    Subsystems.ChipletSelectors.s1, Subsystems.ChipletSelectors.s2Next,
    curr_chipletSelectors_s0Col_eq, curr_chipletSelectors_s1Col_eq,
    next_chipletSelectors_s2Col_eq, curr_chipletMemory_isReadCol_eq,
    next_chipletMemory_isReadCol_eq, curr_chipletMemory_clkCol_eq,
    next_chipletMemory_clkCol_eq, next_chipletMemory_dInvCol_eq,
    next_chipletMemory_sameCtxWordFlagCol_eq, toSymbolicFrame, FExpr.eval,
    Builder.whenTransition, Builder.gate, Builder.assertZero, BaseConstraint.eval,
    BaseConstraint.expr, AirRow.boundary, AirRow.baseAt, AirRow.base,
    SymbolicFrame.colCurr, SymbolicFrame.colNext, h51, h52, h53, h54, h60, h67,
    h68]
  ring

theorem bridge_chiplet_memory_17 (r : AirRow) :
    Constraints.Symbolic.ChipletMemory.base[17]! (toSymbolicFrame r) =
      (Subsystems.ChipletMemory.valueConsistency value0).eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change
    (fun f =>
      (((f.is_transition * ((f.colCurr 51 * f.colCurr 52) * (1 - f.colNext 53))) *
          (f.colNext 54 + (((1 - f.colNext 54) * (1 - f.colNext 55)) *
            (1 - ((1 - f.colNext 59) * (1 - f.colNext 58)))))) *
        (f.colNext 61 - (f.colNext 68 * f.colCurr 61))))
      (toSymbolicFrame r) = (Subsystems.ChipletMemory.valueConsistency value0).eval r
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  have h54 : 54 < MainWidth := by decide
  have h55 : 55 < MainWidth := by decide
  have h58 : 58 < MainWidth := by decide
  have h59 : 59 < MainWidth := by decide
  have h61 : 61 < MainWidth := by decide
  have h68 : 68 < MainWidth := by decide
  simp [Subsystems.ChipletMemory.valueConsistency, Subsystems.ChipletMemory.transitionZero,
    Subsystems.ChipletMemory.flagMemoryActiveNotLast, Subsystems.ChipletMemory.nextValueConstraintFlag,
    Subsystems.ChipletMemory.valueConstraintFlag, Subsystems.ChipletMemory.valueSelectionFlag,
    Subsystems.ChipletMemory.oneMinus, Subsystems.ChipletMemory.one,
    Subsystems.ChipletMemory.isReadNext, Subsystems.ChipletMemory.isWordNext,
    Subsystems.ChipletMemory.idx0Next, Subsystems.ChipletMemory.idx1Next,
    Subsystems.ChipletMemory.valueNext, Subsystems.ChipletMemory.value,
    Subsystems.ChipletMemory.sameCtxWordFlagNext, Subsystems.ChipletMemory.valueCol,
    Subsystems.ChipletMemory.memoryValueOffset, Subsystems.ChipletMemory.memoryTraceOffset,
    Subsystems.ChipletMemory.chipletsOffset, Subsystems.ChipletMemory.s0,
    Subsystems.ChipletMemory.s1, Subsystems.ChipletMemory.s2Next,
    Subsystems.ChipletSelectors.s0, Subsystems.ChipletSelectors.s1,
    Subsystems.ChipletSelectors.s2Next, Subsystems.ChipletSelectors.chipletsOffset,
    curr_chipletSelectors_s0Col_eq, curr_chipletSelectors_s1Col_eq,
    next_chipletSelectors_s2Col_eq, next_chipletMemory_isReadCol_eq,
    next_chipletMemory_isWordCol_eq, next_chipletMemory_idx0Col_eq,
    next_chipletMemory_idx1Col_eq, next_chipletMemory_sameCtxWordFlagCol_eq,
    toSymbolicFrame, FExpr.eval, Builder.whenTransition, Builder.gate,
    Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr, AirRow.boundary,
    AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, SymbolicFrame.colNext,
    h51, h52, h53, h54, h55, h58, h59, h61, h68]
  ring

theorem bridge_chiplet_memory_18 (r : AirRow) :
    Constraints.Symbolic.ChipletMemory.base[18]! (toSymbolicFrame r) =
      (Subsystems.ChipletMemory.valueConsistency value1).eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change
    (fun f =>
      (((f.is_transition * ((f.colCurr 51 * f.colCurr 52) * (1 - f.colNext 53))) *
          (f.colNext 54 + (((1 - f.colNext 54) * (1 - f.colNext 55)) *
            (1 - ((1 - f.colNext 59) * f.colNext 58))))) *
        (f.colNext 62 - (f.colNext 68 * f.colCurr 62))))
      (toSymbolicFrame r) = (Subsystems.ChipletMemory.valueConsistency value1).eval r
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  have h54 : 54 < MainWidth := by decide
  have h55 : 55 < MainWidth := by decide
  have h58 : 58 < MainWidth := by decide
  have h59 : 59 < MainWidth := by decide
  have h62 : 62 < MainWidth := by decide
  have h68 : 68 < MainWidth := by decide
  simp [Subsystems.ChipletMemory.valueConsistency, Subsystems.ChipletMemory.transitionZero,
    Subsystems.ChipletMemory.flagMemoryActiveNotLast, Subsystems.ChipletMemory.nextValueConstraintFlag,
    Subsystems.ChipletMemory.valueConstraintFlag, Subsystems.ChipletMemory.valueSelectionFlag,
    Subsystems.ChipletMemory.oneMinus, Subsystems.ChipletMemory.one,
    Subsystems.ChipletMemory.isReadNext, Subsystems.ChipletMemory.isWordNext,
    Subsystems.ChipletMemory.idx0Next, Subsystems.ChipletMemory.idx1Next,
    Subsystems.ChipletMemory.valueNext, Subsystems.ChipletMemory.value,
    Subsystems.ChipletMemory.sameCtxWordFlagNext, Subsystems.ChipletMemory.valueCol,
    Subsystems.ChipletMemory.memoryValueOffset, Subsystems.ChipletMemory.memoryTraceOffset,
    Subsystems.ChipletMemory.chipletsOffset, Subsystems.ChipletMemory.s0,
    Subsystems.ChipletMemory.s1, Subsystems.ChipletMemory.s2Next,
    Subsystems.ChipletSelectors.s0, Subsystems.ChipletSelectors.s1,
    Subsystems.ChipletSelectors.s2Next, Subsystems.ChipletSelectors.chipletsOffset,
    curr_chipletSelectors_s0Col_eq, curr_chipletSelectors_s1Col_eq,
    next_chipletSelectors_s2Col_eq, next_chipletMemory_isReadCol_eq,
    next_chipletMemory_isWordCol_eq, next_chipletMemory_idx0Col_eq,
    next_chipletMemory_idx1Col_eq, next_chipletMemory_sameCtxWordFlagCol_eq,
    toSymbolicFrame, FExpr.eval, Builder.whenTransition, Builder.gate,
    Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr, AirRow.boundary,
    AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, SymbolicFrame.colNext,
    h51, h52, h53, h54, h55, h58, h59, h62, h68]
  ring

theorem bridge_chiplet_memory_19 (r : AirRow) :
    Constraints.Symbolic.ChipletMemory.base[19]! (toSymbolicFrame r) =
      (Subsystems.ChipletMemory.valueConsistency value2).eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change
    (fun f =>
      (((f.is_transition * ((f.colCurr 51 * f.colCurr 52) * (1 - f.colNext 53))) *
          (f.colNext 54 + (((1 - f.colNext 54) * (1 - f.colNext 55)) *
            (1 - (f.colNext 59 * (1 - f.colNext 58)))))) *
        (f.colNext 63 - (f.colNext 68 * f.colCurr 63))))
      (toSymbolicFrame r) = (Subsystems.ChipletMemory.valueConsistency value2).eval r
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  have h54 : 54 < MainWidth := by decide
  have h55 : 55 < MainWidth := by decide
  have h58 : 58 < MainWidth := by decide
  have h59 : 59 < MainWidth := by decide
  have h63 : 63 < MainWidth := by decide
  have h68 : 68 < MainWidth := by decide
  simp [Subsystems.ChipletMemory.valueConsistency, Subsystems.ChipletMemory.transitionZero,
    Subsystems.ChipletMemory.flagMemoryActiveNotLast, Subsystems.ChipletMemory.nextValueConstraintFlag,
    Subsystems.ChipletMemory.valueConstraintFlag, Subsystems.ChipletMemory.valueSelectionFlag,
    Subsystems.ChipletMemory.oneMinus, Subsystems.ChipletMemory.one,
    Subsystems.ChipletMemory.isReadNext, Subsystems.ChipletMemory.isWordNext,
    Subsystems.ChipletMemory.idx0Next, Subsystems.ChipletMemory.idx1Next,
    Subsystems.ChipletMemory.valueNext, Subsystems.ChipletMemory.value,
    Subsystems.ChipletMemory.sameCtxWordFlagNext, Subsystems.ChipletMemory.valueCol,
    Subsystems.ChipletMemory.memoryValueOffset, Subsystems.ChipletMemory.memoryTraceOffset,
    Subsystems.ChipletMemory.chipletsOffset, Subsystems.ChipletMemory.s0,
    Subsystems.ChipletMemory.s1, Subsystems.ChipletMemory.s2Next,
    Subsystems.ChipletSelectors.s0, Subsystems.ChipletSelectors.s1,
    Subsystems.ChipletSelectors.s2Next, Subsystems.ChipletSelectors.chipletsOffset,
    curr_chipletSelectors_s0Col_eq, curr_chipletSelectors_s1Col_eq,
    next_chipletSelectors_s2Col_eq, next_chipletMemory_isReadCol_eq,
    next_chipletMemory_isWordCol_eq, next_chipletMemory_idx0Col_eq,
    next_chipletMemory_idx1Col_eq, next_chipletMemory_sameCtxWordFlagCol_eq,
    toSymbolicFrame, FExpr.eval, Builder.whenTransition, Builder.gate,
    Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr, AirRow.boundary,
    AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, SymbolicFrame.colNext,
    h51, h52, h53, h54, h55, h58, h59, h63, h68]
  ring

theorem bridge_chiplet_memory_20 (r : AirRow) :
    Constraints.Symbolic.ChipletMemory.base[20]! (toSymbolicFrame r) =
      (Subsystems.ChipletMemory.valueConsistency value3).eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change
    (fun f =>
      (((f.is_transition * ((f.colCurr 51 * f.colCurr 52) * (1 - f.colNext 53))) *
          (f.colNext 54 + (((1 - f.colNext 54) * (1 - f.colNext 55)) *
            (1 - (f.colNext 59 * f.colNext 58))))) *
        (f.colNext 64 - (f.colNext 68 * f.colCurr 64))))
      (toSymbolicFrame r) = (Subsystems.ChipletMemory.valueConsistency value3).eval r
  have h51 : 51 < MainWidth := by decide
  have h52 : 52 < MainWidth := by decide
  have h53 : 53 < MainWidth := by decide
  have h54 : 54 < MainWidth := by decide
  have h55 : 55 < MainWidth := by decide
  have h58 : 58 < MainWidth := by decide
  have h59 : 59 < MainWidth := by decide
  have h64 : 64 < MainWidth := by decide
  have h68 : 68 < MainWidth := by decide
  simp [Subsystems.ChipletMemory.valueConsistency, Subsystems.ChipletMemory.transitionZero,
    Subsystems.ChipletMemory.flagMemoryActiveNotLast, Subsystems.ChipletMemory.nextValueConstraintFlag,
    Subsystems.ChipletMemory.valueConstraintFlag, Subsystems.ChipletMemory.valueSelectionFlag,
    Subsystems.ChipletMemory.oneMinus, Subsystems.ChipletMemory.one,
    Subsystems.ChipletMemory.isReadNext, Subsystems.ChipletMemory.isWordNext,
    Subsystems.ChipletMemory.idx0Next, Subsystems.ChipletMemory.idx1Next,
    Subsystems.ChipletMemory.valueNext, Subsystems.ChipletMemory.value,
    Subsystems.ChipletMemory.sameCtxWordFlagNext, Subsystems.ChipletMemory.valueCol,
    Subsystems.ChipletMemory.memoryValueOffset, Subsystems.ChipletMemory.memoryTraceOffset,
    Subsystems.ChipletMemory.chipletsOffset, Subsystems.ChipletMemory.s0,
    Subsystems.ChipletMemory.s1, Subsystems.ChipletMemory.s2Next,
    Subsystems.ChipletSelectors.s0, Subsystems.ChipletSelectors.s1,
    Subsystems.ChipletSelectors.s2Next, Subsystems.ChipletSelectors.chipletsOffset,
    curr_chipletSelectors_s0Col_eq, curr_chipletSelectors_s1Col_eq,
    next_chipletSelectors_s2Col_eq, next_chipletMemory_isReadCol_eq,
    next_chipletMemory_isWordCol_eq, next_chipletMemory_idx0Col_eq,
    next_chipletMemory_idx1Col_eq, next_chipletMemory_sameCtxWordFlagCol_eq,
    toSymbolicFrame, FExpr.eval, Builder.whenTransition, Builder.gate,
    Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr, AirRow.boundary,
    AirRow.baseAt, AirRow.base, SymbolicFrame.colCurr, SymbolicFrame.colNext,
    h51, h52, h53, h54, h55, h58, h59, h64, h68]
  ring

end MidenLean.AIR.Semantics.Refinement.SymbolicToCanonical
