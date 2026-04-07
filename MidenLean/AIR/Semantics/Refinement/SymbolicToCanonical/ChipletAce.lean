import MidenLean.AIR.Semantics.Tactics
import MidenLean.AIR.Semantics.Subsystems.ChipletAce
import MidenLean.AIR.Constraints.Symbolic.ChipletAce

set_option maxHeartbeats 32000000

namespace MidenLean.AIR.Semantics.Refinement.SymbolicToCanonical

open MidenLean
open MidenLean.AIR
open MidenLean.AIR.Semantics
open MidenLean.AIR.Semantics.Tactics
open MidenLean.AIR.Semantics.Builder

/-!
The symbolic ACE extractor already matches the canonical ACE-local payload
layout: both use the ACE selectors `s0 .. s3` at `cols 51 .. 54`, followed by
ACE payload columns `55 .. 69`. This file bridges the extracted ACE constraints
to the canonical ACE semantics through an ACE-specific symbolic projection that
is now the identity on main columns.
-/

private def aceMainCol (i : Nat) : Nat := i

/-- ACE-specific symbolic projection for the now-direct ACE-local column layout. -/
def toChipletAceSymbolicFrame (r : AirRow) : SymbolicFrame :=
  { toSymbolicFrame r with
    curr := fun i => if h : aceMainCol i < MainWidth then r.curr ⟨aceMainCol i, h⟩ else 0
    next := fun i => if h : aceMainCol i < MainWidth then r.next ⟨aceMainCol i, h⟩ else 0
  }

@[simp] theorem toChipletAceSymbolicFrame_isTransition (r : AirRow) :
    (toChipletAceSymbolicFrame r).is_transition = r.isTransition := rfl

@[simp] theorem aceMainCol_51 : aceMainCol 51 = 51 := by native_decide
@[simp] theorem aceMainCol_52 : aceMainCol 52 = 52 := by native_decide
@[simp] theorem aceMainCol_53 : aceMainCol 53 = 53 := by native_decide
@[simp] theorem aceMainCol_54 : aceMainCol 54 = 54 := by native_decide
@[simp] theorem aceMainCol_55 : aceMainCol 55 = 55 := by native_decide
@[simp] theorem aceMainCol_56 : aceMainCol 56 = 56 := by native_decide
@[simp] theorem aceMainCol_57 : aceMainCol 57 = 57 := by native_decide
@[simp] theorem aceMainCol_58 : aceMainCol 58 = 58 := by native_decide
@[simp] theorem aceMainCol_59 : aceMainCol 59 = 59 := by native_decide
@[simp] theorem aceMainCol_60 : aceMainCol 60 = 60 := by native_decide
@[simp] theorem aceMainCol_61 : aceMainCol 61 = 61 := by native_decide
@[simp] theorem aceMainCol_62 : aceMainCol 62 = 62 := by native_decide
@[simp] theorem aceMainCol_63 : aceMainCol 63 = 63 := by native_decide
@[simp] theorem aceMainCol_64 : aceMainCol 64 = 64 := by native_decide
@[simp] theorem aceMainCol_65 : aceMainCol 65 = 65 := by native_decide
@[simp] theorem aceMainCol_66 : aceMainCol 66 = 66 := by native_decide
@[simp] theorem aceMainCol_67 : aceMainCol 67 = 67 := by native_decide
@[simp] theorem aceMainCol_68 : aceMainCol 68 = 68 := by native_decide
@[simp] theorem aceMainCol_69 : aceMainCol 69 = 69 := by native_decide

theorem toChipletAceSymbolicFrame_colCurr (r : AirRow) (i : Nat) :
    (toChipletAceSymbolicFrame r).colCurr i =
      (if h : aceMainCol i < MainWidth then r.curr ⟨aceMainCol i, h⟩ else 0) := rfl

theorem toChipletAceSymbolicFrame_colNext (r : AirRow) (i : Nat) :
    (toChipletAceSymbolicFrame r).colNext i =
      (if h : aceMainCol i < MainWidth then r.next ⟨aceMainCol i, h⟩ else 0) := rfl

@[simp] theorem chipletAce_oneMinus_eval (expr : FExpr) (r : AirRow) :
    (Subsystems.ChipletAce.oneMinus expr).eval r = 1 - expr.eval r := by
  simp [Subsystems.ChipletAce.oneMinus, Subsystems.ChipletAce.one, FExpr.eval]

@[simp] theorem chipletAce_felt_ofNat_four_eq : (Felt.ofNat 4 : Felt) = 4 := rfl

private theorem hMain51 : 51 < MainWidth := by decide
private theorem hMain52 : 52 < MainWidth := by decide
private theorem hMain53 : 53 < MainWidth := by decide
private theorem hMain54 : 54 < MainWidth := by decide
private theorem hMain55 : 55 < MainWidth := by decide
private theorem hMain56 : 56 < MainWidth := by decide
private theorem hMain57 : 57 < MainWidth := by decide
private theorem hMain58 : 58 < MainWidth := by decide
private theorem hMain59 : 59 < MainWidth := by decide
private theorem hMain60 : 60 < MainWidth := by decide
private theorem hMain61 : 61 < MainWidth := by decide
private theorem hMain62 : 62 < MainWidth := by decide
private theorem hMain63 : 63 < MainWidth := by decide
private theorem hMain64 : 64 < MainWidth := by decide
private theorem hMain65 : 65 < MainWidth := by decide
private theorem hMain66 : 66 < MainWidth := by decide
private theorem hMain67 : 67 < MainWidth := by decide
private theorem hMain68 : 68 < MainWidth := by decide
private theorem hMain69 : 69 < MainWidth := by decide

@[simp] theorem chipletAce_curr_51_any_eq (r : AirRow) (h : 51 < MainWidth) :
    r.curr ⟨51, h⟩ = r.curr 51 := rfl

@[simp] theorem chipletAce_curr_52_any_eq (r : AirRow) (h : 52 < MainWidth) :
    r.curr ⟨52, h⟩ = r.curr 52 := rfl

@[simp] theorem chipletAce_curr_53_any_eq (r : AirRow) (h : 53 < MainWidth) :
    r.curr ⟨53, h⟩ = r.curr 53 := rfl

@[simp] theorem chipletAce_curr_54_any_eq (r : AirRow) (h : 54 < MainWidth) :
    r.curr ⟨54, h⟩ = r.curr 54 := rfl

@[simp] theorem chipletAce_curr_55_any_eq (r : AirRow) (h : 55 < MainWidth) :
    r.curr ⟨55, h⟩ = r.curr 55 := rfl

@[simp] theorem chipletAce_curr_56_any_eq (r : AirRow) (h : 56 < MainWidth) :
    r.curr ⟨56, h⟩ = r.curr 56 := rfl

@[simp] theorem chipletAce_curr_57_any_eq (r : AirRow) (h : 57 < MainWidth) :
    r.curr ⟨57, h⟩ = r.curr 57 := rfl

@[simp] theorem chipletAce_curr_58_any_eq (r : AirRow) (h : 58 < MainWidth) :
    r.curr ⟨58, h⟩ = r.curr 58 := rfl

@[simp] theorem chipletAce_curr_59_any_eq (r : AirRow) (h : 59 < MainWidth) :
    r.curr ⟨59, h⟩ = r.curr 59 := rfl

@[simp] theorem chipletAce_curr_60_any_eq (r : AirRow) (h : 60 < MainWidth) :
    r.curr ⟨60, h⟩ = r.curr 60 := rfl

@[simp] theorem chipletAce_curr_61_any_eq (r : AirRow) (h : 61 < MainWidth) :
    r.curr ⟨61, h⟩ = r.curr 61 := rfl

@[simp] theorem chipletAce_curr_62_any_eq (r : AirRow) (h : 62 < MainWidth) :
    r.curr ⟨62, h⟩ = r.curr 62 := rfl

@[simp] theorem chipletAce_curr_63_any_eq (r : AirRow) (h : 63 < MainWidth) :
    r.curr ⟨63, h⟩ = r.curr 63 := rfl

@[simp] theorem chipletAce_curr_64_any_eq (r : AirRow) (h : 64 < MainWidth) :
    r.curr ⟨64, h⟩ = r.curr 64 := rfl

@[simp] theorem chipletAce_curr_65_any_eq (r : AirRow) (h : 65 < MainWidth) :
    r.curr ⟨65, h⟩ = r.curr 65 := rfl

@[simp] theorem chipletAce_curr_66_any_eq (r : AirRow) (h : 66 < MainWidth) :
    r.curr ⟨66, h⟩ = r.curr 66 := rfl

@[simp] theorem chipletAce_curr_67_any_eq (r : AirRow) (h : 67 < MainWidth) :
    r.curr ⟨67, h⟩ = r.curr 67 := rfl

@[simp] theorem chipletAce_curr_68_any_eq (r : AirRow) (h : 68 < MainWidth) :
    r.curr ⟨68, h⟩ = r.curr 68 := rfl

@[simp] theorem chipletAce_curr_69_any_eq (r : AirRow) (h : 69 < MainWidth) :
    r.curr ⟨69, h⟩ = r.curr 69 := rfl

@[simp] theorem chipletAce_next_51_any_eq (r : AirRow) (h : 51 < MainWidth) :
    r.next ⟨51, h⟩ = r.next 51 := rfl

@[simp] theorem chipletAce_next_52_any_eq (r : AirRow) (h : 52 < MainWidth) :
    r.next ⟨52, h⟩ = r.next 52 := rfl

@[simp] theorem chipletAce_next_53_any_eq (r : AirRow) (h : 53 < MainWidth) :
    r.next ⟨53, h⟩ = r.next 53 := rfl

@[simp] theorem chipletAce_next_54_any_eq (r : AirRow) (h : 54 < MainWidth) :
    r.next ⟨54, h⟩ = r.next 54 := rfl

@[simp] theorem chipletAce_next_55_any_eq (r : AirRow) (h : 55 < MainWidth) :
    r.next ⟨55, h⟩ = r.next 55 := rfl

@[simp] theorem chipletAce_next_56_any_eq (r : AirRow) (h : 56 < MainWidth) :
    r.next ⟨56, h⟩ = r.next 56 := rfl

@[simp] theorem chipletAce_next_57_any_eq (r : AirRow) (h : 57 < MainWidth) :
    r.next ⟨57, h⟩ = r.next 57 := rfl

@[simp] theorem chipletAce_next_58_any_eq (r : AirRow) (h : 58 < MainWidth) :
    r.next ⟨58, h⟩ = r.next 58 := rfl

@[simp] theorem chipletAce_next_59_any_eq (r : AirRow) (h : 59 < MainWidth) :
    r.next ⟨59, h⟩ = r.next 59 := rfl

@[simp] theorem chipletAce_next_60_any_eq (r : AirRow) (h : 60 < MainWidth) :
    r.next ⟨60, h⟩ = r.next 60 := rfl

@[simp] theorem chipletAce_next_61_any_eq (r : AirRow) (h : 61 < MainWidth) :
    r.next ⟨61, h⟩ = r.next 61 := rfl

@[simp] theorem chipletAce_next_62_any_eq (r : AirRow) (h : 62 < MainWidth) :
    r.next ⟨62, h⟩ = r.next 62 := rfl

@[simp] theorem chipletAce_next_63_any_eq (r : AirRow) (h : 63 < MainWidth) :
    r.next ⟨63, h⟩ = r.next 63 := rfl

@[simp] theorem chipletAce_next_64_any_eq (r : AirRow) (h : 64 < MainWidth) :
    r.next ⟨64, h⟩ = r.next 64 := rfl

@[simp] theorem chipletAce_next_65_any_eq (r : AirRow) (h : 65 < MainWidth) :
    r.next ⟨65, h⟩ = r.next 65 := rfl

@[simp] theorem chipletAce_next_66_any_eq (r : AirRow) (h : 66 < MainWidth) :
    r.next ⟨66, h⟩ = r.next 66 := rfl

@[simp] theorem chipletAce_next_67_any_eq (r : AirRow) (h : 67 < MainWidth) :
    r.next ⟨67, h⟩ = r.next 67 := rfl

@[simp] theorem chipletAce_next_68_any_eq (r : AirRow) (h : 68 < MainWidth) :
    r.next ⟨68, h⟩ = r.next 68 := rfl

@[simp] theorem chipletAce_next_69_any_eq (r : AirRow) (h : 69 < MainWidth) :
    r.next ⟨69, h⟩ = r.next 69 := rfl

@[simp] theorem chipletAce_symCurr_51_eq (r : AirRow) :
    (toChipletAceSymbolicFrame r).colCurr 51 = r.curr 51 := by
  simp [toChipletAceSymbolicFrame_colCurr, hMain51]

@[simp] theorem chipletAce_symCurr_52_eq (r : AirRow) :
    (toChipletAceSymbolicFrame r).colCurr 52 = r.curr 52 := by
  simp [toChipletAceSymbolicFrame_colCurr, hMain52]

@[simp] theorem chipletAce_symCurr_53_eq (r : AirRow) :
    (toChipletAceSymbolicFrame r).colCurr 53 = r.curr 53 := by
  simp [toChipletAceSymbolicFrame_colCurr, hMain53]

@[simp] theorem chipletAce_symCurr_54_eq (r : AirRow) :
    (toChipletAceSymbolicFrame r).colCurr 54 = r.curr 54 := by
  simp [toChipletAceSymbolicFrame_colCurr, hMain54]

@[simp] theorem chipletAce_symCurr_55_eq (r : AirRow) :
    (toChipletAceSymbolicFrame r).colCurr 55 = r.curr 55 := by
  simp [toChipletAceSymbolicFrame_colCurr, hMain55]

@[simp] theorem chipletAce_symCurr_56_eq (r : AirRow) :
    (toChipletAceSymbolicFrame r).colCurr 56 = r.curr 56 := by
  simp [toChipletAceSymbolicFrame_colCurr, hMain56]

@[simp] theorem chipletAce_symCurr_57_eq (r : AirRow) :
    (toChipletAceSymbolicFrame r).colCurr 57 = r.curr 57 := by
  simp [toChipletAceSymbolicFrame_colCurr, hMain57]

@[simp] theorem chipletAce_symCurr_58_eq (r : AirRow) :
    (toChipletAceSymbolicFrame r).colCurr 58 = r.curr 58 := by
  simp [toChipletAceSymbolicFrame_colCurr, hMain58]

@[simp] theorem chipletAce_symCurr_59_eq (r : AirRow) :
    (toChipletAceSymbolicFrame r).colCurr 59 = r.curr 59 := by
  simp [toChipletAceSymbolicFrame_colCurr, hMain59]

@[simp] theorem chipletAce_symCurr_60_eq (r : AirRow) :
    (toChipletAceSymbolicFrame r).colCurr 60 = r.curr 60 := by
  simp [toChipletAceSymbolicFrame_colCurr, hMain60]

@[simp] theorem chipletAce_symCurr_61_eq (r : AirRow) :
    (toChipletAceSymbolicFrame r).colCurr 61 = r.curr 61 := by
  simp [toChipletAceSymbolicFrame_colCurr, hMain61]

@[simp] theorem chipletAce_symCurr_62_eq (r : AirRow) :
    (toChipletAceSymbolicFrame r).colCurr 62 = r.curr 62 := by
  simp [toChipletAceSymbolicFrame_colCurr, hMain62]

@[simp] theorem chipletAce_symCurr_63_eq (r : AirRow) :
    (toChipletAceSymbolicFrame r).colCurr 63 = r.curr 63 := by
  simp [toChipletAceSymbolicFrame_colCurr, hMain63]

@[simp] theorem chipletAce_symCurr_64_eq (r : AirRow) :
    (toChipletAceSymbolicFrame r).colCurr 64 = r.curr 64 := by
  simp [toChipletAceSymbolicFrame_colCurr, hMain64]

@[simp] theorem chipletAce_symCurr_65_eq (r : AirRow) :
    (toChipletAceSymbolicFrame r).colCurr 65 = r.curr 65 := by
  simp [toChipletAceSymbolicFrame_colCurr, hMain65]

@[simp] theorem chipletAce_symCurr_66_eq (r : AirRow) :
    (toChipletAceSymbolicFrame r).colCurr 66 = r.curr 66 := by
  simp [toChipletAceSymbolicFrame_colCurr, hMain66]

@[simp] theorem chipletAce_symCurr_67_eq (r : AirRow) :
    (toChipletAceSymbolicFrame r).colCurr 67 = r.curr 67 := by
  simp [toChipletAceSymbolicFrame_colCurr, hMain67]

@[simp] theorem chipletAce_symCurr_68_eq (r : AirRow) :
    (toChipletAceSymbolicFrame r).colCurr 68 = r.curr 68 := by
  simp [toChipletAceSymbolicFrame_colCurr, hMain68]

@[simp] theorem chipletAce_symCurr_69_eq (r : AirRow) :
    (toChipletAceSymbolicFrame r).colCurr 69 = r.curr 69 := by
  simp [toChipletAceSymbolicFrame_colCurr, hMain69]

@[simp] theorem chipletAce_symNext_51_eq (r : AirRow) :
    (toChipletAceSymbolicFrame r).colNext 51 = r.next 51 := by
  simp [toChipletAceSymbolicFrame_colNext, hMain51]

@[simp] theorem chipletAce_symNext_52_eq (r : AirRow) :
    (toChipletAceSymbolicFrame r).colNext 52 = r.next 52 := by
  simp [toChipletAceSymbolicFrame_colNext, hMain52]

@[simp] theorem chipletAce_symNext_53_eq (r : AirRow) :
    (toChipletAceSymbolicFrame r).colNext 53 = r.next 53 := by
  simp [toChipletAceSymbolicFrame_colNext, hMain53]

@[simp] theorem chipletAce_symNext_54_eq (r : AirRow) :
    (toChipletAceSymbolicFrame r).colNext 54 = r.next 54 := by
  simp [toChipletAceSymbolicFrame_colNext, hMain54]

@[simp] theorem chipletAce_symNext_55_eq (r : AirRow) :
    (toChipletAceSymbolicFrame r).colNext 55 = r.next 55 := by
  simp [toChipletAceSymbolicFrame_colNext, hMain55]

@[simp] theorem chipletAce_symNextField_55_eq (r : AirRow) :
    (toChipletAceSymbolicFrame r).next 55 = r.next 55 := by
  simp [toChipletAceSymbolicFrame, hMain55]

@[simp] theorem chipletAce_symNext_56_eq (r : AirRow) :
    (toChipletAceSymbolicFrame r).colNext 56 = r.next 56 := by
  simp [toChipletAceSymbolicFrame_colNext, hMain56]

@[simp] theorem chipletAce_symNext_57_eq (r : AirRow) :
    (toChipletAceSymbolicFrame r).colNext 57 = r.next 57 := by
  simp [toChipletAceSymbolicFrame_colNext, hMain57]

@[simp] theorem chipletAce_symNext_58_eq (r : AirRow) :
    (toChipletAceSymbolicFrame r).colNext 58 = r.next 58 := by
  simp [toChipletAceSymbolicFrame_colNext, hMain58]

@[simp] theorem chipletAce_symNext_59_eq (r : AirRow) :
    (toChipletAceSymbolicFrame r).colNext 59 = r.next 59 := by
  simp [toChipletAceSymbolicFrame_colNext, hMain59]

@[simp] theorem chipletAce_symNext_60_eq (r : AirRow) :
    (toChipletAceSymbolicFrame r).colNext 60 = r.next 60 := by
  simp [toChipletAceSymbolicFrame_colNext, hMain60]

@[simp] theorem chipletAce_symNext_61_eq (r : AirRow) :
    (toChipletAceSymbolicFrame r).colNext 61 = r.next 61 := by
  simp [toChipletAceSymbolicFrame_colNext, hMain61]

@[simp] theorem chipletAce_symNext_62_eq (r : AirRow) :
    (toChipletAceSymbolicFrame r).colNext 62 = r.next 62 := by
  simp [toChipletAceSymbolicFrame_colNext, hMain62]

@[simp] theorem chipletAce_symNext_63_eq (r : AirRow) :
    (toChipletAceSymbolicFrame r).colNext 63 = r.next 63 := by
  simp [toChipletAceSymbolicFrame_colNext, hMain63]

@[simp] theorem chipletAce_symNext_64_eq (r : AirRow) :
    (toChipletAceSymbolicFrame r).colNext 64 = r.next 64 := by
  simp [toChipletAceSymbolicFrame_colNext, hMain64]

@[simp] theorem chipletAce_symNext_65_eq (r : AirRow) :
    (toChipletAceSymbolicFrame r).colNext 65 = r.next 65 := by
  simp [toChipletAceSymbolicFrame_colNext, hMain65]

@[simp] theorem chipletAce_symNext_66_eq (r : AirRow) :
    (toChipletAceSymbolicFrame r).colNext 66 = r.next 66 := by
  simp [toChipletAceSymbolicFrame_colNext, hMain66]

@[simp] theorem chipletAce_symNext_67_eq (r : AirRow) :
    (toChipletAceSymbolicFrame r).colNext 67 = r.next 67 := by
  simp [toChipletAceSymbolicFrame_colNext, hMain67]

@[simp] theorem chipletAce_symNext_68_eq (r : AirRow) :
    (toChipletAceSymbolicFrame r).colNext 68 = r.next 68 := by
  simp [toChipletAceSymbolicFrame_colNext, hMain68]

@[simp] theorem chipletAce_symNext_69_eq (r : AirRow) :
    (toChipletAceSymbolicFrame r).colNext 69 = r.next 69 := by
  simp [toChipletAceSymbolicFrame_colNext, hMain69]

theorem bridge_chiplet_ace_0 (r : AirRow) :
    Constraints.Symbolic.ChipletAce.base[0]! (toChipletAceSymbolicFrame r) =
      Subsystems.ChipletAce.sstartBinary.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => (((((f.colCurr 51 * f.colCurr 52) * f.colCurr 53) *
      (1 - f.colCurr 54)) * f.colCurr 55) * (f.colCurr 55 - 1)))
      (toChipletAceSymbolicFrame r) = Subsystems.ChipletAce.sstartBinary.eval r
  simp [Subsystems.ChipletAce.sstartBinary, Subsystems.ChipletAce.integrityZero,
    Subsystems.ChipletAce.aceFlag, Subsystems.ChipletAce.sstart, Subsystems.ChipletAce.one,
    Subsystems.ChipletAce.sstartCol, Subsystems.ChipletAce.aceTraceOffset,
    Subsystems.ChipletAce.chipletsOffset, Subsystems.ChipletSelectors.aceChipletFlag,
    Subsystems.ChipletSelectors.s012, Subsystems.ChipletSelectors.s01,
    Subsystems.ChipletSelectors.notS3, Subsystems.ChipletSelectors.s0,
    Subsystems.ChipletSelectors.s1, Subsystems.ChipletSelectors.s2,
    Subsystems.ChipletSelectors.s3, Subsystems.ChipletSelectors.s0Col,
    Subsystems.ChipletSelectors.s1Col, Subsystems.ChipletSelectors.s2Col,
    Subsystems.ChipletSelectors.s3Col, Subsystems.ChipletSelectors.chipletsOffset,
    toChipletAceSymbolicFrame_colCurr, aceMainCol, FExpr.eval, Builder.gate,
    Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr, AirRow.baseAt, AirRow.base,
    hMain51, hMain52, hMain53, hMain54, hMain55]
  all_goals ring_nf

theorem bridge_chiplet_ace_1 (r : AirRow) :
    Constraints.Symbolic.ChipletAce.base[1]! (toChipletAceSymbolicFrame r) =
      Subsystems.ChipletAce.sblockBinary.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => (((((f.colCurr 51 * f.colCurr 52) * f.colCurr 53) *
      (1 - f.colCurr 54)) * f.colCurr 56) * (f.colCurr 56 - 1)))
      (toChipletAceSymbolicFrame r) = Subsystems.ChipletAce.sblockBinary.eval r
  simp [Subsystems.ChipletAce.sblockBinary, Subsystems.ChipletAce.integrityZero,
    Subsystems.ChipletAce.aceFlag, Subsystems.ChipletAce.sblock, Subsystems.ChipletAce.one,
    Subsystems.ChipletAce.sblockCol, Subsystems.ChipletAce.aceTraceOffset,
    Subsystems.ChipletAce.chipletsOffset, Subsystems.ChipletSelectors.aceChipletFlag,
    Subsystems.ChipletSelectors.s012, Subsystems.ChipletSelectors.s01,
    Subsystems.ChipletSelectors.notS3, Subsystems.ChipletSelectors.s0,
    Subsystems.ChipletSelectors.s1, Subsystems.ChipletSelectors.s2,
    Subsystems.ChipletSelectors.s3, Subsystems.ChipletSelectors.s0Col,
    Subsystems.ChipletSelectors.s1Col, Subsystems.ChipletSelectors.s2Col,
    Subsystems.ChipletSelectors.s3Col, Subsystems.ChipletSelectors.chipletsOffset,
    toChipletAceSymbolicFrame_colCurr, aceMainCol, FExpr.eval, Builder.gate,
    Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr, AirRow.baseAt, AirRow.base,
    hMain51, hMain52, hMain53, hMain54, hMain56]
  ring_nf

theorem bridge_chiplet_ace_2 (r : AirRow) :
    Constraints.Symbolic.ChipletAce.base[2]! (toChipletAceSymbolicFrame r) =
      Subsystems.ChipletAce.lastAceRowNotSectionStart.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => (((((f.colCurr 51 * f.colCurr 52) * f.colCurr 53) *
      (1 - f.colCurr 54)) * (f.is_transition * f.colNext 54)) * f.colCurr 55))
      (toChipletAceSymbolicFrame r) = Subsystems.ChipletAce.lastAceRowNotSectionStart.eval r
  simp [Subsystems.ChipletAce.lastAceRowNotSectionStart, Subsystems.ChipletAce.transitionZero,
    Subsystems.ChipletAce.aceFlag, Subsystems.ChipletAce.flagAceLast, Subsystems.ChipletAce.sstart,
    Subsystems.ChipletAce.sstartCol, Subsystems.ChipletAce.aceTraceOffset,
    Subsystems.ChipletAce.chipletsOffset, Subsystems.ChipletSelectors.aceChipletFlag,
    Subsystems.ChipletSelectors.s3Next, Subsystems.ChipletSelectors.s012,
    Subsystems.ChipletSelectors.s01, Subsystems.ChipletSelectors.notS3,
    Subsystems.ChipletSelectors.s0, Subsystems.ChipletSelectors.s1,
    Subsystems.ChipletSelectors.s2, Subsystems.ChipletSelectors.s3,
    Subsystems.ChipletSelectors.s0Col, Subsystems.ChipletSelectors.s1Col,
    Subsystems.ChipletSelectors.s2Col, Subsystems.ChipletSelectors.s3Col,
    Subsystems.ChipletSelectors.chipletsOffset, FExpr.eval, Builder.whenTransition,
    Builder.gate, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.boundary, AirRow.baseAt, AirRow.base, hMain51, hMain52, hMain53, hMain54,
    hMain55]
  all_goals ring_nf

theorem bridge_chiplet_ace_3 (r : AirRow) :
    Constraints.Symbolic.ChipletAce.base[3]! (toChipletAceSymbolicFrame r) =
      Subsystems.ChipletAce.noConsecutiveSectionStarts.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => ((((((f.colCurr 51 * f.colCurr 52) * f.colCurr 53) *
      (1 - f.colCurr 54)) * (f.is_transition * (1 - f.colNext 54))) *
      f.colCurr 55) * f.colNext 55))
      (toChipletAceSymbolicFrame r) = Subsystems.ChipletAce.noConsecutiveSectionStarts.eval r
  simp [Subsystems.ChipletAce.noConsecutiveSectionStarts, Subsystems.ChipletAce.transitionZero,
    Subsystems.ChipletAce.aceFlag, Subsystems.ChipletAce.flagAceNext, Subsystems.ChipletAce.sstart,
    Subsystems.ChipletAce.sstartNext, Subsystems.ChipletAce.one, Subsystems.ChipletAce.sstartCol,
    Subsystems.ChipletAce.aceTraceOffset, Subsystems.ChipletAce.chipletsOffset,
    Subsystems.ChipletSelectors.aceChipletFlag, Subsystems.ChipletSelectors.s3Next,
    Subsystems.ChipletSelectors.s012, Subsystems.ChipletSelectors.s01,
    Subsystems.ChipletSelectors.notS3, Subsystems.ChipletSelectors.s0,
    Subsystems.ChipletSelectors.s1, Subsystems.ChipletSelectors.s2,
    Subsystems.ChipletSelectors.s3, Subsystems.ChipletSelectors.s0Col,
    Subsystems.ChipletSelectors.s1Col, Subsystems.ChipletSelectors.s2Col,
    Subsystems.ChipletSelectors.s3Col, Subsystems.ChipletSelectors.chipletsOffset,
    toChipletAceSymbolicFrame_colCurr, toChipletAceSymbolicFrame_colNext, aceMainCol,
    FExpr.eval, Builder.whenTransition, Builder.gate, Builder.assertZero,
    BaseConstraint.eval, BaseConstraint.expr, AirRow.boundary, AirRow.baseAt, AirRow.base,
    hMain51, hMain52, hMain53, hMain54, hMain55]
  all_goals ring_nf

theorem bridge_chiplet_ace_4 (r : AirRow) :
    Constraints.Symbolic.ChipletAce.base[4]! (toChipletAceSymbolicFrame r) =
      Subsystems.ChipletAce.sectionStartsWithRead.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => (((((f.colCurr 51 * f.colCurr 52) * f.colCurr 53) *
      (1 - f.colCurr 54)) * f.colCurr 55) * f.colCurr 56))
      (toChipletAceSymbolicFrame r) = Subsystems.ChipletAce.sectionStartsWithRead.eval r
  simp [Subsystems.ChipletAce.sectionStartsWithRead, Subsystems.ChipletAce.integrityZero,
    Subsystems.ChipletAce.aceFlag, Subsystems.ChipletAce.sstart, Subsystems.ChipletAce.sblock,
    Subsystems.ChipletAce.sstartCol, Subsystems.ChipletAce.sblockCol,
    Subsystems.ChipletAce.aceTraceOffset, Subsystems.ChipletAce.chipletsOffset,
    Subsystems.ChipletSelectors.aceChipletFlag, Subsystems.ChipletSelectors.s012,
    Subsystems.ChipletSelectors.s01, Subsystems.ChipletSelectors.notS3,
    Subsystems.ChipletSelectors.s0, Subsystems.ChipletSelectors.s1,
    Subsystems.ChipletSelectors.s2, Subsystems.ChipletSelectors.s3,
    Subsystems.ChipletSelectors.s0Col, Subsystems.ChipletSelectors.s1Col,
    Subsystems.ChipletSelectors.s2Col, Subsystems.ChipletSelectors.s3Col,
    Subsystems.ChipletSelectors.chipletsOffset, toChipletAceSymbolicFrame_colCurr,
    aceMainCol, FExpr.eval, Builder.gate, Builder.assertZero, BaseConstraint.eval,
    BaseConstraint.expr, AirRow.baseAt, AirRow.base, hMain51, hMain52, hMain53,
    hMain54, hMain55, hMain56]
  all_goals ring_nf

theorem bridge_chiplet_ace_5 (r : AirRow) :
    Constraints.Symbolic.ChipletAce.base[5]! (toChipletAceSymbolicFrame r) =
      Subsystems.ChipletAce.noEvalToReadWithinSection.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => (((((((f.colCurr 51 * f.colCurr 52) * f.colCurr 53) *
      (1 - f.colCurr 54)) * (f.is_transition * (1 - f.colNext 54))) *
      (1 - f.colNext 55)) * f.colCurr 56) * (1 - f.colNext 56)))
      (toChipletAceSymbolicFrame r) =
        Subsystems.ChipletAce.noEvalToReadWithinSection.eval r
  simp [Subsystems.ChipletAce.noEvalToReadWithinSection, Subsystems.ChipletAce.transitionZero,
    Subsystems.ChipletAce.aceFlag, Subsystems.ChipletAce.flagAceNext, Subsystems.ChipletAce.fNext,
    Subsystems.ChipletAce.sblock, Subsystems.ChipletAce.sblockNext, Subsystems.ChipletAce.one,
    Subsystems.ChipletAce.sblockCol, Subsystems.ChipletAce.sstartNext,
    Subsystems.ChipletAce.sstartCol, Subsystems.ChipletAce.aceTraceOffset,
    Subsystems.ChipletAce.chipletsOffset, Subsystems.ChipletSelectors.aceChipletFlag,
    Subsystems.ChipletSelectors.s3Next, Subsystems.ChipletSelectors.s012,
    Subsystems.ChipletSelectors.s01, Subsystems.ChipletSelectors.notS3,
    Subsystems.ChipletSelectors.s0, Subsystems.ChipletSelectors.s1,
    Subsystems.ChipletSelectors.s2, Subsystems.ChipletSelectors.s3,
    Subsystems.ChipletSelectors.s0Col, Subsystems.ChipletSelectors.s1Col,
    Subsystems.ChipletSelectors.s2Col, Subsystems.ChipletSelectors.s3Col,
    Subsystems.ChipletSelectors.chipletsOffset, FExpr.eval, Builder.whenTransition,
    Builder.gate, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.boundary, AirRow.baseAt, AirRow.base, hMain51, hMain52, hMain53, hMain54,
    hMain55, hMain56]
  all_goals ring_nf

theorem bridge_chiplet_ace_6 (r : AirRow) :
    Constraints.Symbolic.ChipletAce.base[6]! (toChipletAceSymbolicFrame r) =
      Subsystems.ChipletAce.sectionsEndWithEval.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => ((((((f.colCurr 51 * f.colCurr 52) * f.colCurr 53) *
      (1 - f.colCurr 54)) * f.is_transition) *
      ((((1 - f.colNext 54) * f.colNext 55) + f.colNext 54) -
        (((1 - f.colNext 54) * f.colNext 55) * f.colNext 54))) *
      (1 - f.colCurr 56))) (toChipletAceSymbolicFrame r) =
        Subsystems.ChipletAce.sectionsEndWithEval.eval r
  simp [Subsystems.ChipletAce.sectionsEndWithEval, Subsystems.ChipletAce.transitionZero,
    Subsystems.ChipletAce.aceFlag, Subsystems.ChipletAce.fEnd, Subsystems.ChipletAce.binaryOr,
    Subsystems.ChipletAce.flagAceNext, Subsystems.ChipletAce.sstartNext,
    Subsystems.ChipletAce.flagAceLast, Subsystems.ChipletAce.sblock,
    Subsystems.ChipletAce.one, Subsystems.ChipletAce.sstartCol, Subsystems.ChipletAce.sblockCol,
    Subsystems.ChipletAce.aceTraceOffset, Subsystems.ChipletAce.chipletsOffset,
    Subsystems.ChipletSelectors.aceChipletFlag, Subsystems.ChipletSelectors.s3Next,
    Subsystems.ChipletSelectors.s012, Subsystems.ChipletSelectors.s01,
    Subsystems.ChipletSelectors.notS3, Subsystems.ChipletSelectors.s0,
    Subsystems.ChipletSelectors.s1, Subsystems.ChipletSelectors.s2,
    Subsystems.ChipletSelectors.s3, Subsystems.ChipletSelectors.s0Col,
    Subsystems.ChipletSelectors.s1Col, Subsystems.ChipletSelectors.s2Col,
    Subsystems.ChipletSelectors.s3Col, Subsystems.ChipletSelectors.chipletsOffset,
    toChipletAceSymbolicFrame_colCurr, toChipletAceSymbolicFrame_colNext, aceMainCol,
    FExpr.eval, Builder.whenTransition, Builder.gate, Builder.assertZero,
    BaseConstraint.eval, BaseConstraint.expr, AirRow.boundary, AirRow.baseAt, AirRow.base,
    hMain51, hMain52, hMain53, hMain54, hMain55, hMain56]
  all_goals ring_nf

theorem bridge_chiplet_ace_7 (r : AirRow) :
    Constraints.Symbolic.ChipletAce.base[7]! (toChipletAceSymbolicFrame r) =
      Subsystems.ChipletAce.ctxConsistencyWithinSection.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => ((((((f.colCurr 51 * f.colCurr 52) * f.colCurr 53) *
      (1 - f.colCurr 54)) * (f.is_transition * (1 - f.colNext 54))) *
      (1 - f.colNext 55)) * (f.colNext 57 - f.colCurr 57)))
      (toChipletAceSymbolicFrame r) =
        Subsystems.ChipletAce.ctxConsistencyWithinSection.eval r
  simp [Subsystems.ChipletAce.ctxConsistencyWithinSection, Subsystems.ChipletAce.transitionZero,
    Subsystems.ChipletAce.withinSectionGate, Subsystems.ChipletAce.aceFlag,
    Subsystems.ChipletAce.flagAceNext, Subsystems.ChipletAce.flagWithinSection,
    Subsystems.ChipletAce.ctxNext, Subsystems.ChipletAce.ctx, Subsystems.ChipletAce.one,
    Subsystems.ChipletAce.sstartNext, Subsystems.ChipletAce.ctxCol, Subsystems.ChipletAce.sstartCol,
    Subsystems.ChipletAce.aceTraceOffset, Subsystems.ChipletAce.chipletsOffset,
    Subsystems.ChipletSelectors.aceChipletFlag, Subsystems.ChipletSelectors.s3Next,
    Subsystems.ChipletSelectors.s012, Subsystems.ChipletSelectors.s01,
    Subsystems.ChipletSelectors.notS3, Subsystems.ChipletSelectors.s0,
    Subsystems.ChipletSelectors.s1, Subsystems.ChipletSelectors.s2,
    Subsystems.ChipletSelectors.s3, Subsystems.ChipletSelectors.s0Col,
    Subsystems.ChipletSelectors.s1Col, Subsystems.ChipletSelectors.s2Col,
    Subsystems.ChipletSelectors.s3Col, Subsystems.ChipletSelectors.chipletsOffset,
    toChipletAceSymbolicFrame_colCurr, toChipletAceSymbolicFrame_colNext, aceMainCol,
    FExpr.eval, Builder.whenTransition, Builder.gate, Builder.assertZero,
    BaseConstraint.eval, BaseConstraint.expr, AirRow.boundary, AirRow.baseAt, AirRow.base,
    hMain51, hMain52, hMain53, hMain54, hMain55, hMain57]
  all_goals ring_nf

theorem bridge_chiplet_ace_8 (r : AirRow) :
    Constraints.Symbolic.ChipletAce.base[8]! (toChipletAceSymbolicFrame r) =
      Subsystems.ChipletAce.clkConsistencyWithinSection.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => ((((((f.colCurr 51 * f.colCurr 52) * f.colCurr 53) *
      (1 - f.colCurr 54)) * (f.is_transition * (1 - f.colNext 54))) *
      (1 - f.colNext 55)) * (f.colNext 59 - f.colCurr 59)))
      (toChipletAceSymbolicFrame r) =
        Subsystems.ChipletAce.clkConsistencyWithinSection.eval r
  simp [Subsystems.ChipletAce.clkConsistencyWithinSection, Subsystems.ChipletAce.transitionZero,
    Subsystems.ChipletAce.withinSectionGate, Subsystems.ChipletAce.aceFlag,
    Subsystems.ChipletAce.flagAceNext, Subsystems.ChipletAce.flagWithinSection,
    Subsystems.ChipletAce.clkNext, Subsystems.ChipletAce.clk, Subsystems.ChipletAce.one,
    Subsystems.ChipletAce.sstartNext, Subsystems.ChipletAce.clkCol, Subsystems.ChipletAce.sstartCol,
    Subsystems.ChipletAce.aceTraceOffset, Subsystems.ChipletAce.chipletsOffset,
    Subsystems.ChipletSelectors.aceChipletFlag, Subsystems.ChipletSelectors.s3Next,
    Subsystems.ChipletSelectors.s012, Subsystems.ChipletSelectors.s01,
    Subsystems.ChipletSelectors.notS3, Subsystems.ChipletSelectors.s0,
    Subsystems.ChipletSelectors.s1, Subsystems.ChipletSelectors.s2,
    Subsystems.ChipletSelectors.s3, Subsystems.ChipletSelectors.s0Col,
    Subsystems.ChipletSelectors.s1Col, Subsystems.ChipletSelectors.s2Col,
    Subsystems.ChipletSelectors.s3Col, Subsystems.ChipletSelectors.chipletsOffset,
    toChipletAceSymbolicFrame_colCurr, toChipletAceSymbolicFrame_colNext, aceMainCol,
    FExpr.eval, Builder.whenTransition, Builder.gate, Builder.assertZero,
    BaseConstraint.eval, BaseConstraint.expr, AirRow.boundary, AirRow.baseAt, AirRow.base,
    hMain51, hMain52, hMain53, hMain54, hMain55, hMain59]
  all_goals ring_nf

theorem bridge_chiplet_ace_9 (r : AirRow) :
    Constraints.Symbolic.ChipletAce.base[9]! (toChipletAceSymbolicFrame r) =
      Subsystems.ChipletAce.ptrAdvanceWithinSection.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => ((((((f.colCurr 51 * f.colCurr 52) * f.colCurr 53) *
      (1 - f.colCurr 54)) * (f.is_transition * (1 - f.colNext 54))) *
      (1 - f.colNext 55)) *
      (f.colNext 58 - ((f.colCurr 58 + (Felt.ofNat 4 * (1 - f.colCurr 56))) + f.colCurr 56))))
      (toChipletAceSymbolicFrame r) =
        Subsystems.ChipletAce.ptrAdvanceWithinSection.eval r
  simp [Subsystems.ChipletAce.ptrAdvanceWithinSection, Subsystems.ChipletAce.transitionEq,
    Subsystems.ChipletAce.withinSectionGate, Subsystems.ChipletAce.expectedPtrNext,
    Subsystems.ChipletAce.aceFlag, Subsystems.ChipletAce.flagAceNext,
    Subsystems.ChipletAce.flagWithinSection, Subsystems.ChipletAce.ptrNext,
    Subsystems.ChipletAce.ptr, Subsystems.ChipletAce.fRead, Subsystems.ChipletAce.fEval,
    Subsystems.ChipletAce.four, Subsystems.ChipletAce.one, Subsystems.ChipletAce.sstartNext,
    Subsystems.ChipletAce.sblock, Subsystems.ChipletAce.ptrCol, Subsystems.ChipletAce.sstartCol,
    Subsystems.ChipletAce.sblockCol, Subsystems.ChipletAce.aceTraceOffset,
    Subsystems.ChipletAce.chipletsOffset, Subsystems.ChipletSelectors.aceChipletFlag,
    Subsystems.ChipletSelectors.s3Next, Subsystems.ChipletSelectors.s012,
    Subsystems.ChipletSelectors.s01, Subsystems.ChipletSelectors.notS3,
    Subsystems.ChipletSelectors.s0, Subsystems.ChipletSelectors.s1,
    Subsystems.ChipletSelectors.s2, Subsystems.ChipletSelectors.s3,
    Subsystems.ChipletSelectors.s0Col, Subsystems.ChipletSelectors.s1Col,
    Subsystems.ChipletSelectors.s2Col, Subsystems.ChipletSelectors.s3Col,
    Subsystems.ChipletSelectors.chipletsOffset, toChipletAceSymbolicFrame_colCurr,
    toChipletAceSymbolicFrame_colNext, aceMainCol, FExpr.eval, Builder.whenTransition,
    Builder.gate, Builder.assertEq, Builder.assertZero, BaseConstraint.eval,
    BaseConstraint.expr, AirRow.boundary, AirRow.baseAt, AirRow.base, hMain51, hMain52,
    hMain53, hMain54, hMain55, hMain56, hMain58]
  ring_nf

theorem bridge_chiplet_ace_10 (r : AirRow) :
    Constraints.Symbolic.ChipletAce.base[10]! (toChipletAceSymbolicFrame r) =
      Subsystems.ChipletAce.id0DecrementsWithinSection.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => ((((((f.colCurr 51 * f.colCurr 52) * f.colCurr 53) *
      (1 - f.colCurr 54)) * (f.is_transition * (1 - f.colNext 54))) *
      (1 - f.colNext 55)) *
      (f.colCurr 61 - ((f.colNext 61 + ((1 - f.colCurr 56) + (1 - f.colCurr 56))) +
        f.colCurr 56)))) (toChipletAceSymbolicFrame r) =
        Subsystems.ChipletAce.id0DecrementsWithinSection.eval r
  simp [Subsystems.ChipletAce.id0DecrementsWithinSection, Subsystems.ChipletAce.transitionEq,
    Subsystems.ChipletAce.withinSectionGate, Subsystems.ChipletAce.expectedId0,
    Subsystems.ChipletAce.aceFlag, Subsystems.ChipletAce.flagAceNext,
    Subsystems.ChipletAce.flagWithinSection, Subsystems.ChipletAce.id0,
    Subsystems.ChipletAce.id0Next, Subsystems.ChipletAce.fRead, Subsystems.ChipletAce.fEval,
    Subsystems.ChipletAce.double, Subsystems.ChipletAce.one, Subsystems.ChipletAce.sstartNext,
    Subsystems.ChipletAce.sblock, Subsystems.ChipletAce.id0Col, Subsystems.ChipletAce.sstartCol,
    Subsystems.ChipletAce.sblockCol, Subsystems.ChipletAce.aceTraceOffset,
    Subsystems.ChipletAce.chipletsOffset, Subsystems.ChipletSelectors.aceChipletFlag,
    Subsystems.ChipletSelectors.s3Next, Subsystems.ChipletSelectors.s012,
    Subsystems.ChipletSelectors.s01, Subsystems.ChipletSelectors.notS3,
    Subsystems.ChipletSelectors.s0, Subsystems.ChipletSelectors.s1,
    Subsystems.ChipletSelectors.s2, Subsystems.ChipletSelectors.s3,
    Subsystems.ChipletSelectors.s0Col, Subsystems.ChipletSelectors.s1Col,
    Subsystems.ChipletSelectors.s2Col, Subsystems.ChipletSelectors.s3Col,
    Subsystems.ChipletSelectors.chipletsOffset, toChipletAceSymbolicFrame_colCurr,
    toChipletAceSymbolicFrame_colNext, aceMainCol, FExpr.eval, Builder.whenTransition,
    Builder.gate, Builder.assertEq, Builder.assertZero, BaseConstraint.eval,
    BaseConstraint.expr, AirRow.boundary, AirRow.baseAt, AirRow.base, hMain51, hMain52,
    hMain53, hMain54, hMain55, hMain56, hMain61]
  all_goals ring_nf

theorem bridge_chiplet_ace_11 (r : AirRow) :
    Constraints.Symbolic.ChipletAce.base[11]! (toChipletAceSymbolicFrame r) =
      Subsystems.ChipletAce.readIdsConsecutive.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => (((((f.colCurr 51 * f.colCurr 52) * f.colCurr 53) *
      (1 - f.colCurr 54)) * (1 - f.colCurr 56)) *
      ((f.colCurr 64 - f.colCurr 61) + 1))) (toChipletAceSymbolicFrame r) =
        Subsystems.ChipletAce.readIdsConsecutive.eval r
  simp [Subsystems.ChipletAce.readIdsConsecutive, Subsystems.ChipletAce.integrityZero,
    Subsystems.ChipletAce.aceFlag, Subsystems.ChipletAce.fRead, Subsystems.ChipletAce.id1,
    Subsystems.ChipletAce.id0, Subsystems.ChipletAce.one, Subsystems.ChipletAce.sblock,
    Subsystems.ChipletAce.id1Col, Subsystems.ChipletAce.id0Col, Subsystems.ChipletAce.sblockCol,
    Subsystems.ChipletAce.aceTraceOffset, Subsystems.ChipletAce.chipletsOffset,
    Subsystems.ChipletSelectors.aceChipletFlag, Subsystems.ChipletSelectors.s012,
    Subsystems.ChipletSelectors.s01, Subsystems.ChipletSelectors.notS3,
    Subsystems.ChipletSelectors.s0, Subsystems.ChipletSelectors.s1,
    Subsystems.ChipletSelectors.s2, Subsystems.ChipletSelectors.s3,
    Subsystems.ChipletSelectors.s0Col, Subsystems.ChipletSelectors.s1Col,
    Subsystems.ChipletSelectors.s2Col, Subsystems.ChipletSelectors.s3Col,
    Subsystems.ChipletSelectors.chipletsOffset, toChipletAceSymbolicFrame_colCurr,
    aceMainCol, FExpr.eval, Builder.gate, Builder.assertZero, BaseConstraint.eval,
    BaseConstraint.expr, AirRow.baseAt, AirRow.base, hMain51, hMain52, hMain53,
    hMain54, hMain56, hMain61, hMain64]
  all_goals ring_nf

theorem bridge_chiplet_ace_12 (r : AirRow) :
    Constraints.Symbolic.ChipletAce.base[12]! (toChipletAceSymbolicFrame r) =
      Subsystems.ChipletAce.readToEvalHandoff.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => (((f.is_transition * (((f.colCurr 51 * f.colCurr 52) *
      f.colCurr 53) * (1 - f.colCurr 54))) * (1 - f.colCurr 56)) *
      ((((1 - f.colNext 56) * f.colNext 67) + (f.colNext 56 * f.colNext 61)) -
        f.colCurr 67))) (toChipletAceSymbolicFrame r) =
          Subsystems.ChipletAce.readToEvalHandoff.eval r
  simp [Subsystems.ChipletAce.readToEvalHandoff, Subsystems.ChipletAce.transitionZero,
    Subsystems.ChipletAce.aceFlag, Subsystems.ChipletAce.fRead,
    Subsystems.ChipletAce.readToEvalSelected, Subsystems.ChipletAce.fReadNext,
    Subsystems.ChipletAce.fEvalNext, Subsystems.ChipletAce.nEvalNext,
    Subsystems.ChipletAce.id0Next, Subsystems.ChipletAce.nEval, Subsystems.ChipletAce.one,
    Subsystems.ChipletAce.sblock, Subsystems.ChipletAce.sblockNext, Subsystems.ChipletAce.nEvalCol,
    Subsystems.ChipletAce.id0Col, Subsystems.ChipletAce.sblockCol,
    Subsystems.ChipletAce.aceTraceOffset, Subsystems.ChipletAce.chipletsOffset,
    Subsystems.ChipletSelectors.aceChipletFlag, Subsystems.ChipletSelectors.s012,
    Subsystems.ChipletSelectors.s01, Subsystems.ChipletSelectors.notS3,
    Subsystems.ChipletSelectors.s0, Subsystems.ChipletSelectors.s1,
    Subsystems.ChipletSelectors.s2, Subsystems.ChipletSelectors.s3,
    Subsystems.ChipletSelectors.s0Col, Subsystems.ChipletSelectors.s1Col,
    Subsystems.ChipletSelectors.s2Col, Subsystems.ChipletSelectors.s3Col,
    Subsystems.ChipletSelectors.chipletsOffset, toChipletAceSymbolicFrame_colCurr,
    toChipletAceSymbolicFrame_colNext, aceMainCol, FExpr.eval, Builder.whenTransition,
    Builder.gate, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.boundary, AirRow.baseAt, AirRow.base, hMain51, hMain52, hMain53, hMain54,
    hMain56, hMain61, hMain67]
  all_goals ring_nf

theorem bridge_chiplet_ace_13 (r : AirRow) :
    Constraints.Symbolic.ChipletAce.base[13]! (toChipletAceSymbolicFrame r) =
      Subsystems.ChipletAce.evalOpRange.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => (((((((f.colCurr 51 * f.colCurr 52) * f.colCurr 53) *
      (1 - f.colCurr 54)) * f.colCurr 56) * f.colCurr 60) *
      (f.colCurr 60 - 1)) * (f.colCurr 60 + 1))) (toChipletAceSymbolicFrame r) =
        Subsystems.ChipletAce.evalOpRange.eval r
  simp [Subsystems.ChipletAce.evalOpRange, Subsystems.ChipletAce.integrityZero,
    Subsystems.ChipletAce.aceFlag, Subsystems.ChipletAce.fEval, Subsystems.ChipletAce.op,
    Subsystems.ChipletAce.one, Subsystems.ChipletAce.sblock, Subsystems.ChipletAce.opCol,
    Subsystems.ChipletAce.sblockCol, Subsystems.ChipletAce.aceTraceOffset,
    Subsystems.ChipletAce.chipletsOffset, Subsystems.ChipletSelectors.aceChipletFlag,
    Subsystems.ChipletSelectors.s012, Subsystems.ChipletSelectors.s01,
    Subsystems.ChipletSelectors.notS3, Subsystems.ChipletSelectors.s0,
    Subsystems.ChipletSelectors.s1, Subsystems.ChipletSelectors.s2,
    Subsystems.ChipletSelectors.s3, Subsystems.ChipletSelectors.s0Col,
    Subsystems.ChipletSelectors.s1Col, Subsystems.ChipletSelectors.s2Col,
    Subsystems.ChipletSelectors.s3Col, Subsystems.ChipletSelectors.chipletsOffset,
    FExpr.eval, Builder.gate,
    Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr, AirRow.baseAt, AirRow.base,
    hMain51, hMain52, hMain53, hMain54, hMain56, hMain60]
  all_goals ring_nf

theorem bridge_chiplet_ace_14 (r : AirRow) :
    Constraints.Symbolic.ChipletAce.base[14]! (toChipletAceSymbolicFrame r) =
      Subsystems.ChipletAce.evalResult0.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => (((((f.colCurr 51 * f.colCurr 52) * f.colCurr 53) *
      (1 - f.colCurr 54)) * f.colCurr 56) *
      ((((f.colCurr 60 * f.colCurr 60) *
          ((f.colCurr 65 + (f.colCurr 68 * f.colCurr 60)) -
            ((f.colCurr 65 * f.colCurr 68) + (Felt.ofNat 7 * (f.colCurr 66 * f.colCurr 69))))) +
        ((f.colCurr 65 * f.colCurr 68) + (Felt.ofNat 7 * (f.colCurr 66 * f.colCurr 69)))) -
        f.colCurr 62))) (toChipletAceSymbolicFrame r) =
          Subsystems.ChipletAce.evalResult0.eval r
  simp [Subsystems.ChipletAce.evalResult0, Subsystems.ChipletAce.integrityEq,
    Subsystems.ChipletAce.aceFlag, Subsystems.ChipletAce.fEval, Subsystems.ChipletAce.expectedEval0,
    Subsystems.ChipletAce.opSquare, Subsystems.ChipletAce.linearExpected0,
    Subsystems.ChipletAce.nonlinearExpected0, Subsystems.ChipletAce.quadMulRe,
    Subsystems.ChipletAce.seven, Subsystems.ChipletAce.op, Subsystems.ChipletAce.v20,
    Subsystems.ChipletAce.v10, Subsystems.ChipletAce.v11, Subsystems.ChipletAce.v21,
    Subsystems.ChipletAce.v00, Subsystems.ChipletAce.one, Subsystems.ChipletAce.sblock,
    Subsystems.ChipletAce.opCol, Subsystems.ChipletAce.v20Col, Subsystems.ChipletAce.v10Col,
    Subsystems.ChipletAce.v11Col, Subsystems.ChipletAce.v21Col, Subsystems.ChipletAce.v00Col,
    Subsystems.ChipletAce.sblockCol, Subsystems.ChipletAce.aceTraceOffset,
    Subsystems.ChipletAce.chipletsOffset, Subsystems.ChipletSelectors.aceChipletFlag,
    Subsystems.ChipletSelectors.s012, Subsystems.ChipletSelectors.s01,
    Subsystems.ChipletSelectors.notS3, Subsystems.ChipletSelectors.s0,
    Subsystems.ChipletSelectors.s1, Subsystems.ChipletSelectors.s2,
    Subsystems.ChipletSelectors.s3, Subsystems.ChipletSelectors.s0Col,
    Subsystems.ChipletSelectors.s1Col, Subsystems.ChipletSelectors.s2Col,
    Subsystems.ChipletSelectors.s3Col, Subsystems.ChipletSelectors.chipletsOffset,
    FExpr.eval, Builder.gate,
    Builder.assertEq, Builder.assertZero, BaseConstraint.eval, BaseConstraint.expr,
    AirRow.baseAt, AirRow.base, hMain51, hMain52, hMain53, hMain54, hMain56,
    hMain60, hMain62, hMain65, hMain66, hMain68, hMain69]
  all_goals ring_nf
  first | trivial | (left; trivial) | (left; left; trivial)

theorem bridge_chiplet_ace_15 (r : AirRow) :
    Constraints.Symbolic.ChipletAce.base[15]! (toChipletAceSymbolicFrame r) =
      Subsystems.ChipletAce.evalResult1.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => (((((f.colCurr 51 * f.colCurr 52) * f.colCurr 53) *
      (1 - f.colCurr 54)) * f.colCurr 56) *
      ((((f.colCurr 60 * f.colCurr 60) *
          ((f.colCurr 66 + (f.colCurr 69 * f.colCurr 60)) -
            ((f.colCurr 65 * f.colCurr 69) + (f.colCurr 66 * f.colCurr 68)))) +
        ((f.colCurr 65 * f.colCurr 69) + (f.colCurr 66 * f.colCurr 68))) -
        f.colCurr 63))) (toChipletAceSymbolicFrame r) =
          Subsystems.ChipletAce.evalResult1.eval r
  simp [Subsystems.ChipletAce.evalResult1, Subsystems.ChipletAce.integrityEq,
    Subsystems.ChipletAce.aceFlag, Subsystems.ChipletAce.fEval, Subsystems.ChipletAce.expectedEval1,
    Subsystems.ChipletAce.opSquare, Subsystems.ChipletAce.linearExpected1,
    Subsystems.ChipletAce.nonlinearExpected1, Subsystems.ChipletAce.quadMulIm,
    Subsystems.ChipletAce.op, Subsystems.ChipletAce.v20, Subsystems.ChipletAce.v11,
    Subsystems.ChipletAce.v10, Subsystems.ChipletAce.v21, Subsystems.ChipletAce.v01,
    Subsystems.ChipletAce.one, Subsystems.ChipletAce.sblock, Subsystems.ChipletAce.opCol,
    Subsystems.ChipletAce.v20Col, Subsystems.ChipletAce.v11Col, Subsystems.ChipletAce.v10Col,
    Subsystems.ChipletAce.v21Col, Subsystems.ChipletAce.v01Col, Subsystems.ChipletAce.sblockCol,
    Subsystems.ChipletAce.aceTraceOffset, Subsystems.ChipletAce.chipletsOffset,
    Subsystems.ChipletSelectors.aceChipletFlag, Subsystems.ChipletSelectors.s012,
    Subsystems.ChipletSelectors.s01, Subsystems.ChipletSelectors.notS3,
    Subsystems.ChipletSelectors.s0, Subsystems.ChipletSelectors.s1,
    Subsystems.ChipletSelectors.s2, Subsystems.ChipletSelectors.s3,
    Subsystems.ChipletSelectors.s0Col, Subsystems.ChipletSelectors.s1Col,
    Subsystems.ChipletSelectors.s2Col, Subsystems.ChipletSelectors.s3Col,
    Subsystems.ChipletSelectors.chipletsOffset, FExpr.eval, Builder.gate, Builder.assertEq,
    Builder.assertZero,
    BaseConstraint.eval, BaseConstraint.expr, AirRow.baseAt, AirRow.base, hMain51,
    hMain52, hMain53, hMain54, hMain56, hMain60, hMain63, hMain65, hMain66,
    hMain68, hMain69]
  all_goals ring_nf
  first | trivial | (left; trivial) | (left; left; trivial)

theorem bridge_chiplet_ace_16 (r : AirRow) :
    Constraints.Symbolic.ChipletAce.base[16]! (toChipletAceSymbolicFrame r) =
      Subsystems.ChipletAce.finalV00Zero.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => ((((((f.colCurr 51 * f.colCurr 52) * f.colCurr 53) *
      (1 - f.colCurr 54)) * f.is_transition) *
      ((((1 - f.colNext 54) * f.colNext 55) + f.colNext 54) -
        (((1 - f.colNext 54) * f.colNext 55) * f.colNext 54))) *
      f.colCurr 62)) (toChipletAceSymbolicFrame r) =
        Subsystems.ChipletAce.finalV00Zero.eval r
  simp [Subsystems.ChipletAce.finalV00Zero, Subsystems.ChipletAce.transitionZero,
    Subsystems.ChipletAce.aceFlag, Subsystems.ChipletAce.fEnd, Subsystems.ChipletAce.binaryOr,
    Subsystems.ChipletAce.flagAceNext, Subsystems.ChipletAce.sstartNext,
    Subsystems.ChipletAce.flagAceLast, Subsystems.ChipletAce.v00, Subsystems.ChipletAce.one,
    Subsystems.ChipletAce.sstartCol, Subsystems.ChipletAce.v00Col,
    Subsystems.ChipletAce.aceTraceOffset, Subsystems.ChipletAce.chipletsOffset,
    Subsystems.ChipletSelectors.aceChipletFlag, Subsystems.ChipletSelectors.s3Next,
    Subsystems.ChipletSelectors.s012, Subsystems.ChipletSelectors.s01,
    Subsystems.ChipletSelectors.notS3, Subsystems.ChipletSelectors.s0,
    Subsystems.ChipletSelectors.s1, Subsystems.ChipletSelectors.s2,
    Subsystems.ChipletSelectors.s3, Subsystems.ChipletSelectors.s0Col,
    Subsystems.ChipletSelectors.s1Col, Subsystems.ChipletSelectors.s2Col,
    Subsystems.ChipletSelectors.s3Col, Subsystems.ChipletSelectors.chipletsOffset,
    toChipletAceSymbolicFrame_colCurr, toChipletAceSymbolicFrame_colNext, aceMainCol,
    FExpr.eval, Builder.whenTransition, Builder.gate, Builder.assertZero,
    BaseConstraint.eval, BaseConstraint.expr, AirRow.boundary, AirRow.baseAt, AirRow.base,
    hMain51, hMain52, hMain53, hMain54, hMain55, hMain62]
  all_goals ring_nf

theorem bridge_chiplet_ace_17 (r : AirRow) :
    Constraints.Symbolic.ChipletAce.base[17]! (toChipletAceSymbolicFrame r) =
      Subsystems.ChipletAce.finalV01Zero.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => ((((((f.colCurr 51 * f.colCurr 52) * f.colCurr 53) *
      (1 - f.colCurr 54)) * f.is_transition) *
      ((((1 - f.colNext 54) * f.colNext 55) + f.colNext 54) -
        (((1 - f.colNext 54) * f.colNext 55) * f.colNext 54))) *
      f.colCurr 63)) (toChipletAceSymbolicFrame r) =
        Subsystems.ChipletAce.finalV01Zero.eval r
  simp [Subsystems.ChipletAce.finalV01Zero, Subsystems.ChipletAce.transitionZero,
    Subsystems.ChipletAce.aceFlag, Subsystems.ChipletAce.fEnd, Subsystems.ChipletAce.binaryOr,
    Subsystems.ChipletAce.flagAceNext, Subsystems.ChipletAce.sstartNext,
    Subsystems.ChipletAce.flagAceLast, Subsystems.ChipletAce.v01, Subsystems.ChipletAce.one,
    Subsystems.ChipletAce.sstartCol, Subsystems.ChipletAce.v01Col,
    Subsystems.ChipletAce.aceTraceOffset, Subsystems.ChipletAce.chipletsOffset,
    Subsystems.ChipletSelectors.aceChipletFlag, Subsystems.ChipletSelectors.s3Next,
    Subsystems.ChipletSelectors.s012, Subsystems.ChipletSelectors.s01,
    Subsystems.ChipletSelectors.notS3, Subsystems.ChipletSelectors.s0,
    Subsystems.ChipletSelectors.s1, Subsystems.ChipletSelectors.s2,
    Subsystems.ChipletSelectors.s3, Subsystems.ChipletSelectors.s0Col,
    Subsystems.ChipletSelectors.s1Col, Subsystems.ChipletSelectors.s2Col,
    Subsystems.ChipletSelectors.s3Col, Subsystems.ChipletSelectors.chipletsOffset,
    toChipletAceSymbolicFrame_colCurr, toChipletAceSymbolicFrame_colNext, aceMainCol,
    FExpr.eval, Builder.whenTransition, Builder.gate, Builder.assertZero,
    BaseConstraint.eval, BaseConstraint.expr, AirRow.boundary, AirRow.baseAt, AirRow.base,
    hMain51, hMain52, hMain53, hMain54, hMain55, hMain63]
  all_goals ring_nf

theorem bridge_chiplet_ace_18 (r : AirRow) :
    Constraints.Symbolic.ChipletAce.base[18]! (toChipletAceSymbolicFrame r) =
      Subsystems.ChipletAce.finalId0Zero.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => ((((((f.colCurr 51 * f.colCurr 52) * f.colCurr 53) *
      (1 - f.colCurr 54)) * f.is_transition) *
      ((((1 - f.colNext 54) * f.colNext 55) + f.colNext 54) -
        (((1 - f.colNext 54) * f.colNext 55) * f.colNext 54))) *
      f.colCurr 61)) (toChipletAceSymbolicFrame r) =
        Subsystems.ChipletAce.finalId0Zero.eval r
  simp [Subsystems.ChipletAce.finalId0Zero, Subsystems.ChipletAce.transitionZero,
    Subsystems.ChipletAce.aceFlag, Subsystems.ChipletAce.fEnd, Subsystems.ChipletAce.binaryOr,
    Subsystems.ChipletAce.flagAceNext, Subsystems.ChipletAce.sstartNext,
    Subsystems.ChipletAce.flagAceLast, Subsystems.ChipletAce.id0, Subsystems.ChipletAce.one,
    Subsystems.ChipletAce.sstartCol, Subsystems.ChipletAce.id0Col,
    Subsystems.ChipletAce.aceTraceOffset, Subsystems.ChipletAce.chipletsOffset,
    Subsystems.ChipletSelectors.aceChipletFlag, Subsystems.ChipletSelectors.s3Next,
    Subsystems.ChipletSelectors.s012, Subsystems.ChipletSelectors.s01,
    Subsystems.ChipletSelectors.notS3, Subsystems.ChipletSelectors.s0,
    Subsystems.ChipletSelectors.s1, Subsystems.ChipletSelectors.s2,
    Subsystems.ChipletSelectors.s3, Subsystems.ChipletSelectors.s0Col,
    Subsystems.ChipletSelectors.s1Col, Subsystems.ChipletSelectors.s2Col,
    Subsystems.ChipletSelectors.s3Col, Subsystems.ChipletSelectors.chipletsOffset,
    toChipletAceSymbolicFrame_colCurr, toChipletAceSymbolicFrame_colNext, aceMainCol,
    FExpr.eval, Builder.whenTransition, Builder.gate, Builder.assertZero,
    BaseConstraint.eval, BaseConstraint.expr, AirRow.boundary, AirRow.baseAt, AirRow.base,
    hMain51, hMain52, hMain53, hMain54, hMain55, hMain61]
  all_goals ring_nf

theorem bridge_chiplet_ace_19 (r : AirRow) :
    Constraints.Symbolic.ChipletAce.base[19]! (toChipletAceSymbolicFrame r) =
      Subsystems.ChipletAce.firstRowStart.eval r := by
  rw [getElem!_pos (h := by native_decide)]
  change (fun f => (((f.is_transition * ((f.colCurr 51 * f.colCurr 52) *
      (1 - f.colCurr 53))) * (f.colNext 53 * (1 - f.colNext 54))) *
      (f.colNext 55 - 1))) (toChipletAceSymbolicFrame r) =
        Subsystems.ChipletAce.firstRowStart.eval r
  simp [Subsystems.ChipletAce.firstRowStart, Subsystems.ChipletAce.transitionEq,
    Subsystems.ChipletAce.flagNextRowFirstAce, Subsystems.ChipletAce.memoryFlag,
    Subsystems.ChipletAce.sstartNext, Subsystems.ChipletAce.one,
    Subsystems.ChipletAce.sstartCol, Subsystems.ChipletAce.aceTraceOffset,
    Subsystems.ChipletAce.chipletsOffset, Subsystems.ChipletSelectors.memoryChipletFlag,
    Subsystems.ChipletSelectors.s01, Subsystems.ChipletSelectors.notS2,
    Subsystems.ChipletSelectors.s2Next, Subsystems.ChipletSelectors.notS3,
    Subsystems.ChipletSelectors.s3Next, Subsystems.ChipletSelectors.s0,
    Subsystems.ChipletSelectors.s1, Subsystems.ChipletSelectors.s2,
    Subsystems.ChipletSelectors.s0Col, Subsystems.ChipletSelectors.s1Col,
    Subsystems.ChipletSelectors.s2Col, Subsystems.ChipletSelectors.s3Col,
    Subsystems.ChipletSelectors.chipletsOffset, toChipletAceSymbolicFrame_colCurr,
    toChipletAceSymbolicFrame_colNext, aceMainCol, FExpr.eval, Builder.whenTransition,
    Builder.gate, Builder.assertEq, Builder.assertZero, BaseConstraint.eval,
    BaseConstraint.expr, AirRow.boundary, AirRow.baseAt, AirRow.base, hMain51,
    hMain52, hMain53, hMain54, hMain55]
  all_goals ring_nf

end MidenLean.AIR.Semantics.Refinement.SymbolicToCanonical
