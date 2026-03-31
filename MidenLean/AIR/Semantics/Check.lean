import Mathlib.Data.List.Basic
import MidenLean.AIR.Semantics.Builder
/-!
# Canonical AIR Satisfaction Layer

Step 5 wires up the executable semantics: a row is accepted iff every
canonical constraint evaluates to zero. This layer still stops short of
subsystem logic, symbolic bridges, or whole-VM witnesses.
-/

namespace MidenLean.AIR.Semantics.Check

open MidenLean
open MidenLean.AIR.Semantics
open MidenLean.AIR.Semantics.Builder

@[simp]
theorem quadFelt_check_zero_eq_true_iff (q : QuadFelt) :
    QuadFelt.check_zero q = true ↔ q = 0 := by
  constructor
  · intro h
    cases q with
    | mk re im =>
        simp [QuadFelt.check_zero, Bool.and_eq_true, beq_iff_eq] at h
        rcases h with ⟨rfl, rfl⟩
        rfl
  · intro h
    cases h
    simp [QuadFelt.check_zero]

/-- A row satisfies the base-field constraints when each constraint evaluates to zero. -/
def satisfiesBase (r : AirRow) (cs : BaseConstraintSet) : Prop :=
  ∀ c ∈ cs, c.eval r = 0

/-- Boolean check for base-field constraints. -/
def checkBase (r : AirRow) (cs : BaseConstraintSet) : Bool :=
  cs.all fun c => c.eval r == 0

/-- A row satisfies the extension-field constraints when each evaluates to zero. -/
def satisfiesExt (r : AirRow) (cs : ExtConstraintSet) : Prop :=
  ∀ c ∈ cs, c.eval r = 0

/-- Boolean check for extension-field constraints. -/
def checkExt (r : AirRow) (cs : ExtConstraintSet) : Bool :=
  cs.all fun c => QuadFelt.check_zero (c.eval r)

theorem checkBase_eq_true_iff_satisfiesBase (r : AirRow) (cs : BaseConstraintSet) :
    checkBase r cs = true ↔ satisfiesBase r cs := by
  simp [checkBase, satisfiesBase, List.all_eq_true, beq_iff_eq]

theorem checkBase_sound (r : AirRow) (cs : BaseConstraintSet) :
    checkBase r cs = true → satisfiesBase r cs :=
  checkBase_eq_true_iff_satisfiesBase r cs |>.mp

theorem checkBase_complete (r : AirRow) (cs : BaseConstraintSet) :
    satisfiesBase r cs → checkBase r cs = true :=
  checkBase_eq_true_iff_satisfiesBase r cs |>.mpr

theorem checkExt_eq_true_iff_satisfiesExt (r : AirRow) (cs : ExtConstraintSet) :
    checkExt r cs = true ↔ satisfiesExt r cs := by
  simp [checkExt, satisfiesExt, List.all_eq_true, quadFelt_check_zero_eq_true_iff]

theorem checkExt_sound (r : AirRow) (cs : ExtConstraintSet) :
    checkExt r cs = true → satisfiesExt r cs :=
  checkExt_eq_true_iff_satisfiesExt r cs |>.mp

theorem checkExt_complete (r : AirRow) (cs : ExtConstraintSet) :
    satisfiesExt r cs → checkExt r cs = true :=
  checkExt_eq_true_iff_satisfiesExt r cs |>.mpr

private def smokeRow : AirRow := {}

#eval checkBase smokeRow [assertZero (FExpr.const 0)]
#eval checkBase smokeRow [assertZero (FExpr.const 1)]
#eval checkExt smokeRow [assertZeroExt (QExpr.const 0)]
#eval checkExt smokeRow [assertZeroExt (QExpr.const (QuadFelt.ofFelt 1))]

end MidenLean.AIR.Semantics.Check
