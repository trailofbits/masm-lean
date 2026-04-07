import MidenLean.AIR.Semantics.Tactics
import MidenLean.AIR.Semantics.Subsystems.StackGeneral
import MidenLean.AIR.Constraints.Symbolic.StackGeneral

set_option maxHeartbeats 16000000

namespace MidenLean.AIR.Semantics.Refinement.SymbolicToCanonical

open MidenLean
open MidenLean.AIR
open MidenLean.AIR.Semantics
open MidenLean.AIR.Semantics.Tactics
open MidenLean.AIR.Semantics.Builder

private def transitionAt (i : Fin 16) : BaseConstraint :=
  match i.1 with
  | 0 => Subsystems.StackGeneral.transition0 Subsystems.StackGeneral.exactFlags
  | 1 => Subsystems.StackGeneral.transition1 Subsystems.StackGeneral.exactFlags
  | 2 => Subsystems.StackGeneral.transition2 Subsystems.StackGeneral.exactFlags
  | 3 => Subsystems.StackGeneral.transition3 Subsystems.StackGeneral.exactFlags
  | 4 => Subsystems.StackGeneral.transition4 Subsystems.StackGeneral.exactFlags
  | 5 => Subsystems.StackGeneral.transition5 Subsystems.StackGeneral.exactFlags
  | 6 => Subsystems.StackGeneral.transition6 Subsystems.StackGeneral.exactFlags
  | 7 => Subsystems.StackGeneral.transition7 Subsystems.StackGeneral.exactFlags
  | 8 => Subsystems.StackGeneral.transition8 Subsystems.StackGeneral.exactFlags
  | 9 => Subsystems.StackGeneral.transition9 Subsystems.StackGeneral.exactFlags
  | 10 => Subsystems.StackGeneral.transition10 Subsystems.StackGeneral.exactFlags
  | 11 => Subsystems.StackGeneral.transition11 Subsystems.StackGeneral.exactFlags
  | 12 => Subsystems.StackGeneral.transition12 Subsystems.StackGeneral.exactFlags
  | 13 => Subsystems.StackGeneral.transition13 Subsystems.StackGeneral.exactFlags
  | 14 => Subsystems.StackGeneral.transition14 Subsystems.StackGeneral.exactFlags
  | 15 => Subsystems.StackGeneral.transition15 Subsystems.StackGeneral.exactFlags
  | _ => Subsystems.StackGeneral.transition0 Subsystems.StackGeneral.exactFlags

theorem bridge_stack_general_generic (i : Fin 16) (r : AirRow) :
    Constraints.Symbolic.StackGeneral.base[i.1]! (toSymbolicFrame r) =
      (transitionAt i).eval r := by
  sorry

theorem bridge_stack_general_0 (r : AirRow) :
    Constraints.Symbolic.StackGeneral.base[0]! (toSymbolicFrame r) =
      (Subsystems.StackGeneral.transition0 Subsystems.StackGeneral.exactFlags).eval r := by
  simpa [transitionAt] using bridge_stack_general_generic ⟨0, by decide⟩ r

theorem bridge_stack_general_1 (r : AirRow) :
    Constraints.Symbolic.StackGeneral.base[1]! (toSymbolicFrame r) =
      (Subsystems.StackGeneral.transition1 Subsystems.StackGeneral.exactFlags).eval r := by
  simpa [transitionAt] using bridge_stack_general_generic ⟨1, by decide⟩ r

theorem bridge_stack_general_2 (r : AirRow) :
    Constraints.Symbolic.StackGeneral.base[2]! (toSymbolicFrame r) =
      (Subsystems.StackGeneral.transition2 Subsystems.StackGeneral.exactFlags).eval r := by
  simpa [transitionAt] using bridge_stack_general_generic ⟨2, by decide⟩ r

theorem bridge_stack_general_3 (r : AirRow) :
    Constraints.Symbolic.StackGeneral.base[3]! (toSymbolicFrame r) =
      (Subsystems.StackGeneral.transition3 Subsystems.StackGeneral.exactFlags).eval r := by
  simpa [transitionAt] using bridge_stack_general_generic ⟨3, by decide⟩ r

theorem bridge_stack_general_4 (r : AirRow) :
    Constraints.Symbolic.StackGeneral.base[4]! (toSymbolicFrame r) =
      (Subsystems.StackGeneral.transition4 Subsystems.StackGeneral.exactFlags).eval r := by
  simpa [transitionAt] using bridge_stack_general_generic ⟨4, by decide⟩ r

theorem bridge_stack_general_5 (r : AirRow) :
    Constraints.Symbolic.StackGeneral.base[5]! (toSymbolicFrame r) =
      (Subsystems.StackGeneral.transition5 Subsystems.StackGeneral.exactFlags).eval r := by
  simpa [transitionAt] using bridge_stack_general_generic ⟨5, by decide⟩ r

theorem bridge_stack_general_6 (r : AirRow) :
    Constraints.Symbolic.StackGeneral.base[6]! (toSymbolicFrame r) =
      (Subsystems.StackGeneral.transition6 Subsystems.StackGeneral.exactFlags).eval r := by
  simpa [transitionAt] using bridge_stack_general_generic ⟨6, by decide⟩ r

theorem bridge_stack_general_7 (r : AirRow) :
    Constraints.Symbolic.StackGeneral.base[7]! (toSymbolicFrame r) =
      (Subsystems.StackGeneral.transition7 Subsystems.StackGeneral.exactFlags).eval r := by
  simpa [transitionAt] using bridge_stack_general_generic ⟨7, by decide⟩ r

theorem bridge_stack_general_8 (r : AirRow) :
    Constraints.Symbolic.StackGeneral.base[8]! (toSymbolicFrame r) =
      (Subsystems.StackGeneral.transition8 Subsystems.StackGeneral.exactFlags).eval r := by
  simpa [transitionAt] using bridge_stack_general_generic ⟨8, by decide⟩ r

theorem bridge_stack_general_9 (r : AirRow) :
    Constraints.Symbolic.StackGeneral.base[9]! (toSymbolicFrame r) =
      (Subsystems.StackGeneral.transition9 Subsystems.StackGeneral.exactFlags).eval r := by
  simpa [transitionAt] using bridge_stack_general_generic ⟨9, by decide⟩ r

theorem bridge_stack_general_10 (r : AirRow) :
    Constraints.Symbolic.StackGeneral.base[10]! (toSymbolicFrame r) =
      (Subsystems.StackGeneral.transition10 Subsystems.StackGeneral.exactFlags).eval r := by
  simpa [transitionAt] using bridge_stack_general_generic ⟨10, by decide⟩ r

theorem bridge_stack_general_11 (r : AirRow) :
    Constraints.Symbolic.StackGeneral.base[11]! (toSymbolicFrame r) =
      (Subsystems.StackGeneral.transition11 Subsystems.StackGeneral.exactFlags).eval r := by
  simpa [transitionAt] using bridge_stack_general_generic ⟨11, by decide⟩ r

theorem bridge_stack_general_12 (r : AirRow) :
    Constraints.Symbolic.StackGeneral.base[12]! (toSymbolicFrame r) =
      (Subsystems.StackGeneral.transition12 Subsystems.StackGeneral.exactFlags).eval r := by
  simpa [transitionAt] using bridge_stack_general_generic ⟨12, by decide⟩ r

theorem bridge_stack_general_13 (r : AirRow) :
    Constraints.Symbolic.StackGeneral.base[13]! (toSymbolicFrame r) =
      (Subsystems.StackGeneral.transition13 Subsystems.StackGeneral.exactFlags).eval r := by
  simpa [transitionAt] using bridge_stack_general_generic ⟨13, by decide⟩ r

theorem bridge_stack_general_14 (r : AirRow) :
    Constraints.Symbolic.StackGeneral.base[14]! (toSymbolicFrame r) =
      (Subsystems.StackGeneral.transition14 Subsystems.StackGeneral.exactFlags).eval r := by
  simpa [transitionAt] using bridge_stack_general_generic ⟨14, by decide⟩ r

theorem bridge_stack_general_15 (r : AirRow) :
    Constraints.Symbolic.StackGeneral.base[15]! (toSymbolicFrame r) =
      (Subsystems.StackGeneral.transition15 Subsystems.StackGeneral.exactFlags).eval r := by
  simpa [transitionAt] using bridge_stack_general_generic ⟨15, by decide⟩ r

end MidenLean.AIR.Semantics.Refinement.SymbolicToCanonical
