import MidenLean.AIR.Semantics.Tactics
import MidenLean.AIR.Semantics.Subsystems.PublicInputs
import MidenLean.AIR.Constraints.Symbolic.PublicInputs

set_option maxHeartbeats 16000000

namespace MidenLean.AIR.Semantics.Refinement.SymbolicToCanonical

open MidenLean
open MidenLean.AIR
open MidenLean.AIR.Semantics
open MidenLean.AIR.Semantics.Tactics
open Lean Parser Elab Command

syntax (name := mkFirstPublicInputsBridge)
  "mkFirstPublicInputsBridge " ident num num num num : command

macro_rules
  | `(mkFirstPublicInputsBridge $name:ident $n:num $i:num $pub:num $main:num) =>
      `(theorem $name (r : AirRow) :
          Constraints.Symbolic.PublicInputs.base[$n]! (toSymbolicFrame r) =
            (Subsystems.PublicInputs.firstRowConstraint ⟨$i, by decide⟩).eval r := by
        rw [Constraints.Symbolic.PublicInputs.base]
        rw [getElem!_pos (h := by native_decide)]
        change (fun f => f.is_first_row * (f.s $i - f.publicValue $pub)) (toSymbolicFrame r) =
          r.isFirst * (r.curr ⟨$main, by decide⟩ - r.globals.publicValue ⟨$pub, by decide⟩)
        have hRing :
            r.isFirst * (r.curr ⟨$main, by decide⟩ - r.globals.publicValue ⟨$pub, by decide⟩) =
              r.isFirst * r.curr ⟨$main, by decide⟩ -
                r.isFirst * r.globals.publicValue ⟨$pub, by decide⟩ := by
          ring
        rw [hRing]
        simp [SymbolicFrame.s, toSymbolicFrame,
          show $main < MainWidth by decide,
          show $pub < PublicWidth by decide]
        ring)

syntax (name := mkLastPublicInputsBridge)
  "mkLastPublicInputsBridge " ident num num num num : command

macro_rules
  | `(mkLastPublicInputsBridge $name:ident $n:num $i:num $pub:num $main:num) =>
      `(theorem $name (r : AirRow) :
          Constraints.Symbolic.PublicInputs.base[$n]! (toSymbolicFrame r) =
            (Subsystems.PublicInputs.lastRowConstraint ⟨$i, by decide⟩).eval r := by
        rw [Constraints.Symbolic.PublicInputs.base]
        rw [getElem!_pos (h := by native_decide)]
        change (fun f => f.is_last_row * (f.s $i - f.publicValue $pub)) (toSymbolicFrame r) =
          r.isLast * (r.curr ⟨$main, by decide⟩ - r.globals.publicValue ⟨$pub, by decide⟩)
        have hRing :
            r.isLast * (r.curr ⟨$main, by decide⟩ - r.globals.publicValue ⟨$pub, by decide⟩) =
              r.isLast * r.curr ⟨$main, by decide⟩ -
                r.isLast * r.globals.publicValue ⟨$pub, by decide⟩ := by
          ring
        rw [hRing]
        simp [SymbolicFrame.s, toSymbolicFrame,
          show $main < MainWidth by decide,
          show $pub < PublicWidth by decide]
        ring)

mkFirstPublicInputsBridge bridge_public_inputs_0 0 0 4 30
mkFirstPublicInputsBridge bridge_public_inputs_1 1 1 5 31
mkFirstPublicInputsBridge bridge_public_inputs_2 2 2 6 32
mkFirstPublicInputsBridge bridge_public_inputs_3 3 3 7 33
mkFirstPublicInputsBridge bridge_public_inputs_4 4 4 8 34
mkFirstPublicInputsBridge bridge_public_inputs_5 5 5 9 35
mkFirstPublicInputsBridge bridge_public_inputs_6 6 6 10 36
mkFirstPublicInputsBridge bridge_public_inputs_7 7 7 11 37
mkFirstPublicInputsBridge bridge_public_inputs_8 8 8 12 38
mkFirstPublicInputsBridge bridge_public_inputs_9 9 9 13 39
mkFirstPublicInputsBridge bridge_public_inputs_10 10 10 14 40
mkFirstPublicInputsBridge bridge_public_inputs_11 11 11 15 41
mkFirstPublicInputsBridge bridge_public_inputs_12 12 12 16 42
mkFirstPublicInputsBridge bridge_public_inputs_13 13 13 17 43
mkFirstPublicInputsBridge bridge_public_inputs_14 14 14 18 44
mkFirstPublicInputsBridge bridge_public_inputs_15 15 15 19 45

mkLastPublicInputsBridge bridge_public_inputs_16 16 0 20 30
mkLastPublicInputsBridge bridge_public_inputs_17 17 1 21 31
mkLastPublicInputsBridge bridge_public_inputs_18 18 2 22 32
mkLastPublicInputsBridge bridge_public_inputs_19 19 3 23 33
mkLastPublicInputsBridge bridge_public_inputs_20 20 4 24 34
mkLastPublicInputsBridge bridge_public_inputs_21 21 5 25 35
mkLastPublicInputsBridge bridge_public_inputs_22 22 6 26 36
mkLastPublicInputsBridge bridge_public_inputs_23 23 7 27 37
mkLastPublicInputsBridge bridge_public_inputs_24 24 8 28 38
mkLastPublicInputsBridge bridge_public_inputs_25 25 9 29 39
mkLastPublicInputsBridge bridge_public_inputs_26 26 10 30 40
mkLastPublicInputsBridge bridge_public_inputs_27 27 11 31 41
mkLastPublicInputsBridge bridge_public_inputs_28 28 12 32 42
mkLastPublicInputsBridge bridge_public_inputs_29 29 13 33 43
mkLastPublicInputsBridge bridge_public_inputs_30 30 14 34 44
mkLastPublicInputsBridge bridge_public_inputs_31 31 15 35 45

end MidenLean.AIR.Semantics.Refinement.SymbolicToCanonical
