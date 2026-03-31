import MidenLean.AIR.Semantics.Check
import MidenLean.AIR.Semantics.Spec.StackArith
/-!
# StackArith Spec/Implementation Gaps

This file records concrete rows accepted by the current Rust-facing
implementation AIR but rejected by the intended mathematical spec.

The first such gaps are:

- the high output of `U32ADD` / `U32ADD3`, where the current
  implementation layer accepts `s1' = h3 * 2^16 + h2`, while the intended spec
  requires both the visible high output to be the carry `h2` and the extra
  helper limb `h3` to be zero.
- the helper limbs of `U32SUB`, where the current implementation layer leaves
  `h2` and `h3` unconstrained but the intended spec requires both to be zero.
-/

namespace MidenLean.AIR.Semantics.Gaps.StackArith

open MidenLean
open MidenLean.AIR.Semantics
open MidenLean.AIR.Semantics.Check

/-- Counterexample row for `U32ADD`: the current implementation AIR accepts
`(s0, s1) = (0, 0)` with `h3 = 1`, `h0 = h1 = h2 = 0`, and `s1' = 65536`.
The intended spec rejects it because the visible high output is not the
documented carry and because the extra helper limb is not zero. -/
def u32AddCarryGapRow : AirRow := {
  curr := fun j =>
    match j.val with
    | 13 => 1  -- b6
    | 19 => 1  -- h3
    | _ => 0
  next := fun j =>
    match j.val with
    | 31 => 65536
    | _ => 0
  isTransition := 1
}

/-- Counterexample row for `U32ADD3`: the current implementation AIR accepts
`(s0, s1, s2) = (0, 0, 0)` with `h3 = 1`, `h0 = h1 = h2 = 0`, and
`s1' = 65536`. The intended spec rejects it for the same two reasons as the
`U32ADD` row above. -/
def u32Add3CarryGapRow : AirRow := {
  curr := fun j =>
    match j.val with
    | 13 => 1  -- b6
    | 10 => 1  -- b3
    | 9 => 1   -- b2
    | 19 => 1  -- h3
    | _ => 0
  next := fun j =>
    match j.val with
    | 31 => 65536
    | _ => 0
  isTransition := 1
}

theorem u32Add_impl_accepts_gap_row :
    checkBase u32AddCarryGapRow
      [MidenLean.AIR.Semantics.Subsystems.StackArith.u32TwoOutputsLo,
       MidenLean.AIR.Semantics.Subsystems.StackArith.u32TwoOutputsHi,
       MidenLean.AIR.Semantics.Subsystems.StackArith.u32AddInput] = true := by
  native_decide

theorem u32Add_spec_rejects_gap_row :
    checkBase u32AddCarryGapRow MidenLean.AIR.Semantics.Spec.StackArith.u32Add = false := by
  native_decide

theorem u32Add_impl_satisfies_gap_row :
    satisfiesBase u32AddCarryGapRow
      [MidenLean.AIR.Semantics.Subsystems.StackArith.u32TwoOutputsLo,
       MidenLean.AIR.Semantics.Subsystems.StackArith.u32TwoOutputsHi,
       MidenLean.AIR.Semantics.Subsystems.StackArith.u32AddInput] := by
  exact (checkBase_eq_true_iff_satisfiesBase _ _).mp u32Add_impl_accepts_gap_row

theorem u32Add_not_satisfies_spec_gap_row :
    ¬ satisfiesBase u32AddCarryGapRow MidenLean.AIR.Semantics.Spec.StackArith.u32Add := by
  intro hspec
  have hcheck :
      checkBase u32AddCarryGapRow MidenLean.AIR.Semantics.Spec.StackArith.u32Add = true :=
    (checkBase_eq_true_iff_satisfiesBase _ _).mpr hspec
  simp [u32Add_spec_rejects_gap_row] at hcheck

theorem u32Add3_impl_accepts_gap_row :
    checkBase u32Add3CarryGapRow
      [MidenLean.AIR.Semantics.Subsystems.StackArith.u32TwoOutputsLo,
       MidenLean.AIR.Semantics.Subsystems.StackArith.u32TwoOutputsHi,
       MidenLean.AIR.Semantics.Subsystems.StackArith.u32Add3Input] = true := by
  native_decide

theorem u32Add3_spec_rejects_gap_row :
    checkBase u32Add3CarryGapRow MidenLean.AIR.Semantics.Spec.StackArith.u32Add3 = false := by
  native_decide

theorem u32Add3_impl_satisfies_gap_row :
    satisfiesBase u32Add3CarryGapRow
      [MidenLean.AIR.Semantics.Subsystems.StackArith.u32TwoOutputsLo,
       MidenLean.AIR.Semantics.Subsystems.StackArith.u32TwoOutputsHi,
       MidenLean.AIR.Semantics.Subsystems.StackArith.u32Add3Input] := by
  exact (checkBase_eq_true_iff_satisfiesBase _ _).mp u32Add3_impl_accepts_gap_row

theorem u32Add3_not_satisfies_spec_gap_row :
    ¬ satisfiesBase u32Add3CarryGapRow MidenLean.AIR.Semantics.Spec.StackArith.u32Add3 := by
  intro hspec
  have hcheck :
      checkBase u32Add3CarryGapRow MidenLean.AIR.Semantics.Spec.StackArith.u32Add3 = true :=
    (checkBase_eq_true_iff_satisfiesBase _ _).mpr hspec
  simp [u32Add3_spec_rejects_gap_row] at hcheck

/-- Counterexample row for `U32SUB`: the current implementation AIR accepts
the visible subtraction relation with `h2 = 1`, even though the docs require
`h2 = h3 = 0` for this operation. -/
def u32SubHelperGapRow : AirRow := {
  curr := fun j =>
    match j.val with
    | 8 => 1   -- b1
    | 13 => 1  -- b6
    | 16 => 4  -- h0
    | 18 => 1  -- h2
    | 30 => 5  -- s0
    | 31 => 9  -- s1
    | _ => 0
  next := fun j =>
    match j.val with
    | 30 => 0  -- borrow
    | 31 => 4  -- diff
    | _ => 0
  isTransition := 1
}

theorem u32Sub_impl_accepts_gap_row :
    checkBase u32SubHelperGapRow
      [MidenLean.AIR.Semantics.Subsystems.StackArith.u32SubDiff,
       MidenLean.AIR.Semantics.Subsystems.StackArith.u32SubBorrowBinary,
       MidenLean.AIR.Semantics.Subsystems.StackArith.u32SubLow] = true := by
  native_decide

theorem u32Sub_spec_rejects_gap_row :
    checkBase u32SubHelperGapRow MidenLean.AIR.Semantics.Spec.StackArith.u32Sub = false := by
  native_decide

theorem u32Sub_impl_satisfies_gap_row :
    satisfiesBase u32SubHelperGapRow
      [MidenLean.AIR.Semantics.Subsystems.StackArith.u32SubDiff,
       MidenLean.AIR.Semantics.Subsystems.StackArith.u32SubBorrowBinary,
       MidenLean.AIR.Semantics.Subsystems.StackArith.u32SubLow] := by
  exact (checkBase_eq_true_iff_satisfiesBase _ _).mp u32Sub_impl_accepts_gap_row

theorem u32Sub_not_satisfies_spec_gap_row :
    ¬ satisfiesBase u32SubHelperGapRow MidenLean.AIR.Semantics.Spec.StackArith.u32Sub := by
  intro hspec
  have hcheck :
      checkBase u32SubHelperGapRow MidenLean.AIR.Semantics.Spec.StackArith.u32Sub = true :=
    (checkBase_eq_true_iff_satisfiesBase _ _).mpr hspec
  simp [u32Sub_spec_rejects_gap_row] at hcheck

#eval checkBase u32AddCarryGapRow
  [MidenLean.AIR.Semantics.Subsystems.StackArith.u32TwoOutputsLo,
   MidenLean.AIR.Semantics.Subsystems.StackArith.u32TwoOutputsHi,
   MidenLean.AIR.Semantics.Subsystems.StackArith.u32AddInput]
#eval checkBase u32AddCarryGapRow MidenLean.AIR.Semantics.Spec.StackArith.u32Add
#eval checkBase u32Add3CarryGapRow
  [MidenLean.AIR.Semantics.Subsystems.StackArith.u32TwoOutputsLo,
   MidenLean.AIR.Semantics.Subsystems.StackArith.u32TwoOutputsHi,
   MidenLean.AIR.Semantics.Subsystems.StackArith.u32Add3Input]
#eval checkBase u32Add3CarryGapRow MidenLean.AIR.Semantics.Spec.StackArith.u32Add3
#eval checkBase u32SubHelperGapRow
  [MidenLean.AIR.Semantics.Subsystems.StackArith.u32SubDiff,
   MidenLean.AIR.Semantics.Subsystems.StackArith.u32SubBorrowBinary,
   MidenLean.AIR.Semantics.Subsystems.StackArith.u32SubLow]
#eval checkBase u32SubHelperGapRow MidenLean.AIR.Semantics.Spec.StackArith.u32Sub

end MidenLean.AIR.Semantics.Gaps.StackArith
