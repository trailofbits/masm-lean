import MidenLean.AIR.Semantics.Check
/-!
# Chiplet Selector AIR Implementation Layer

This file encodes the canonical chiplet-selector main-trace AIR slice backed by
`air/src/constraints/chiplets/selectors.rs`.

The chiplet trace begins at `CHIPLETS_OFFSET = 51`, so the top-level selector
columns are:

- `s0`: `col 51`
- `s1`: `col 52`
- `s2`: `col 53`
- `s3`: `col 54`
- `s4`: `col 55`

These selectors lay out chiplets in monotone order:

- hasher: `!s0`
- bitwise: `s0 * !s1`
- memory: `s0 * s1 * !s2`
- ACE: `s0 * s1 * s2 * !s3`
- kernel ROM: `s0 * s1 * s2 * s3 * !s4`

The Rust AIR enforces exactly two families of constraints:

1. hierarchical binary constraints for each selector bit;
2. transition stability constraints, which forbid `1 -> 0` regressions once a
   selector's prefix is active.
-/

namespace MidenLean.AIR.Semantics.Subsystems.ChipletSelectors

open MidenLean
open MidenLean.AIR.Semantics
open MidenLean.AIR.Semantics.Builder
open MidenLean.AIR.Semantics.Check

/-- Chiplet trace offset `CHIPLETS_OFFSET = 51`. -/
def chipletsOffset : Nat := 51

/-- Current-row chiplet selector `s0` (`col 51`). -/
def s0Col : MainCol := ⟨chipletsOffset, by decide⟩
/-- Current-row chiplet selector `s1` (`col 52`). -/
def s1Col : MainCol := ⟨chipletsOffset + 1, by decide⟩
/-- Current-row chiplet selector `s2` (`col 53`). -/
def s2Col : MainCol := ⟨chipletsOffset + 2, by decide⟩
/-- Current-row chiplet selector `s3` (`col 54`). -/
def s3Col : MainCol := ⟨chipletsOffset + 3, by decide⟩
/-- Current-row chiplet selector `s4` (`col 55`). -/
def s4Col : MainCol := ⟨chipletsOffset + 4, by decide⟩

/-- Current-row selector expression `s0`. -/
def s0 : FExpr := FExpr.curr s0Col
/-- Current-row selector expression `s1`. -/
def s1 : FExpr := FExpr.curr s1Col
/-- Current-row selector expression `s2`. -/
def s2 : FExpr := FExpr.curr s2Col
/-- Current-row selector expression `s3`. -/
def s3 : FExpr := FExpr.curr s3Col
/-- Current-row selector expression `s4`. -/
def s4 : FExpr := FExpr.curr s4Col

/-- Next-row selector expression `s0'`. -/
def s0Next : FExpr := FExpr.next s0Col
/-- Next-row selector expression `s1'`. -/
def s1Next : FExpr := FExpr.next s1Col
/-- Next-row selector expression `s2'`. -/
def s2Next : FExpr := FExpr.next s2Col
/-- Next-row selector expression `s3'`. -/
def s3Next : FExpr := FExpr.next s3Col
/-- Next-row selector expression `s4'`. -/
def s4Next : FExpr := FExpr.next s4Col

/-- Complement expression `1 - s0`. -/
def notS0 : FExpr := FExpr.minus (FExpr.const 1) s0
/-- Complement expression `1 - s1`. -/
def notS1 : FExpr := FExpr.minus (FExpr.const 1) s1
/-- Complement expression `1 - s2`. -/
def notS2 : FExpr := FExpr.minus (FExpr.const 1) s2
/-- Complement expression `1 - s3`. -/
def notS3 : FExpr := FExpr.minus (FExpr.const 1) s3
/-- Complement expression `1 - s4`. -/
def notS4 : FExpr := FExpr.minus (FExpr.const 1) s4

/-- Shared prefix `s0 * s1`. -/
def s01 : FExpr := FExpr.times s0 s1

/-- Shared prefix `s0 * s1 * s2`. -/
def s012 : FExpr := FExpr.times s01 s2

/-- Shared prefix `s0 * s1 * s2 * s3`. -/
def s0123 : FExpr := FExpr.times s012 s3

/-- Shared prefix `s0 * s1 * s2 * s3 * s4`. -/
def s01234 : FExpr := FExpr.times s0123 s4

/-- Current-row hasher chiplet active flag `!s0`. -/
def hasherChipletFlag : FExpr := notS0

/-- Current-row bitwise chiplet active flag `s0 * !s1`. -/
def bitwiseChipletFlag : FExpr := FExpr.times s0 notS1

/-- Current-row memory chiplet active flag `s0 * s1 * !s2`. -/
def memoryChipletFlag : FExpr := FExpr.times s01 notS2

/-- Current-row ACE chiplet active flag `s0 * s1 * s2 * !s3`. -/
def aceChipletFlag : FExpr := FExpr.times s012 notS3

/-- Current-row kernel ROM chiplet active flag `s0 * s1 * s2 * s3 * !s4`. -/
def kernelRomChipletFlag : FExpr := FExpr.times s0123 notS4

/-- Canonical AIR binary constraint for `s0`. -/
def s0Binary : BaseConstraint :=
  assertZero <| FExpr.times s0 (FExpr.minus s0 (FExpr.const 1))

/-- Canonical AIR binary constraint for `s1`, gated by `s0`. -/
def s1Binary : BaseConstraint :=
  gate s0 <| assertZero <| FExpr.times s1 (FExpr.minus s1 (FExpr.const 1))

/-- Canonical AIR binary constraint for `s2`, gated by `s0 * s1`. -/
def s2Binary : BaseConstraint :=
  gate s01 <| assertZero <| FExpr.times s2 (FExpr.minus s2 (FExpr.const 1))

/-- Canonical AIR binary constraint for `s3`, gated by `s0 * s1 * s2`. -/
def s3Binary : BaseConstraint :=
  gate s012 <| assertZero <| FExpr.times s3 (FExpr.minus s3 (FExpr.const 1))

/-- Canonical AIR binary constraint for `s4`, gated by `s0 * s1 * s2 * s3`. -/
def s4Binary : BaseConstraint :=
  gate s0123 <| assertZero <| FExpr.times s4 (FExpr.minus s4 (FExpr.const 1))

/-- Canonical AIR stability constraint for `s0`. -/
def s0Stability : BaseConstraint :=
  whenTransition <| gate s0 <| assertEq s0Next s0

/-- Canonical AIR stability constraint for `s1`, gated by `s0 * s1`. -/
def s1Stability : BaseConstraint :=
  whenTransition <| gate s01 <| assertEq s1Next s1

/-- Canonical AIR stability constraint for `s2`, gated by `s0 * s1 * s2`. -/
def s2Stability : BaseConstraint :=
  whenTransition <| gate s012 <| assertEq s2Next s2

/-- Canonical AIR stability constraint for `s3`, gated by `s0 * s1 * s2 * s3`. -/
def s3Stability : BaseConstraint :=
  whenTransition <| gate s0123 <| assertEq s3Next s3

/-- Canonical AIR stability constraint for `s4`, gated by `s0 * s1 * s2 * s3 * s4`. -/
def s4Stability : BaseConstraint :=
  whenTransition <| gate s01234 <| assertEq s4Next s4

/-- Canonical chiplet-selector base constraints in Rust assertion order. -/
def base : BaseConstraintSet := allOf
  [s0Binary, s1Binary, s2Binary, s3Binary, s4Binary,
   s0Stability, s1Stability, s2Stability, s3Stability, s4Stability]

private def selectorCols
    (s0Val s1Val s2Val s3Val s4Val : Felt)
    (j : MainCol) : Felt :=
  match j.val with
  | 51 => s0Val
  | 52 => s1Val
  | 53 => s2Val
  | 54 => s3Val
  | 55 => s4Val
  | _ => 0

private def selectorRow
    (currS0 currS1 currS2 currS3 currS4
     nextS0 nextS1 nextS2 nextS3 nextS4
     isTransition : Felt) : AirRow := {
  curr := selectorCols currS0 currS1 currS2 currS3 currS4
  next := selectorCols nextS0 nextS1 nextS2 nextS3 nextS4
  isTransition := isTransition
}

private def goodMemoryToAceRow : AirRow :=
  selectorRow 1 1 0 0 0 1 1 1 0 0 1

private def badBitwiseToHasherRow : AirRow :=
  selectorRow 1 0 0 0 0 0 0 0 0 0 1

private def badS1BinaryRow : AirRow :=
  selectorRow 1 2 0 0 0 1 2 0 0 0 1

private def badKernelRomRegressionRow : AirRow :=
  selectorRow 1 1 1 1 1 1 1 1 1 0 1

#eval checkBase goodMemoryToAceRow base
#eval checkBase badBitwiseToHasherRow base
#eval checkBase badS1BinaryRow base
#eval checkBase badKernelRomRegressionRow base

end MidenLean.AIR.Semantics.Subsystems.ChipletSelectors
