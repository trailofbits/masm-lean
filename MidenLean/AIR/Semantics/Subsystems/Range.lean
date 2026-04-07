import MidenLean.AIR.Semantics.Check
/-!
# Range AIR Implementation Layer

This file encodes the canonical range-checker main-trace AIR slice backed by
`air/src/constraints/range/mod.rs`.

The trace layout comes from `air/src/trace/range.rs`: the range-checker
multiplicity column `M` is `col 49`, and the checked-value column `V` is
`col 50`. Only `V` participates in these three main-trace constraints; the
range-checker bus constraints belong elsewhere.
-/

namespace MidenLean.AIR.Semantics.Subsystems.Range

open MidenLean
open MidenLean.AIR.Semantics
open MidenLean.AIR.Semantics.Builder
open MidenLean.AIR.Semantics.Check

/-- Range-checker multiplicity column `M` (`col 49`).
It is tracked here for layout fidelity but unused by the main-trace constraints. -/
def rangeMCol : MainCol := ⟨49, by decide⟩

/-- Range-checker value column `V` (`col 50`). -/
def rangeVCol : MainCol := ⟨50, by decide⟩

/-- Current-row range-checker value `v`. -/
def rangeV : FExpr := FExpr.curr rangeVCol

/-- Next-row range-checker value `v'`. -/
def rangeVNext : FExpr := FExpr.next rangeVCol

/-- Canonical range-checker delta `v' - v`. -/
def changeV : FExpr := FExpr.minus rangeVNext rangeV

/-- Canonical AIR boundary constraint `v[0] = 0`. -/
def vFirst : BaseConstraint :=
  gate (FExpr.boundary BoundaryFlag.first) <| assertEq rangeV (FExpr.const 0)

/-- Canonical AIR boundary constraint `v[last] = 65535`. -/
def vLast : BaseConstraint :=
  gate (FExpr.boundary BoundaryFlag.last) <| assertEq rangeV (FExpr.const 65535)

/-- Canonical degree-9 AIR transition constraint for the allowed range-checker
jumps `{0, 1, 3, 9, 27, 81, 243, 729, 2187}`. -/
def vTransition : BaseConstraint :=
  whenTransition <| assertZero <|
    FExpr.times changeV <|
      FExpr.times (FExpr.minus changeV (FExpr.const 1)) <|
        FExpr.times (FExpr.minus changeV (FExpr.const 3)) <|
          FExpr.times (FExpr.minus changeV (FExpr.const 9)) <|
            FExpr.times (FExpr.minus changeV (FExpr.const 27)) <|
              FExpr.times (FExpr.minus changeV (FExpr.const 81)) <|
                FExpr.times (FExpr.minus changeV (FExpr.const 243)) <|
                  FExpr.times (FExpr.minus changeV (FExpr.const 729)) <|
                    (FExpr.minus changeV (FExpr.const 2187))

/-- Canonical range-checker base constraints. -/
def base : BaseConstraintSet := allOf [vFirst, vLast, vTransition]

private def rangeCurr (j : MainCol) : Felt :=
  match j.val with
  | 50 => 100
  | _ => 0

private def goodRangeNext (j : MainCol) : Felt :=
  match j.val with
  | 50 => 101
  | _ => 0

private def badRangeNext (j : MainCol) : Felt :=
  match j.val with
  | 50 => 102
  | _ => 0

private def goodTransitionRow : AirRow := {
  curr := rangeCurr
  next := goodRangeNext
  isTransition := 1
}

private def badTransitionRow : AirRow := {
  curr := rangeCurr
  next := badRangeNext
  isTransition := 1
}

#eval checkBase goodTransitionRow base
#eval checkBase badTransitionRow base

end MidenLean.AIR.Semantics.Subsystems.Range
