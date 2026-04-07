import MidenLean.AIR.Semantics.Check
/-!
# Public Input AIR Implementation Layer

This file encodes the canonical public-input boundary slice backed by
`air/src/constraints/public_inputs.rs`.

The relevant layout is:

- visible stack `s0..s15`: `cols 30..45`
- public values: `40` entries total
  - `0..3`: program hash
  - `4..19`: stack inputs
  - `20..35`: stack outputs
  - `36..39`: transcript state

Rust reads stack inputs and outputs from the tail of `public_values`, but with
`NUM_PUBLIC_VALUES = 40` this reduces to the fixed offsets above:

- `stack_inputs[i] = public_values[4 + i]`
- `stack_outputs[i] = public_values[20 + i]`

The canonical AIR constraints are the 32 boundary equalities:

- first row: `stack[i] = stack_inputs[i]` for `i ∈ 0..15`
- last row: `stack[i] = stack_outputs[i]` for `i ∈ 0..15`
-/

namespace MidenLean.AIR.Semantics.Subsystems.PublicInputs

open MidenLean
open MidenLean.AIR.Semantics
open MidenLean.AIR.Semantics.Builder
open MidenLean.AIR.Semantics.Check

/-- Number of visible stack slots constrained by the public I/O boundary. -/
abbrev StackDepth : Nat := 16

/-- Typed visible-stack index `0..15`. -/
abbrev StackIndex := Fin StackDepth

/-- First visible-stack column offset (`s0 = col 30`). -/
abbrev stackBase : Nat := 30

/-- First public stack-input offset (`stack_inputs[0] = public_values[4]`). -/
abbrev stackInputBase : Nat := 4

/-- First public stack-output offset (`stack_outputs[0] = public_values[20]`). -/
abbrev stackOutputBase : Nat := 20

/-- Current-row visible-stack column `s[i]` (`cols 30..45`). -/
def stackCol (i : StackIndex) : MainCol := ⟨stackBase + i.val, by
  have hlt : stackBase + i.val < stackBase + StackDepth :=
    Nat.add_lt_add_left i.is_lt stackBase
  exact lt_of_lt_of_le hlt (by decide)
⟩

/-- Public-value column for `stack_inputs[i]` (`cols 4..19`). -/
def stackInputCol (i : StackIndex) : PublicCol := ⟨stackInputBase + i.val, by
  have hlt : stackInputBase + i.val < stackInputBase + StackDepth :=
    Nat.add_lt_add_left i.is_lt stackInputBase
  exact lt_of_lt_of_le hlt (by decide)
⟩

/-- Public-value column for `stack_outputs[i]` (`cols 20..35`). -/
def stackOutputCol (i : StackIndex) : PublicCol := ⟨stackOutputBase + i.val, by
  have hlt : stackOutputBase + i.val < stackOutputBase + StackDepth :=
    Nat.add_lt_add_left i.is_lt stackOutputBase
  exact lt_of_lt_of_le hlt (by decide)
⟩

/-- Current-row visible-stack expression `s[i]`. -/
def stack (i : StackIndex) : FExpr := FExpr.curr (stackCol i)

/-- Public input expression `stack_inputs[i]`. -/
def stackInput (i : StackIndex) : FExpr := FExpr.publicValue (stackInputCol i)

/-- Public output expression `stack_outputs[i]`. -/
def stackOutput (i : StackIndex) : FExpr := FExpr.publicValue (stackOutputCol i)

/-- Canonical AIR boundary constraint `s[i][first] = stack_inputs[i]`. -/
def firstRowConstraint (i : StackIndex) : BaseConstraint :=
  gate (FExpr.boundary BoundaryFlag.first) <| assertEq (stack i) (stackInput i)

/-- Canonical AIR boundary constraint `s[i][last] = stack_outputs[i]`. -/
def lastRowConstraint (i : StackIndex) : BaseConstraint :=
  gate (FExpr.boundary BoundaryFlag.last) <| assertEq (stack i) (stackOutput i)

/-- The 16 first-row stack-input boundary constraints, in stack order. -/
def firstRow : BaseConstraintSet :=
  List.ofFn fun i : StackIndex => firstRowConstraint i

/-- The 16 last-row stack-output boundary constraints, in stack order. -/
def lastRow : BaseConstraintSet :=
  List.ofFn fun i : StackIndex => lastRowConstraint i

/-- Canonical public-input boundary constraints. -/
def base : BaseConstraintSet := allOf (firstRow ++ lastRow)

private def smokeCurr (s0 : Felt) (j : MainCol) : Felt :=
  match j.val with
  | 30 => s0
  | _ => 0

private def smokePublicValues (input0 : Felt) (j : PublicCol) : Felt :=
  match j.val with
  | 4 => input0
  | _ => 0

private def smokeFirstRow (s0 input0 : Felt) : AirRow := {
  curr := smokeCurr s0
  globals := {
    publicValue := smokePublicValues input0
  }
  isFirst := 1
}

#eval checkBase (smokeFirstRow 42 42) base
#eval checkBase (smokeFirstRow 42 99) base

end MidenLean.AIR.Semantics.Subsystems.PublicInputs
