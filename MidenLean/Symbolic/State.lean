import MidenLean.Symbolic.Expr

/-!
# Symbolic State (Phase 5)

Symbolic state tracking stack, memory, local frames, and advice as
symbolic expressions. The `models` relation ties each symbolic component
to its concrete counterpart under an assignment.
-/

namespace MidenLean.Symbolic

/-- Symbolic state tracking the stack, memory, frames, and advice. -/
structure State where
  stack : List Expr
  memory : Nat → Expr := fun _ => .lit 0
  frames : List LocalFrame := []
  advice : List Expr := []
  -- Note: Repr not derived due to function-typed `memory` field.

/-- The symbolic state models the concrete state when every component agrees
    under the assignment `σ`. The concrete stack may have additional elements
    (`rest`) below the symbolic portion. -/
def State.models (ss : State) (cs : Concrete.State) (σ : Assignment)
    (rest : List Felt) : Prop :=
  cs.stack = ss.stack.map (Expr.eval σ) ++ rest ∧
  (∀ addr, cs.memory addr = (ss.memory addr).eval σ) ∧
  cs.frames = ss.frames ∧
  cs.advice = ss.advice.map (Expr.eval σ)

/-- Construct initial symbolic state for `n` input variables. -/
def State.ofInputs (n : Nat) : State :=
  { stack := (List.range n).map Expr.var
    memory := fun _ => .lit 0
    frames := []
    advice := [] }

/-- Construct initial symbolic state for `n` input variables and an advice
    list. -/
def State.ofInputsWithAdvice (n : Nat) (adv : List Expr) : State :=
  { stack := (List.range n).map Expr.var
    memory := fun _ => .lit 0
    frames := []
    advice := adv }

/-- Construct initial symbolic state for `n` input variables and a list of
    local frames. -/
def State.ofInputsWithFrames (n : Nat) (fr : List LocalFrame) : State :=
  { stack := (List.range n).map Expr.var
    memory := fun _ => .lit 0
    frames := fr
    advice := [] }

end MidenLean.Symbolic
