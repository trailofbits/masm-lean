import MidenLean.Symbolic.Expr

/-!
# Symbolic State (Phase 2 Spike)

Symbolic state tracking stack contents as symbolic expressions.
Phase 5 adds memory, frames, and advice.
-/

namespace MidenLean.Symbolic

/-- Symbolic state tracking the stack as a list of expressions. -/
structure State where
  stack : List Expr
  deriving Repr, BEq

/-- The symbolic stack models the top of the concrete stack.
    The concrete stack may have additional elements (`rest`) below. -/
def State.models (ss : State) (cs : MidenState) (σ : Assignment)
    (rest : List Felt) : Prop :=
  cs.stack = ss.stack.map (Expr.eval σ) ++ rest

/-- Construct initial symbolic state for n input variables. -/
def State.ofInputs (n : Nat) : State :=
  { stack := (List.range n).map Expr.var }

end MidenLean.Symbolic
