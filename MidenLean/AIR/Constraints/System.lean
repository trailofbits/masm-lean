import MidenLean.AIR.Frame
/-!
# System AIR Constraints

Hand-translated from `audit-miden-vm/air/src/constraints/system/mod.rs`.
System constraints enforce clock, context, and function hash transitions.

Note: op flags (is_call, is_syscall, etc.) are not modeled in Frame.
We express constraints in terms of the columns that ARE modeled (clk, ctx)
and leave flag-gated constraints parametric on the flag values.
-/

namespace MidenLean.AIR.Constraints.System

open MidenLean MidenLean.AIR

/-- Clock first row: clk[0] = 0. (boundary constraint) -/
def clk_first_row : ConstraintSet := [
  fun f => f.clk
]

/-- Clock transition: clk' = clk + 1. (transition constraint) -/
def clk_transition : ConstraintSet := [
  fun f => f.clk' - (f.clk + 1)
]

end MidenLean.AIR.Constraints.System
