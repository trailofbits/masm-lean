import MidenLean.AIR.Frame
/-!
# Stack Overflow Constraints

Hand-translated from `audit-miden-vm/air/src/constraints/stack/overflow/mod.rs`.

## Boundary constraints
- First row: b0 = 16 (stack starts at depth 16)
- Last row: b0 = 16 (stack returns to depth 16)
- First row: b1 = 0 (no overflow entries initially)
- Last row: b1 = 0 (overflow table empty at end)

## Transition constraints
Stack depth changes based on shift flags (not modeled here — need op flags).
-/

namespace MidenLean.AIR.Constraints.Overflow

open MidenLean MidenLean.AIR

/-- First row: stack depth = 16. -/
def depth_first_row : ConstraintSet := [
  fun f => f.b0 - 16
]

/-- Last row: stack depth = 16. (boundary constraint on last row) -/
def depth_last_row : ConstraintSet := [
  fun f => f.b0 - 16
]

/-- First row: overflow pointer = 0. -/
def overflow_ptr_first_row : ConstraintSet := [
  fun f => f.b1
]

/-- Last row: overflow pointer = 0. -/
def overflow_ptr_last_row : ConstraintSet := [
  fun f => f.b1
]

end MidenLean.AIR.Constraints.Overflow
