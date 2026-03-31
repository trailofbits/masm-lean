import MidenLean.Spec.WordOrder

/-!
# Debug Stack Observer Specification

This module models the `debug.stack` observer boundary only.

It does **not** claim anything about VM execution correctness or AIR soundness.
It specifies how a pre-materialized stack view is projected into debug slots.
-/

namespace MidenLean

/-- One printed debug slot: either a concrete stack value or an explicit `EMPTY`. -/
abbrev DebugSlot := Option Felt

/-- Number of stack items requested by `debug.stack.n`.

Rust source behavior:
- `n = 0` means "show all available stack items".
- `n > 0` means "show exactly `n` slots", with `EMPTY` padding if needed.
-/
def debugStackCount (stack : List Felt) (n : Nat) : Nat :=
  if n = 0 then stack.length else n

/-- Observer slots produced for `debug.stack.n`.

Index `0` corresponds to top-of-stack, preserving stack orientation. -/
def projectDebugSlots : List Felt → Nat → List DebugSlot
  | _, 0 => []
  | [], n + 1 => none :: projectDebugSlots [] n
  | x :: xs, n + 1 => some x :: projectDebugSlots xs n

/-- Observer slots produced for `debug.stack.n`.

Index `0` corresponds to top-of-stack, preserving stack orientation. -/
def debugStackSlots (stack : List Felt) (n : Nat) : List DebugSlot :=
  let count := debugStackCount stack n
  projectDebugSlots stack count

/-- Optional "remaining item count" for partial interval views.

This matches the Rust branch used for headers: only set when fewer items than
stack length are requested. -/
def debugStackRemaining (stack : List Felt) (n : Nat) : Option Nat :=
  let count := debugStackCount stack n
  if count < stack.length then some (stack.length - count) else none

@[simp] theorem debugStackCount_zero (stack : List Felt) :
    debugStackCount stack 0 = stack.length := by
  simp [debugStackCount]

@[simp] theorem debugStackCount_pos (stack : List Felt) {n : Nat} (hn : n ≠ 0) :
    debugStackCount stack n = n := by
  simp [debugStackCount, hn]

/-- Concrete prefix extraction preserves top-to-bottom order. -/
theorem debugStackSlots_prefix4
    (a b c d : Felt) (tail : List Felt) :
    debugStackSlots (a :: b :: c :: d :: tail) 4 =
      [some a, some b, some c, some d] := by
  rfl

/-- Over-requested slots are filled with `EMPTY` (`none`). -/
theorem debugStackSlots_pad_empty
    (a b : Felt) :
    debugStackSlots [a, b] 4 = [some a, some b, none, none] := by
  rfl

/-- Reading exactly the stack length yields all values with no `EMPTY`. -/
theorem projectDebugSlots_all_some (stack : List Felt) :
    projectDebugSlots stack stack.length = stack.map some := by
  induction stack with
  | nil =>
      simp [projectDebugSlots]
  | cons x xs ih =>
      simp [projectDebugSlots, ih]

/-- `debug.stack.0` returns all available stack items with no extra `EMPTY` slots. -/
theorem debugStackSlots_zero_means_all (stack : List Felt) :
    debugStackSlots stack 0 = stack.map some := by
  simp [debugStackSlots, debugStackCount, projectDebugSlots_all_some]

/-- If the stack was already rewritten as a `reversew`-style result, the observer
shows exactly that rewritten order. -/
theorem debugStackSlots_reflects_reversew_style :
    debugStackSlots [4, 3, 2, 1, 5, 6, 7, 8] 8 =
      [some (4 : Felt), some 3, some 2, some 1, some 5, some 6, some 7, some 8] := by
  rfl

/-- If the stack was already rewritten as a `reversedw`-style result, the observer
shows exactly that rewritten order. -/
theorem debugStackSlots_reflects_reversedw_style :
    debugStackSlots [8, 7, 6, 5, 1, 2, 3, 4] 8 =
      [some (8 : Felt), some 7, some 6, some 5, some 1, some 2, some 3, some 4] := by
  rfl

@[simp] theorem debugStackRemaining_partial
    (a b c d : Felt) :
    debugStackRemaining [a, b, c, d] 3 = some 1 := by
  simp [debugStackRemaining, debugStackCount]

@[simp] theorem debugStackRemaining_full
    (a b c d : Felt) :
    debugStackRemaining [a, b, c, d] 0 = none := by
  simp [debugStackRemaining, debugStackCount]

@[simp] theorem debugStackRemaining_overrequest
    (a b c d : Felt) :
    debugStackRemaining [a, b, c, d] 20 = none := by
  simp [debugStackRemaining, debugStackCount]

end MidenLean
