import MidenLean.AIR.ExtField
/-!
# Symbolic AIR Frame

This is the Lean target for the symbolic extractor in
`masm-lean/masm-to-lean/src/symbolic.rs`.

Unlike `Frame` and `TraceFrame`, this model follows the `p3_air`
`SymbolicAirBuilder` interface directly:

- `curr` / `next` are raw main-trace columns indexed by `Nat`
- `auxCurr` / `auxNext` are raw extension-field permutation columns
- `challenge` / `permValue` are verifier inputs emitted by the permutation bus
- `is_first_row` / `is_last_row` / `is_transition` are the synthetic selector
  leaves produced by the symbolic builder

The named accessors below are grounded in the Rust `MainTraceRow` layout:

- system: `clk = 0`, `ctx = 1`
- decoder helpers: `16 .. 21`
- visible stack: `30 .. 45`
- stack depth / overflow address / overflow helper: `46 .. 48`
-/

namespace MidenLean.AIR

open MidenLean

/-- Raw symbolic frame used by the extracted AIR constraints. -/
structure SymbolicFrame where
  /-- Main-trace columns in the current row. -/
  curr : Nat → Felt := fun _ => 0
  /-- Main-trace columns in the next row. -/
  next : Nat → Felt := fun _ => 0
  /-- Auxiliary permutation columns in the current row. -/
  auxCurr : Nat → QuadFelt := fun _ => 0
  /-- Auxiliary permutation columns in the next row. -/
  auxNext : Nat → QuadFelt := fun _ => 0
  /-- Random verifier challenges used by the permutation buses. -/
  challenge : Nat → QuadFelt := fun _ => 0
  /-- Final committed permutation values. -/
  permValue : Nat → QuadFelt := fun _ => 0
  /-- Public input values (stack inputs/outputs + program hash + transcript). -/
  publicValue : Nat → Felt := fun _ => 0
  /-- Periodic column values (hasher round constants, bitwise selectors). -/
  periodic : Nat → Felt := fun _ => 0
  /-- Preprocessed column values (unused in Miden). -/
  preprocessed : Nat → Felt := fun _ => 0
  /-- `p3` symbolic selector for the first row. -/
  is_first_row : Felt := 0
  /-- `p3` symbolic selector for the last row. -/
  is_last_row : Felt := 0
  /-- `p3` symbolic selector for transition rows. -/
  is_transition : Felt := 0

-- ============================================================================
-- Raw accessors
-- ============================================================================

/-- Current-row main column by raw index. -/
abbrev SymbolicFrame.colCurr (f : SymbolicFrame) (i : Nat) : Felt := f.curr i

/-- Next-row main column by raw index. -/
abbrev SymbolicFrame.colNext (f : SymbolicFrame) (i : Nat) : Felt := f.next i

-- ============================================================================
-- Named accessors matching the Rust trace layout
-- ============================================================================

abbrev SymbolicFrame.clk  (f : SymbolicFrame) : Felt := f.curr 0
abbrev SymbolicFrame.clk' (f : SymbolicFrame) : Felt := f.next 0
abbrev SymbolicFrame.ctx  (f : SymbolicFrame) : Felt := f.curr 1
abbrev SymbolicFrame.ctx' (f : SymbolicFrame) : Felt := f.next 1

/-- Decoder helper registers (`decoder[16..21]`). -/
abbrev SymbolicFrame.h  (f : SymbolicFrame) (i : Nat) : Felt := f.curr (16 + i)
abbrev SymbolicFrame.h' (f : SymbolicFrame) (i : Nat) : Felt := f.next (16 + i)

/-- Visible stack columns (`stack[0..15]`). -/
abbrev SymbolicFrame.s  (f : SymbolicFrame) (i : Nat) : Felt := f.curr (30 + i)
abbrev SymbolicFrame.s' (f : SymbolicFrame) (i : Nat) : Felt := f.next (30 + i)

/-- Stack depth (`stack[16]`) and next-row depth. -/
abbrev SymbolicFrame.b0  (f : SymbolicFrame) : Felt := f.curr 46
abbrev SymbolicFrame.b0' (f : SymbolicFrame) : Felt := f.next 46

/-- Overflow-table address (`stack[17]`) and next-row address. -/
abbrev SymbolicFrame.b1  (f : SymbolicFrame) : Felt := f.curr 47
abbrev SymbolicFrame.b1' (f : SymbolicFrame) : Felt := f.next 47

/-- Overflow helper (`stack[18]` in the Rust stack segment). -/
abbrev SymbolicFrame.h0_overflow  (f : SymbolicFrame) : Felt := f.curr 48
abbrev SymbolicFrame.h0_overflow' (f : SymbolicFrame) : Felt := f.next 48

-- ============================================================================
-- Constraint types
-- ============================================================================

/-- A base-field symbolic AIR constraint. -/
abbrev SymbolicConstraint := SymbolicFrame → Felt

/-- An extension-field symbolic AIR constraint. -/
abbrev SymbolicBusConstraint := SymbolicFrame → QuadFelt

/-- Propositional satisfaction for base constraints. -/
def SymbolicFrame.satisfiesBase (f : SymbolicFrame) (cs : List SymbolicConstraint) : Prop :=
  ∀ c ∈ cs, c f = 0

/-- Propositional satisfaction for extension-field constraints. -/
def SymbolicFrame.satisfiesBus (f : SymbolicFrame) (cs : List SymbolicBusConstraint) : Prop :=
  ∀ c ∈ cs, c f = 0

end MidenLean.AIR
