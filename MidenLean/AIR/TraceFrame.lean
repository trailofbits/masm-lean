import MidenLean.Felt
import MidenLean.AIR.ExtField
/-!
# Full Trace Frame

A `TraceFrame` models two consecutive rows of the complete Miden VM execution trace
(71 main columns + 8 aux columns), matching the output of the symbolic constraint
extractor. Every AIR constraint is a function `TraceFrame → Felt` (base) or
`TraceFrame → QuadFelt` (extension/bus).

## Column layout (main trace, 71 columns)

| Range   | Width | Section       | Key columns                          |
|---------|-------|---------------|--------------------------------------|
| 0..5    | 6     | System        | clk(0), ctx(1), fn_hash(2..5)        |
| 6..29   | 24    | Decoder       | op_bits(7..13), helpers(16..21), ...  |
| 30..48  | 19    | Stack         | s0..s15(30..45), b0(46), b1(47), h0(48) |
| 49..50  | 2     | Range checker | V(49), ...                           |
| 51..70  | 20    | Chiplets      | selectors, hasher, bitwise, memory, ... |

## Aux trace (8 extension-field columns)

| Index | Name              |
|-------|-------------------|
| 0     | p1_block_stack    |
| 1     | p2_block_hash     |
| 2     | p3_op_group       |
| 3     | p1_stack          |
| 4     | b_range (LogUp)   |
| 5     | b_hash_kernel     |
| 6     | b_chiplets        |
| 7     | v_wiring          |
-/

namespace MidenLean.AIR

open MidenLean

/-- A full transition frame: two consecutive rows of the Miden VM execution trace.
    Covers all 71 main columns and 8 aux columns. -/
structure TraceFrame where
  /-- Main trace columns in current row (indices 0..70). -/
  curr : Fin 71 → Felt
  /-- Main trace columns in next row (indices 0..70). -/
  next : Fin 71 → Felt
  /-- Aux trace columns in current row (extension field, indices 0..7). -/
  aux_curr : Fin 8 → QuadFelt
  /-- Aux trace columns in next row. -/
  aux_next : Fin 8 → QuadFelt
  /-- Random challenges from verifier (2 values). -/
  challenge : Fin 2 → QuadFelt
  /-- Committed final values for aux columns (checked by reduced_aux_values). -/
  perm_value : Fin 8 → QuadFelt

-- ============================================================================
-- Named accessors (convenience over raw column indices)
-- ============================================================================

-- System columns
abbrev TraceFrame.clk  (f : TraceFrame) := f.curr ⟨0, by omega⟩
abbrev TraceFrame.clk' (f : TraceFrame) := f.next ⟨0, by omega⟩
abbrev TraceFrame.ctx  (f : TraceFrame) := f.curr ⟨1, by omega⟩
abbrev TraceFrame.ctx' (f : TraceFrame) := f.next ⟨1, by omega⟩

-- Stack columns (30..45)
abbrev TraceFrame.s  (f : TraceFrame) (i : Fin 16) : Felt := f.curr ⟨30 + i.val, by omega⟩
abbrev TraceFrame.s' (f : TraceFrame) (i : Fin 16) : Felt := f.next ⟨30 + i.val, by omega⟩

-- Helper registers (decoder columns 16..21)
abbrev TraceFrame.h (f : TraceFrame) (i : Fin 6) : Felt := f.curr ⟨16 + i.val, by omega⟩

-- Stack depth / overflow
abbrev TraceFrame.b0  (f : TraceFrame) := f.curr ⟨46, by omega⟩
abbrev TraceFrame.b0' (f : TraceFrame) := f.next ⟨46, by omega⟩
abbrev TraceFrame.b1  (f : TraceFrame) := f.curr ⟨47, by omega⟩
abbrev TraceFrame.b1' (f : TraceFrame) := f.next ⟨47, by omega⟩

-- ============================================================================
-- Constraint types
-- ============================================================================

/-- A base-field AIR constraint: must evaluate to zero. -/
abbrev TraceConstraint := TraceFrame → Felt

/-- An extension-field (bus) constraint: must evaluate to zero. -/
abbrev ExtTraceConstraint := TraceFrame → QuadFelt

/-- Propositional satisfaction for a list of base constraints. -/
def TraceFrame.satisfiesBase (f : TraceFrame) (cs : List TraceConstraint) : Prop :=
  ∀ c ∈ cs, c f = 0

/-- Propositional satisfaction for a list of extension constraints. -/
def TraceFrame.satisfiesExt (f : TraceFrame) (cs : List ExtTraceConstraint) : Prop :=
  ∀ c ∈ cs, c f = 0

end MidenLean.AIR
