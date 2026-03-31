import MidenLean.Felt
/-!
# AIR Constraint Framework

Executable semantics for Miden VM AIR (Algebraic Intermediate Representation)
constraints. This provides the foundation for:
1. Extracting constraints from the Rust constraint builder
2. Evaluating constraints on concrete trace frames (#eval)
3. Proving constraint soundness (AIR satisfaction → semantic correctness)

## Architecture

- `Frame`: A transition frame (current row + next row) with stack and helper columns
- `Constraint`: A polynomial `Frame → Felt` that must evaluate to zero
- `ConstraintSet`: A list of constraints for a single operation
- `Frame.satisfies`: Propositional satisfaction (for proofs)
- `Frame.check`: Executable satisfaction (for #eval / differential testing)

## Trust boundaries

Range checker bus guarantees (h0..h3 ∈ [0, 2^16)) are modeled as the
`Frame.RangeChecked` assumption. Local constraint soundness proofs assume
this; the bus argument is audited separately.
-/

namespace MidenLean.AIR

open MidenLean

-- ============================================================================
-- Core types
-- ============================================================================

/-- A transition frame: two consecutive rows of the Miden VM execution trace.
    Models the columns referenced by stack, system, and overflow AIR constraints.

    ## Column mapping to `MainTraceRow`
    - `s[0..15]`  → `stack[0..15]`  (visible stack top)
    - `s'[0..15]` → next row stack
    - `h[0..5]`   → `decoder[USER_OP_HELPERS_OFFSET..+6]`
    - `b0`        → `stack[16]` (stack depth)
    - `b1`        → `stack[17]` (overflow table address)
    - `clk`       → system clock column
    - `ctx`       → execution context ID -/
structure Frame where
  /-- Stack columns in the current row (s0..s15). -/
  s  : Fin 16 → Felt
  /-- Stack columns in the next row (s0'..s15'). -/
  s' : Fin 16 → Felt
  /-- Helper registers in the current row (h0..h5).
      These are stored at `decoder[USER_OP_HELPERS_OFFSET..]` in the Rust trace. -/
  h  : Fin 6 → Felt
  /-- Stack depth (b0, stack column 16). -/
  b0 : Felt := 0
  /-- Next-row stack depth. -/
  b0' : Felt := 0
  /-- Overflow table address (b1, stack column 17). -/
  b1 : Felt := 0
  /-- Next-row overflow table address. -/
  b1' : Felt := 0
  /-- Clock cycle. -/
  clk : Felt := 0
  /-- Next-row clock. -/
  clk' : Felt := 0
  /-- Execution context. -/
  ctx : Felt := 0
  /-- Next-row context. -/
  ctx' : Felt := 0

/-- A single AIR constraint: a polynomial over a transition frame that
    must evaluate to zero when the corresponding operation flag is active. -/
abbrev Constraint := Frame → Felt

/-- A set of constraints for a single operation.
    Each entry corresponds to one `assert_zero` call in the Rust `enforce_main`. -/
abbrev ConstraintSet := List Constraint

-- ============================================================================
-- Satisfaction
-- ============================================================================

/-- Propositional satisfaction: every constraint evaluates to zero. -/
def Frame.satisfies (f : Frame) (cs : ConstraintSet) : Prop :=
  ∀ c ∈ cs, c f = 0

/-- Executable satisfaction check (for `#eval` and differential testing). -/
def Frame.check (f : Frame) (cs : ConstraintSet) : Bool :=
  cs.all (fun c => c f == 0)

/-- Satisfaction of concatenation splits into satisfaction of both parts. -/
theorem Frame.satisfies_append (f : Frame) (a b : ConstraintSet) :
    f.satisfies (a ++ b) ↔ f.satisfies a ∧ f.satisfies b := by
  simp only [Frame.satisfies, List.mem_append]
  constructor
  · intro h; exact ⟨fun c hc => h c (Or.inl hc), fun c hc => h c (Or.inr hc)⟩
  · intro ⟨ha, hb⟩ c hc; rcases hc with hc | hc
    · exact ha c hc
    · exact hb c hc

/-- `check` is sound: if it returns true, propositional satisfaction holds. -/
theorem Frame.check_sound (f : Frame) (cs : ConstraintSet) :
    f.check cs = true → f.satisfies cs := by
  intro hcheck c hc
  simp [Frame.check, List.all_eq_true] at hcheck
  have := hcheck (fun f => c f) hc
  simp at this
  exact this

-- ============================================================================
-- Range checker model
-- ============================================================================

/-- The range checker bus guarantees helper registers h0..h3 are in [0, 2^16).
    This is a global trace property enforced by the permutation argument.
    We model it as a local assumption for per-operation soundness proofs. -/
structure Frame.RangeChecked (f : Frame) : Prop where
  h0_lt : (f.h 0).val < 2^16
  h1_lt : (f.h 1).val < 2^16
  h2_lt : (f.h 2).val < 2^16
  h3_lt : (f.h 3).val < 2^16

-- ============================================================================
-- Constants matching the Rust constraint code
-- ============================================================================

abbrev two_pow_16 : Felt := Felt.ofNat (2^16)
abbrev two_pow_32 : Felt := Felt.ofNat (2^32)
abbrev two_pow_48 : Felt := Felt.ofNat (2^48)
abbrev two_pow_32_minus_one : Felt := Felt.ofNat (2^32 - 1)

-- ============================================================================
-- U32 limb helpers (match Rust's v_lo, v_hi, v48, v64)
-- ============================================================================

/-- Low 32-bit limb: `h1 * 2^16 + h0`. -/
def Frame.v_lo (f : Frame) : Felt := f.h 1 * two_pow_16 + f.h 0

/-- High 32-bit limb: `h3 * 2^16 + h2`. -/
def Frame.v_hi (f : Frame) : Felt := f.h 3 * two_pow_16 + f.h 2

/-- Low 48-bit value: `h2 * 2^32 + v_lo`. -/
def Frame.v48 (f : Frame) : Felt := f.h 2 * two_pow_32 + f.v_lo

/-- Full 64-bit value: `h3 * 2^48 + v48`. -/
def Frame.v64 (f : Frame) : Felt := f.h 3 * two_pow_48 + f.v48

-- ============================================================================
-- Test vector constructor
-- ============================================================================

/-- Build a Frame from flat lists of natural numbers (for test vectors).
    Missing entries are padded with 0. The `extra` list provides
    [b0, b0', b1, b1', clk, clk', ctx, ctx'] if needed. -/
def Frame.ofLists (s s' : List Nat) (h : List Nat)
    (extra : List Nat := []) : Frame where
  s   := fun i => Felt.ofNat (s.getD i 0)
  s'  := fun i => Felt.ofNat (s'.getD i 0)
  h   := fun i => Felt.ofNat (h.getD i 0)
  b0  := Felt.ofNat (extra.getD 0 0)
  b0' := Felt.ofNat (extra.getD 1 0)
  b1  := Felt.ofNat (extra.getD 2 0)
  b1' := Felt.ofNat (extra.getD 3 0)
  clk := Felt.ofNat (extra.getD 4 0)
  clk' := Felt.ofNat (extra.getD 5 0)
  ctx := Felt.ofNat (extra.getD 6 0)
  ctx' := Felt.ofNat (extra.getD 7 0)

-- ============================================================================
-- Smoke tests
-- ============================================================================

section SmokeTests

private def smoke_add : ConstraintSet := [
  fun f => f.s' 0 - (f.s 0 + f.s 1)
]

-- Positive: 3 + 5 = 8
#eval (Frame.ofLists [3, 5] [8] []).check smoke_add  -- true

-- Negative: 3 + 5 ≠ 7
#eval (Frame.ofLists [3, 5] [7] []).check smoke_add  -- false

-- U32 limb check: v_lo should be h1*65536 + h0
-- h=[2, 1, 0, 0, 0, 0] → v_lo = 1*65536 + 2 = 65538
#eval (Frame.ofLists [] [] [2, 1, 0, 0, 0, 0]).v_lo == Felt.ofNat 65538  -- true
#eval (Frame.ofLists [] [] [2, 1, 0, 0, 0, 0]).v_hi == Felt.ofNat 0      -- true

end SmokeTests

end MidenLean.AIR
