/-
  AIR constraints for Miden VM stack manipulation and I/O operations.

  Extracted from:
    air/src/constraints/stack/ops/mod.rs      — per-operation rewrite constraints
    air/src/constraints/stack/general/mod.rs  — general stack transition (shift) constraints

  ## Architecture

  The Miden VM enforces stack transitions through two layers:

  1. **Op-specific constraints** (`ops/mod.rs`): For each operation, a small number of
     constraints enforce that specific stack positions hold the correct value in the next
     row. These constraints are multiplied by the operation flag, so they are only active
     when that operation is executing.

  2. **General shift constraints** (`general/mod.rs`): For every stack position 0..15,
     a constraint of the form
       s'[i] * flag_sum = no_shift[i] * s[i]
                        + left_shift[i+1] * s[i+1]
                        + right_shift[i-1] * s[i-1]
     enforces that "unmentioned" positions copy/shift correctly. The shift flags are
     composite sums of all operation flags that cause that shift type at that position.

  ## Scope

  This file focuses on the operations used in SHA-256 kernel procedures:
  DUP (0-7, 9, 11, 13, 15), SWAP, MOVUP (2-8), MOVDN (2-8), PAD, DROP.
  Word swap operations (SWAPW, SWAPW2, SWAPW3, SWAPDW) are included for completeness.

  ## Gap Analysis (AIR vs Processor)

  - **DUP**: The op constraint only enforces `s0' = s[n]`. The remaining positions
    (right shift from i-1) are enforced by the general constraints. The AIR does NOT
    independently verify that `s1' = s0`; it relies on the general shift constraint
    with the right_shift flag being active for DUP.

  - **MOVUP/MOVDN**: Only one position is constrained by the op-specific constraint
    (the moved element). All intermediate positions are handled by the general shift
    constraints, which must use the correct shift flag at each position. The per-position
    shift flags are built incrementally in `op_flags/mod.rs`: for MOVUP(n), right_shift
    is active at positions 0..n (elements pushed down) and the individual movup flag is
    subtracted from right_shift at position n+1 onward. For MOVDN(n), left_shift is
    active at positions 0..n-1 and the movdn flag is subtracted at position n onward.
    This incremental construction is error-prone; a mistake in one subtraction would
    weaken constraints for all higher positions.

  - **DROP**: Has NO op-specific constraint at all. It is purely a left shift operation.
    The general constraints enforce `s'[i] = s[i+1]` for all visible positions. At
    position 15, the left-shift case is handled by overflow (zeroing) constraints
    outside this module.

  - **PAD**: The op constraint enforces `s0' = 0`. The right shift of remaining
    elements is enforced by general constraints. The AIR does not redundantly check
    that `s1' = s0`.

  - **General constraint form**: The constraint is
      `s'[i] * flag_sum = expected`
    rather than `s'[i] = expected`. When `flag_sum = 0` (no applicable flag), the
    constraint degenerates to `0 = 0` and is trivially satisfied, meaning s'[i] is
    completely unconstrained. This could be a gap if an operation accidentally has
    zero flag contribution at some position. In practice, every valid operation should
    contribute to at least one flag at every position.
-/
import MidenLean.Felt

namespace MidenLean.AIR

-- ============================================================================
-- Op-specific constraints (from ops/mod.rs)
-- ============================================================================
-- These enforce the "rewrite" that an operation performs on specific stack
-- positions. They are conditional: multiplied by the op flag, so they are
-- trivially satisfied (0 = 0) when the operation is not active.

/-- AIR constraint for PAD: pushes 0 onto the stack.
    The only op-specific constraint is `s0' = 0`.
    The right shift of remaining elements (`s1' = s0`, `s2' = s1`, ...) is
    enforced by the general stack constraints with right_shift active. -/
def air_pad (s' : Fin 16 → Felt) : Prop :=
  s' 0 = 0

/-- AIR constraint for DUP.0 (DUP): copies s[0] to the top.
    Op-specific: `s0' = s0`.
    Right shift of remaining elements is enforced by general constraints. -/
def air_dup0 (s : Fin 16 → Felt) (s' : Fin 16 → Felt) : Prop :=
  s' 0 = s 0

/-- AIR constraint for DUP.1: copies s[1] to the top.
    Op-specific: `s0' = s1`. -/
def air_dup1 (s : Fin 16 → Felt) (s' : Fin 16 → Felt) : Prop :=
  s' 0 = s 1

/-- AIR constraint for DUP.2: copies s[2] to the top.
    Op-specific: `s0' = s2`. -/
def air_dup2 (s : Fin 16 → Felt) (s' : Fin 16 → Felt) : Prop :=
  s' 0 = s 2

/-- AIR constraint for DUP.3: copies s[3] to the top.
    Op-specific: `s0' = s3`. -/
def air_dup3 (s : Fin 16 → Felt) (s' : Fin 16 → Felt) : Prop :=
  s' 0 = s 3

/-- AIR constraint for DUP.4: copies s[4] to the top.
    Op-specific: `s0' = s4`. -/
def air_dup4 (s : Fin 16 → Felt) (s' : Fin 16 → Felt) : Prop :=
  s' 0 = s 4

/-- AIR constraint for DUP.5: copies s[5] to the top.
    Op-specific: `s0' = s5`. -/
def air_dup5 (s : Fin 16 → Felt) (s' : Fin 16 → Felt) : Prop :=
  s' 0 = s 5

/-- AIR constraint for DUP.6: copies s[6] to the top.
    Op-specific: `s0' = s6`. -/
def air_dup6 (s : Fin 16 → Felt) (s' : Fin 16 → Felt) : Prop :=
  s' 0 = s 6

/-- AIR constraint for DUP.7: copies s[7] to the top.
    Op-specific: `s0' = s7`. -/
def air_dup7 (s : Fin 16 → Felt) (s' : Fin 16 → Felt) : Prop :=
  s' 0 = s 7

/-- AIR constraint for DUP.9: copies s[9] to the top.
    Op-specific: `s0' = s9`. -/
def air_dup9 (s : Fin 16 → Felt) (s' : Fin 16 → Felt) : Prop :=
  s' 0 = s 9

/-- AIR constraint for DUP.11: copies s[11] to the top.
    Op-specific: `s0' = s11`. -/
def air_dup11 (s : Fin 16 → Felt) (s' : Fin 16 → Felt) : Prop :=
  s' 0 = s 11

/-- AIR constraint for DUP.13: copies s[13] to the top.
    Op-specific: `s0' = s13`. -/
def air_dup13 (s : Fin 16 → Felt) (s' : Fin 16 → Felt) : Prop :=
  s' 0 = s 13

/-- AIR constraint for DUP.15: copies s[15] to the top.
    Op-specific: `s0' = s15`. -/
def air_dup15 (s : Fin 16 → Felt) (s' : Fin 16 → Felt) : Prop :=
  s' 0 = s 15

/-- AIR constraint for SWAP: exchange top two stack elements.
    Op-specific: `s0' = s1` and `s1' = s0`.
    Positions 2..15 have no_shift active (general constraints enforce `s'[i] = s[i]`). -/
def air_swap (s : Fin 16 → Felt) (s' : Fin 16 → Felt) : Prop :=
  s' 0 = s 1
  ∧ s' 1 = s 0

/-- AIR constraint for MOVUP.2: move s[2] to the top.
    Op-specific: `s0' = s2`.
    General constraints enforce: positions 1..2 right-shift, positions 3..15 no-shift. -/
def air_movup2 (s : Fin 16 → Felt) (s' : Fin 16 → Felt) : Prop :=
  s' 0 = s 2

/-- AIR constraint for MOVUP.3: move s[3] to the top.
    Op-specific: `s0' = s3`. -/
def air_movup3 (s : Fin 16 → Felt) (s' : Fin 16 → Felt) : Prop :=
  s' 0 = s 3

/-- AIR constraint for MOVUP.4: move s[4] to the top.
    Op-specific: `s0' = s4`. -/
def air_movup4 (s : Fin 16 → Felt) (s' : Fin 16 → Felt) : Prop :=
  s' 0 = s 4

/-- AIR constraint for MOVUP.5: move s[5] to the top.
    Op-specific: `s0' = s5`. -/
def air_movup5 (s : Fin 16 → Felt) (s' : Fin 16 → Felt) : Prop :=
  s' 0 = s 5

/-- AIR constraint for MOVUP.6: move s[6] to the top.
    Op-specific: `s0' = s6`. -/
def air_movup6 (s : Fin 16 → Felt) (s' : Fin 16 → Felt) : Prop :=
  s' 0 = s 6

/-- AIR constraint for MOVUP.7: move s[7] to the top.
    Op-specific: `s0' = s7`. -/
def air_movup7 (s : Fin 16 → Felt) (s' : Fin 16 → Felt) : Prop :=
  s' 0 = s 7

/-- AIR constraint for MOVUP.8: move s[8] to the top.
    Op-specific: `s0' = s8`. -/
def air_movup8 (s : Fin 16 → Felt) (s' : Fin 16 → Felt) : Prop :=
  s' 0 = s 8

/-- AIR constraint for MOVDN.2: move s[0] down to position 2.
    Op-specific: `s2' = s0`.
    General constraints enforce: positions 0..1 left-shift, positions 3..15 no-shift. -/
def air_movdn2 (s : Fin 16 → Felt) (s' : Fin 16 → Felt) : Prop :=
  s' 2 = s 0

/-- AIR constraint for MOVDN.3: move s[0] down to position 3.
    Op-specific: `s3' = s0`. -/
def air_movdn3 (s : Fin 16 → Felt) (s' : Fin 16 → Felt) : Prop :=
  s' 3 = s 0

/-- AIR constraint for MOVDN.4: move s[0] down to position 4.
    Op-specific: `s4' = s0`. -/
def air_movdn4 (s : Fin 16 → Felt) (s' : Fin 16 → Felt) : Prop :=
  s' 4 = s 0

/-- AIR constraint for MOVDN.5: move s[0] down to position 5.
    Op-specific: `s5' = s0`. -/
def air_movdn5 (s : Fin 16 → Felt) (s' : Fin 16 → Felt) : Prop :=
  s' 5 = s 0

/-- AIR constraint for MOVDN.6: move s[0] down to position 6.
    Op-specific: `s6' = s0`. -/
def air_movdn6 (s : Fin 16 → Felt) (s' : Fin 16 → Felt) : Prop :=
  s' 6 = s 0

/-- AIR constraint for MOVDN.7: move s[0] down to position 7.
    Op-specific: `s7' = s0`. -/
def air_movdn7 (s : Fin 16 → Felt) (s' : Fin 16 → Felt) : Prop :=
  s' 7 = s 0

/-- AIR constraint for MOVDN.8: move s[0] down to position 8.
    Op-specific: `s8' = s0`. -/
def air_movdn8 (s : Fin 16 → Felt) (s' : Fin 16 → Felt) : Prop :=
  s' 8 = s 0

-- ============================================================================
-- General stack transition constraints (from general/mod.rs)
-- ============================================================================
-- These enforce that every stack position transitions correctly based on
-- which shift type is active. The shift flags are composite sums built from
-- all individual operation flags.
--
-- The constraint at each position has the form:
--   s'[i] * flag_sum = no_shift[i] * s[i]
--                     + left_shift[i+1] * s[i+1]
--                     + right_shift[i-1] * s[i-1]
--
-- This is NOT `s'[i] = ...` but rather a product form. When flag_sum != 0
-- (which should hold for every valid operation), dividing both sides by
-- flag_sum yields the expected equality. When flag_sum = 0, the constraint
-- is trivially 0 = 0 and s'[i] is unconstrained.

/-- Shift type active at a given stack position for a given operation. -/
inductive ShiftType where
  | noShift    -- s'[i] = s[i]  (position unchanged)
  | leftShift  -- s'[i] = s[i+1]  (stack shrinks; element from above fills in)
  | rightShift -- s'[i] = s[i-1]  (stack grows; element from below fills in)
  deriving Repr, BEq

/-- General stack transition constraint at position 0.
    Position 0 can receive from: no_shift (s[0]) or left_shift (s[1]).
    Right shift at position 0 means a new value is pushed (handled by op-specific). -/
def air_general_pos0
    (s : Fin 16 → Felt) (s' : Fin 16 → Felt)
    (no_shift_0 left_shift_1 : Felt) : Prop :=
  s' 0 * (no_shift_0 + left_shift_1) =
    no_shift_0 * s 0 + left_shift_1 * s 1

/-- General stack transition constraint at position i (1 <= i <= 14).
    All three shift types are possible. -/
def air_general_mid
    (s : Fin 16 → Felt) (s' : Fin 16 → Felt)
    (i : Fin 16)
    (no_shift_i left_shift_ip1 right_shift_im1 : Felt)
    (_hi : 1 ≤ i.val) (_lo : i.val ≤ 14) : Prop :=
  s' i * (no_shift_i + left_shift_ip1 + right_shift_im1) =
    no_shift_i * s i
    + left_shift_ip1 * s ⟨i.val + 1, by omega⟩
    + right_shift_im1 * s ⟨i.val - 1, by omega⟩

/-- General stack transition constraint at position 15.
    Position 15 can receive from: no_shift (s[15]) or right_shift (s[14]).
    Left shift at position 15 is handled by overflow/zeroing constraints. -/
def air_general_pos15
    (s : Fin 16 → Felt) (s' : Fin 16 → Felt)
    (no_shift_15 right_shift_14 : Felt) : Prop :=
  s' 15 * (no_shift_15 + right_shift_14) =
    no_shift_15 * s 15 + right_shift_14 * s 14

-- ============================================================================
-- Combined constraints: op-specific + general shift
-- ============================================================================
-- These combine the op-specific rewrite constraints with the expected general
-- shift behavior to give the full picture of what the AIR enforces for each
-- operation. The general constraints use flag_sum = 1 (since exactly one
-- operation executes per cycle) to simplify to direct equalities.
--
-- NOTE: In the actual AIR, flag_sum at each position is the sum of all
-- operation flags that contribute a given shift type. When exactly one
-- operation flag is 1, flag_sum = 1 at each position, and the general
-- constraint simplifies to s'[i] = s[i] / s[i+1] / s[i-1].

/-- Full AIR constraint for PAD assuming flag_sum = 1 at every position.
    Op-specific: s0' = 0.
    General (right shift): s'[i+1] = s[i] for i = 0..14. -/
def air_pad_full (s : Fin 16 → Felt) (s' : Fin 16 → Felt) : Prop :=
  s' 0 = 0
  ∧ ∀ i : Fin 15, s' ⟨i.val + 1, by omega⟩ = s ⟨i.val, by omega⟩

/-- Full AIR constraint for DUP.0 assuming flag_sum = 1 at every position.
    Op-specific: s0' = s0.
    General (right shift): s'[i+1] = s[i] for i = 0..14. -/
def air_dup0_full (s : Fin 16 → Felt) (s' : Fin 16 → Felt) : Prop :=
  s' 0 = s 0
  ∧ ∀ i : Fin 15, s' ⟨i.val + 1, by omega⟩ = s ⟨i.val, by omega⟩

/-- Full AIR constraint for DUP.1 assuming flag_sum = 1.
    Op-specific: s0' = s1.
    General (right shift): s'[i+1] = s[i] for i = 0..14. -/
def air_dup1_full (s : Fin 16 → Felt) (s' : Fin 16 → Felt) : Prop :=
  s' 0 = s 1
  ∧ ∀ i : Fin 15, s' ⟨i.val + 1, by omega⟩ = s ⟨i.val, by omega⟩

/-- Full AIR constraint for DUP.n (generic) assuming flag_sum = 1.
    Op-specific: s0' = s[n].
    General (right shift): s'[i+1] = s[i] for i = 0..14. -/
def air_dupN_full (s : Fin 16 → Felt) (s' : Fin 16 → Felt) (n : Fin 16) : Prop :=
  s' 0 = s n
  ∧ ∀ i : Fin 15, s' ⟨i.val + 1, by omega⟩ = s ⟨i.val, by omega⟩

/-- Full AIR constraint for SWAP assuming flag_sum = 1.
    Op-specific: s0' = s1, s1' = s0.
    General (no shift from position 2): s'[i] = s[i] for i = 2..15. -/
def air_swap_full (s : Fin 16 → Felt) (s' : Fin 16 → Felt) : Prop :=
  s' 0 = s 1
  ∧ s' 1 = s 0
  ∧ ∀ i : Fin 14, s' ⟨i.val + 2, by omega⟩ = s ⟨i.val + 2, by omega⟩

/-- Full AIR constraint for MOVUP.n (2 <= n <= 8) assuming flag_sum = 1.

    Processor semantics for MOVUP.n:
      Before: s[0], s[1], ..., s[n-1], s[n], s[n+1], ...
      After:  s[n], s[0], s[1], ..., s[n-1], s[n+1], ...

    The AIR enforces this through:
      - Op-specific: s'[0] = s[n]
      - General right_shift at positions 1..n: s'[i] = s[i-1]
        (elements 0..n-1 are pushed down by one to make room)
      - General no_shift at positions n+1..15: s'[i] = s[i]
        (elements below the extracted element are unchanged) -/
def air_movup_full (s : Fin 16 → Felt) (s' : Fin 16 → Felt) (n : Nat)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 8) : Prop :=
  -- Op-specific: top gets the element from depth n
  s' 0 = s ⟨n, by omega⟩
  -- Positions 1..n: right shift (pushed down by 1)
  ∧ (∀ i : Nat, 1 ≤ i → i ≤ n →
      s' ⟨i, by omega⟩ = s ⟨i - 1, by omega⟩)
  -- Positions n+1..15: no shift (unchanged)
  ∧ (∀ i : Nat, n + 1 ≤ i → i ≤ 15 →
      s' ⟨i, by omega⟩ = s ⟨i, by omega⟩)

/-- Full AIR constraint for MOVDN.n (2 <= n <= 8) assuming flag_sum = 1.

    Processor semantics for MOVDN.n:
      Before: s[0], s[1], ..., s[n], s[n+1], ...
      After:  s[1], s[2], ..., s[n], s[0], s[n+1], ...

    The AIR enforces this through:
      - General left_shift at positions 0..n-1: s'[i] = s[i+1]
        (elements shift up to fill the gap left by s[0])
      - Op-specific: s'[n] = s[0]
      - General no_shift at positions n+1..15: s'[i] = s[i]
        (elements below the insertion point are unchanged) -/
def air_movdn_full (s : Fin 16 → Felt) (s' : Fin 16 → Felt) (n : Nat)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 8) : Prop :=
  -- Positions 0..n-1: left shift (each gets the element from one position deeper)
  (∀ i : Nat, i ≤ n - 1 →
    s' ⟨i, by omega⟩ = s ⟨i + 1, by omega⟩)
  -- Op-specific: position n gets s[0]
  ∧ s' ⟨n, by omega⟩ = s 0
  -- Positions n+1..15: no shift (unchanged)
  ∧ (∀ i : Nat, n + 1 ≤ i → i ≤ 15 →
      s' ⟨i, by omega⟩ = s ⟨i, by omega⟩)

/-- Full AIR constraint for DROP assuming flag_sum = 1.
    DROP has no op-specific constraint. It is purely a left shift:
      s'[i] = s[i+1]   for i = 0..14
    Position 15 receives from overflow (outside this module's scope);
    the overflow constraints zero it or load from the overflow table. -/
def air_drop_full (s : Fin 16 → Felt) (s' : Fin 16 → Felt) : Prop :=
  ∀ i : Fin 15, s' ⟨i.val, by omega⟩ = s ⟨i.val + 1, by omega⟩

-- ============================================================================
-- Additional word/double-word swap operations
-- ============================================================================

/-- Full AIR constraint for SWAPW: swap words [0..3] and [4..7].
    Op-specific: 8 constraints swapping corresponding positions.
    General (no shift at positions 8..15): positions 8..15 unchanged. -/
def air_swapw_full (s : Fin 16 → Felt) (s' : Fin 16 → Felt) : Prop :=
  s' 0 = s 4 ∧ s' 1 = s 5 ∧ s' 2 = s 6 ∧ s' 3 = s 7
  ∧ s' 4 = s 0 ∧ s' 5 = s 1 ∧ s' 6 = s 2 ∧ s' 7 = s 3
  ∧ ∀ i : Fin 8, s' ⟨i.val + 8, by omega⟩ = s ⟨i.val + 8, by omega⟩

/-- Full AIR constraint for SWAPW2: swap words [0..3] and [8..11].
    Op-specific: 8 constraints swapping corresponding positions.
    General (no shift at 4..7 and 12..15): those positions unchanged. -/
def air_swapw2_full (s : Fin 16 → Felt) (s' : Fin 16 → Felt) : Prop :=
  s' 0 = s 8 ∧ s' 1 = s 9 ∧ s' 2 = s 10 ∧ s' 3 = s 11
  ∧ s' 8 = s 0 ∧ s' 9 = s 1 ∧ s' 10 = s 2 ∧ s' 11 = s 3
  ∧ (∀ i : Fin 4, s' ⟨i.val + 4, by omega⟩ = s ⟨i.val + 4, by omega⟩)
  ∧ (∀ i : Fin 4, s' ⟨i.val + 12, by omega⟩ = s ⟨i.val + 12, by omega⟩)

/-- Full AIR constraint for SWAPW3: swap words [0..3] and [12..15].
    Op-specific: 8 constraints swapping corresponding positions.
    General (no shift at 4..11): those positions unchanged. -/
def air_swapw3_full (s : Fin 16 → Felt) (s' : Fin 16 → Felt) : Prop :=
  s' 0 = s 12 ∧ s' 1 = s 13 ∧ s' 2 = s 14 ∧ s' 3 = s 15
  ∧ s' 12 = s 0 ∧ s' 13 = s 1 ∧ s' 14 = s 2 ∧ s' 15 = s 3
  ∧ ∀ i : Fin 8, s' ⟨i.val + 4, by omega⟩ = s ⟨i.val + 4, by omega⟩

/-- Full AIR constraint for SWAPDW: swap double-words [0..7] and [8..15].
    Op-specific: 16 constraints swapping all corresponding positions. -/
def air_swapdw_full (s : Fin 16 → Felt) (s' : Fin 16 → Felt) : Prop :=
  (∀ i : Fin 8, s' ⟨i.val, by omega⟩ = s ⟨i.val + 8, by omega⟩)
  ∧ (∀ i : Fin 8, s' ⟨i.val + 8, by omega⟩ = s ⟨i.val, by omega⟩)

-- ============================================================================
-- Raw general constraint (product form, as in the actual AIR)
-- ============================================================================
-- The following captures the exact algebraic form of the general constraint,
-- including the product with flag_sum. This is the form a prover must satisfy
-- and is useful for checking soundness of the constraint system.

/-- Raw general stack transition constraint for all 16 positions.
    `ns`, `ls`, `rs` are the no_shift, left_shift, right_shift flag values
    at each position for the current operation.

    Note: `ls 0` is unused (left_shift is not defined at position 0) and
    `rs 15` is unused (right_shift is not defined at position 15, as it
    would require access to position 16 which is in the overflow table). -/
def air_general_raw
    (s : Fin 16 → Felt) (s' : Fin 16 → Felt)
    (ns ls rs : Fin 16 → Felt) : Prop :=
  -- Position 0: no right shift contribution (right shift = new value pushed)
  s' 0 * (ns 0 + ls 1) = ns 0 * s 0 + ls 1 * s 1
  -- Positions 1..14: all three shift types
  ∧ (∀ i : Fin 14,
      let j : Fin 16 := ⟨i.val + 1, by omega⟩
      s' j * (ns j + ls ⟨i.val + 2, by omega⟩ + rs ⟨i.val, by omega⟩) =
        ns j * s j
        + ls ⟨i.val + 2, by omega⟩ * s ⟨i.val + 2, by omega⟩
        + rs ⟨i.val, by omega⟩ * s ⟨i.val, by omega⟩)
  -- Position 15: no left shift contribution (handled by overflow)
  ∧ s' 15 * (ns 15 + rs 14) = ns 15 * s 15 + rs 14 * s 14

end MidenLean.AIR
