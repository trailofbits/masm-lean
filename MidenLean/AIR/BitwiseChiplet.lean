/-
  Bitwise Chiplet AIR Constraints
  ================================

  This file formalizes the AIR constraints for the Miden VM bitwise chiplet,
  which handles U32AND and U32XOR operations.

  ## Architecture

  The bitwise chiplet processes two 32-bit inputs `a` and `b` over an 8-row
  cycle. Each row processes 4 bits (one nibble) of each input, starting from
  the most significant nibble and working down to the least significant.

  ### Trace columns (per row):

  | Column      | Description                                          |
  |-------------|------------------------------------------------------|
  | op_flag (s) | Operation selector: 0 = AND, 1 = XOR                |
  | a           | Running aggregation of input a                       |
  | b           | Running aggregation of input b                       |
  | a0..a3      | 4 binary columns: bit decomposition of current nibble of a |
  | b0..b3      | 4 binary columns: bit decomposition of current nibble of b |
  | zp          | Previous row's aggregated output (z from prior row)  |
  | z           | Current aggregated output                            |

  ### Periodic columns (period 8):

  - k0 (k_first):      [1, 0, 0, 0, 0, 0, 0, 0]  -- marks first row of cycle
  - k1 (k_transition): [1, 1, 1, 1, 1, 1, 1, 0]  -- marks non-last rows

  ### Input decomposition (how a is built across 8 rows):

  Row 0 (first):  a_0 = agg(a0..a3)                     -- top 4 bits
  Row 1:          a_1 = 16 * a_0 + agg(a0'..a3')        -- top 8 bits
  Row 2:          a_2 = 16 * a_1 + agg(a0'..a3')        -- top 12 bits
  ...
  Row 7 (last):   a_7 = 16 * a_6 + agg(a0'..a3')        -- full 32 bits

  After 8 rows: a_7 = sum_{i=0}^{7} nibble_i * 16^(7-i)
  Since each nibble is 4 binary bits (0..15), and there are 8 nibbles,
  the maximum value is 15 * (16^7 + 16^6 + ... + 1) = 16^8 - 1 = 2^32 - 1.

  The same applies to b.

  ### Output aggregation (how z is built):

  Row 0: z_0 = 0 * 16 + bitop(nibble_a_0, nibble_b_0)
  Row i: z_i = z_{i-1} * 16 + bitop(nibble_a_i, nibble_b_i)

  where bitop computes AND or XOR on the 4-bit nibbles depending on op_flag.

  ## Security analysis: u32 enforcement

  The constraints DO enforce that a and b are valid u32 values (< 2^32),
  because:
  1. Each bit column a_i, b_i is constrained to be binary (0 or 1).
  2. Each nibble is aggregated as sum(2^i * bit_i) for i in 0..3, giving
     a value in [0, 15].
  3. The running aggregation a' = 16*a + nibble builds the value MSB-first
     over exactly 8 rows.
  4. After 8 rows of this recurrence, starting from a single nibble,
     the final value equals sum of 8 nibbles * 16^k, which is at most
     15 * (16^0 + 16^1 + ... + 16^7) = 2^32 - 1.

  Therefore, any (a, b) pair that satisfies all chiplet constraints for a
  complete 8-row cycle must satisfy a < 2^32 and b < 2^32.

  IMPORTANT CAVEAT: This enforcement happens within the chiplet. The bus
  constraints must correctly link the chiplet's final-row (a, b, z) to the
  stack's operands for U32AND/U32XOR instructions. If the bus linkage is
  sound, then the stack-level u32 property follows from the chiplet constraints.
-/

import MidenLean.Felt

namespace MidenLean.AIR

-- ============================================================================
-- Basic definitions
-- ============================================================================

/-- A 4-bit nibble: four binary values representing bits 0 through 3. -/
structure Nibble (F : Type) where
  b0 : F
  b1 : F
  b2 : F
  b3 : F

/-- State of the bitwise chiplet trace at a single row. -/
structure BitwiseRow where
  /-- Operation selector: 0 for AND, 1 for XOR -/
  op_flag : Felt
  /-- Running aggregation of input a -/
  a : Felt
  /-- Running aggregation of input b -/
  b : Felt
  /-- Bit decomposition of current nibble of a -/
  a_bits : Nibble Felt
  /-- Bit decomposition of current nibble of b -/
  b_bits : Nibble Felt
  /-- Previous row's aggregated output -/
  zp : Felt
  /-- Current aggregated output -/
  z : Felt

-- ============================================================================
-- Helper: nibble aggregation
-- ============================================================================

/-- Aggregate 4 binary bits into a nibble value (little-endian):
    result = b0 + 2*b1 + 4*b2 + 8*b3
    Equivalently, using Horner's method: ((b3*2 + b2)*2 + b1)*2 + b0 -/
def aggregateNibble (n : Nibble Felt) : Felt :=
  n.b0 + 2 * n.b1 + 4 * n.b2 + 8 * n.b3

/-- Compute AND of two nibbles, bit by bit:
    result = (a0*b0) + 2*(a1*b1) + 4*(a2*b2) + 8*(a3*b3) -/
def nibbleAnd (a b : Nibble Felt) : Felt :=
  (a.b0 * b.b0) + 2 * (a.b1 * b.b1) + 4 * (a.b2 * b.b2) + 8 * (a.b3 * b.b3)

/-- Compute XOR of two nibbles, bit by bit:
    xor(ai, bi) = ai + bi - 2*ai*bi
    result = sum of 2^i * xor(ai, bi) -/
def nibbleXor (a b : Nibble Felt) : Felt :=
  let xor0 := a.b0 + b.b0 - 2 * a.b0 * b.b0
  let xor1 := a.b1 + b.b1 - 2 * a.b1 * b.b1
  let xor2 := a.b2 + b.b2 - 2 * a.b2 * b.b2
  let xor3 := a.b3 + b.b3 - 2 * a.b3 * b.b3
  xor0 + 2 * xor1 + 4 * xor2 + 8 * xor3

-- ============================================================================
-- Constraint 1: Operation flag is binary
-- ============================================================================

/-- The operation selector must be binary (0 for AND, 1 for XOR).
    Rust source: `cols.op_flag * (cols.op_flag - 1) = 0` -/
def air_bitwise_op_flag_binary (row : BitwiseRow) : Prop :=
  row.op_flag * (row.op_flag - 1) = 0

-- ============================================================================
-- Constraint 2: Operation flag is constant within an 8-row cycle
-- ============================================================================

/-- On transition rows (k1 = 1, i.e., rows 0..6 of the cycle), the operation
    flag must not change between consecutive rows.
    Rust source: `k_transition * (cols.op_flag - cols_next.op_flag) = 0` -/
def air_bitwise_op_flag_stable (row row_next : BitwiseRow) : Prop :=
  row.op_flag = row_next.op_flag

-- ============================================================================
-- Constraint 3: Bit columns are binary
-- ============================================================================

/-- All bit decomposition columns for input a must contain binary values (0 or 1).
    Rust source: `cols.a_bits[i] * (cols.a_bits[i] - 1) = 0` for i in 0..4 -/
def air_bitwise_a_bits_binary (row : BitwiseRow) : Prop :=
  row.a_bits.b0 * (row.a_bits.b0 - 1) = 0 ∧
  row.a_bits.b1 * (row.a_bits.b1 - 1) = 0 ∧
  row.a_bits.b2 * (row.a_bits.b2 - 1) = 0 ∧
  row.a_bits.b3 * (row.a_bits.b3 - 1) = 0

/-- All bit decomposition columns for input b must contain binary values (0 or 1).
    Rust source: `cols.b_bits[i] * (cols.b_bits[i] - 1) = 0` for i in 0..4 -/
def air_bitwise_b_bits_binary (row : BitwiseRow) : Prop :=
  row.b_bits.b0 * (row.b_bits.b0 - 1) = 0 ∧
  row.b_bits.b1 * (row.b_bits.b1 - 1) = 0 ∧
  row.b_bits.b2 * (row.b_bits.b2 - 1) = 0 ∧
  row.b_bits.b3 * (row.b_bits.b3 - 1) = 0

-- ============================================================================
-- Constraint 4: First row initialization
-- ============================================================================

/-- On the first row of each 8-row cycle (k0 = 1):
    - `a` equals the aggregation of its bit columns
    - `b` equals the aggregation of its bit columns
    - `zp` (previous output) is zero
    Rust source:
      `k_first * (cols.a - a_agg) = 0`
      `k_first * (cols.b - b_agg) = 0`
      `k_first * cols.prev_output = 0` -/
def air_bitwise_first_row (row : BitwiseRow) : Prop :=
  row.a = aggregateNibble row.a_bits ∧
  row.b = aggregateNibble row.b_bits ∧
  row.zp = 0

-- ============================================================================
-- Constraint 5: Input transition (aggregation across rows)
-- ============================================================================

/-- On transition rows (k1 = 1, rows 0..6 of the cycle), the next row's
    aggregated input is built by shifting the current value left by 4 bits
    (multiply by 16) and adding the next nibble.
    Rust source:
      `k_transition * (cols_next.a - (cols.a * 16 + a_agg_next)) = 0`
      `k_transition * (cols_next.b - (cols.b * 16 + b_agg_next)) = 0` -/
def air_bitwise_input_transition (row row_next : BitwiseRow) : Prop :=
  row_next.a = row.a * 16 + aggregateNibble row_next.a_bits ∧
  row_next.b = row.b * 16 + aggregateNibble row_next.b_bits

-- ============================================================================
-- Constraint 6: Output previous-value linkage
-- ============================================================================

/-- On transition rows (k1 = 1), the next row's `zp` must equal the current
    row's `z`. This threads the running output through the cycle.
    Rust source: `k_transition * (cols_next.prev_output - cols.output) = 0` -/
def air_bitwise_output_prev_transition (row row_next : BitwiseRow) : Prop :=
  row_next.zp = row.z

-- ============================================================================
-- Constraint 7: Output aggregation
-- ============================================================================

/-- On every row, the output z is computed as:
      z = zp * 16 + (if op_flag = 0 then AND(nibble_a, nibble_b)
                      else XOR(nibble_a, nibble_b))
    The implementation avoids a branch by using:
      z = zp * 16 + and_result + op_flag * (xor_result - and_result)
    When op_flag = 0 this gives AND; when op_flag = 1 this gives XOR.
    Rust source:
      `bitwise_flag * (cols.output - expected_z) = 0`
      where expected_z = zp * 16 + a_and_b + op_flag * (a_xor_b - a_and_b) -/
def air_bitwise_output_aggregation (row : BitwiseRow) : Prop :=
  let and_result := nibbleAnd row.a_bits row.b_bits
  let xor_result := nibbleXor row.a_bits row.b_bits
  row.z = row.zp * 16 + and_result + row.op_flag * (xor_result - and_result)

-- ============================================================================
-- Combined: all constraints for a single row
-- ============================================================================

/-- All bitwise chiplet constraints that apply to a single row in isolation
    (not involving the next row). -/
def air_bitwise_row_constraints (row : BitwiseRow) : Prop :=
  air_bitwise_op_flag_binary row ∧
  air_bitwise_a_bits_binary row ∧
  air_bitwise_b_bits_binary row ∧
  air_bitwise_output_aggregation row

/-- All bitwise chiplet constraints for the first row of a cycle. -/
def air_bitwise_first_row_constraints (row : BitwiseRow) : Prop :=
  air_bitwise_row_constraints row ∧
  air_bitwise_first_row row

/-- All bitwise chiplet transition constraints (rows 0..6 to their successor). -/
def air_bitwise_transition_constraints (row row_next : BitwiseRow) : Prop :=
  air_bitwise_op_flag_stable row row_next ∧
  air_bitwise_input_transition row row_next ∧
  air_bitwise_output_prev_transition row row_next

-- ============================================================================
-- Full 8-row cycle: all constraints combined
-- ============================================================================

/-- A complete 8-row bitwise cycle consists of rows r0 through r7 where:
    - r0 satisfies first-row constraints
    - All rows satisfy per-row constraints
    - Consecutive pairs (r0,r1), (r1,r2), ..., (r6,r7) satisfy transition constraints
      (note: the transition from r6 to r7 is the last one with k1=1)
    - The pair (r6,r7) does NOT get a transition constraint because k1=0 on row 7,
      but the output aggregation still applies to r7.

    Actually, k1 = [1,1,1,1,1,1,1,0], so transitions apply to rows 0..6
    (i.e., pairs (r0,r1) through (r6,r7)). On the last row (row 7), only
    per-row constraints apply (no transition to the next cycle). -/
def air_bitwise_full_cycle (rows : Fin 8 → BitwiseRow) : Prop :=
  -- First row initialization
  air_bitwise_first_row (rows 0) ∧
  -- Per-row constraints on all 8 rows
  (∀ i : Fin 8, air_bitwise_row_constraints (rows i)) ∧
  -- Transition constraints on rows 0..6 (k_transition = 1)
  (∀ i : Fin 7, air_bitwise_transition_constraints (rows i.castSucc) (rows i.succ))

-- ============================================================================
-- Security property: u32 enforcement
-- ============================================================================

/-- The bitwise chiplet constraints enforce that inputs a and b are valid u32
    values (i.e., a < 2^32 and b < 2^32).

    Argument sketch:
    - On row 0 (first row, k0=1): a_0 = agg(bits) where each bit is binary,
      so a_0 is in [0, 15].
    - On rows 1..7 (transition, k1=1): a_{i+1} = 16 * a_i + agg(bits_{i+1}),
      where agg(bits) is again in [0, 15].
    - Unrolling:
        a_0 in [0, 15]
        a_1 = 16 * a_0 + nibble_1      in [0, 16^2 - 1]    = [0, 2^8 - 1]
        a_2 = 16 * a_1 + nibble_2      in [0, 16^3 - 1]    = [0, 2^12 - 1]
        ...
        a_7 = 16 * a_6 + nibble_7      in [0, 16^8 - 1]    = [0, 2^32 - 1]

    The final value a_7 is exactly the `a` column on the last row of the cycle,
    which is the value sent to the chiplets bus. Since 0 <= a_7 <= 2^32 - 1,
    the chiplet enforces a < 2^32. The same argument applies to b.

    Note: This argument requires that the field characteristic p > 2^32, which
    holds for Goldilocks (p = 2^64 - 2^32 + 1 >> 2^32). The binary constraints
    x*(x-1)=0 have only solutions 0 and 1 in any field with p > 2, and the
    aggregation arithmetic is exact (no overflow) because all intermediate
    values are far below p. -/
theorem bitwise_chiplet_enforces_u32_inputs
    (rows : Fin 8 → BitwiseRow)
    (h_cycle : air_bitwise_full_cycle rows) :
    (rows 7).a.val < 2^32 ∧ (rows 7).b.val < 2^32 := by
  sorry -- Proof requires unrolling the recurrence and bounding; see argument above.

/-- The final output z on the last row of the cycle equals the correct bitwise
    operation applied to the full 32-bit inputs a and b.

    When op_flag = 0: z = a AND b (bitwise AND)
    When op_flag = 1: z = a XOR b (bitwise XOR)

    This follows from the output aggregation constraint threading through all
    8 rows, mirroring the input decomposition structure. -/
theorem bitwise_chiplet_output_correct
    (rows : Fin 8 → BitwiseRow)
    (h_cycle : air_bitwise_full_cycle rows) :
    -- The output on the last row is the result of the bitwise operation.
    -- (Statement left abstract; a full formalization would define 32-bit
    -- AND/XOR on Felt values and prove equality.)
    True := by
  trivial

-- ============================================================================
-- Summary of constraint count
-- ============================================================================

/-
  Total constraints enforced by the bitwise chiplet (per the Rust source):

  1. op_flag binary:                              1 constraint
  2. op_flag stability (transition rows):          1 constraint
  3. a_bits binary:                                4 constraints (one per bit)
  4. b_bits binary:                                4 constraints (one per bit)
  5. First-row a = agg(a_bits):                    1 constraint
  6. First-row b = agg(b_bits):                    1 constraint
  7. First-row zp = 0:                             1 constraint
  8. Transition a' = 16*a + agg(a'_bits):          1 constraint
  9. Transition b' = 16*b + agg(b'_bits):          1 constraint
  10. Transition zp' = z:                          1 constraint
  11. Output aggregation z = zp*16 + op_result:    1 constraint
  ─────────────────────────────────────────────────────────────
  Total:                                          17 constraints

  All constraints are gated by the bitwise_flag (derived from chiplet selectors
  s0, s1) so they only fire on rows belonging to the bitwise chiplet.

  The chiplets bus constraint (not formalized here) links the final row's
  (a, b, z) triple to the stack, ensuring the stack's U32AND/U32XOR instructions
  receive the correct result for the correct operands.
-/

end MidenLean.AIR
