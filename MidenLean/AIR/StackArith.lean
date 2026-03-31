import MidenLean.Semantics

/-!
# AIR constraints: StackArith

Extracted from `stack_arith/mod.rs`.

Each definition captures the polynomial constraints that the STARK verifier
enforces for a given operation. When the operation flag is active, every
conjunct must hold over the Goldilocks field (p = 2^64 - 2^32 + 1).

## Variable conventions

- `s0, s1, ...` -- stack elements before the operation (current row)
- `s0', s1', ...` -- stack elements after the operation (next row)
- `h0, h1, ...` -- helper registers (nondeterministic, prover-supplied)
- Helper registers marked as range-checked are constrained to `[0, 2^16)` by the
  range checker bus (not captured in these local constraints).
- Constraints marked `[integrity]` allow higher polynomial degree.

## Derived quantities

The u32 operations use composite limb values built from the 16-bit helper registers:

- `v_lo  = h1 * 2^16 + h0`          -- low  32-bit limb
- `v_hi  = h3 * 2^16 + h2`          -- high 32-bit limb
- `v48   = h2 * 2^32  + v_lo`       -- low  48 bits
- `v64   = h3 * 2^48  + v48`        -- full 64-bit value
-/

namespace Miden.AIR.StackArith

open MidenLean

-- ============================================================================
-- Field arithmetic operations
-- ============================================================================

/-- AIR constraints for ADD.
    s0' = s0 + s1.
    1 exact constraint. -/
def air_add (s0 s1 : Felt) (s0' : Felt) : Prop :=
  s0' = s0 + s1

/-- AIR constraints for NEG.
    s0' = -s0 (additive inverse).
    1 exact constraint. -/
def air_neg (s0 : Felt) (s0' : Felt) : Prop :=
  s0' + s0 = Felt.ofNat 0

/-- AIR constraints for MUL.
    s0' = s0 * s1.
    1 exact constraint. -/
def air_mul (s0 s1 : Felt) (s0' : Felt) : Prop :=
  s0' = s0 * s1

/-- AIR constraints for INV.
    s0' * s0 = 1 (multiplicative inverse).
    1 exact constraint. -/
def air_inv (s0 : Felt) (s0' : Felt) : Prop :=
  s0' * s0 = Felt.ofNat 1

/-- AIR constraints for INCR.
    s0' = s0 + 1.
    1 exact constraint. -/
def air_incr (s0 : Felt) (s0' : Felt) : Prop :=
  s0' = s0 + Felt.ofNat 1

/-- AIR constraints for NOT.
    s0 must be boolean, and s0' = 1 - s0.
    1 integrity + 1 exact constraint. -/
def air_not (s0 : Felt) (s0' : Felt) : Prop :=
  -- s0 is boolean [integrity]
  s0 * (s0 - Felt.ofNat 1) = Felt.ofNat 0
  -- s0 + s0' = 1 [exact]
  ∧ s0 + s0' = Felt.ofNat 1

/-- AIR constraints for AND (boolean AND).
    Both inputs must be boolean, and s0' = s0 * s1.
    2 integrity + 1 exact constraint. -/
def air_and (s0 s1 : Felt) (s0' : Felt) : Prop :=
  -- s0 is boolean [integrity]
  s0 * (s0 - Felt.ofNat 1) = Felt.ofNat 0
  -- s1 is boolean [integrity]
  ∧ s1 * (s1 - Felt.ofNat 1) = Felt.ofNat 0
  -- s0' = s0 * s1 [exact]
  ∧ s0' = s0 * s1

/-- AIR constraints for OR (boolean OR).
    Both inputs must be boolean, and s0' = s0 + s1 - s0 * s1.
    2 integrity + 1 exact constraint. -/
def air_or (s0 s1 : Felt) (s0' : Felt) : Prop :=
  -- s0 is boolean [integrity]
  s0 * (s0 - Felt.ofNat 1) = Felt.ofNat 0
  -- s1 is boolean [integrity]
  ∧ s1 * (s1 - Felt.ofNat 1) = Felt.ofNat 0
  -- s0' = s0 + s1 - s0 * s1 [exact]
  ∧ s0' = s0 + s1 - s0 * s1

/-- AIR constraints for EQ.
    If s0 = s1 then s0' = 1; otherwise h0 = 1/(s0-s1) and s0' = 0.
    2 exact constraints. -/
def air_eq (s0 s1 : Felt) (s0' : Felt) (h0 : Felt) : Prop :=
  -- (s0 - s1) * s0' = 0 [exact]
  (s0 - s1) * s0' = Felt.ofNat 0
  -- s0' = 1 - (s0 - s1) * h0 [exact]
  ∧ s0' = Felt.ofNat 1 - (s0 - s1) * h0

/-- AIR constraints for EQZ.
    If s0 = 0 then s0' = 1; otherwise h0 = 1/s0 and s0' = 0.
    2 exact constraints. -/
def air_eqz (s0 : Felt) (s0' : Felt) (h0 : Felt) : Prop :=
  -- s0 * s0' = 0 [exact]
  s0 * s0' = Felt.ofNat 0
  -- s0' = 1 - s0 * h0 [exact]
  ∧ s0' = Felt.ofNat 1 - s0 * h0

/-- AIR constraints for EXPACC.
    Computes s1' = s1^2 (squaring), s2' = s2 * exp_val where
    exp_val = 1 + (s1 - 1) * s0', and s3 = s3' * 2 + s0' with s0' boolean.
    5 exact constraints. -/
def air_expacc (s0' s1 s2 s3 s1' s2' s3' : Felt) (h0 : Felt) : Prop :=
  -- s1' = s1^2 [exact]
  s1' = s1 * s1
  -- h0 (exp_val) = 1 + (s1 - 1) * s0' [exact]
  ∧ h0 - Felt.ofNat 1 = (s1 - Felt.ofNat 1) * s0'
  -- s2' = s2 * h0 [exact]
  ∧ s2' = s2 * h0
  -- s3 = s3' * 2 + s0' [exact]
  ∧ s3 = s3' * Felt.ofNat 2 + s0'
  -- s0' is boolean [exact]
  ∧ s0' * (s0' - Felt.ofNat 1) = Felt.ofNat 0

/-- AIR constraints for EXT2MUL (extension field multiplication).
    Computes (c0, c1) = (a0, a1) * (b0, b1) in GF(p^2) with irreducible x^2 - 7.
    4 exact constraints. -/
def air_ext2mul (s0 s1 s2 s3 s0' s1' s2' s3' : Felt) : Prop :=
  -- s0' = s0 (pass-through b0) [exact]
  s0' = s0
  -- s1' = s1 (pass-through b1) [exact]
  ∧ s1' = s1
  -- s2' = a0*b0 + 7 * a1*b1 [exact]
  ∧ s2' = s2 * s0 + Felt.ofNat 7 * (s3 * s1)
  -- s3' = (a0+a1)*(b0+b1) - a0*b0 - a1*b1 [exact]
  ∧ s3' = (s2 + s3) * (s0 + s1) - s2 * s0 - s3 * s1

-- ============================================================================
-- U32 operations
-- ============================================================================

/-- AIR constraints for U32SPLIT.
    Decomposes s0 into a 64-bit value: s0 = h3*2^48 + h2*2^32 + h1*2^16 + h0.
    Output: s0' = h1*2^16 + h0 (low 32 bits), s1' = h3*2^16 + h2 (high 32 bits).
    1 integrity constraint for the decomposition, plus shared output constraints.
    Helper registers h0..h3 are range-checked to 16 bits by the range checker bus.
    An additional validity check constrains the high part:
    if v_hi = 2^32 - 1 then v_lo must be 0 (prevents ambiguous representations). -/
def air_u32split (s0 s0' s1' : Felt) (h0 h1 h2 h3 h4 : Felt) : Prop :=
  let v_lo := h1 * Felt.ofNat (2^16) + h0
  let v_hi := h3 * Felt.ofNat (2^16) + h2
  let v48  := h2 * Felt.ofNat (2^32) + v_lo
  let v64  := h3 * Felt.ofNat (2^48) + v48
  -- Main decomposition: s0 = v64 [integrity]
  s0 = v64
  -- Output lo: s0' = v_lo [exact]
  ∧ s0' = v_lo
  -- Output hi: s1' = v_hi [exact]
  ∧ s1' = v_hi
  -- Element validity: (1 - h4*(2^32-1 - v_hi)) * v_lo = 0 [integrity]
  ∧ (Felt.ofNat 1 - h4 * (Felt.ofNat (2^32 - 1) - v_hi)) * v_lo = Felt.ofNat 0
  -- Range checks
  ∧ h0.val < 2^16 ∧ h1.val < 2^16 ∧ h2.val < 2^16 ∧ h3.val < 2^16

/-- AIR constraints for U32ADD.
    Adds two stack elements: s0 + s1 = h2*2^32 + h1*2^16 + h0.
    Output: s0' = h1*2^16 + h0 (low 32 bits), s1' = h3*2^16 + h2 (carry/high).
    Helper registers h0..h3 are range-checked to 16 bits by the range checker bus. -/
def air_u32add (s0 s1 s0' s1' : Felt) (h0 h1 h2 h3 : Felt) : Prop :=
  let v_lo := h1 * Felt.ofNat (2^16) + h0
  let v_hi := h3 * Felt.ofNat (2^16) + h2
  let v48  := h2 * Felt.ofNat (2^32) + v_lo
  -- s0 + s1 = v48 [integrity]
  s0 + s1 = v48
  -- Output lo: s0' = v_lo [exact]
  ∧ s0' = v_lo
  -- Output hi: s1' = v_hi [exact]
  ∧ s1' = v_hi
  -- Range checks
  ∧ h0.val < 2^16 ∧ h1.val < 2^16 ∧ h2.val < 2^16 ∧ h3.val < 2^16

/-- AIR constraints for U32ADD3.
    Adds three stack elements: s0 + s1 + s2 = h2*2^32 + h1*2^16 + h0.
    Output: s0' = h1*2^16 + h0 (low 32 bits), s1' = h3*2^16 + h2 (carry/high).
    Helper registers h0..h3 are range-checked to 16 bits by the range checker bus. -/
def air_u32add3 (s0 s1 s2 s0' s1' : Felt) (h0 h1 h2 h3 : Felt) : Prop :=
  let v_lo := h1 * Felt.ofNat (2^16) + h0
  let v_hi := h3 * Felt.ofNat (2^16) + h2
  let v48  := h2 * Felt.ofNat (2^32) + v_lo
  -- s0 + s1 + s2 = v48 [integrity]
  s0 + s1 + s2 = v48
  -- Output lo: s0' = v_lo [exact]
  ∧ s0' = v_lo
  -- Output hi: s1' = v_hi [exact]
  ∧ s1' = v_hi
  -- Range checks
  ∧ h0.val < 2^16 ∧ h1.val < 2^16 ∧ h2.val < 2^16 ∧ h3.val < 2^16

/-- AIR constraints for U32SUB.
    Subtracts: s1 = s0 + s1' - s0' * 2^32 where s0' is the borrow bit (0 or 1).
    Output: s0' = borrow (boolean), s1' = h1*2^16 + h0 (the difference, range-checked).
    3 exact constraints.
    Helper registers h0..h3 are range-checked to 16 bits by the range checker bus. -/
def air_u32sub (s0 s1 s0' s1' : Felt) (h0 h1 h2 h3 : Felt) : Prop :=
  let v_lo := h1 * Felt.ofNat (2^16) + h0
  -- s1 = s0 + s1' - s0' * 2^32 [exact]
  s1 = s0 + s1' - s0' * Felt.ofNat (2^32)
  -- s0' is boolean (borrow bit) [exact]
  ∧ s0' * (s0' - Felt.ofNat 1) = Felt.ofNat 0
  -- s1' = v_lo [exact]
  ∧ s1' = v_lo
  -- Range checks
  ∧ h0.val < 2^16 ∧ h1.val < 2^16 ∧ h2.val < 2^16 ∧ h3.val < 2^16

/-- AIR constraints for U32MUL.
    Multiplies: s0 * s1 = h3*2^48 + h2*2^32 + h1*2^16 + h0.
    Output: s0' = h1*2^16 + h0 (low 32 bits), s1' = h3*2^16 + h2 (high 32 bits).
    1 integrity constraint.
    An additional validity check constrains the high part:
    if v_hi = 2^32 - 1 then v_lo must be 0.
    Helper registers h0..h3 are range-checked to 16 bits by the range checker bus. -/
def air_u32mul (s0 s1 s0' s1' : Felt) (h0 h1 h2 h3 h4 : Felt) : Prop :=
  let v_lo := h1 * Felt.ofNat (2^16) + h0
  let v_hi := h3 * Felt.ofNat (2^16) + h2
  let v48  := h2 * Felt.ofNat (2^32) + v_lo
  let v64  := h3 * Felt.ofNat (2^48) + v48
  -- s0 * s1 = v64 [integrity]
  s0 * s1 = v64
  -- Output lo: s0' = v_lo [exact]
  ∧ s0' = v_lo
  -- Output hi: s1' = v_hi [exact]
  ∧ s1' = v_hi
  -- Element validity: (1 - h4*(2^32-1 - v_hi)) * v_lo = 0 [integrity]
  ∧ (Felt.ofNat 1 - h4 * (Felt.ofNat (2^32 - 1) - v_hi)) * v_lo = Felt.ofNat 0
  -- Range checks
  ∧ h0.val < 2^16 ∧ h1.val < 2^16 ∧ h2.val < 2^16 ∧ h3.val < 2^16

/-- AIR constraints for U32MADD (multiply-add).
    s0 * s1 + s2 = h3*2^48 + h2*2^32 + h1*2^16 + h0.
    Output: s0' = h1*2^16 + h0 (low 32 bits), s1' = h3*2^16 + h2 (high 32 bits).
    1 integrity constraint.
    An additional validity check constrains the high part.
    Helper registers h0..h3 are range-checked to 16 bits by the range checker bus. -/
def air_u32madd (s0 s1 s2 s0' s1' : Felt) (h0 h1 h2 h3 h4 : Felt) : Prop :=
  let v_lo := h1 * Felt.ofNat (2^16) + h0
  let v_hi := h3 * Felt.ofNat (2^16) + h2
  let v48  := h2 * Felt.ofNat (2^32) + v_lo
  let v64  := h3 * Felt.ofNat (2^48) + v48
  -- s0 * s1 + s2 = v64 [integrity]
  s0 * s1 + s2 = v64
  -- Output lo: s0' = v_lo [exact]
  ∧ s0' = v_lo
  -- Output hi: s1' = v_hi [exact]
  ∧ s1' = v_hi
  -- Element validity: (1 - h4*(2^32-1 - v_hi)) * v_lo = 0 [integrity]
  ∧ (Felt.ofNat 1 - h4 * (Felt.ofNat (2^32 - 1) - v_hi)) * v_lo = Felt.ofNat 0
  -- Range checks
  ∧ h0.val < 2^16 ∧ h1.val < 2^16 ∧ h2.val < 2^16 ∧ h3.val < 2^16

/-- AIR constraints for U32DIV.
    Division: s1 = s0 * s1' + s0' (quotient and remainder).
    Additional constraints ensure 0 <= s0' < s0 via:
    s1 - s1' = v_lo (the remainder is range-checked) and
    s0 - s0' = v_hi + 1 (the divisor minus remainder is positive).
    3 exact constraints.
    Helper registers h0..h3 are range-checked to 16 bits by the range checker bus. -/
def air_u32div (s0 s1 s0' s1' : Felt) (h0 h1 h2 h3 : Felt) : Prop :=
  let v_lo := h1 * Felt.ofNat (2^16) + h0
  let v_hi := h3 * Felt.ofNat (2^16) + h2
  -- s1 = s0 * s1' + s0' (division equation) [exact]
  s1 = s0 * s1' + s0'
  -- s1 - s1' = v_lo (quotient range check) [exact]
  ∧ s1 - s1' = v_lo
  -- s0 - s0' = v_hi + 1 (remainder < divisor) [exact]
  ∧ s0 - s0' = v_hi + Felt.ofNat 1
  -- Range checks
  ∧ h0.val < 2^16 ∧ h1.val < 2^16 ∧ h2.val < 2^16 ∧ h3.val < 2^16

/-- AIR constraints for U32ASSERT2.
    Asserts that s0 and s1 are valid u32 values by checking their 16-bit decomposition.
    s0' = h3*2^16 + h2, s1' = h1*2^16 + h0.
    2 exact constraints.
    Helper registers h0..h3 are range-checked to 16 bits by the range checker bus. -/
def air_u32assert2 (s0' s1' : Felt) (h0 h1 h2 h3 : Felt) : Prop :=
  let v_lo := h1 * Felt.ofNat (2^16) + h0
  let v_hi := h3 * Felt.ofNat (2^16) + h2
  -- s0' = v_hi [exact]
  s0' = v_hi
  -- s1' = v_lo [exact]
  ∧ s1' = v_lo
  -- Range checks
  ∧ h0.val < 2^16 ∧ h1.val < 2^16 ∧ h2.val < 2^16 ∧ h3.val < 2^16

end Miden.AIR.StackArith
