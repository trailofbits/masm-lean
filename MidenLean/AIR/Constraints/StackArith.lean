import MidenLean.AIR.Frame
/-!
# Stack Arithmetic AIR Constraints

Hand-translated from `audit-miden-vm/air/src/constraints/stack/stack_arith/mod.rs`.
Each `ConstraintSet` corresponds to one operation, containing exactly the constraints
that are active when that operation's flag is 1 (flag prefix stripped).

## Constraint sources

- Constraints marked `[integrity]` use `assert_zero_integrity` in Rust (higher degree).
- Constraints marked `[shared]` come from composite-flag `assert_zero` calls
  (output constraints shared across multiple u32 ops).
- Range checks (h0..h3 ∈ [0, 2^16)) are NOT included here — they come from the
  range checker bus and are modeled by `Frame.RangeChecked`.
-/

namespace MidenLean.AIR.Constraints

open MidenLean MidenLean.AIR

-- ============================================================================
-- Field arithmetic operations
-- ============================================================================

/-- ADD: s0' = s0 + s1. (1 constraint) -/
def add : ConstraintSet := [
  -- idx 0: s0' - (s0 + s1)
  fun f => f.s' 0 - (f.s 0 + f.s 1)
]

/-- NEG: s0' = -s0. (1 constraint) -/
def neg : ConstraintSet := [
  -- idx 1: s0' + s0
  fun f => f.s' 0 + f.s 0
]

/-- MUL: s0' = s0 * s1. (1 constraint) -/
def mul : ConstraintSet := [
  -- idx 2: s0' - s0 * s1
  fun f => f.s' 0 - f.s 0 * f.s 1
]

/-- INV: s0' * s0 = 1. (1 constraint) -/
def inv : ConstraintSet := [
  -- idx 3: s0' * s0 - 1
  fun f => f.s' 0 * f.s 0 - 1
]

/-- INCR: s0' = s0 + 1. (1 constraint) -/
def incr : ConstraintSet := [
  -- idx 4: s0' - s0 - 1
  fun f => f.s' 0 - f.s 0 - 1
]

/-- NOT: s0 is boolean, s0' = 1 - s0. (2 constraints) -/
def not : ConstraintSet := [
  -- idx 5: s0 * (s0 - 1) [integrity]
  fun f => f.s 0 * (f.s 0 - 1),
  -- idx 6: s0 + s0' - 1
  fun f => f.s 0 + f.s' 0 - 1
]

/-- AND: s0, s1 boolean, s0' = s0 * s1. (3 constraints) -/
def and : ConstraintSet := [
  -- idx 7: s0 * (s0 - 1) [integrity]
  fun f => f.s 0 * (f.s 0 - 1),
  -- idx 8: s1 * (s1 - 1) [integrity]
  fun f => f.s 1 * (f.s 1 - 1),
  -- idx 9: s0' - s0 * s1
  fun f => f.s' 0 - f.s 0 * f.s 1
]

/-- OR: s0, s1 boolean, s0' = s0 + s1 - s0*s1. (3 constraints) -/
def or : ConstraintSet := [
  -- idx 10: s0 * (s0 - 1) [integrity]
  fun f => f.s 0 * (f.s 0 - 1),
  -- idx 11: s1 * (s1 - 1) [integrity]
  fun f => f.s 1 * (f.s 1 - 1),
  -- idx 12: s0' - (s0 + s1 - s0 * s1)
  fun f => f.s' 0 - (f.s 0 + f.s 1 - f.s 0 * f.s 1)
]

/-- EQ: if s0 = s1 then s0' = 1, else h0 = 1/(s0-s1) and s0' = 0. (2 constraints) -/
def eq : ConstraintSet := [
  -- idx 13: (s0 - s1) * s0'
  fun f => (f.s 0 - f.s 1) * f.s' 0,
  -- idx 14: s0' - (1 - (s0 - s1) * h0)
  fun f => f.s' 0 - (1 - (f.s 0 - f.s 1) * f.h 0)
]

/-- EQZ: if s0 = 0 then s0' = 1, else h0 = 1/s0 and s0' = 0. (2 constraints) -/
def eqz : ConstraintSet := [
  -- idx 15: s0 * s0'
  fun f => f.s 0 * f.s' 0,
  -- idx 16: s0' - (1 - s0 * h0)
  fun f => f.s' 0 - (1 - f.s 0 * f.h 0)
]

/-- EXPACC: square-and-multiply accumulation step. (5 constraints)
    s1' = s1², h0 = 1 + (s1-1)*s0', s2' = s2*h0, s3 = s3'*2 + s0', s0' boolean. -/
def expacc : ConstraintSet := [
  -- idx 17: s1' - s1 * s1
  fun f => f.s' 1 - f.s 1 * f.s 1,
  -- idx 18: h0 - 1 - (s1 - 1) * s0'
  fun f => f.h 0 - 1 - (f.s 1 - 1) * f.s' 0,
  -- idx 19: s2' - s2 * h0
  fun f => f.s' 2 - f.s 2 * f.h 0,
  -- idx 20: s3 - s3' * 2 - s0'
  fun f => f.s 3 - f.s' 3 * 2 - f.s' 0,
  -- idx 21: s0' * (s0' - 1)
  fun f => f.s' 0 * (f.s' 0 - 1)
]

/-- EXT2MUL: extension field multiplication in GF(p²) with x² - 7. (4 constraints) -/
def ext2mul : ConstraintSet := [
  -- idx 22: s0' - s0 (pass-through b0)
  fun f => f.s' 0 - f.s 0,
  -- idx 23: s1' - s1 (pass-through b1)
  fun f => f.s' 1 - f.s 1,
  -- idx 24: s2' - (s2*s0 + 7 * s3*s1)
  fun f => f.s' 2 - (f.s 2 * f.s 0 + 7 * (f.s 3 * f.s 1)),
  -- idx 25: s3' - ((s2+s3)*(s0+s1) - s2*s0 - s3*s1)
  fun f => f.s' 3 - ((f.s 2 + f.s 3) * (f.s 0 + f.s 1) - f.s 2 * f.s 0 - f.s 3 * f.s 1)
]

-- ============================================================================
-- U32 operations
-- ============================================================================

/-- U32SPLIT: decompose s0 into (lo32, hi32). (4 constraints)
    s0 = v64 [integrity], s0' = v_lo [shared], s1' = v_hi [shared],
    element validity [shared integrity]. -/
def u32split : ConstraintSet := [
  -- idx 26: (1 - h4*(2^32-1 - v_hi)) * v_lo [shared integrity]
  fun f => (1 - f.h 4 * (two_pow_32_minus_one - f.v_hi)) * f.v_lo,
  -- idx 27: s0' - v_lo [shared output]
  fun f => f.s' 0 - f.v_lo,
  -- idx 28: s1' - v_hi [shared output]
  fun f => f.s' 1 - f.v_hi,
  -- idx 29: s0 - v64 [integrity]
  fun f => f.s 0 - f.v64
]

/-- U32ADD: s0 + s1 = v48, output (v_lo, v_hi). (3 constraints) -/
def u32add : ConstraintSet := [
  -- idx 27: s0' - v_lo [shared output]
  fun f => f.s' 0 - f.v_lo,
  -- idx 28: s1' - v_hi [shared output]
  fun f => f.s' 1 - f.v_hi,
  -- idx 30: s0 + s1 - v48 [integrity]
  fun f => f.s 0 + f.s 1 - f.v48
]

/-- U32ADD3: s0 + s1 + s2 = v48, output (v_lo, v_hi). (3 constraints) -/
def u32add3 : ConstraintSet := [
  -- idx 27: s0' - v_lo [shared output]
  fun f => f.s' 0 - f.v_lo,
  -- idx 28: s1' - v_hi [shared output]
  fun f => f.s' 1 - f.v_hi,
  -- idx 31: s0 + s1 + s2 - v48 [integrity]
  fun f => f.s 0 + f.s 1 + f.s 2 - f.v48
]

/-- U32SUB: s1 = s0 + s1' - s0'*2^32, s0' boolean (borrow), s1' = v_lo. (3 constraints) -/
def u32sub : ConstraintSet := [
  -- idx 32: s1 - (s0 + s1' - s0' * 2^32)
  fun f => f.s 1 - (f.s 0 + f.s' 1 - f.s' 0 * two_pow_32),
  -- idx 33: s0' * (s0' - 1)
  fun f => f.s' 0 * (f.s' 0 - 1),
  -- idx 34: s1' - v_lo
  fun f => f.s' 1 - f.v_lo
]

/-- U32MUL: s0 * s1 = v64, output (v_lo, v_hi), element validity. (4 constraints) -/
def u32mul : ConstraintSet := [
  -- idx 26: (1 - h4*(2^32-1 - v_hi)) * v_lo [shared integrity]
  fun f => (1 - f.h 4 * (two_pow_32_minus_one - f.v_hi)) * f.v_lo,
  -- idx 27: s0' - v_lo [shared output]
  fun f => f.s' 0 - f.v_lo,
  -- idx 28: s1' - v_hi [shared output]
  fun f => f.s' 1 - f.v_hi,
  -- idx 35: s0 * s1 - v64 [integrity]
  fun f => f.s 0 * f.s 1 - f.v64
]

/-- U32MADD: s0 * s1 + s2 = v64, output (v_lo, v_hi), element validity. (4 constraints) -/
def u32madd : ConstraintSet := [
  -- idx 26: (1 - h4*(2^32-1 - v_hi)) * v_lo [shared integrity]
  fun f => (1 - f.h 4 * (two_pow_32_minus_one - f.v_hi)) * f.v_lo,
  -- idx 27: s0' - v_lo [shared output]
  fun f => f.s' 0 - f.v_lo,
  -- idx 28: s1' - v_hi [shared output]
  fun f => f.s' 1 - f.v_hi,
  -- idx 36: s0 * s1 + s2 - v64 [integrity]
  fun f => f.s 0 * f.s 1 + f.s 2 - f.v64
]

/-- U32DIV: s1 = s0 * s1' + s0' (division), with range-checked bounds. (3 constraints) -/
def u32div : ConstraintSet := [
  -- idx 37: s1 - (s0 * s1' + s0')
  fun f => f.s 1 - (f.s 0 * f.s' 1 + f.s' 0),
  -- idx 38: s1 - s1' - v_lo (ensures dividend ≥ quotient)
  fun f => f.s 1 - f.s' 1 - f.v_lo,
  -- idx 39: s0 - s0' - (v_hi + 1) (ensures remainder < divisor)
  fun f => f.s 0 - f.s' 0 - (f.v_hi + 1)
]

/-- U32ASSERT2: assert s0 and s1 are u32 via limb decomposition. (2 constraints) -/
def u32assert2 : ConstraintSet := [
  -- idx 40: s0' - v_hi
  fun f => f.s' 0 - f.v_hi,
  -- idx 41: s1' - v_lo
  fun f => f.s' 1 - f.v_lo
]

-- ============================================================================
-- Smoke tests: one positive + one negative per category
-- ============================================================================

section Tests

-- ADD: 3 + 5 = 8
#eval (Frame.ofLists [3, 5] [8] []).check add           -- true
#eval (Frame.ofLists [3, 5] [7] []).check add           -- false

-- NEG: s0' + s0 = 0 mod p. s0=1 → s0'=p-1
#eval (Frame.ofLists [1] [18446744069414584320] []).check neg  -- true (p-1)
#eval (Frame.ofLists [1] [1] []).check neg                     -- false

-- MUL: 3 * 7 = 21
#eval (Frame.ofLists [3, 7] [21] []).check mul           -- true
#eval (Frame.ofLists [3, 7] [20] []).check mul           -- false

-- INV: 2 * (p+1)/2 = 1 mod p. inv(2) = (p+1)/2
-- p = 2^64 - 2^32 + 1 = 18446744069414584321
-- (p+1)/2 = 9223372034707292161
#eval (Frame.ofLists [2] [9223372034707292161] []).check inv   -- true
#eval (Frame.ofLists [2] [5] []).check inv                      -- false

-- INCR: 41 + 1 = 42
#eval (Frame.ofLists [41] [42] []).check incr            -- true
#eval (Frame.ofLists [41] [43] []).check incr            -- false

-- NOT: s0=1, s0'=0
#eval (Frame.ofLists [1] [0] []).check not               -- true
#eval (Frame.ofLists [2] [0] []).check not               -- false (s0 not boolean)

-- AND: 1 AND 1 = 1
#eval (Frame.ofLists [1, 1] [1] []).check and            -- true
#eval (Frame.ofLists [1, 0] [1] []).check and            -- false

-- OR: 1 OR 0 = 1
#eval (Frame.ofLists [1, 0] [1] []).check or             -- true
#eval (Frame.ofLists [1, 0] [0] []).check or             -- false

-- EQ: s0=s1=5 → s0'=1 (h0 irrelevant when equal)
#eval (Frame.ofLists [5, 5] [1] [0]).check eq            -- true
#eval (Frame.ofLists [5, 5] [0] [0]).check eq            -- false

-- EQZ: s0=0 → s0'=1
#eval (Frame.ofLists [0] [1] [0]).check eqz              -- true
#eval (Frame.ofLists [0] [0] [0]).check eqz              -- false

-- U32ADD: 3 + 5 = 8, v_lo=8, v_hi=0
-- h=[lo16(8), hi16(8), lo16(0), hi16(0)] = [8, 0, 0, 0]
#eval (Frame.ofLists [3, 5] [8, 0] [8, 0, 0, 0]).check u32add   -- true
#eval (Frame.ofLists [3, 5] [7, 0] [8, 0, 0, 0]).check u32add   -- false

-- U32ADD with carry: 2^32-1 + 1 = 2^32 → lo=0, hi=1
-- v48 = h2*2^32 + h1*2^16 + h0 = 0*2^32 + 0*2^16 + 0 = 0... wait
-- s0 + s1 = (2^32-1) + 1 = 2^32 = v48
-- v_lo = h1*2^16 + h0, v_hi = h3*2^16 + h2
-- We need v48 = 2^32 = h2*2^32 + h1*2^16 + h0
-- So h2=1, h1=0, h0=0 → v48 = 1*2^32 = 2^32. v_lo = 0. v_hi = h3*2^16+h2 = 0+1 = 1.
#eval (Frame.ofLists [4294967295, 1] [0, 1] [0, 0, 1, 0]).check u32add  -- true

-- U32SUB: 10 - 3 = 7, borrow=0
-- s0=3, s1=10, s0'=0 (borrow), s1'=7
-- v_lo = h1*2^16+h0 = 7, so h0=7, h1=0
#eval (Frame.ofLists [3, 10] [0, 7] [7, 0, 0, 0]).check u32sub  -- true
#eval (Frame.ofLists [3, 10] [1, 7] [7, 0, 0, 0]).check u32sub  -- false

-- U32MUL: 65536 * 65536 = 2^32. v64 = 2^32.
-- v_lo=0, v_hi=1. h=[0, 0, 1, 0, 0, 0]. s0'=v_lo=0, s1'=v_hi=1.
-- Validity: (1 - h4*(2^32-1 - 1)) * 0 = 0 (v_lo=0 trivially satisfies).
#eval (Frame.ofLists [65536, 65536] [0, 1] [0, 0, 1, 0, 0]).check u32mul   -- true
#eval (Frame.ofLists [65536, 65536] [1, 1] [0, 0, 1, 0, 0]).check u32mul   -- false

-- U32DIV: 10 / 3 = quot 3, rem 1
-- s0=3 (divisor), s1=10 (dividend), s0'=1 (remainder), s1'=3 (quotient)
-- constraint 1: 10 = 3*3 + 1 = 10 ✓
-- constraint 2: s1 - s1' = 10 - 3 = 7 = v_lo → h0=7, h1=0
-- constraint 3: s0 - s0' = 3 - 1 = 2 = v_hi + 1 → v_hi = 1 → h2=1, h3=0
#eval (Frame.ofLists [3, 10] [1, 3] [7, 0, 1, 0]).check u32div   -- true
#eval (Frame.ofLists [3, 10] [2, 3] [7, 0, 1, 0]).check u32div   -- false

-- U32ASSERT2: s0=100, s1=200. s0'=v_hi (s0 decomp), s1'=v_lo (s1 decomp)
-- Wait, u32assert2 checks s0 and s1 are u32 via:
--   s0' = v_hi = h3*2^16+h2 and s1' = v_lo = h1*2^16+h0
-- But these are just checking the decomposition exists, not that s0=v_hi or s1=v_lo.
-- Actually looking at Rust: the constraint just says s0_next = v_hi and s1_next = v_lo.
-- The processor sets s0_next = s0, s1_next = s1, h decomposition of s0 and s1.
-- Actually I think the processor decomposes both values using the helpers:
-- s0 is decomposed into h2,h3 (its 16-bit limbs) and s1 into h0,h1.
-- s0' = s0 = h3*2^16+h2 = v_hi, s1' = s1 = h1*2^16+h0 = v_lo
-- The range check on h0..h3 then proves both are u32.
#eval (Frame.ofLists [0, 0] [100, 200] [200, 0, 100, 0]).check u32assert2  -- true
#eval (Frame.ofLists [0, 0] [100, 201] [200, 0, 100, 0]).check u32assert2  -- false

end Tests

end MidenLean.AIR.Constraints
