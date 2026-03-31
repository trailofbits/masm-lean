import MidenLean.AIR.Constraints.StackArith
import MidenLean.Proofs.Helpers
/-!
# AIR Constraint Soundness Proofs: Stack Arithmetic

For each stack_arith operation, we prove that constraint satisfaction implies
the correct semantic relationship between inputs and outputs.

These are **per-instruction** soundness theorems at the AIR level:
if the constraint polynomials all evaluate to zero on a transition frame,
then the next-row values are determined by the current-row values according
to the instruction specification.

## Trust assumptions

- `Frame.RangeChecked`: helper registers h0..h3 are in [0, 2^16).
  This is enforced by the range checker bus (audited separately).
- The constraint definitions in `Constraints.StackArith` faithfully
  reflect the Rust `enforce_main` code. This is validated by differential
  testing against real VM traces (see `Tests/StackArithDiff.lean`).
-/

namespace MidenLean.AIR.Proofs

open MidenLean MidenLean.AIR MidenLean.AIR.Constraints

-- ============================================================================
-- Helpers: extract constraints from small lists without field-simp
-- ============================================================================

private theorem sat1 (f : Frame) (c : Constraint) :
    f.satisfies [c] ↔ c f = 0 := by
  simp [Frame.satisfies]

private theorem sat2 (f : Frame) (c1 c2 : Constraint) :
    f.satisfies [c1, c2] ↔ c1 f = 0 ∧ c2 f = 0 := by
  unfold Frame.satisfies; constructor
  · intro h; exact ⟨h _ (by simp), h _ (by simp)⟩
  · intro ⟨h1, h2⟩ c hc; simp at hc; rcases hc with rfl | rfl <;> assumption

private theorem sat3 (f : Frame) (c1 c2 c3 : Constraint) :
    f.satisfies [c1, c2, c3] ↔ c1 f = 0 ∧ c2 f = 0 ∧ c3 f = 0 := by
  unfold Frame.satisfies; constructor
  · intro h; exact ⟨h _ (by simp), h _ (by simp), h _ (by simp)⟩
  · intro ⟨h1, h2, h3⟩ c hc; simp at hc; rcases hc with rfl | rfl | rfl <;> assumption

private theorem sat4 (f : Frame) (c1 c2 c3 c4 : Constraint) :
    f.satisfies [c1, c2, c3, c4] ↔ c1 f = 0 ∧ c2 f = 0 ∧ c3 f = 0 ∧ c4 f = 0 := by
  unfold Frame.satisfies; constructor
  · intro h; exact ⟨h _ (by simp), h _ (by simp), h _ (by simp), h _ (by simp)⟩
  · intro ⟨h1, h2, h3, h4⟩ c hc
    simp at hc; rcases hc with rfl | rfl | rfl | rfl <;> assumption

private theorem sat5 (f : Frame) (c1 c2 c3 c4 c5 : Constraint) :
    f.satisfies [c1, c2, c3, c4, c5] ↔
    c1 f = 0 ∧ c2 f = 0 ∧ c3 f = 0 ∧ c4 f = 0 ∧ c5 f = 0 := by
  unfold Frame.satisfies; constructor
  · intro h
    exact ⟨h _ (by simp), h _ (by simp), h _ (by simp), h _ (by simp), h _ (by simp)⟩
  · intro ⟨h1, h2, h3, h4, h5⟩ c hc
    simp at hc; rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption

-- ============================================================================
-- Field arithmetic soundness
-- ============================================================================

/-- ADD: constraint satisfaction implies s0' = s0 + s1. -/
theorem air_add_sound (f : Frame) (hsat : f.satisfies Constraints.add) :
    f.s' 0 = f.s 0 + f.s 1 := by
  rw [Constraints.add, sat1] at hsat; exact sub_eq_zero.mp hsat

/-- NEG: constraint satisfaction implies s0' = -s0. -/
theorem air_neg_sound (f : Frame) (hsat : f.satisfies Constraints.neg) :
    f.s' 0 = -f.s 0 := by
  rw [Constraints.neg, sat1] at hsat; exact add_eq_zero_iff_eq_neg.mp hsat

/-- MUL: constraint satisfaction implies s0' = s0 * s1. -/
theorem air_mul_sound (f : Frame) (hsat : f.satisfies Constraints.mul) :
    f.s' 0 = f.s 0 * f.s 1 := by
  rw [Constraints.mul, sat1] at hsat; exact sub_eq_zero.mp hsat

/-- INV: constraint satisfaction implies s0' * s0 = 1. -/
theorem air_inv_sound (f : Frame) (hsat : f.satisfies Constraints.inv) :
    f.s' 0 * f.s 0 = 1 := by
  rw [Constraints.inv, sat1] at hsat; exact sub_eq_zero.mp hsat

/-- INCR: constraint satisfaction implies s0' = s0 + 1. -/
theorem air_incr_sound (f : Frame) (hsat : f.satisfies Constraints.incr) :
    f.s' 0 = f.s 0 + 1 := by
  rw [Constraints.incr, sat1] at hsat
  exact sub_eq_zero.mp (show f.s' 0 - (f.s 0 + 1) = 0 by linear_combination hsat)

/-- NOT: s0 is boolean and s0' = 1 - s0. -/
theorem air_not_sound (f : Frame) (hsat : f.satisfies Constraints.not) :
    f.s 0 * (f.s 0 - 1) = 0 ∧ f.s' 0 = 1 - f.s 0 := by
  rw [Constraints.not, sat2] at hsat
  exact ⟨hsat.1, by linear_combination hsat.2⟩

/-- AND: both inputs boolean, s0' = s0 * s1. -/
theorem air_and_sound (f : Frame) (hsat : f.satisfies Constraints.and) :
    f.s 0 * (f.s 0 - 1) = 0 ∧ f.s 1 * (f.s 1 - 1) = 0 ∧ f.s' 0 = f.s 0 * f.s 1 := by
  rw [Constraints.and, sat3] at hsat
  exact ⟨hsat.1, hsat.2.1, sub_eq_zero.mp hsat.2.2⟩

/-- OR: both inputs boolean, s0' = s0 + s1 - s0*s1. -/
theorem air_or_sound (f : Frame) (hsat : f.satisfies Constraints.or) :
    f.s 0 * (f.s 0 - 1) = 0 ∧ f.s 1 * (f.s 1 - 1) = 0
    ∧ f.s' 0 = f.s 0 + f.s 1 - f.s 0 * f.s 1 := by
  rw [Constraints.or, sat3] at hsat
  exact ⟨hsat.1, hsat.2.1, by linear_combination hsat.2.2⟩

/-- EQ: (s0-s1)*s0' = 0 and s0' = 1 - (s0-s1)*h0.
    Together these force s0'=1 when s0=s1, and s0'=0 otherwise. -/
theorem air_eq_sound (f : Frame) (hsat : f.satisfies Constraints.eq) :
    (f.s 0 - f.s 1) * f.s' 0 = 0 ∧ f.s' 0 = 1 - (f.s 0 - f.s 1) * f.h 0 := by
  rw [Constraints.eq, sat2] at hsat
  exact ⟨hsat.1, by linear_combination hsat.2⟩

/-- EQZ: s0*s0' = 0 and s0' = 1 - s0*h0.
    Together these force s0'=1 when s0=0, and s0'=0 otherwise. -/
theorem air_eqz_sound (f : Frame) (hsat : f.satisfies Constraints.eqz) :
    f.s 0 * f.s' 0 = 0 ∧ f.s' 0 = 1 - f.s 0 * f.h 0 := by
  rw [Constraints.eqz, sat2] at hsat
  exact ⟨hsat.1, by linear_combination hsat.2⟩

/-- EXPACC: squaring step s1'=s1², accumulation s2'=s2*h0, bit decomposition. -/
theorem air_expacc_sound (f : Frame) (hsat : f.satisfies Constraints.expacc) :
    f.s' 1 = f.s 1 * f.s 1
    ∧ f.h 0 = 1 + (f.s 1 - 1) * f.s' 0
    ∧ f.s' 2 = f.s 2 * f.h 0
    ∧ f.s 3 = f.s' 3 * 2 + f.s' 0
    ∧ f.s' 0 * (f.s' 0 - 1) = 0 := by
  rw [Constraints.expacc, sat5] at hsat
  obtain ⟨h1, h2, h3, h4, h5⟩ := hsat
  exact ⟨sub_eq_zero.mp h1,
         by linear_combination h2,
         sub_eq_zero.mp h3,
         by linear_combination h4,
         h5⟩

/-- EXT2MUL: extension field multiplication in GF(p²). -/
theorem air_ext2mul_sound (f : Frame) (hsat : f.satisfies Constraints.ext2mul) :
    f.s' 0 = f.s 0
    ∧ f.s' 1 = f.s 1
    ∧ f.s' 2 = f.s 2 * f.s 0 + 7 * (f.s 3 * f.s 1)
    ∧ f.s' 3 = (f.s 2 + f.s 3) * (f.s 0 + f.s 1) - f.s 2 * f.s 0 - f.s 3 * f.s 1 := by
  rw [Constraints.ext2mul, sat4] at hsat
  obtain ⟨h1, h2, h3, h4⟩ := hsat
  exact ⟨sub_eq_zero.mp h1, sub_eq_zero.mp h2,
         by linear_combination h3, by linear_combination h4⟩

-- ============================================================================
-- U32 soundness
-- ============================================================================

/-- U32ADD: outputs are the limb decomposition, input sum equals v48. -/
theorem air_u32add_sound (f : Frame) (hsat : f.satisfies Constraints.u32add) :
    f.s' 0 = f.v_lo ∧ f.s' 1 = f.v_hi ∧ f.s 0 + f.s 1 = f.v48 := by
  rw [Constraints.u32add, sat3] at hsat
  exact ⟨sub_eq_zero.mp hsat.1, sub_eq_zero.mp hsat.2.1, sub_eq_zero.mp hsat.2.2⟩

/-- U32ADD3: outputs are the limb decomposition, three-input sum equals v48. -/
theorem air_u32add3_sound (f : Frame) (hsat : f.satisfies Constraints.u32add3) :
    f.s' 0 = f.v_lo ∧ f.s' 1 = f.v_hi ∧ f.s 0 + f.s 1 + f.s 2 = f.v48 := by
  rw [Constraints.u32add3, sat3] at hsat
  exact ⟨sub_eq_zero.mp hsat.1, sub_eq_zero.mp hsat.2.1, sub_eq_zero.mp hsat.2.2⟩

/-- U32SUB: subtraction with borrow bit and range-checked result. -/
theorem air_u32sub_sound (f : Frame) (hsat : f.satisfies Constraints.u32sub) :
    f.s 1 = f.s 0 + f.s' 1 - f.s' 0 * two_pow_32
    ∧ f.s' 0 * (f.s' 0 - 1) = 0
    ∧ f.s' 1 = f.v_lo := by
  rw [Constraints.u32sub, sat3] at hsat
  exact ⟨by linear_combination hsat.1, hsat.2.1, sub_eq_zero.mp hsat.2.2⟩

/-- U32SPLIT: decompose felt into (lo32, hi32) with validity check. -/
theorem air_u32split_sound (f : Frame) (hsat : f.satisfies Constraints.u32split) :
    (1 - f.h 4 * (two_pow_32_minus_one - f.v_hi)) * f.v_lo = 0
    ∧ f.s' 0 = f.v_lo
    ∧ f.s' 1 = f.v_hi
    ∧ f.s 0 = f.v64 := by
  rw [Constraints.u32split, sat4] at hsat
  exact ⟨hsat.1, sub_eq_zero.mp hsat.2.1, sub_eq_zero.mp hsat.2.2.1,
         sub_eq_zero.mp hsat.2.2.2⟩

/-- U32MUL: multiplication with validity check, outputs are limb decomposition. -/
theorem air_u32mul_sound (f : Frame) (hsat : f.satisfies Constraints.u32mul) :
    (1 - f.h 4 * (two_pow_32_minus_one - f.v_hi)) * f.v_lo = 0
    ∧ f.s' 0 = f.v_lo
    ∧ f.s' 1 = f.v_hi
    ∧ f.s 0 * f.s 1 = f.v64 := by
  rw [Constraints.u32mul, sat4] at hsat
  exact ⟨hsat.1, sub_eq_zero.mp hsat.2.1, sub_eq_zero.mp hsat.2.2.1,
         sub_eq_zero.mp hsat.2.2.2⟩

/-- U32MADD: multiply-add with validity check. -/
theorem air_u32madd_sound (f : Frame) (hsat : f.satisfies Constraints.u32madd) :
    (1 - f.h 4 * (two_pow_32_minus_one - f.v_hi)) * f.v_lo = 0
    ∧ f.s' 0 = f.v_lo
    ∧ f.s' 1 = f.v_hi
    ∧ f.s 0 * f.s 1 + f.s 2 = f.v64 := by
  rw [Constraints.u32madd, sat4] at hsat
  exact ⟨hsat.1, sub_eq_zero.mp hsat.2.1, sub_eq_zero.mp hsat.2.2.1,
         sub_eq_zero.mp hsat.2.2.2⟩

/-- U32DIV: division equation with range-checked bounds. -/
theorem air_u32div_sound (f : Frame) (hsat : f.satisfies Constraints.u32div) :
    f.s 1 = f.s 0 * f.s' 1 + f.s' 0
    ∧ f.s 1 - f.s' 1 = f.v_lo
    ∧ f.s 0 - f.s' 0 = f.v_hi + 1 := by
  rw [Constraints.u32div, sat3] at hsat
  exact ⟨by linear_combination hsat.1,
         by linear_combination hsat.2.1,
         by linear_combination hsat.2.2⟩

/-- U32ASSERT2: outputs equal the limb decomposition (asserting u32). -/
theorem air_u32assert2_sound (f : Frame) (hsat : f.satisfies Constraints.u32assert2) :
    f.s' 0 = f.v_hi ∧ f.s' 1 = f.v_lo := by
  rw [Constraints.u32assert2, sat2] at hsat
  exact ⟨sub_eq_zero.mp hsat.1, sub_eq_zero.mp hsat.2⟩

/-- The low 32-bit limb extracted from range-checked 16-bit helpers is a valid
`u32`. -/
theorem v_lo_isU32_of_rangeChecked (f : Frame) (hrc : Frame.RangeChecked f) :
    f.v_lo.IsU32 := by
  have hv :
      f.v_lo = Felt.ofNat ((f.h 1).val * 2 ^ 16 + (f.h 0).val) := by
    unfold Frame.v_lo two_pow_16 Felt.ofNat
    conv_lhs =>
      rw [← ZMod.natCast_zmod_val (f.h 1), ← ZMod.natCast_zmod_val (f.h 0)]
    simp [Nat.cast_add, Nat.cast_mul, add_comm, mul_comm]
  rw [hv]
  unfold Felt.IsU32
  rw [felt_ofNat_val_lt _]
  · have h0 := hrc.h0_lt
    have h1 := hrc.h1_lt
    omega
  · have h0 := hrc.h0_lt
    have h1 := hrc.h1_lt
    unfold GOLDILOCKS_PRIME
    omega

/-- The high 32-bit limb extracted from range-checked 16-bit helpers is a valid
`u32`. -/
theorem v_hi_isU32_of_rangeChecked (f : Frame) (hrc : Frame.RangeChecked f) :
    f.v_hi.IsU32 := by
  have hv :
      f.v_hi = Felt.ofNat ((f.h 3).val * 2 ^ 16 + (f.h 2).val) := by
    unfold Frame.v_hi two_pow_16 Felt.ofNat
    conv_lhs =>
      rw [← ZMod.natCast_zmod_val (f.h 3), ← ZMod.natCast_zmod_val (f.h 2)]
    simp [Nat.cast_add, Nat.cast_mul, add_comm, mul_comm]
  rw [hv]
  unfold Felt.IsU32
  rw [felt_ofNat_val_lt _]
  · have h2 := hrc.h2_lt
    have h3 := hrc.h3_lt
    omega
  · have h2 := hrc.h2_lt
    have h3 := hrc.h3_lt
    unfold GOLDILOCKS_PRIME
    omega

/-- `u32assert2` plus the range-checker bus guarantees both preserved outputs
are valid `u32` values. -/
theorem air_u32assert2_outputs_u32
    (f : Frame) (hsat : f.satisfies Constraints.u32assert2) (hrc : Frame.RangeChecked f) :
    (f.s' 0).IsU32 ∧ (f.s' 1).IsU32 := by
  rcases air_u32assert2_sound f hsat with ⟨hs0, hs1⟩
  rw [hs0, hs1]
  exact ⟨v_hi_isU32_of_rangeChecked f hrc, v_lo_isU32_of_rangeChecked f hrc⟩

end MidenLean.AIR.Proofs
