import MidenLean.Proofs.Helpers
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean

/-- Procedure environment for manual u64 proofs that call other u64 procedures. -/
def u64ProcEnv : ProcEnv := fun name =>
  match name with
  | "overflowing_add" => some Miden.Core.U64.overflowing_add
  | "gt" => some Miden.Core.U64.gt
  | "lt" => some Miden.Core.U64.lt
  | "divmod" => some Miden.Core.U64.divmod
  | "wrapping_mul" => some Miden.Core.U64.wrapping_mul
  | _ => none

-- ============================================================================
-- U64 type: a 64-bit unsigned integer as two u32 Felt limbs
-- ============================================================================

/-- A 64-bit unsigned integer represented as two u32 Felt limbs (little-endian).
    `lo` is the low 32-bit limb, `hi` is the high 32-bit limb.
    The u32 invariant is enforced by the structure fields. -/
structure U64 where
  lo : Felt
  hi : Felt
  lo_u32 : lo.isU32 = true
  hi_u32 : hi.isU32 = true

namespace U64

/-- Reconstruct the natural number value: `hi * 2^32 + lo`. -/
def toNat (x : U64) : Nat := x.hi.val * 2^32 + x.lo.val

theorem toNat_lt (x : U64) : x.toNat < 2^64 := by
  unfold toNat
  have hlo := x.lo_u32; have hhi := x.hi_u32
  simp only [Felt.isU32, decide_eq_true_eq] at *
  omega

theorem toNat_def (x : U64) : x.toNat = x.hi.val * 2^32 + x.lo.val := rfl

end U64

-- ============================================================================
-- Comparison bridging lemma
-- ============================================================================

/-- The hi_eq check in comparison formulas is equivalent to a_hi.val = b_hi.val
    for u32 inputs. -/
theorem hi_eq_iff_val_eq (a_hi b_hi : Felt)
    (ha : a_hi.isU32 = true) (hb : b_hi.isU32 = true) :
    (Felt.ofNat (u32OverflowingSub a_hi.val b_hi.val).2 == (0 : Felt)) =
    decide (a_hi.val = b_hi.val) := by
  simp only [Felt.isU32, decide_eq_true_eq] at ha hb
  -- LHS is decide (Felt.ofNat ... = 0)
  show decide _ = decide _
  apply decide_eq_decide.mpr
  constructor
  · intro h
    have hval := u32OverflowingSub_snd_val a_hi.val b_hi.val (by omega) (by omega)
    have : (Felt.ofNat (u32OverflowingSub a_hi.val b_hi.val).2).val = 0 := by
      rw [h]; rfl
    rw [hval] at this
    exact (u32OverflowingSub_snd_eq_zero_iff a_hi.val b_hi.val (by omega) (by omega)).mp this
  · intro h
    have : (u32OverflowingSub a_hi.val b_hi.val).2 = 0 :=
      (u32OverflowingSub_snd_eq_zero_iff a_hi.val b_hi.val (by omega) (by omega)).mpr h
    simp [this, Felt.ofNat]

/-- The borrow-based comparison formula is equivalent to `a.toNat < b.toNat`.

    This bridges the low-level formula used in `u64_lt_raw` to the
    high-level mathematical comparison. -/
theorem u64_borrow_iff_lt (a b : U64) :
    let borrow_lo := decide (a.lo.val < b.lo.val)
    let borrow_hi := decide (a.hi.val < b.hi.val)
    let hi_eq := Felt.ofNat (u32OverflowingSub a.hi.val b.hi.val).2 == (0 : Felt)
    (borrow_hi || (hi_eq && borrow_lo)) = decide (a.toNat < b.toNat) := by
  simp only
  rw [hi_eq_iff_val_eq a.hi b.hi a.hi_u32 b.hi_u32]
  simp only [U64.toNat]
  have halo := a.lo_u32; have hahi := a.hi_u32
  have hblo := b.lo_u32; have hbhi := b.hi_u32
  simp only [Felt.isU32, decide_eq_true_eq] at halo hahi hblo hbhi
  -- Case split on all three boolean decisions
  cases h1 : decide (a.hi.val < b.hi.val) <;>
  cases h2 : decide (a.hi.val = b.hi.val) <;>
  cases h3 : decide (a.lo.val < b.lo.val) <;>
  simp_all [decide_eq_true_eq, decide_eq_false_iff_not] <;>
  omega

-- ============================================================================
-- Arithmetic bridging lemmas
-- ============================================================================

/-- The carry-based addition formula reconstructs to `a.toNat + b.toNat`. -/
theorem u64_carry_add_spec (a_lo a_hi b_lo b_hi : Nat)
    (ha_lo : a_lo < 2^32) (ha_hi : a_hi < 2^32)
    (hb_lo : b_lo < 2^32) (hb_hi : b_hi < 2^32) :
    let lo_sum := a_lo + b_lo
    let carry := lo_sum / 2^32
    let hi_sum := a_hi + b_hi + carry
    let overflow := hi_sum / 2^32
    overflow * 2^64 + (hi_sum % 2^32) * 2^32 + lo_sum % 2^32 =
    (a_hi * 2^32 + a_lo) + (b_hi * 2^32 + b_lo) := by
  omega

/-- The overflowing_sub borrow is equivalent to `a.toNat < b.toNat`. -/
theorem u64_sub_borrow_iff_lt (a b : U64) :
    let sub_lo := u32OverflowingSub a.lo.val b.lo.val
    let sub_hi := u32OverflowingSub a.hi.val b.hi.val
    let borrow_adj := decide (sub_hi.2 < sub_lo.1)
    let borrow_hi := decide (a.hi.val < b.hi.val)
    (borrow_adj || borrow_hi) = decide (a.toNat < b.toNat) := by
  simp only [U64.toNat]
  have halo := a.lo_u32; have hahi := a.hi_u32
  have hblo := b.lo_u32; have hbhi := b.hi_u32
  simp only [Felt.isU32, decide_eq_true_eq] at halo hahi hblo hbhi
  unfold u32OverflowingSub u32Max
  -- Resolve all if-then-else conditions, then case-split on decides
  split_ifs <;>
  cases h1 : decide (a.hi.val < b.hi.val) <;>
  simp_all [decide_eq_true_eq, decide_eq_false_iff_not] <;>
  omega

end MidenLean.Proofs
