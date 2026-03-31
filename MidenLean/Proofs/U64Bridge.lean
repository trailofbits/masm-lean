/-
  MidenLean.Proofs.U64Bridge
  Bridge lemmas connecting implementation-level u64 comparison specs
  to mathematical u64 comparison.

  The existing proofs express comparison results in terms of
  u32OverflowingSub intermediate values. These bridge lemmas connect
  that formulation to the natural mathematical comparison on
  reconstructed u64 values.
-/
import MidenLean.Proofs.Helpers
import MidenLean.Proofs.U64.Lt
import MidenLean.Proofs.U64.Gt
import MidenLean.Proofs.U64.Lte
import MidenLean.Proofs.U64.Gte

namespace MidenLean.Proofs

open MidenLean

-- ============================================================================
-- u64 reconstruction
-- ============================================================================

/-- Reconstruct a u64 value from its two u32 limbs. -/
def toU64 (lo hi : Felt) : Nat :=
  hi.val * 2^32 + lo.val

-- ============================================================================
-- Core bridge: u32OverflowingSub-based comparison ↔ mathematical comparison
-- ============================================================================

/-- The borrow from u32OverflowingSub equals `decide (a < b)`. -/
theorem u32OverflowingSub_fst_eq_decide (a b : Nat) :
    (u32OverflowingSub a b).1 = if a < b then 1 else 0 := by
  unfold u32OverflowingSub
  split <;> omega

/-- The diff from u32OverflowingSub is zero iff a = b (for valid u32 inputs). -/
theorem u32OverflowingSub_snd_eq_zero_iff (a b : Nat) (ha : a < 2^32) (hb : b < 2^32) :
    (u32OverflowingSub a b).2 = 0 ↔ a = b := by
  unfold u32OverflowingSub
  constructor
  · intro h; split at h <;> omega
  · intro h; subst h; simp [u32OverflowingSub]; omega

/-- The comparison `borrow_hi || (hi_eq && borrow_lo)` is equivalent to
    the mathematical u64 less-than. -/
theorem u64_lt_bridge (a_lo a_hi b_lo b_hi : Nat)
    (ha_lo : a_lo < 2^32) (ha_hi : a_hi < 2^32)
    (hb_lo : b_lo < 2^32) (hb_hi : b_hi < 2^32) :
    (decide (a_hi < b_hi) || (decide ((u32OverflowingSub a_hi b_hi).2 = 0) && decide (a_lo < b_lo)))
    = decide (a_hi * 2^32 + a_lo < b_hi * 2^32 + b_lo) := by
  rw [u32OverflowingSub_snd_eq_zero_iff _ _ ha_hi hb_hi]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro (h | ⟨h_eq, h_lo⟩) <;> omega
  · intro h
    by_cases h_hi : a_hi < b_hi
    · left; exact h_hi
    · right; constructor <;> omega

/-- u64 greater-than bridge. -/
theorem u64_gt_bridge (a_lo a_hi b_lo b_hi : Nat)
    (ha_lo : a_lo < 2^32) (ha_hi : a_hi < 2^32)
    (hb_lo : b_lo < 2^32) (hb_hi : b_hi < 2^32) :
    (decide (b_hi < a_hi) || (decide ((u32OverflowingSub b_hi a_hi).2 = 0) && decide (b_lo < a_lo)))
    = decide (a_hi * 2^32 + a_lo > b_hi * 2^32 + b_lo) := by
  rw [show (a_hi * 2^32 + a_lo > b_hi * 2^32 + b_lo) = (b_hi * 2^32 + b_lo < a_hi * 2^32 + a_lo) from by omega]
  exact u64_lt_bridge b_lo b_hi a_lo a_hi hb_lo hb_hi ha_lo ha_hi

-- ============================================================================
-- Strengthened comparison theorems
-- ============================================================================

/-- u64.lt computes mathematical less-than on u64 values. -/
theorem u64_lt_math
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest)
    (ha_lo : a_lo.isU32 = true) (ha_hi : a_hi.isU32 = true)
    (hb_lo : b_lo.isU32 = true) (hb_hi : b_hi.isU32 = true) :
    exec 20 s Miden.Core.U64.lt =
    some (s.withStack (
      (if toU64 a_lo a_hi < toU64 b_lo b_hi then (1 : Felt) else 0) :: rest)) := by
  -- Use the existing implementation-level proof
  rw [u64_lt_correct a_lo a_hi b_lo b_hi rest s hs ha_lo ha_hi hb_lo hb_hi]
  -- Bridge: show the two formulations are equal
  congr 1; congr 1; congr 1
  unfold toU64
  sorry -- needs: bridge the Felt.ofNat/BEq formulation to the decide formulation

/-- u64.gt computes mathematical greater-than on u64 values. -/
theorem u64_gt_math
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest)
    (ha_lo : a_lo.isU32 = true) (ha_hi : a_hi.isU32 = true)
    (hb_lo : b_lo.isU32 = true) (hb_hi : b_hi.isU32 = true) :
    exec 20 s Miden.Core.U64.gt =
    some (s.withStack (
      (if toU64 a_lo a_hi > toU64 b_lo b_hi then (1 : Felt) else 0) :: rest)) := by
  rw [u64_gt_correct a_lo a_hi b_lo b_hi rest s hs ha_lo ha_hi hb_lo hb_hi]
  congr 1; congr 1; congr 1
  unfold toU64
  sorry -- same bridge needed

end MidenLean.Proofs
