import MidenLean.Proofs.Helpers

namespace MidenLean

/-- Interpret two u32 limbs as a 64-bit unsigned integer.
    lo is the low 32 bits, hi is the high 32 bits. -/
def toU64 (lo hi : Felt) : Nat :=
  hi.val * 2^32 + lo.val

/-- Interpret four u32 limbs as a 128-bit unsigned integer.
    a0 is the least significant limb, a3 the most significant.
    This matches Miden's word layout where a3 is at stack
    position 3 (deepest of the word). -/
def toU128 (a0 a1 a2 a3 : Felt) : Nat :=
  a3.val * 2^96 + a2.val * 2^64 + a1.val * 2^32 + a0.val

theorem toU64_lt_2_64 (lo hi : Felt)
    (hlo : lo.isU32 = true) (hhi : hi.isU32 = true) :
    toU64 lo hi < 2^64 := by
  simp only [toU64, Felt.isU32, decide_eq_true_eq] at *
  omega

theorem toU128_lt_2_128 (a0 a1 a2 a3 : Felt)
    (h0 : a0.isU32 = true) (h1 : a1.isU32 = true)
    (h2 : a2.isU32 = true) (h3 : a3.isU32 = true) :
    toU128 a0 a1 a2 a3 < 2^128 := by
  simp only [toU128, Felt.isU32, decide_eq_true_eq] at *
  omega

/-- Two u64 values are equal iff their limbs are pairwise
    equal (given isU32 on all limbs). -/
theorem toU64_eq_iff (a_lo a_hi b_lo b_hi : Felt)
    (halo : a_lo.isU32 = true) (_hahi : a_hi.isU32 = true)
    (hblo : b_lo.isU32 = true) (hbhi : b_hi.isU32 = true) :
    toU64 a_lo a_hi = toU64 b_lo b_hi ↔
    a_lo = b_lo ∧ a_hi = b_hi := by
  simp only [toU64, Felt.isU32, decide_eq_true_eq] at *
  constructor
  · intro h
    have hmod : a_lo.val = b_lo.val := by omega
    have hdiv : a_hi.val = b_hi.val := by omega
    exact ⟨ZMod.val_injective _ hmod, ZMod.val_injective _ hdiv⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- u64 less-than in terms of limbs: a < b iff
    a_hi < b_hi, or a_hi = b_hi and a_lo < b_lo. -/
theorem toU64_lt_iff (a_lo a_hi b_lo b_hi : Felt)
    (halo : a_lo.isU32 = true) (_hahi : a_hi.isU32 = true)
    (hblo : b_lo.isU32 = true) (_hbhi : b_hi.isU32 = true) :
    toU64 a_lo a_hi < toU64 b_lo b_hi ↔
    a_hi.val < b_hi.val ∨
    (a_hi.val = b_hi.val ∧ a_lo.val < b_lo.val) := by
  simp only [toU64, Felt.isU32, decide_eq_true_eq] at *
  omega

/-- u128 less-than in terms of 4 limbs (lexicographic
    from most significant). -/
theorem toU128_lt_iff (a0 a1 a2 a3 b0 b1 b2 b3 : Felt)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (ha2 : a2.isU32 = true) (_ha3 : a3.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true)
    (hb2 : b2.isU32 = true) (_ : b3.isU32 = true) :
    toU128 a0 a1 a2 a3 < toU128 b0 b1 b2 b3 ↔
    a3.val < b3.val ∨
    (a3.val = b3.val ∧ (a2.val < b2.val ∨
    (a2.val = b2.val ∧ (a1.val < b1.val ∨
    (a1.val = b1.val ∧ a0.val < b0.val))))) := by
  simp only [toU128, Felt.isU32, decide_eq_true_eq] at *
  omega

/-- u32OverflowingSub a b has .2 == 0 (as Felt) iff
    a = b, given both are u32 values. -/
theorem u32OverflowingSub_snd_eq_zero_iff (a b : Nat)
    (ha : a < 2^32) (hb : b < 2^32) :
    (Felt.ofNat (u32OverflowingSub a b).2 == (0 : Felt))
    = decide (a = b) := by
  unfold u32OverflowingSub u32Max Felt.ofNat
  simp only [Bool.beq_eq_decide_eq]
  rw [decide_eq_decide]
  split
  · -- a >= b case: result = a - b
    rename_i h
    have hlt : a - b < GOLDILOCKS_PRIME := by
      unfold GOLDILOCKS_PRIME; omega
    constructor
    · intro heq
      have hval := ZMod.val_natCast (n := GOLDILOCKS_PRIME) (a - b)
      rw [heq, ZMod.val_zero, Nat.mod_eq_of_lt hlt] at hval
      omega
    · intro heq; subst heq; simp
  · -- a < b case: result = 2^32 + a - b
    rename_i h
    have hlt : 2^32 - b + a < GOLDILOCKS_PRIME := by
      unfold GOLDILOCKS_PRIME; omega
    constructor
    · intro heq
      have hval := ZMod.val_natCast (n := GOLDILOCKS_PRIME) (2^32 - b + a)
      rw [heq, ZMod.val_zero, Nat.mod_eq_of_lt hlt] at hval
      omega
    · intro heq; omega

/-- The u64.lt comparison condition (using u32OverflowingSub)
    equals decide (toU64 a < toU64 b). -/
theorem u64_lt_condition_eq (a_lo a_hi b_lo b_hi : Felt)
    (halo : a_lo.isU32 = true) (hahi : a_hi.isU32 = true)
    (hblo : b_lo.isU32 = true) (hbhi : b_hi.isU32 = true) :
    (decide (a_hi.val < b_hi.val) ||
     ((Felt.ofNat (u32OverflowingSub a_hi.val b_hi.val).2
       == (0 : Felt)) &&
      decide (a_lo.val < b_lo.val))) =
    decide (toU64 a_lo a_hi < toU64 b_lo b_hi) := by
  simp only [Felt.isU32, decide_eq_true_eq] at hahi hbhi
  rw [u32OverflowingSub_snd_eq_zero_iff _ _ hahi hbhi]
  rw [show decide (toU64 a_lo a_hi < toU64 b_lo b_hi) =
    decide (a_hi.val < b_hi.val ∨
      (a_hi.val = b_hi.val ∧ a_lo.val < b_lo.val)) from by
    congr 1
    exact propext (toU64_lt_iff a_lo a_hi b_lo b_hi
      halo (by simp [Felt.isU32, decide_eq_true_eq]; omega)
      hblo (by simp [Felt.isU32, decide_eq_true_eq]; omega))]
  simp only [Bool.decide_or, Bool.decide_and]

end MidenLean
