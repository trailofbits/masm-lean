import MidenLean.Felt

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
    (halo : a_lo.isU32 = true) (hahi : a_hi.isU32 = true)
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
    (halo : a_lo.isU32 = true) (hahi : a_hi.isU32 = true)
    (hblo : b_lo.isU32 = true) (hbhi : b_hi.isU32 = true) :
    toU64 a_lo a_hi < toU64 b_lo b_hi ↔
    a_hi.val < b_hi.val ∨
    (a_hi.val = b_hi.val ∧ a_lo.val < b_lo.val) := by
  simp only [toU64, Felt.isU32, decide_eq_true_eq] at *
  omega

/-- u128 less-than in terms of 4 limbs (lexicographic
    from most significant). -/
theorem toU128_lt_iff (a0 a1 a2 a3 b0 b1 b2 b3 : Felt)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (ha2 : a2.isU32 = true) (ha3 : a3.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true)
    (hb2 : b2.isU32 = true) (_ : b3.isU32 = true) :
    toU128 a0 a1 a2 a3 < toU128 b0 b1 b2 b3 ↔
    a3.val < b3.val ∨
    (a3.val = b3.val ∧ (a2.val < b2.val ∨
    (a2.val = b2.val ∧ (a1.val < b1.val ∨
    (a1.val = b1.val ∧ a0.val < b0.val))))) := by
  simp only [toU128, Felt.isU32, decide_eq_true_eq] at *
  omega

end MidenLean
