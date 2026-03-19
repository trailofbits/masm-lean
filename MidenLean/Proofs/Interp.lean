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

/-- toU64 neq in terms of limb neq: a != b iff
    a_lo != b_lo or a_hi != b_hi (given isU32). -/
theorem toU64_neq_iff (a_lo a_hi b_lo b_hi : Felt)
    (halo : a_lo.isU32 = true) (hahi : a_hi.isU32 = true)
    (hblo : b_lo.isU32 = true) (hbhi : b_hi.isU32 = true) :
    toU64 a_lo a_hi ≠ toU64 b_lo b_hi ↔
    a_lo ≠ b_lo ∨ a_hi ≠ b_hi := by
  rw [not_iff_comm, not_or, not_not, not_not]
  exact (toU64_eq_iff a_lo a_hi b_lo b_hi
    halo hahi hblo hbhi).symm

/-- testBit decomposition for toU64: toU64 lo hi =
    2^32 * hi.val + lo.val, so testBit decomposes
    by the 32-bit boundary. -/
private theorem toU64_testBit (lo hi : Felt)
    (hlo : lo.isU32 = true) (j : Nat) :
    (toU64 lo hi).testBit j =
    if j < 32 then lo.val.testBit j
    else hi.val.testBit (j - 32) := by
  simp only [toU64, Felt.isU32, decide_eq_true_eq] at *
  rw [show hi.val * 2 ^ 32 + lo.val =
    2 ^ 32 * hi.val + lo.val from by ring]
  exact Nat.testBit_two_pow_mul_add hi.val hlo j

/-- For n < GOLDILOCKS_PRIME, (Felt.ofNat n).val = n. -/
private theorem felt_ofNat_val (n : Nat)
    (h : n < GOLDILOCKS_PRIME) :
    (Felt.ofNat n).val = n := by
  simp only [Felt.ofNat]
  exact ZMod.val_natCast_of_lt h

/-- Helper: bitwise operation on u32 limbs is small
    enough for Felt.ofNat roundtrip. -/
private theorem bitwise_u32_lt_prime {a b : Nat}
    (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    a &&& b < GOLDILOCKS_PRIME ∧
    a ||| b < GOLDILOCKS_PRIME ∧
    a ^^^ b < GOLDILOCKS_PRIME := by
  unfold GOLDILOCKS_PRIME
  exact ⟨Nat.lt_of_le_of_lt (Nat.and_le_left ..)
      (by omega),
    Nat.lt_of_lt_of_le (Nat.or_lt_two_pow ha hb)
      (by omega),
    Nat.lt_of_lt_of_le (Nat.xor_lt_two_pow ha hb)
      (by omega)⟩

/-- isU32 in Nat.lt form, for passing to bitwise
    bounds lemmas. -/
private theorem isU32_lt (a : Felt)
    (h : a.isU32 = true) : a.val < 2 ^ 32 := by
  simp only [Felt.isU32, decide_eq_true_eq] at h
  exact h

/-- Felt.ofNat roundtrip for values under u32 bound. -/
private theorem felt_ofNat_isU32 (n : Nat)
    (h : n < 2 ^ 32) : (Felt.ofNat n).isU32 = true := by
  simp only [Felt.isU32, decide_eq_true_eq, Felt.ofNat]
  exact Nat.lt_of_lt_of_le
    (show (n : ZMod GOLDILOCKS_PRIME).val < 2 ^ 32 from by
      rw [ZMod.val_natCast_of_lt (by unfold GOLDILOCKS_PRIME; omega)]
      exact h)
    (le_refl _)

/-- Limb-level bitwise AND equals u64-level AND. -/
theorem toU64_and (a_lo a_hi b_lo b_hi : Felt)
    (halo : a_lo.isU32 = true)
    (hahi : a_hi.isU32 = true)
    (hblo : b_lo.isU32 = true)
    (_hbhi : b_hi.isU32 = true) :
    toU64 (Felt.ofNat (a_lo.val &&& b_lo.val))
          (Felt.ofNat (a_hi.val &&& b_hi.val)) =
    toU64 a_lo a_hi &&& toU64 b_lo b_hi := by
  have hlo_u32 : (a_lo.val &&& b_lo.val) < 2 ^ 32 :=
    Nat.lt_of_le_of_lt (Nat.and_le_left ..) (isU32_lt _ halo)
  have hhi_u32 : (a_hi.val &&& b_hi.val) < 2 ^ 32 :=
    Nat.lt_of_le_of_lt (Nat.and_le_left ..) (isU32_lt _ hahi)
  have hlo_is := felt_ofNat_isU32 _ hlo_u32
  have hhi_is := felt_ofNat_isU32 _ hhi_u32
  have hlo_p : (a_lo.val &&& b_lo.val) < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; omega
  have hhi_p : (a_hi.val &&& b_hi.val) < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; omega
  apply Nat.eq_of_testBit_eq; intro j
  rw [toU64_testBit _ _ hlo_is, Nat.testBit_and,
    toU64_testBit a_lo a_hi halo,
    toU64_testBit b_lo b_hi hblo,
    felt_ofNat_val _ hlo_p, felt_ofNat_val _ hhi_p]
  split <;> simp [Nat.testBit_and]

/-- Limb-level bitwise OR equals u64-level OR. -/
theorem toU64_or (a_lo a_hi b_lo b_hi : Felt)
    (halo : a_lo.isU32 = true)
    (hahi : a_hi.isU32 = true)
    (hblo : b_lo.isU32 = true)
    (hbhi : b_hi.isU32 = true) :
    toU64 (Felt.ofNat (a_lo.val ||| b_lo.val))
          (Felt.ofNat (a_hi.val ||| b_hi.val)) =
    toU64 a_lo a_hi ||| toU64 b_lo b_hi := by
  have hlo_u32 := Nat.or_lt_two_pow (isU32_lt _ halo) (isU32_lt _ hblo)
  have hhi_u32 := Nat.or_lt_two_pow (isU32_lt _ hahi) (isU32_lt _ hbhi)
  have hlo_is := felt_ofNat_isU32 _ hlo_u32
  have hhi_is := felt_ofNat_isU32 _ hhi_u32
  have hlo_p : (a_lo.val ||| b_lo.val) < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; omega
  have hhi_p : (a_hi.val ||| b_hi.val) < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; omega
  apply Nat.eq_of_testBit_eq; intro j
  rw [toU64_testBit _ _ hlo_is, Nat.testBit_or,
    toU64_testBit a_lo a_hi halo,
    toU64_testBit b_lo b_hi hblo,
    felt_ofNat_val _ hlo_p, felt_ofNat_val _ hhi_p]
  split <;> simp [Nat.testBit_or]

/-- Limb-level bitwise XOR equals u64-level XOR. -/
theorem toU64_xor (a_lo a_hi b_lo b_hi : Felt)
    (halo : a_lo.isU32 = true)
    (hahi : a_hi.isU32 = true)
    (hblo : b_lo.isU32 = true)
    (hbhi : b_hi.isU32 = true) :
    toU64 (Felt.ofNat (a_lo.val ^^^ b_lo.val))
          (Felt.ofNat (a_hi.val ^^^ b_hi.val)) =
    toU64 a_lo a_hi ^^^ toU64 b_lo b_hi := by
  have hlo_u32 := Nat.xor_lt_two_pow (isU32_lt _ halo) (isU32_lt _ hblo)
  have hhi_u32 := Nat.xor_lt_two_pow (isU32_lt _ hahi) (isU32_lt _ hbhi)
  have hlo_is := felt_ofNat_isU32 _ hlo_u32
  have hhi_is := felt_ofNat_isU32 _ hhi_u32
  have hlo_p : (a_lo.val ^^^ b_lo.val) < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; omega
  have hhi_p : (a_hi.val ^^^ b_hi.val) < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; omega
  apply Nat.eq_of_testBit_eq; intro j
  rw [toU64_testBit _ _ hlo_is, Nat.testBit_xor,
    toU64_testBit a_lo a_hi halo,
    toU64_testBit b_lo b_hi hblo,
    felt_ofNat_val _ hlo_p, felt_ofNat_val _ hhi_p]
  split <;> simp [Nat.testBit_xor]

/-- The cross-product carry chain used by wrapping_mul,
    shl, and other procedures correctly computes the
    low 64 bits of the full product.
    This is the key bridge between limb-level
    u32WidenMul accumulation and u64-level
    multiplication. -/
theorem cross_product_mod_2_64
    (a_lo a_hi b_lo b_hi : Nat) :
    let prod_lo := a_lo * b_lo
    let cross1 := b_hi * a_lo + prod_lo / 2 ^ 32
    let cross2 := b_lo * a_hi + cross1 % 2 ^ 32
    (cross2 % 2 ^ 32) * 2 ^ 32 + prod_lo % 2 ^ 32 =
    ((a_hi * 2 ^ 32 + a_lo) *
     (b_hi * 2 ^ 32 + b_lo)) % 2 ^ 64 := by
  -- The full product expands as:
  -- a_hi*b_hi*2^64 + (a_hi*b_lo + a_lo*b_hi)*2^32
  --   + a_lo*b_lo
  -- Mod 2^64, the a_hi*b_hi*2^64 term vanishes.
  -- The remaining low 64 bits decompose as:
  --   hi32 = ((a_hi*b_lo + a_lo*b_hi)*2^32
  --           + a_lo*b_lo) / 2^32 % 2^32
  --   lo32 = a_lo*b_lo % 2^32
  -- The carry chain computes exactly this.
  simp only
  -- Step 1: show the full product mod 2^64 equals
  -- the reduced product mod 2^64
  have h_expand : (a_hi * 2^32 + a_lo) *
      (b_hi * 2^32 + b_lo) =
      a_hi * b_hi * 2^64 +
      (a_hi * b_lo + a_lo * b_hi) * 2^32 +
      a_lo * b_lo := by ring
  rw [h_expand]
  -- Step 2: eliminate the 2^64 multiple
  have h_mod : (a_hi * b_hi * 2^64 +
      (a_hi * b_lo + a_lo * b_hi) * 2^32 +
      a_lo * b_lo) % 2^64 =
      ((a_hi * b_lo + a_lo * b_hi) * 2^32 +
       a_lo * b_lo) % 2^64 := by omega
  rw [h_mod]
  -- Decompose a_lo*b_lo via div/mod
  set p := a_lo * b_lo
  have hp := Nat.div_add_mod p (2^32)
  -- Rewrite the reduced product using carry chain
  have h3 : (a_hi * b_lo + a_lo * b_hi) * 2^32 +
      p = (a_hi * b_lo + a_lo * b_hi +
      p / 2^32) * 2^32 + p % 2^32 := by omega
  rw [h3]
  -- cross1 = b_hi*a_lo + p/2^32
  -- a_hi*b_lo + a_lo*b_hi + p/2^32
  --   = b_lo*a_hi + cross1  (by ring on first two)
  set c1 := b_hi * a_lo + p / 2^32
  have hc1_eq : a_hi * b_lo + a_lo * b_hi +
      p / 2^32 = b_lo * a_hi + c1 := by
    simp [c1]; ring
  rw [hc1_eq]
  -- Decompose c1 via div/mod
  have hc1 := Nat.div_add_mod c1 (2^32)
  -- b_lo*a_hi + c1
  -- = b_lo*a_hi + (c1/2^32)*2^32 + c1%2^32
  -- = (c1/2^32)*2^32 + (b_lo*a_hi + c1%2^32)
  -- = (c1/2^32)*2^32 + cross2
  set c2 := b_lo * a_hi + c1 % 2^32
  have h4 : (b_lo * a_hi + c1) * 2^32 +
      p % 2^32 = c1 / 2^32 * 2^64 +
      c2 * 2^32 + p % 2^32 := by omega
  rw [h4]
  -- Mod 2^64 eliminates the c1/2^32 * 2^64 term
  have h5 : (c1 / 2^32 * 2^64 + c2 * 2^32 +
      p % 2^32) % 2^64 =
      (c2 * 2^32 + p % 2^32) % 2^64 := by omega
  rw [h5]
  -- c2*2^32 = (c2%2^32)*2^32 + (c2/2^32)*2^64
  -- so mod 2^64 gives (c2%2^32)*2^32 + p%2^32
  -- which is < 2^64, so mod is identity
  have hc2_bound : c2 % 2^32 * 2^32 +
      p % 2^32 < 2^64 := by
    have := Nat.mod_lt c2 (show 0 < 2^32 by omega)
    have := Nat.mod_lt p (show 0 < 2^32 by omega)
    omega
  have h6 : (c2 * 2^32 + p % 2^32) % 2^64 =
      c2 % 2^32 * 2^32 + p % 2^32 := by
    have hc2dm := Nat.div_add_mod c2 (2^32)
    have : c2 * 2^32 = c2 / 2^32 * 2^64 +
        c2 % 2^32 * 2^32 := by omega
    rw [this]; omega
  rw [h6]

/-- Splitting a Felt into lo32/hi32 and reassembling
    via toU64 recovers the original value,
    provided it fits in 64 bits. -/
theorem felt_lo32_hi32_toU64 (n : Nat)
    (h : n < GOLDILOCKS_PRIME) :
    toU64 (Felt.ofNat n).lo32 (Felt.ofNat n).hi32 =
    n := by
  simp only [toU64, Felt.lo32, Felt.hi32, Felt.ofNat]
  have hval : (n : ZMod GOLDILOCKS_PRIME).val = n :=
    ZMod.val_natCast_of_lt h
  rw [hval]
  have h32_lo : n % 2^32 < GOLDILOCKS_PRIME := by
    unfold GOLDILOCKS_PRIME; omega
  have h32_hi : n / 2^32 < GOLDILOCKS_PRIME := by
    unfold GOLDILOCKS_PRIME at h ⊢
    omega
  rw [ZMod.val_natCast_of_lt h32_lo,
    ZMod.val_natCast_of_lt h32_hi]
  omega

/-- Count leading zeros of a 64-bit value represented
    as two u32 limbs. If hi is zero, count all 32 bits
    of hi plus leading zeros of lo. -/
def u64CountLeadingZeros (lo hi : Nat) : Nat :=
  if hi = 0 then u32CountLeadingZeros lo + 32
  else u32CountLeadingZeros hi

/-- Count trailing zeros of a 64-bit value represented
    as two u32 limbs. If lo is zero, count all 32 bits
    of lo plus trailing zeros of hi. -/
def u64CountTrailingZeros (lo hi : Nat) : Nat :=
  if lo = 0 then u32CountTrailingZeros hi + 32
  else u32CountTrailingZeros lo

/-- Count leading ones of a 64-bit value. -/
def u64CountLeadingOnes (lo hi : Nat) : Nat :=
  u64CountLeadingZeros (lo ^^^ (u32Max - 1))
    (hi ^^^ (u32Max - 1))

/-- Count trailing ones of a 64-bit value. -/
def u64CountTrailingOnes (lo hi : Nat) : Nat :=
  u64CountTrailingZeros (lo ^^^ (u32Max - 1))
    (hi ^^^ (u32Max - 1))

/-- The schoolbook carry chain for widening multiplication
    reconstructs the full 128-bit product. -/
theorem widening_mul_carry_chain
    (a_lo a_hi b_lo b_hi : Nat) :
    let pp := b_lo * a_lo
    let c1 := b_hi * a_lo + pp / 2^32
    let c2 := b_lo * a_hi + c1 % 2^32
    let hi := b_hi * a_hi + c2 / 2^32
    let wa := c1 / 2^32 + hi % 2^32
    (wa / 2^32 + hi / 2^32) * 2^96 +
    (wa % 2^32) * 2^64 +
    (c2 % 2^32) * 2^32 +
    pp % 2^32 =
    (a_hi * 2^32 + a_lo) *
    (b_hi * 2^32 + b_lo) := by
  simp only
  -- Name the elementary products for linearity
  set pp := b_lo * a_lo
  set ph := b_hi * a_lo
  set pl := b_lo * a_hi
  set hh := b_hi * a_hi
  have h_rhs :
      (a_hi * 2^32 + a_lo) * (b_hi * 2^32 + b_lo) =
      hh * 2^64 + pl * 2^32 + ph * 2^32 + pp := by
    simp [pp, pl, ph, hh]; ring
  rw [h_rhs]
  have d0 := Nat.div_add_mod pp (2^32)
  have d1 := Nat.div_add_mod (ph + pp / 2^32) (2^32)
  have d2 := Nat.div_add_mod
    (pl + (ph + pp / 2^32) % 2^32) (2^32)
  have d3 := Nat.div_add_mod
    (hh + (pl + (ph + pp / 2^32) % 2^32) /
      2^32) (2^32)
  have d4 := Nat.div_add_mod
    ((ph + pp / 2^32) / 2^32 +
      (hh + (pl + (ph + pp / 2^32) % 2^32) /
        2^32) % 2^32) (2^32)
  omega

/-- The divmod carry chain: given that the cross-product
    assertions and a == b*q + r checks all pass, the
    u64-level identity holds. This is a Nat-level lemma
    that omega can close. -/
theorem divmod_carry_chain
    (a_lo a_hi b_lo b_hi q_lo q_hi r_lo r_hi : Nat)
    -- Cross-product b*q fits in 64 bits
    (hp2 : (b_hi * q_lo + (b_lo * q_lo) / 2^32) /
      2^32 = 0)
    (hp3 : (b_lo * q_hi + (b_hi * q_lo +
      (b_lo * q_lo) / 2^32) % 2^32) / 2^32 = 0)
    (hqb : b_hi * q_hi = 0)
    -- a == b*q + r verification
    (hcarry : (r_hi + (b_lo * q_hi + (b_hi * q_lo +
      (b_lo * q_lo) / 2^32) % 2^32) % 2^32 +
      (r_lo + (b_lo * q_lo) % 2^32) / 2^32) /
      2^32 = 0)
    (hahi : a_hi = (r_hi + (b_lo * q_hi +
      (b_hi * q_lo + (b_lo * q_lo) / 2^32) % 2^32) %
      2^32 + (r_lo + (b_lo * q_lo) % 2^32) /
      2^32) % 2^32)
    (halo : a_lo = (r_lo +
      (b_lo * q_lo) % 2^32) % 2^32) :
    a_hi * 2^32 + a_lo =
    (b_hi * 2^32 + b_lo) * (q_hi * 2^32 + q_lo) +
    (r_hi * 2^32 + r_lo) := by
  -- Name the elementary products
  set p0 := b_lo * q_lo
  set c1 := b_hi * q_lo + p0 / 2^32
  set c2 := b_lo * q_hi + c1 % 2^32
  -- Decompose all div/mod pairs
  have d0 := Nat.div_add_mod p0 (2^32)
  have d1 := Nat.div_add_mod c1 (2^32)
  have d2 := Nat.div_add_mod c2 (2^32)
  have d3 := Nat.div_add_mod
    (r_lo + p0 % 2^32) (2^32)
  have d4 := Nat.div_add_mod
    (r_hi + c2 % 2^32 +
      (r_lo + p0 % 2^32) / 2^32) (2^32)
  -- Ring-expand the RHS product
  set ph := b_hi * q_lo
  set pl := b_lo * q_hi
  set hh := b_hi * q_hi
  have h_rhs :
      (b_hi * 2^32 + b_lo) * (q_hi * 2^32 + q_lo) =
      hh * 2^64 + pl * 2^32 + ph * 2^32 + p0 := by
    simp [p0, pl, ph, hh]; ring
  rw [halo, hahi, h_rhs]
  omega

/-- For shift >= 32, integer division of a 64-bit value
    by 2^shift reduces to dividing the high limb by
    2^(shift-32). -/
theorem shr_hi_only (lo hi shift : Nat)
    (hlo : lo < 2^32) (hge : 32 ≤ shift) :
    (hi * 2^32 + lo) / 2^shift =
    hi / 2^(shift - 32) := by
  have h2 : 2^shift = 2^32 * 2^(shift - 32) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [h2, ← Nat.div_div_eq_div_mul]
  have : (hi * 2^32 + lo) / 2^32 = hi := by
    rw [show hi * 2^32 + lo = lo + hi * 2^32 from
      by ring, Nat.add_mul_div_right lo hi (by omega)]
    omega
  rw [this]

/-- For shift < 32, the right-shift of a 64-bit value
    decomposes into hi/2^shift (high limb), lo/2^shift
    (low limb) plus (hi%2^shift)*2^(32-shift) (spillover
    from high to low). -/
theorem shr_lo_decomp (lo hi shift : Nat)
    (_hlo : lo < 2^32) (_hhi : hi < 2^32)
    (hlt : shift < 32) (_hpos : 0 < shift) :
    (hi / 2^shift) * 2^32 +
    (lo / 2^shift + (hi % 2^shift) *
      2^(32 - shift)) =
    (hi * 2^32 + lo) / 2^shift := by
  set k := 2^shift with hk_def
  set m := 2^(32 - shift) with hm_def
  have hkm : m * k = 2^32 := by
    rw [hm_def, hk_def, ← Nat.pow_add]; congr 1; omega
  have hk_pos : 0 < k := hk_def ▸ Nat.two_pow_pos _
  -- Step 1: rewrite to expose k factor
  rw [show hi * 2^32 + lo = lo + hi * m * k from
    by rw [← hkm]; ring,
    Nat.add_mul_div_right lo (hi * m) hk_pos]
  -- Goal: (hi/k)*2^32 + (lo/k + hi%k*m) = lo/k + hi*m
  -- Step 2: hi*m = (hi/k)*k*m + (hi%k)*m
  --             = (hi/k)*2^32 + (hi%k)*m
  have hd := Nat.div_add_mod hi k
  have h2 : hi * m = hi / k * (m * k) + hi % k * m :=
    by rw [Nat.mul_comm (hi / k) (m * k)]; nlinarith
  rw [hkm] at h2; omega

/-- In the Goldilocks field, 2^32 * (2^shift)^(-1) =
    2^(32-shift) for shift < 32. -/
theorem felt_pow2_inv_mul (shift : Nat)
    (hlt : shift < 32) :
    (4294967296 : Felt) *
    (Felt.ofNat (2^shift) : Felt)⁻¹ =
    Felt.ofNat (2^(32 - shift)) := by
  have hne : (Felt.ofNat (2^shift) : Felt) ≠ 0 := by
    simp only [Felt.ofNat, ne_eq]
    intro h
    have hval := congrArg ZMod.val h
    rw [ZMod.val_zero, ZMod.val_natCast_of_lt (by
      unfold GOLDILOCKS_PRIME
      calc 2^shift ≤ 2^31 :=
        Nat.pow_le_pow_right (by omega) (by omega)
      _ < _ := by omega)] at hval
    exact absurd hval (Nat.ne_of_gt
      (Nat.two_pow_pos shift))
  have hmul : Felt.ofNat (2^shift) *
      Felt.ofNat (2^(32-shift)) =
      (4294967296 : Felt) := by
    simp only [Felt.ofNat]
    push_cast
    show (2 : ZMod GOLDILOCKS_PRIME)^shift *
      (2 : ZMod GOLDILOCKS_PRIME)^(32-shift) =
      4294967296
    rw [← pow_add]
    show (2 : ZMod GOLDILOCKS_PRIME)^(shift + (32 - shift))
      = 4294967296
    rw [show shift + (32 - shift) = 32 from by omega]
    native_decide
  rw [← hmul, mul_comm (Felt.ofNat (2^shift)) _,
    mul_assoc, mul_inv_cancel₀ hne, mul_one]

end MidenLean
