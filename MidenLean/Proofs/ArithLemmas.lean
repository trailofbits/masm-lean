import MidenLean.Proofs.U32.Common

/-!
# Arithmetic automation lemmas

Consolidates isU32 propagation lemmas under `@[miden_u32]` and
Felt.ofNat value recovery lemmas under `@[miden_val]`.

`simp only [miden_u32]` closes `_.isU32 = true` goals.
`simp only [miden_val]` reduces `(Felt.ofNat expr).val` to `expr`.
-/

namespace MidenLean

-- Re-tag existing isU32 lemmas with @[miden_u32]

-- From Helpers.lean
attribute [miden_u32] felt_ofNat_isU32_of_lt
attribute [miden_u32] u32OverflowingSub_fst_isU32
attribute [miden_u32] u32OverflowingSub_snd_isU32
attribute [miden_u32] u32_mod_isU32
attribute [miden_u32] u32_div_2_32_isU32
attribute [miden_u32] u32_prod_div_isU32

-- From U32/Common.lean (in Proofs namespace)
attribute [miden_u32] Proofs.U32.felt5_isU32
attribute [miden_u32] Proofs.U32.felt31_isU32
attribute [miden_u32] Proofs.U32.felt32_isU32
attribute [miden_u32] Proofs.U32.felt64_isU32
attribute [miden_u32] Proofs.U32.felt128_isU32
attribute [miden_u32] Proofs.U32.lo32_isU32
attribute [miden_u32] Proofs.U32.hi32_isU32_of_val_lt_2_64
attribute [miden_u32] Proofs.U32.boolFelt_isU32
attribute [miden_u32] Proofs.U32.u32Shr_result_isU32
attribute [miden_u32] Proofs.u32_madd_div_isU32

-- Re-tag existing value recovery lemmas with @[miden_val]

-- From Helpers.lean
attribute [miden_val] felt_ofNat_val_lt
attribute [miden_val] u32OverflowingSub_snd_val

-- From U32/Common.lean
attribute [miden_val] Proofs.u32_mod_val
attribute [miden_val] Proofs.u32_madd_div_val
attribute [miden_val] Proofs.u32_add_div_val
attribute [miden_val] Proofs.u32_add3_div_val
attribute [miden_val] Proofs.u32_prod_mod_add_div_val

/-- Small powers of two remain below the Goldilocks prime. -/
@[miden_bound] theorem pow2_lt_goldilocks_of_lt64 (n : Nat) (h : n < 64) :
    2 ^ n < GOLDILOCKS_PRIME := by
  have h1 : 2 ^ n ≤ 2 ^ 63 := by
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : (2 : Nat) ^ 63 < GOLDILOCKS_PRIME := by
    unfold GOLDILOCKS_PRIME
    norm_num
  omega

/-- Small powers of two stay below `2^64` after embedding into `Felt`. -/
@[miden_bound] theorem felt_pow2_val_lt_2_64 (n : Nat) (h : n < 64) :
    (Felt.ofNat (2 ^ n)).val < 2 ^ 64 := by
  rw [felt_ofNat_val_lt _ (pow2_lt_goldilocks_of_lt64 n h)]
  exact Nat.pow_lt_pow_right (by omega) h

/-- Subtracting 64 from a u32 shift amount below 128 yields a value below 64. -/
@[miden_bound] theorem u32OverflowingSub64_snd_val_lt_64
    (shift : Felt)
    (hshift_u32 : shift.isU32 = true)
    (hshift_ge64 : ¬ shift.val < 64)
    (hshift_lt128 : shift.val < 128) :
    (Felt.ofNat (u32OverflowingSub shift.val 64).2).val < 64 := by
  have hge : shift.val >= 64 := by omega
  rw [u32OverflowingSub_snd_val shift.val 64
    (by simpa [Felt.isU32, decide_eq_true_eq] using hshift_u32)
    (by norm_num)]
  simp only [u32OverflowingSub, ge_iff_le, hge, ↓reduceIte, gt_iff_lt]
  omega

/-- The raw Nat result of subtracting 64 from a u32 shift amount below 128 is below 64. -/
@[miden_bound] theorem u32OverflowingSub64_snd_lt_64
    (shift : Felt)
    (hshift_u32 : shift.isU32 = true)
    (hshift_ge64 : ¬ shift.val < 64)
    (hshift_lt128 : shift.val < 128) :
    (u32OverflowingSub shift.val 64).2 < 64 := by
  have hshift_u32' : shift.val < 2 ^ 32 := by
    simpa [Felt.isU32, decide_eq_true_eq] using hshift_u32
  have hsnd_val :
      (Felt.ofNat (u32OverflowingSub shift.val 64).2).val = (u32OverflowingSub shift.val 64).2 := by
    exact u32OverflowingSub_snd_val shift.val 64 hshift_u32' (by norm_num)
  have hfelt_lt64 :=
    u32OverflowingSub64_snd_val_lt_64 shift hshift_u32 hshift_ge64 hshift_lt128
  rw [hsnd_val] at hfelt_lt64
  exact hfelt_lt64

/-- The boolean `Felt` literals are u32. These are what a case split on a
    borrow or comparison flag leaves behind, once `boolFelt_isU32`'s `if` has
    been reduced away. -/
@[miden_u32] theorem felt_zero_isU32 : (0 : Felt).isU32 = true :=
  felt_ofNat_isU32_of_lt 0 (by norm_num)

@[miden_u32] theorem felt_one_isU32 : (1 : Felt).isU32 = true :=
  felt_ofNat_isU32_of_lt 1 (by norm_num)

/-- The `Felt` literal `31`, the mask used by the u64 rotate procedures, has
    `val = 31`. -/
@[miden_val, miden_bound] theorem felt31_val : (31 : Felt).val = 31 :=
  felt_ofNat_val_lt 31 (by unfold GOLDILOCKS_PRIME; omega)

/-- Masking with `b` cannot exceed any bound on `b`. This discharges the
    `valLeq` shift bounds that `pow2` imposes on a masked shift amount, where
    the mask and the bound are both literals. -/
@[miden_bound] theorem land_le_of_right_le (a b n : Nat) (h : b ≤ n) : a &&& b ≤ n :=
  le_trans Nat.and_le_right h

/-- A power of two whose exponent is masked by a small literal round-trips
    through `Felt`: the mask bounds the exponent, so the power stays below the
    prime. The `b < 64` side condition is decidable for the literal masks that
    the rotate and shift procedures use. -/
@[miden_val, miden_bound] theorem felt_ofNat_pow2_land_val (a b : Nat) (hb : b < 64) :
    (Felt.ofNat (2 ^ (a &&& b))).val = 2 ^ (a &&& b) :=
  felt_ofNat_val_lt _ (pow2_lt_goldilocks_of_lt64 _ (lt_of_le_of_lt Nat.and_le_right hb))

/-- A power of two whose exponent is masked by a literal below `32` is u32. -/
@[miden_u32] theorem felt_ofNat_pow2_land_isU32 (a b : Nat) (hb : b < 32) :
    (Felt.ofNat (2 ^ (a &&& b))).isU32 = true := by
  apply felt_ofNat_isU32_of_lt
  calc 2 ^ (a &&& b) ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) Nat.and_le_right
    _ < 2 ^ 32 := Nat.pow_lt_pow_right (by omega) hb

/-- The borrow of `u32OverflowingSub` is set exactly on underflow. -/
@[miden_bound] theorem u32OverflowingSub_fst_eq_one_iff (a b : Nat) :
    (u32OverflowingSub a b).1 = 1 ↔ a < b := by
  unfold u32OverflowingSub; split <;> simp <;> omega

/-- The borrow of `u32OverflowingSub` is a boolean, after embedding into `Felt`.
    This is the `Precondition.isBool` obligation `cswap` leaves on a borrow. -/
@[miden_bound] theorem felt_ofNat_u32OverflowingSub_fst_isBool (a b : Nat) :
    Felt.ofNat (u32OverflowingSub a b).1 = 0 ∨ Felt.ofNat (u32OverflowingSub a b).1 = 1 := by
  unfold u32OverflowingSub; split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- MASM `or` applied to two borrow flags. The symbolic `or` node evaluates to
    the arithmetic form `x + y - x * y`; on the `0`/`1` values a borrow can take
    that is the disjunction of the two underflow conditions. This is the shape
    every multi-limb subtraction leaves where the VM combines the current limb's
    borrow with the propagated one. -/
@[miden_bound] theorem felt_borrow_or (u v w z : Nat) :
    Felt.ofNat (u32OverflowingSub u v).1 + Felt.ofNat (u32OverflowingSub w z).1 -
        Felt.ofNat (u32OverflowingSub u v).1 * Felt.ofNat (u32OverflowingSub w z).1 =
      if u < v ∨ w < z then 1 else 0 := by
  rw [u32OverflowingSub_borrow_ite u v, u32OverflowingSub_borrow_ite w z]
  by_cases huv : u < v <;> by_cases hwz : w < z <;>
    simp [huv, hwz]

-- New isU32 propagation lemmas.
--
-- The modulus is spelled `2 ^ 32` throughout, never `u32Max`: `simp` normalizes
-- goals towards `2 ^ 32` and the literal `4294967296`, and matching does not see
-- through the three spellings, so a bank lemma keyed on `u32Max` is true,
-- provable, and never fires. `midenSimpBankNumerals` in `MidenLean/Linters.lean`
-- enforces that, and there is a longer account of the failure mode in
-- `Symbolic/Reflect.lean`.

/-- The carry from adding three u32 values is u32. -/
@[miden_u32] theorem u32_add3_div_isU32 (a b c : Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) :
    (Felt.ofNat ((a.val + b.val + c.val) / 2^32)).isU32 = true := by
  apply felt_ofNat_isU32_of_lt
  simp only [Felt.isU32, decide_eq_true_eq] at ha hb hc; omega

/-- Bitwise AND of u32 values is u32. -/
@[miden_u32] theorem u32And_isU32 (a b : Felt)
    (ha : a.isU32 = true) :
    (Felt.ofNat (a.val &&& b.val)).isU32 = true := by
  apply felt_ofNat_isU32_of_lt
  simp only [Felt.isU32, decide_eq_true_eq] at ha
  exact lt_of_le_of_lt Nat.and_le_left ha

/-- Bitwise OR of u32 values is u32. -/
@[miden_u32] theorem u32Or_isU32 (a b : Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    (Felt.ofNat (a.val ||| b.val)).isU32 = true := by
  apply felt_ofNat_isU32_of_lt
  simp only [Felt.isU32, decide_eq_true_eq] at ha hb
  exact Nat.or_lt_two_pow ha hb

/-- Bitwise XOR of u32 values is u32. -/
@[miden_u32] theorem u32Xor_isU32 (a b : Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    (Felt.ofNat (a.val ^^^ b.val)).isU32 = true := by
  apply felt_ofNat_isU32_of_lt
  simp only [Felt.isU32, decide_eq_true_eq] at ha hb
  exact Nat.xor_lt_two_pow ha hb

/-- Bitwise NOT of a u32 value is u32. -/
@[miden_u32] theorem u32Not_isU32 (a : Felt)
    (ha : a.isU32 = true) :
    (Felt.ofNat (2 ^ 32 - 1 - a.val)).isU32 = true := by
  apply felt_ofNat_isU32_of_lt
  simp only [Felt.isU32, decide_eq_true_eq] at ha
  omega

-- There is no `u32Shl_isU32`: `u32_mod_isU32` above already closes
-- `(Felt.ofNat (n % 2 ^ 32)).isU32 = true` for any numerator, so a shift-specific
-- lemma in the canonical spelling would be subsumed by it.

/-- Right shift of a u32 value is u32. -/
@[miden_u32] theorem u32Shr_isU32 (a b : Felt)
    (ha : a.isU32 = true) :
    (Felt.ofNat (a.val / 2^b.val)).isU32 = true := by
  apply felt_ofNat_isU32_of_lt
  simp only [Felt.isU32, decide_eq_true_eq] at ha
  exact lt_of_le_of_lt (Nat.div_le_self _ _) ha

-- Felt-level isU32 wrappers (matching the hypothesis form from VCG preconditions)

/-- The result of u32OverflowingSub of u32 Felt values is u32. -/
@[miden_u32] theorem u32OverflowingSub_snd_isU32_felt (a b : Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    (Felt.ofNat (u32OverflowingSub a.val b.val).2).isU32 = true := by
  apply u32OverflowingSub_snd_isU32 <;> simp [Felt.isU32, decide_eq_true_eq] at * <;> assumption

-- New value recovery lemmas

/-- u32OverflowingSub borrow round-trips through Felt.ofNat. -/
@[miden_val] theorem u32OverflowingSub_fst_val (a b : Nat) :
    (Felt.ofNat (u32OverflowingSub a b).1).val = (u32OverflowingSub a b).1 := by
  apply felt_ofNat_val_lt
  exact u32_overflow_sub_fst_lt a b

/-- u32OverflowingSub result round-trips through Felt.ofNat for u32 Felt inputs. -/
@[miden_val] theorem u32OverflowingSub_snd_val_felt (a b : Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    (Felt.ofNat (u32OverflowingSub a.val b.val).2).val = (u32OverflowingSub a.val b.val).2 := by
  apply u32OverflowingSub_snd_val <;> simp [Felt.isU32, decide_eq_true_eq] at * <;> assumption

/-- The high 32 bits of a u32 product round-trips through Felt.ofNat. -/
@[miden_val] theorem u32_prod_div_val (a b : Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    (Felt.ofNat (a.val * b.val / 2^32)).val = a.val * b.val / 2^32 := by
  apply felt_ofNat_val_lt
  exact u32_prod_div_lt_prime a b ha hb

-- u32WideMul / u32WideMadd definition unfolding

/-- The low word of u32WideMul is a * b mod 2^32. -/
@[miden_val] theorem u32WideMul_fst (a b : Nat) :
    (u32WideMul a b).1 = a * b % u32Max := by unfold u32WideMul; rfl

/-- The high word of u32WideMul is a * b / 2^32. -/
@[miden_val] theorem u32WideMul_snd (a b : Nat) :
    (u32WideMul a b).2 = a * b / u32Max := by unfold u32WideMul; rfl

/-- The low word of u32WideMadd is (a * b + c) mod 2^32. -/
@[miden_val] theorem u32WideMadd_fst (a b c : Nat) :
    (u32WideMadd a b c).1 = (a * b + c) % u32Max := by unfold u32WideMadd; rfl

/-- The high word of u32WideMadd is (a * b + c) / 2^32. -/
@[miden_val] theorem u32WideMadd_snd (a b c : Nat) :
    (u32WideMadd a b c).2 = (a * b + c) / u32Max := by unfold u32WideMadd; rfl

-- u32WideMul / u32WideMadd isU32 propagation

/-- The low word of u32WideMul is always u32. -/
@[miden_u32] theorem u32WideMul_fst_isU32 (a b : Nat) :
    (Felt.ofNat (u32WideMul a b).1).isU32 = true := by
  apply felt_ofNat_isU32_of_lt
  rw [u32WideMul_fst]; unfold u32Max; exact Nat.mod_lt _ (by positivity)

/-- The high word of u32WideMul of u32 Felt inputs is u32. -/
@[miden_u32] theorem u32WideMul_snd_isU32_felt (a b : Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    (Felt.ofNat (u32WideMul a.val b.val).2).isU32 = true := by
  apply felt_ofNat_isU32_of_lt
  rw [u32WideMul_snd]; unfold u32Max
  simp only [Felt.isU32, decide_eq_true_eq] at ha hb
  exact Nat.div_lt_of_lt_mul (Nat.mul_lt_mul_of_lt_of_lt ha hb)

/-- The low word of u32WideMadd is always u32. -/
@[miden_u32] theorem u32WideMadd_fst_isU32 (a b c : Nat) :
    (Felt.ofNat (u32WideMadd a b c).1).isU32 = true := by
  apply felt_ofNat_isU32_of_lt
  rw [u32WideMadd_fst]; unfold u32Max; exact Nat.mod_lt _ (by positivity)

-- u32WideMul / u32WideMadd value recovery through Felt.ofNat

/-- u32WideMul low word round-trips through Felt.ofNat. -/
@[miden_val] theorem u32WideMul_fst_val (a b : Nat) :
    (Felt.ofNat (u32WideMul a b).1).val = (u32WideMul a b).1 := by
  apply felt_ofNat_val_lt; rw [u32WideMul_fst]
  unfold u32Max GOLDILOCKS_PRIME; exact lt_trans (Nat.mod_lt _ (by positivity)) (by omega)

/-- u32WideMul high word round-trips through Felt.ofNat for u32 inputs. -/
@[miden_val] theorem u32WideMul_snd_val_felt (a b : Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    (Felt.ofNat (u32WideMul a.val b.val).2).val = (u32WideMul a.val b.val).2 := by
  apply felt_ofNat_val_lt; rw [u32WideMul_snd]; unfold u32Max
  exact u32_prod_div_lt_prime a b ha hb

/-- u32WideMadd low word round-trips through Felt.ofNat. -/
@[miden_val] theorem u32WideMadd_fst_val (a b c : Nat) :
    (Felt.ofNat (u32WideMadd a b c).1).val = (u32WideMadd a b c).1 := by
  apply felt_ofNat_val_lt; rw [u32WideMadd_fst]
  unfold u32Max GOLDILOCKS_PRIME; exact lt_trans (Nat.mod_lt _ (by positivity)) (by omega)

end MidenLean
