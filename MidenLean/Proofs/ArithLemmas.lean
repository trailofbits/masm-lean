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

-- New isU32 propagation lemmas

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
    (Felt.ofNat (u32Max - 1 - a.val)).isU32 = true := by
  apply felt_ofNat_isU32_of_lt
  simp only [Felt.isU32, decide_eq_true_eq] at ha
  unfold u32Max; omega

/-- Left shift of a u32 value (mod 2^32) is u32. -/
@[miden_u32] theorem u32Shl_isU32 (a b : Felt) :
    (Felt.ofNat ((a.val * 2^b.val) % u32Max)).isU32 = true := by
  apply felt_ofNat_isU32_of_lt
  unfold u32Max; exact Nat.mod_lt _ (by positivity)

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
