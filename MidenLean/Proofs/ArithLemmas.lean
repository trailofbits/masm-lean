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

-- New isU32 propagation lemmas

/-- The carry from adding three u32 values is u32. -/
@[miden_u32] theorem u32_add3_div_isU32 (a b c : Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) :
    (Felt.ofNat ((a.val + b.val + c.val) / 2^32)).isU32 = true := by
  apply felt_ofNat_isU32_of_lt
  simp only [Felt.isU32, decide_eq_true_eq] at ha hb hc; omega

/-- Bitwise AND of u32 values is u32. -/
@[miden_u32] theorem u32And_isU32 (a b : Felt)
    (ha : a.isU32 = true) (_hb : b.isU32 = true) :
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
@[miden_u32] theorem u32Shl_isU32 (a b : Felt)
    (_ha : a.isU32 = true) (_hb : b.isU32 = true) :
    (Felt.ofNat ((a.val * 2^b.val) % u32Max)).isU32 = true := by
  apply felt_ofNat_isU32_of_lt
  unfold u32Max; exact Nat.mod_lt _ (by positivity)

/-- Right shift of a u32 value is u32. -/
@[miden_u32] theorem u32Shr_isU32 (a b : Felt)
    (ha : a.isU32 = true) (_hb : b.isU32 = true) :
    (Felt.ofNat (a.val / 2^b.val)).isU32 = true := by
  apply felt_ofNat_isU32_of_lt
  simp only [Felt.isU32, decide_eq_true_eq] at ha
  exact lt_of_le_of_lt (Nat.div_le_self _ _) ha

-- New value recovery lemmas

/-- u32OverflowingSub borrow round-trips through Felt.ofNat. -/
@[miden_val] theorem u32OverflowingSub_fst_val (a b : Nat) :
    (Felt.ofNat (u32OverflowingSub a b).1).val = (u32OverflowingSub a b).1 := by
  apply felt_ofNat_val_lt
  exact u32_overflow_sub_fst_lt a b

/-- The high 32 bits of a u32 product round-trips through Felt.ofNat. -/
@[miden_val] theorem u32_prod_div_val (a b : Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    (Felt.ofNat (a.val * b.val / 2^32)).val = a.val * b.val / 2^32 := by
  apply felt_ofNat_val_lt
  exact u32_prod_div_lt_prime a b ha hb

end MidenLean
