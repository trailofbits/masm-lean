import MidenLean.Proofs.Helpers

namespace MidenLean.Proofs

open MidenLean

-- ============================================================================
-- U32 type: a 32-bit unsigned integer as a Felt with a u32 proof
-- ============================================================================

/-- A 32-bit unsigned integer represented as a Felt with a proof that it fits in 32 bits. -/
structure U32 where
  val : Felt
  isU32 : val.isU32 = true

instance : Coe U32 Felt where coe := U32.val

namespace U32

/-- The natural number value of the U32 (IsU32 Felt.val). -/
abbrev toNat (x : U32) : Nat := x.val.val

theorem val_lt (x : U32) : x.val.val < 2^32 := by
  have := x.isU32; simp [Felt.isU32, decide_eq_true_eq] at this; exact this

theorem toNat_lt (x : U32) : x.toNat < 2^32 := x.val_lt

theorem val_lt_prime (x : U32) : x.val.val < GOLDILOCKS_PRIME := by
  have := x.val_lt; unfold GOLDILOCKS_PRIME; omega

/-- Construct a U32 from a natural number (taken mod 2^32). -/
def ofNat (n : Nat) : U32 where
  val := Felt.ofNat (n % 2^32)
  isU32 := u32_mod_isU32 n

/-- Construct a U32 from a natural number known to be < 2^32. -/
def ofNat_lt (n : Nat) (h : n < 2^32) : U32 where
  val := Felt.ofNat n
  isU32 := felt_ofNat_isU32_of_lt n h

-- ============================================================================
-- Constant U32 values that appear frequently in proofs
-- ============================================================================

theorem felt5_isU32 : (5 : Felt).isU32 = true :=
  felt_ofNat_isU32_of_lt 5 (by norm_num)

theorem felt31_isU32 : (31 : Felt).isU32 = true :=
  felt_ofNat_isU32_of_lt 31 (by norm_num)

theorem felt32_isU32 : (32 : Felt).isU32 = true :=
  felt_ofNat_isU32_of_lt 32 (by norm_num)

theorem felt64_isU32 : (64 : Felt).isU32 = true :=
  felt_ofNat_isU32_of_lt 64 (by norm_num)

theorem felt128_isU32 : (128 : Felt).isU32 = true :=
  felt_ofNat_isU32_of_lt 128 (by norm_num)

-- ============================================================================
-- Reusable isU32 results
-- ============================================================================

/-- lo32 is always U32. -/
theorem lo32_isU32 (a : Felt) : a.lo32.isU32 = true := by
  simp only [Felt.lo32]; exact u32_mod_isU32 a.val

/-- hi32 is U32 when the input is < 2^64. -/
theorem hi32_isU32_of_val_lt_2_64 (a : Felt) (h : a.val < 2 ^ 64) :
    a.hi32.isU32 = true := by
  unfold Felt.hi32
  apply felt_ofNat_isU32_of_lt
  exact Nat.div_lt_of_lt_mul (by omega)

/-- A boolean-to-Felt value (if p then 1 else 0) is U32. -/
theorem boolFelt_isU32 (p : Bool) : (if p then (1 : Felt) else 0).isU32 = true := by
  cases p <;> simp [Felt.isU32, Felt.val_one']

/-- u32 shift result is U32. -/
theorem u32Shr_result_isU32 (a shift : Felt)
    (ha : a.isU32 = true) :
    (Felt.ofNat (a.val / 2 ^ shift.val)).isU32 = true := by
  apply felt_ofNat_isU32_of_lt
  have ha_lt : a.val < 2 ^ 32 := by
    simpa [Felt.isU32, decide_eq_true_eq] using ha
  exact lt_of_le_of_lt (Nat.div_le_self _ _) ha_lt

-- Extensionality: two U32s with the same val are equal.
@[ext] theorem ext {a b : U32} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp_all

end U32

end MidenLean.Proofs
