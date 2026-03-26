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

/-- `Felt.ofNat` round-trips through the underlying natural value of a `U32`. -/
@[simp] theorem ofNat_val (x : U32) : Felt.ofNat x.val.val = x.val := by
  apply ZMod.val_injective
  rw [felt_ofNat_val_lt _ x.val_lt_prime]

@[simp] theorem ofNat_toNat (n : Nat) : (U32.ofNat n).toNat = n % 2^32 :=
  felt_ofNat_val_lt _ (u32_mod_lt_prime n)

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

theorem toNat_injective : Function.Injective U32.toNat := by
  intro a b h
  apply ext
  apply ZMod.val_injective
  simpa [U32.toNat] using h

theorem eq_of_toNat_eq {a b : U32} (h : a.toNat = b.toNat) : a = b :=
  toNat_injective h

end U32

-- ============================================================================
-- Reusable U32 multiply-add (madd) lemmas
-- ============================================================================
-- These capture the bounds and round-trip properties of the u32WidenMadd
-- pattern: given u32 values a, b, c, compute (a*b + c) and split into
-- low 32 bits (mod 2^32) and high 32 bits (div 2^32).

/-- The sum `a*b + c` for u32 values is at most `2^64 - 2^32`. -/
theorem u32_madd_sum_le (a b c : Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) :
    a.val * b.val + c.val ≤ (2^32 - 1) * (2^32 - 1) + (2^32 - 1) := by
  simp only [Felt.isU32, decide_eq_true_eq] at ha hb hc
  exact Nat.add_le_add (Nat.mul_le_mul (by omega) (by omega)) (by omega)

/-- The sum `a*b + c` for u32 values fits below the Goldilocks prime. -/
theorem u32_madd_sum_lt_prime (a b c : Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) :
    a.val * b.val + c.val < GOLDILOCKS_PRIME := by
  have := u32_madd_sum_le a b c ha hb hc
  unfold GOLDILOCKS_PRIME; omega

/-- The high 32 bits of `a*b + c` (for u32 a, b, c) fit in 32 bits. -/
@[miden_bound] theorem u32_madd_div_lt_2_32 (a b c : Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) :
    (a.val * b.val + c.val) / 2 ^ 32 < 2 ^ 32 := by
  have := u32_madd_sum_le a b c ha hb hc
  calc (a.val * b.val + c.val) / 2 ^ 32
      ≤ ((2^32 - 1) * (2^32 - 1) + (2^32 - 1)) / 2 ^ 32 := Nat.div_le_div_right this
    _ < 2 ^ 32 := by native_decide

/-- The high 32 bits of `a*b + c` (for u32 a, b, c) are U32 as a Felt. -/
@[miden_bound] theorem u32_madd_div_isU32 (a b c : Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) :
    (Felt.ofNat ((a.val * b.val + c.val) / 2 ^ 32)).isU32 = true :=
  felt_ofNat_isU32_of_lt _ (u32_madd_div_lt_2_32 a b c ha hb hc)

/-- `Felt.ofNat` of any value mod `2^32` round-trips through `.val`. -/
@[miden_bound] theorem u32_mod_val (n : Nat) :
    (Felt.ofNat (n % 2 ^ 32)).val = n % 2 ^ 32 :=
  felt_ofNat_val_lt _ (u32_val_lt_prime _ (Nat.mod_lt _ (by norm_num)))

/-- `Felt.ofNat` of the high 32 bits of `a*b + c` round-trips through `.val`. -/
@[miden_bound] theorem u32_madd_div_val (a b c : Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) :
    (Felt.ofNat ((a.val * b.val + c.val) / 2 ^ 32)).val =
    (a.val * b.val + c.val) / 2 ^ 32 :=
  felt_ofNat_val_lt _ (u32_val_lt_prime _ (u32_madd_div_lt_2_32 a b c ha hb hc))

/-- The high 32 bits of `a*b` (for u32 a, b) fit in 32 bits. -/
@[miden_bound] theorem u32_prod_div_lt_2_32 (a b : Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    a.val * b.val / 2 ^ 32 < 2 ^ 32 := by
  simp only [Felt.isU32, decide_eq_true_eq] at ha hb
  have hprod : a.val * b.val ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := by
    exact Nat.mul_le_mul (Nat.le_pred_of_lt ha) (Nat.le_pred_of_lt hb)
  calc
    a.val * b.val / 2 ^ 32 ≤ ((2 ^ 32 - 1) * (2 ^ 32 - 1)) / 2 ^ 32 := by
      exact Nat.div_le_div_right hprod
    _ < 2 ^ 32 := by native_decide

/-- Adding a u32 value to the low half of a u32 product carries by at most one word. -/
@[miden_bound] theorem u32_prod_mod_add_div_le_one (a b c : Felt)
    (_ha : a.isU32 = true) (_hb : b.isU32 = true) (hc : c.isU32 = true) :
    ((a.val * b.val) % 2 ^ 32 + c.val) / 2 ^ 32 ≤ 1 := by
  simp only [Felt.isU32, decide_eq_true_eq] at hc
  have hmod : (a.val * b.val) % 2 ^ 32 ≤ 2 ^ 32 - 1 := by
    exact Nat.le_pred_of_lt (Nat.mod_lt _ (by positivity))
  calc
    ((a.val * b.val) % 2 ^ 32 + c.val) / 2 ^ 32
        ≤ ((2 ^ 32 - 1) + (2 ^ 32 - 1)) / 2 ^ 32 := by
          apply Nat.div_le_div_right
          omega
    _ ≤ 1 := by native_decide

/-- Adding two u32 values carries by at most one word. -/
@[miden_bound] theorem u32_add_div_le_one (a b : Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    (a.val + b.val) / 2 ^ 32 ≤ 1 := by
  simp only [Felt.isU32, decide_eq_true_eq] at ha hb
  calc
    (a.val + b.val) / 2 ^ 32 ≤ ((2 ^ 32 - 1) + (2 ^ 32 - 1)) / 2 ^ 32 := by
      apply Nat.div_le_div_right
      omega
    _ ≤ 1 := by native_decide

/-- `Felt.ofNat` of the carry from adding a u32 value to the low half of a u32 product
    round-trips through `.val`. -/
@[miden_bound] theorem u32_prod_mod_add_div_val (a b c : Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) :
    (Felt.ofNat (((a.val * b.val) % 2 ^ 32 + c.val) / 2 ^ 32)).val =
      ((a.val * b.val) % 2 ^ 32 + c.val) / 2 ^ 32 := by
  apply felt_ofNat_val_lt
  apply u32_val_lt_prime
  have : ((a.val * b.val) % 2 ^ 32 + c.val) / 2 ^ 32 ≤ 1 :=
    u32_prod_mod_add_div_le_one a b c ha hb hc
  omega

-- ============================================================================
-- Reusable U32 addition carry lemmas
-- ============================================================================
-- For the addition-based carry accumulation steps in multiplication carry chains.

/-- The sum of two u32 values fits below the Goldilocks prime. -/
theorem u32_add_sum_lt_prime (a b : Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    a.val + b.val < GOLDILOCKS_PRIME := by
  simp only [Felt.isU32, decide_eq_true_eq] at ha hb
  unfold GOLDILOCKS_PRIME; omega

/-- The sum of three u32 values fits below the Goldilocks prime. -/
theorem u32_add3_sum_lt_prime (a b c : Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) :
    a.val + b.val + c.val < GOLDILOCKS_PRIME := by
  simp only [Felt.isU32, decide_eq_true_eq] at ha hb hc
  unfold GOLDILOCKS_PRIME; omega

/-- `Felt.ofNat` of `(a + b) / 2^32` round-trips through `.val` for u32 a, b. -/
@[miden_bound] theorem u32_add_div_val (a b : Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    (Felt.ofNat ((a.val + b.val) / 2 ^ 32)).val = (a.val + b.val) / 2 ^ 32 := by
  apply felt_ofNat_val_lt; apply u32_val_lt_prime
  simp only [Felt.isU32, decide_eq_true_eq] at ha hb; omega

/-- `Felt.ofNat` of `(a + b + c) / 2^32` round-trips through `.val` for u32 a, b, c. -/
@[miden_bound] theorem u32_add3_div_val (a b c : Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) :
    (Felt.ofNat ((a.val + b.val + c.val) / 2 ^ 32)).val =
    (a.val + b.val + c.val) / 2 ^ 32 := by
  apply felt_ofNat_val_lt; apply u32_val_lt_prime
  simp only [Felt.isU32, decide_eq_true_eq] at ha hb hc; omega

-- ============================================================================
-- Recomposition lemmas for widening u32 operations
-- ============================================================================

/-- Recompose a widening u32 addition into the original sum. -/
theorem u32WideAdd_spec (a b : Nat) :
    (u32WideAdd a b).1 + (u32WideAdd a b).2 * 2 ^ 32 = a + b := by
  unfold u32WideAdd u32Max
  change (a + b) % 2 ^ 32 + ((a + b) / 2 ^ 32) * 2 ^ 32 = a + b
  rw [Nat.mul_comm]
  exact Nat.mod_add_div (a + b) (2 ^ 32)

/-- Recompose a widening u32 addition of three values into the original sum. -/
theorem u32WideAdd3_spec (a b c : Nat) :
    (u32WideAdd3 a b c).1 + (u32WideAdd3 a b c).2 * 2 ^ 32 = a + b + c := by
  unfold u32WideAdd3 u32Max
  change (a + b + c) % 2 ^ 32 + ((a + b + c) / 2 ^ 32) * 2 ^ 32 = a + b + c
  rw [Nat.mul_comm]
  exact Nat.mod_add_div (a + b + c) (2 ^ 32)

/-- Recompose a widening u32 multiplication into the original product. -/
theorem u32WideMul_spec (a b : Nat) :
    (u32WideMul a b).1 + (u32WideMul a b).2 * 2 ^ 32 = a * b := by
  unfold u32WideMul u32Max
  let prod := b * a
  have h := Nat.mod_add_div prod (2 ^ 32)
  simpa [prod, Nat.mul_comm] using h

/-- Recompose a widening u32 multiply-add into the original result. -/
theorem u32WideMadd_spec (a b c : Nat) :
    (u32WideMadd a b c).1 + (u32WideMadd a b c).2 * 2 ^ 32 = a * b + c := by
  unfold u32WideMadd u32Max
  let result := b * a + c
  have h := Nat.mod_add_div result (2 ^ 32)
  simpa [result, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

/-- A widening multiplication has zero low-and-high-word sum iff the product is zero. -/
theorem u32WideMul_sum_eq_zero_iff (a b : Nat) :
    (u32WideMul a b).1 + (u32WideMul a b).2 = 0 ↔ a * b = 0 := by
  unfold u32WideMul u32Max
  change (a * b) % 2 ^ 32 + (a * b) / 2 ^ 32 = 0 ↔ a * b = 0
  constructor
  · intro h
    have hlo : a * b % 2 ^ 32 = 0 := by omega
    have hhi : a * b / 2 ^ 32 = 0 := by omega
    have hrecomp := Nat.mod_add_div (a * b) (2 ^ 32)
    omega
  · intro h
    simp [h]

end MidenLean.Proofs
