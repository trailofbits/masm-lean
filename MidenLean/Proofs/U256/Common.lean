import Mathlib.Data.Nat.Bitwise
import MidenLean.Proofs.U32.Common
import MidenLean.Generated.U256

namespace MidenLean.Proofs

open MidenLean

-- ============================================================================
-- Procedure environment
-- ============================================================================

/-- Procedure environment for manual u256 proofs that call other u256 procedures. -/
def u256ProcEnv : ProcEnv := fun name =>
  match name with
  | "u256_le_to_be" => some Miden.Core.U256.u256_le_to_be
  | "u256_le_to_be_pair" => some Miden.Core.U256.u256_le_to_be_pair
  | "add_with_carry_be" => some Miden.Core.U256.add_with_carry_be
  | "sub_with_borrow_be" => some Miden.Core.U256.sub_with_borrow_be
  | "mulstep" => some Miden.Core.U256.mulstep
  | "mulstep4" => some Miden.Core.U256.mulstep4
  | _ => none

-- ============================================================================
-- U256 type: a 256-bit unsigned integer as eight U32 limbs
-- ============================================================================

/-- A 256-bit unsigned integer represented as eight U32 limbs (little-endian).
    `a0` is the least significant limb, `a7` is the most significant. -/
structure U256 where
  a0 : U32
  a1 : U32
  a2 : U32
  a3 : U32
  a4 : U32
  a5 : U32
  a6 : U32
  a7 : U32

namespace U256

/-- Reconstruct the natural number value:
    `a7 * 2^224 + a6 * 2^192 + ... + a1 * 2^32 + a0`. -/
def toNat (x : U256) : Nat :=
  x.a7.val.val * 2^224 + x.a6.val.val * 2^192 +
  x.a5.val.val * 2^160 + x.a4.val.val * 2^128 +
  x.a3.val.val * 2^96  + x.a2.val.val * 2^64  +
  x.a1.val.val * 2^32  + x.a0.val.val

theorem toNat_lt (x : U256) : x.toNat < 2^256 := by
  unfold toNat
  have h0 := x.a0.val_lt; have h1 := x.a1.val_lt
  have h2 := x.a2.val_lt; have h3 := x.a3.val_lt
  have h4 := x.a4.val_lt; have h5 := x.a5.val_lt
  have h6 := x.a6.val_lt; have h7 := x.a7.val_lt
  omega

theorem toNat_def (x : U256) :
    x.toNat = x.a7.val.val * 2^224 + x.a6.val.val * 2^192 +
              x.a5.val.val * 2^160 + x.a4.val.val * 2^128 +
              x.a3.val.val * 2^96  + x.a2.val.val * 2^64  +
              x.a1.val.val * 2^32  + x.a0.val.val := rfl

/-- Construct a U256 from a natural number (taken mod 2^256). -/
def ofNat (n : Nat) : U256 where
  a0 := ⟨Felt.ofNat (n % 2^32), u32_mod_isU32 n⟩
  a1 := ⟨Felt.ofNat ((n / 2^32) % 2^32), u32_mod_isU32 (n / 2^32)⟩
  a2 := ⟨Felt.ofNat ((n / 2^64) % 2^32), u32_mod_isU32 (n / 2^64)⟩
  a3 := ⟨Felt.ofNat ((n / 2^96) % 2^32), u32_mod_isU32 (n / 2^96)⟩
  a4 := ⟨Felt.ofNat ((n / 2^128) % 2^32), u32_mod_isU32 (n / 2^128)⟩
  a5 := ⟨Felt.ofNat ((n / 2^160) % 2^32), u32_mod_isU32 (n / 2^160)⟩
  a6 := ⟨Felt.ofNat ((n / 2^192) % 2^32), u32_mod_isU32 (n / 2^192)⟩
  a7 := ⟨Felt.ofNat ((n / 2^224) % 2^32), u32_mod_isU32 (n / 2^224)⟩

@[simp] theorem ofNat_toNat (n : Nat) : (U256.ofNat n).toNat = n % 2^256 := by
  unfold ofNat toNat
  have h0 : (Felt.ofNat (n % 2^32)).val = n % 2^32 :=
    felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)
  have h1 : (Felt.ofNat ((n / 2^32) % 2^32)).val = (n / 2^32) % 2^32 :=
    felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)
  have h2 : (Felt.ofNat ((n / 2^64) % 2^32)).val = (n / 2^64) % 2^32 :=
    felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)
  have h3 : (Felt.ofNat ((n / 2^96) % 2^32)).val = (n / 2^96) % 2^32 :=
    felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)
  have h4 : (Felt.ofNat ((n / 2^128) % 2^32)).val = (n / 2^128) % 2^32 :=
    felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)
  have h5 : (Felt.ofNat ((n / 2^160) % 2^32)).val = (n / 2^160) % 2^32 :=
    felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)
  have h6 : (Felt.ofNat ((n / 2^192) % 2^32)).val = (n / 2^192) % 2^32 :=
    felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)
  have h7 : (Felt.ofNat ((n / 2^224) % 2^32)).val = (n / 2^224) % 2^32 :=
    felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)
  rw [h0, h1, h2, h3, h4, h5, h6, h7]; omega

-- Limb accessors for ofNat (Felt level)
@[simp] theorem ofNat_a0 (n : Nat) : (U256.ofNat n).a0.val = Felt.ofNat (n % 2^32) := rfl
@[simp] theorem ofNat_a1 (n : Nat) : (U256.ofNat n).a1.val = Felt.ofNat ((n / 2^32) % 2^32) := rfl
@[simp] theorem ofNat_a2 (n : Nat) : (U256.ofNat n).a2.val = Felt.ofNat ((n / 2^64) % 2^32) := rfl
@[simp] theorem ofNat_a3 (n : Nat) : (U256.ofNat n).a3.val = Felt.ofNat ((n / 2^96) % 2^32) := rfl
@[simp] theorem ofNat_a4 (n : Nat) : (U256.ofNat n).a4.val = Felt.ofNat ((n / 2^128) % 2^32) := rfl
@[simp] theorem ofNat_a5 (n : Nat) : (U256.ofNat n).a5.val = Felt.ofNat ((n / 2^160) % 2^32) := rfl
@[simp] theorem ofNat_a6 (n : Nat) : (U256.ofNat n).a6.val = Felt.ofNat ((n / 2^192) % 2^32) := rfl
@[simp] theorem ofNat_a7 (n : Nat) : (U256.ofNat n).a7.val = Felt.ofNat ((n / 2^224) % 2^32) := rfl

-- Limb accessors for ofNat (Nat level)
@[simp] theorem ofNat_a0_toNat (n : Nat) : (U256.ofNat n).a0.toNat = n % 2^32 :=
  felt_ofNat_val_lt _ (u32_mod_lt_prime n)
@[simp] theorem ofNat_a1_toNat (n : Nat) : (U256.ofNat n).a1.toNat = (n / 2^32) % 2^32 :=
  felt_ofNat_val_lt _ (u32_mod_lt_prime (n / 2^32))
@[simp] theorem ofNat_a2_toNat (n : Nat) : (U256.ofNat n).a2.toNat = (n / 2^64) % 2^32 :=
  felt_ofNat_val_lt _ (u32_mod_lt_prime (n / 2^64))
@[simp] theorem ofNat_a3_toNat (n : Nat) : (U256.ofNat n).a3.toNat = (n / 2^96) % 2^32 :=
  felt_ofNat_val_lt _ (u32_mod_lt_prime (n / 2^96))
@[simp] theorem ofNat_a4_toNat (n : Nat) : (U256.ofNat n).a4.toNat = (n / 2^128) % 2^32 :=
  felt_ofNat_val_lt _ (u32_mod_lt_prime (n / 2^128))
@[simp] theorem ofNat_a5_toNat (n : Nat) : (U256.ofNat n).a5.toNat = (n / 2^160) % 2^32 :=
  felt_ofNat_val_lt _ (u32_mod_lt_prime (n / 2^160))
@[simp] theorem ofNat_a6_toNat (n : Nat) : (U256.ofNat n).a6.toNat = (n / 2^192) % 2^32 :=
  felt_ofNat_val_lt _ (u32_mod_lt_prime (n / 2^192))
@[simp] theorem ofNat_a7_toNat (n : Nat) : (U256.ofNat n).a7.toNat = (n / 2^224) % 2^32 :=
  felt_ofNat_val_lt _ (u32_mod_lt_prime (n / 2^224))

-- Extensionality
@[ext] theorem ext {a b : U256}
    (h0 : a.a0 = b.a0) (h1 : a.a1 = b.a1) (h2 : a.a2 = b.a2) (h3 : a.a3 = b.a3)
    (h4 : a.a4 = b.a4) (h5 : a.a5 = b.a5) (h6 : a.a6 = b.a6) (h7 : a.a7 = b.a7) :
    a = b := by
  cases a; cases b; simp_all

theorem toNat_injective : Function.Injective U256.toNat := by
  intro a b hab
  have ha0 := a.a0.val_lt; have ha1 := a.a1.val_lt
  have ha2 := a.a2.val_lt; have ha3 := a.a3.val_lt
  have ha4 := a.a4.val_lt; have ha5 := a.a5.val_lt
  have ha6 := a.a6.val_lt; have ha7 := a.a7.val_lt
  have hb0 := b.a0.val_lt; have hb1 := b.a1.val_lt
  have hb2 := b.a2.val_lt; have hb3 := b.a3.val_lt
  have hb4 := b.a4.val_lt; have hb5 := b.a5.val_lt
  have hb6 := b.a6.val_lt; have hb7 := b.a7.val_lt
  unfold toNat at hab
  apply ext <;> exact U32.ext (ZMod.val_injective _ (by omega))

theorem eq_of_toNat_eq {a b : U256} (h : a.toNat = b.toNat) : a = b :=
  toNat_injective h

end U256

-- ============================================================================
-- Arithmetic instances
-- ============================================================================

instance : Add U256 where add a b := U256.ofNat (a.toNat + b.toNat)
instance : Sub U256 where sub a b := U256.ofNat (a.toNat + 2^256 - b.toNat)
instance : Mul U256 where mul a b := U256.ofNat (a.toNat * b.toNat)

-- ============================================================================
-- Comparison instances
-- ============================================================================

instance : LT U256 where lt a b := a.toNat < b.toNat
instance : LE U256 where le a b := a.toNat ≤ b.toNat
instance (a b : U256) : Decidable (a < b) := inferInstanceAs (Decidable (a.toNat < b.toNat))
instance (a b : U256) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.toNat ≤ b.toNat))

-- ============================================================================
-- Bitwise instances (limb-wise)
-- ============================================================================

instance : AndOp U256 where and a b := {
  a0 := ⟨Felt.ofNat (a.a0.val.val &&& b.a0.val.val),
    felt_ofNat_isU32_of_lt _ (Nat.lt_of_le_of_lt Nat.and_le_left a.a0.val_lt)⟩
  a1 := ⟨Felt.ofNat (a.a1.val.val &&& b.a1.val.val),
    felt_ofNat_isU32_of_lt _ (Nat.lt_of_le_of_lt Nat.and_le_left a.a1.val_lt)⟩
  a2 := ⟨Felt.ofNat (a.a2.val.val &&& b.a2.val.val),
    felt_ofNat_isU32_of_lt _ (Nat.lt_of_le_of_lt Nat.and_le_left a.a2.val_lt)⟩
  a3 := ⟨Felt.ofNat (a.a3.val.val &&& b.a3.val.val),
    felt_ofNat_isU32_of_lt _ (Nat.lt_of_le_of_lt Nat.and_le_left a.a3.val_lt)⟩
  a4 := ⟨Felt.ofNat (a.a4.val.val &&& b.a4.val.val),
    felt_ofNat_isU32_of_lt _ (Nat.lt_of_le_of_lt Nat.and_le_left a.a4.val_lt)⟩
  a5 := ⟨Felt.ofNat (a.a5.val.val &&& b.a5.val.val),
    felt_ofNat_isU32_of_lt _ (Nat.lt_of_le_of_lt Nat.and_le_left a.a5.val_lt)⟩
  a6 := ⟨Felt.ofNat (a.a6.val.val &&& b.a6.val.val),
    felt_ofNat_isU32_of_lt _ (Nat.lt_of_le_of_lt Nat.and_le_left a.a6.val_lt)⟩
  a7 := ⟨Felt.ofNat (a.a7.val.val &&& b.a7.val.val),
    felt_ofNat_isU32_of_lt _ (Nat.lt_of_le_of_lt Nat.and_le_left a.a7.val_lt)⟩
}

instance : OrOp U256 where or a b := {
  a0 := ⟨Felt.ofNat (a.a0.val.val ||| b.a0.val.val),
    felt_ofNat_isU32_of_lt _ (Nat.or_lt_two_pow a.a0.val_lt b.a0.val_lt)⟩
  a1 := ⟨Felt.ofNat (a.a1.val.val ||| b.a1.val.val),
    felt_ofNat_isU32_of_lt _ (Nat.or_lt_two_pow a.a1.val_lt b.a1.val_lt)⟩
  a2 := ⟨Felt.ofNat (a.a2.val.val ||| b.a2.val.val),
    felt_ofNat_isU32_of_lt _ (Nat.or_lt_two_pow a.a2.val_lt b.a2.val_lt)⟩
  a3 := ⟨Felt.ofNat (a.a3.val.val ||| b.a3.val.val),
    felt_ofNat_isU32_of_lt _ (Nat.or_lt_two_pow a.a3.val_lt b.a3.val_lt)⟩
  a4 := ⟨Felt.ofNat (a.a4.val.val ||| b.a4.val.val),
    felt_ofNat_isU32_of_lt _ (Nat.or_lt_two_pow a.a4.val_lt b.a4.val_lt)⟩
  a5 := ⟨Felt.ofNat (a.a5.val.val ||| b.a5.val.val),
    felt_ofNat_isU32_of_lt _ (Nat.or_lt_two_pow a.a5.val_lt b.a5.val_lt)⟩
  a6 := ⟨Felt.ofNat (a.a6.val.val ||| b.a6.val.val),
    felt_ofNat_isU32_of_lt _ (Nat.or_lt_two_pow a.a6.val_lt b.a6.val_lt)⟩
  a7 := ⟨Felt.ofNat (a.a7.val.val ||| b.a7.val.val),
    felt_ofNat_isU32_of_lt _ (Nat.or_lt_two_pow a.a7.val_lt b.a7.val_lt)⟩
}

instance : XorOp U256 where xor a b := {
  a0 := ⟨Felt.ofNat (a.a0.val.val ^^^ b.a0.val.val),
    felt_ofNat_isU32_of_lt _ (Nat.xor_lt_two_pow a.a0.val_lt b.a0.val_lt)⟩
  a1 := ⟨Felt.ofNat (a.a1.val.val ^^^ b.a1.val.val),
    felt_ofNat_isU32_of_lt _ (Nat.xor_lt_two_pow a.a1.val_lt b.a1.val_lt)⟩
  a2 := ⟨Felt.ofNat (a.a2.val.val ^^^ b.a2.val.val),
    felt_ofNat_isU32_of_lt _ (Nat.xor_lt_two_pow a.a2.val_lt b.a2.val_lt)⟩
  a3 := ⟨Felt.ofNat (a.a3.val.val ^^^ b.a3.val.val),
    felt_ofNat_isU32_of_lt _ (Nat.xor_lt_two_pow a.a3.val_lt b.a3.val_lt)⟩
  a4 := ⟨Felt.ofNat (a.a4.val.val ^^^ b.a4.val.val),
    felt_ofNat_isU32_of_lt _ (Nat.xor_lt_two_pow a.a4.val_lt b.a4.val_lt)⟩
  a5 := ⟨Felt.ofNat (a.a5.val.val ^^^ b.a5.val.val),
    felt_ofNat_isU32_of_lt _ (Nat.xor_lt_two_pow a.a5.val_lt b.a5.val_lt)⟩
  a6 := ⟨Felt.ofNat (a.a6.val.val ^^^ b.a6.val.val),
    felt_ofNat_isU32_of_lt _ (Nat.xor_lt_two_pow a.a6.val_lt b.a6.val_lt)⟩
  a7 := ⟨Felt.ofNat (a.a7.val.val ^^^ b.a7.val.val),
    felt_ofNat_isU32_of_lt _ (Nat.xor_lt_two_pow a.a7.val_lt b.a7.val_lt)⟩
}

-- ============================================================================
-- Equality instance
-- ============================================================================

instance : BEq U256 where beq a b :=
  (a.a0.val == b.a0.val) && (a.a1.val == b.a1.val) &&
  (a.a2.val == b.a2.val) && (a.a3.val == b.a3.val) &&
  (a.a4.val == b.a4.val) && (a.a5.val == b.a5.val) &&
  (a.a6.val == b.a6.val) && (a.a7.val == b.a7.val)

-- ============================================================================
-- Bridging lemmas
-- ============================================================================

namespace U256

-- Comparison bridging
@[simp] theorem lt_iff_toNat_lt (a b : U256) : a < b ↔ a.toNat < b.toNat := Iff.rfl
@[simp] theorem le_iff_toNat_le (a b : U256) : a ≤ b ↔ a.toNat ≤ b.toNat := Iff.rfl

-- Arithmetic bridging
@[simp] theorem toNat_add (a b : U256) : (a + b).toNat = (a.toNat + b.toNat) % 2^256 :=
  ofNat_toNat _
@[simp] theorem toNat_sub (a b : U256) : (a - b).toNat = (a.toNat + 2^256 - b.toNat) % 2^256 :=
  ofNat_toNat _
@[simp] theorem toNat_mul (a b : U256) : (a * b).toNat = (a.toNat * b.toNat) % 2^256 :=
  ofNat_toNat _

-- Bitwise bridging (Felt level)
@[simp] theorem and_a0 (a b : U256) : (a &&& b).a0.val = Felt.ofNat (a.a0.val.val &&& b.a0.val.val) := rfl
@[simp] theorem and_a1 (a b : U256) : (a &&& b).a1.val = Felt.ofNat (a.a1.val.val &&& b.a1.val.val) := rfl
@[simp] theorem and_a2 (a b : U256) : (a &&& b).a2.val = Felt.ofNat (a.a2.val.val &&& b.a2.val.val) := rfl
@[simp] theorem and_a3 (a b : U256) : (a &&& b).a3.val = Felt.ofNat (a.a3.val.val &&& b.a3.val.val) := rfl
@[simp] theorem and_a4 (a b : U256) : (a &&& b).a4.val = Felt.ofNat (a.a4.val.val &&& b.a4.val.val) := rfl
@[simp] theorem and_a5 (a b : U256) : (a &&& b).a5.val = Felt.ofNat (a.a5.val.val &&& b.a5.val.val) := rfl
@[simp] theorem and_a6 (a b : U256) : (a &&& b).a6.val = Felt.ofNat (a.a6.val.val &&& b.a6.val.val) := rfl
@[simp] theorem and_a7 (a b : U256) : (a &&& b).a7.val = Felt.ofNat (a.a7.val.val &&& b.a7.val.val) := rfl

@[simp] theorem or_a0 (a b : U256) : (a ||| b).a0.val = Felt.ofNat (a.a0.val.val ||| b.a0.val.val) := rfl
@[simp] theorem or_a1 (a b : U256) : (a ||| b).a1.val = Felt.ofNat (a.a1.val.val ||| b.a1.val.val) := rfl
@[simp] theorem or_a2 (a b : U256) : (a ||| b).a2.val = Felt.ofNat (a.a2.val.val ||| b.a2.val.val) := rfl
@[simp] theorem or_a3 (a b : U256) : (a ||| b).a3.val = Felt.ofNat (a.a3.val.val ||| b.a3.val.val) := rfl
@[simp] theorem or_a4 (a b : U256) : (a ||| b).a4.val = Felt.ofNat (a.a4.val.val ||| b.a4.val.val) := rfl
@[simp] theorem or_a5 (a b : U256) : (a ||| b).a5.val = Felt.ofNat (a.a5.val.val ||| b.a5.val.val) := rfl
@[simp] theorem or_a6 (a b : U256) : (a ||| b).a6.val = Felt.ofNat (a.a6.val.val ||| b.a6.val.val) := rfl
@[simp] theorem or_a7 (a b : U256) : (a ||| b).a7.val = Felt.ofNat (a.a7.val.val ||| b.a7.val.val) := rfl

@[simp] theorem xor_a0 (a b : U256) : (a ^^^ b).a0.val = Felt.ofNat (a.a0.val.val ^^^ b.a0.val.val) := rfl
@[simp] theorem xor_a1 (a b : U256) : (a ^^^ b).a1.val = Felt.ofNat (a.a1.val.val ^^^ b.a1.val.val) := rfl
@[simp] theorem xor_a2 (a b : U256) : (a ^^^ b).a2.val = Felt.ofNat (a.a2.val.val ^^^ b.a2.val.val) := rfl
@[simp] theorem xor_a3 (a b : U256) : (a ^^^ b).a3.val = Felt.ofNat (a.a3.val.val ^^^ b.a3.val.val) := rfl
@[simp] theorem xor_a4 (a b : U256) : (a ^^^ b).a4.val = Felt.ofNat (a.a4.val.val ^^^ b.a4.val.val) := rfl
@[simp] theorem xor_a5 (a b : U256) : (a ^^^ b).a5.val = Felt.ofNat (a.a5.val.val ^^^ b.a5.val.val) := rfl
@[simp] theorem xor_a6 (a b : U256) : (a ^^^ b).a6.val = Felt.ofNat (a.a6.val.val ^^^ b.a6.val.val) := rfl
@[simp] theorem xor_a7 (a b : U256) : (a ^^^ b).a7.val = Felt.ofNat (a.a7.val.val ^^^ b.a7.val.val) := rfl

-- Equality bridging
@[simp] theorem beq_iff (a b : U256) :
    (a == b) = ((a.a0.val == b.a0.val) && (a.a1.val == b.a1.val) &&
                (a.a2.val == b.a2.val) && (a.a3.val == b.a3.val) &&
                (a.a4.val == b.a4.val) && (a.a5.val == b.a5.val) &&
                (a.a6.val == b.a6.val) && (a.a7.val == b.a7.val)) := rfl

-- ============================================================================
-- isU32 lemmas for U256 limbs
-- ============================================================================

theorem a0_isU32 (x : U256) : x.a0.val.isU32 = true := x.a0.isU32
theorem a1_isU32 (x : U256) : x.a1.val.isU32 = true := x.a1.isU32
theorem a2_isU32 (x : U256) : x.a2.val.isU32 = true := x.a2.isU32
theorem a3_isU32 (x : U256) : x.a3.val.isU32 = true := x.a3.isU32
theorem a4_isU32 (x : U256) : x.a4.val.isU32 = true := x.a4.isU32
theorem a5_isU32 (x : U256) : x.a5.val.isU32 = true := x.a5.isU32
theorem a6_isU32 (x : U256) : x.a6.val.isU32 = true := x.a6.isU32
theorem a7_isU32 (x : U256) : x.a7.val.isU32 = true := x.a7.isU32

-- ============================================================================
-- Eqz helper
-- ============================================================================

/-- A U256 is zero iff all limbs are zero. -/
theorem eqz_iff (x : U256) :
    x.toNat = 0 ↔ x.a0.val.val = 0 ∧ x.a1.val.val = 0 ∧ x.a2.val.val = 0 ∧ x.a3.val.val = 0 ∧
                   x.a4.val.val = 0 ∧ x.a5.val.val = 0 ∧ x.a6.val.val = 0 ∧ x.a7.val.val = 0 := by
  unfold toNat
  constructor
  · intro h; omega
  · intro ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩; omega

end U256

end MidenLean.Proofs
