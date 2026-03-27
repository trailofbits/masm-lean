import Mathlib.Data.Nat.Bitwise
import MidenLean.Proofs.U32.Common
import MidenLean.Generated.U128

namespace MidenLean.Proofs

open MidenLean

theorem stepU32WrappingSubLocal (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .u32WrappingSub =
      some ⟨Felt.ofNat (u32OverflowingSub a.val b.val).2 :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execU32WrappingSub
  simp [ha, hb, MidenState.withStack]

theorem stepU32ShrLocal (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true)
    (hshift : b.val ≤ 31) :
    execInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .u32Shr =
      some ⟨Felt.ofNat (a.val / 2 ^ b.val) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execU32Shr
  simp [ha, hb, show ¬b.val > 31 by omega, MidenState.withStack]

/-- Procedure environment for manual u128 proofs that call other u128 procedures. -/
def u128ProcEnv : ProcEnv := fun name =>
  match name with
  | "overflowing_add" => some Miden.Core.U128.overflowing_add
  | "overflowing_sub" => some Miden.Core.U128.overflowing_sub
  | "overflowing_mul" => some Miden.Core.U128.overflowing_mul
  | "gt" => some Miden.Core.U128.gt
  | "gte" => some Miden.Core.U128.gte
  | "lt" => some Miden.Core.U128.lt
  | "lte" => some Miden.Core.U128.lte
  | "max" => some Miden.Core.U128.max
  | "min" => some Miden.Core.U128.min
  | "wrapping_mul" => some Miden.Core.U128.wrapping_mul
  | "shr_k0" => some Miden.Core.U128.shr_k0
  | "shr_k1" => some Miden.Core.U128.shr_k1
  | "shr_k2" => some Miden.Core.U128.shr_k2
  | "shr_k3" => some Miden.Core.U128.shr_k3
  | "shl" => some Miden.Core.U128.shl
  | "shr" => some Miden.Core.U128.shr
  | "divmod" => some Miden.Core.U128.divmod
  | _ => none

def u128Sub0 (a0 b0 : Felt) : Nat × Nat :=
  u32OverflowingSub a0.val b0.val

def u128Sub1 (a1 b1 : Felt) : Nat × Nat :=
  u32OverflowingSub a1.val b1.val

def u128Borrow1 (a0 a1 b0 b1 : Felt) : Felt :=
  if decide ((u128Sub1 a1 b1).2 < (u128Sub0 a0 b0).1) || decide (a1.val < b1.val) then
    1
  else
    0

def u128Sub2 (a2 b2 : Felt) : Nat × Nat :=
  u32OverflowingSub a2.val b2.val

def u128Borrow2 (a0 a1 a2 b0 b1 b2 : Felt) : Felt :=
  if decide ((u128Sub2 a2 b2).2 < (u128Borrow1 a0 a1 b0 b1).val) || decide (a2.val < b2.val) then
    1
  else
    0

def u128Sub3 (a3 b3 : Felt) : Nat × Nat :=
  u32OverflowingSub a3.val b3.val

def u128LtBool (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) : Bool :=
  decide ((u128Sub3 a3 b3).2 < (u128Borrow2 a0 a1 a2 b0 b1 b2).val) || decide (a3.val < b3.val)

def u128GtBool (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) : Bool :=
  u128LtBool b0 b1 b2 b3 a0 a1 a2 a3

-- ============================================================================
-- U128 type: a 128-bit unsigned integer as four U32 limbs
-- ============================================================================

/-- A 128-bit unsigned integer represented as four U32 limbs (little-endian).
    `a0` is the least significant limb, `a3` is the most significant. -/
structure U128 where
  a0 : U32
  a1 : U32
  a2 : U32
  a3 : U32

namespace U128

/-- Reconstruct the natural number value:
    `a3 * 2^96 + a2 * 2^64 + a1 * 2^32 + a0`. -/
def toNat (x : U128) : Nat :=
  x.a3.val.val * 2^96 + x.a2.val.val * 2^64 + x.a1.val.val * 2^32 + x.a0.val.val

theorem toNat_lt (x : U128) : x.toNat < 2^128 := by
  unfold toNat
  have h0 := x.a0.val_lt; have h1 := x.a1.val_lt
  have h2 := x.a2.val_lt; have h3 := x.a3.val_lt
  omega

theorem toNat_def (x : U128) :
    x.toNat = x.a3.val.val * 2^96 + x.a2.val.val * 2^64 + x.a1.val.val * 2^32 + x.a0.val.val := rfl

/-- Construct a U128 from a natural number (taken mod 2^128). -/
def ofNat (n : Nat) : U128 where
  a0 := ⟨Felt.ofNat (n % 2^32), u32_mod_isU32 n⟩
  a1 := ⟨Felt.ofNat ((n / 2^32) % 2^32), u32_mod_isU32 (n / 2^32)⟩
  a2 := ⟨Felt.ofNat ((n / 2^64) % 2^32), u32_mod_isU32 (n / 2^64)⟩
  a3 := ⟨Felt.ofNat ((n / 2^96) % 2^32), u32_mod_isU32 (n / 2^96)⟩

@[simp] theorem ofNat_toNat (n : Nat) : (U128.ofNat n).toNat = n % 2^128 := by
  unfold ofNat toNat
  have h0 : (Felt.ofNat (n % 2^32)).val = n % 2^32 :=
    felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)
  have h1 : (Felt.ofNat ((n / 2^32) % 2^32)).val = (n / 2^32) % 2^32 :=
    felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)
  have h2 : (Felt.ofNat ((n / 2^64) % 2^32)).val = (n / 2^64) % 2^32 :=
    felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)
  have h3 : (Felt.ofNat ((n / 2^96) % 2^32)).val = (n / 2^96) % 2^32 :=
    felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)
  rw [h0, h1, h2, h3]; omega

@[simp] theorem ofNat_a0 (n : Nat) :
    (U128.ofNat n).a0.val = Felt.ofNat (n % 2^32) := rfl

@[simp] theorem ofNat_a1 (n : Nat) :
    (U128.ofNat n).a1.val = Felt.ofNat ((n / 2^32) % 2^32) := rfl

@[simp] theorem ofNat_a2 (n : Nat) :
    (U128.ofNat n).a2.val = Felt.ofNat ((n / 2^64) % 2^32) := rfl

@[simp] theorem ofNat_a3 (n : Nat) :
    (U128.ofNat n).a3.val = Felt.ofNat ((n / 2^96) % 2^32) := rfl

@[simp] theorem ofNat_a0_toNat (n : Nat) :
    (U128.ofNat n).a0.toNat = n % 2^32 :=
  felt_ofNat_val_lt _ (u32_mod_lt_prime n)

@[simp] theorem ofNat_a1_toNat (n : Nat) :
    (U128.ofNat n).a1.toNat = (n / 2^32) % 2^32 :=
  felt_ofNat_val_lt _ (u32_mod_lt_prime (n / 2^32))

@[simp] theorem ofNat_a2_toNat (n : Nat) :
    (U128.ofNat n).a2.toNat = (n / 2^64) % 2^32 :=
  felt_ofNat_val_lt _ (u32_mod_lt_prime (n / 2^64))

@[simp] theorem ofNat_a3_toNat (n : Nat) :
    (U128.ofNat n).a3.toNat = (n / 2^96) % 2^32 :=
  felt_ofNat_val_lt _ (u32_mod_lt_prime (n / 2^96))

-- Extensionality: two U128s with the same limbs are equal.
@[ext] theorem ext {a b : U128} (h0 : a.a0 = b.a0) (h1 : a.a1 = b.a1)
    (h2 : a.a2 = b.a2) (h3 : a.a3 = b.a3) : a = b := by
  cases a; cases b; simp_all

theorem toNat_injective : Function.Injective U128.toNat := by
  intro a b hab
  have ha0 := a.a0.val_lt; have ha1 := a.a1.val_lt
  have ha2 := a.a2.val_lt; have ha3 := a.a3.val_lt
  have hb0 := b.a0.val_lt; have hb1 := b.a1.val_lt
  have hb2 := b.a2.val_lt; have hb3 := b.a3.val_lt
  unfold toNat at hab
  apply ext <;> exact U32.ext (ZMod.val_injective _ (by omega))

theorem eq_of_toNat_eq {a b : U128} (h : a.toNat = b.toNat) : a = b :=
  toNat_injective h

end U128

-- Arithmetic instances
instance : Add U128 where add a b := U128.ofNat (a.toNat + b.toNat)
instance : Sub U128 where sub a b := U128.ofNat (a.toNat + 2^128 - b.toNat)
instance : Mul U128 where mul a b := U128.ofNat (a.toNat * b.toNat)

-- Comparison instances
instance : LT U128 where lt a b := a.toNat < b.toNat
instance : LE U128 where le a b := a.toNat ≤ b.toNat
instance (a b : U128) : Decidable (a < b) := inferInstanceAs (Decidable (a.toNat < b.toNat))
instance (a b : U128) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.toNat ≤ b.toNat))

-- Bitwise instances
instance : AndOp U128 where and a b := {
  a0 := ⟨Felt.ofNat (a.a0.val.val &&& b.a0.val.val),
    felt_ofNat_isU32_of_lt _ (Nat.lt_of_le_of_lt Nat.and_le_left a.a0.val_lt)⟩
  a1 := ⟨Felt.ofNat (a.a1.val.val &&& b.a1.val.val),
    felt_ofNat_isU32_of_lt _ (Nat.lt_of_le_of_lt Nat.and_le_left a.a1.val_lt)⟩
  a2 := ⟨Felt.ofNat (a.a2.val.val &&& b.a2.val.val),
    felt_ofNat_isU32_of_lt _ (Nat.lt_of_le_of_lt Nat.and_le_left a.a2.val_lt)⟩
  a3 := ⟨Felt.ofNat (a.a3.val.val &&& b.a3.val.val),
    felt_ofNat_isU32_of_lt _ (Nat.lt_of_le_of_lt Nat.and_le_left a.a3.val_lt)⟩
}

instance : OrOp U128 where or a b := {
  a0 := ⟨Felt.ofNat (a.a0.val.val ||| b.a0.val.val),
    felt_ofNat_isU32_of_lt _ (Nat.or_lt_two_pow a.a0.val_lt b.a0.val_lt)⟩
  a1 := ⟨Felt.ofNat (a.a1.val.val ||| b.a1.val.val),
    felt_ofNat_isU32_of_lt _ (Nat.or_lt_two_pow a.a1.val_lt b.a1.val_lt)⟩
  a2 := ⟨Felt.ofNat (a.a2.val.val ||| b.a2.val.val),
    felt_ofNat_isU32_of_lt _ (Nat.or_lt_two_pow a.a2.val_lt b.a2.val_lt)⟩
  a3 := ⟨Felt.ofNat (a.a3.val.val ||| b.a3.val.val),
    felt_ofNat_isU32_of_lt _ (Nat.or_lt_two_pow a.a3.val_lt b.a3.val_lt)⟩
}

instance : XorOp U128 where xor a b := {
  a0 := ⟨Felt.ofNat (a.a0.val.val ^^^ b.a0.val.val),
    felt_ofNat_isU32_of_lt _ (Nat.xor_lt_two_pow a.a0.val_lt b.a0.val_lt)⟩
  a1 := ⟨Felt.ofNat (a.a1.val.val ^^^ b.a1.val.val),
    felt_ofNat_isU32_of_lt _ (Nat.xor_lt_two_pow a.a1.val_lt b.a1.val_lt)⟩
  a2 := ⟨Felt.ofNat (a.a2.val.val ^^^ b.a2.val.val),
    felt_ofNat_isU32_of_lt _ (Nat.xor_lt_two_pow a.a2.val_lt b.a2.val_lt)⟩
  a3 := ⟨Felt.ofNat (a.a3.val.val ^^^ b.a3.val.val),
    felt_ofNat_isU32_of_lt _ (Nat.xor_lt_two_pow a.a3.val_lt b.a3.val_lt)⟩
}

instance : Complement U128 where complement a := {
  a0 := ⟨Felt.ofNat (u32Max - 1 - a.a0.val.val),
    felt_ofNat_isU32_of_lt _ (by have := a.a0.val_lt; unfold u32Max; omega)⟩
  a1 := ⟨Felt.ofNat (u32Max - 1 - a.a1.val.val),
    felt_ofNat_isU32_of_lt _ (by have := a.a1.val_lt; unfold u32Max; omega)⟩
  a2 := ⟨Felt.ofNat (u32Max - 1 - a.a2.val.val),
    felt_ofNat_isU32_of_lt _ (by have := a.a2.val_lt; unfold u32Max; omega)⟩
  a3 := ⟨Felt.ofNat (u32Max - 1 - a.a3.val.val),
    felt_ofNat_isU32_of_lt _ (by have := a.a3.val_lt; unfold u32Max; omega)⟩
}

-- Equality instance
instance : BEq U128 where beq a b :=
  (a.a0.val == b.a0.val) && (a.a1.val == b.a1.val) &&
  (a.a2.val == b.a2.val) && (a.a3.val == b.a3.val)

-- Min/Max instances
instance : Min U128 where min a b := if a ≤ b then a else b
instance : Max U128 where max a b := if b ≤ a then a else b

namespace U128

@[simp] theorem lt_iff_toNat_lt (a b : U128) : a < b ↔ a.toNat < b.toNat := Iff.rfl
@[simp] theorem le_iff_toNat_le (a b : U128) : a ≤ b ↔ a.toNat ≤ b.toNat := Iff.rfl

@[simp] theorem toNat_add (a b : U128) : (a + b).toNat = (a.toNat + b.toNat) % 2^128 :=
  ofNat_toNat _

@[simp] theorem toNat_sub (a b : U128) : (a - b).toNat = (a.toNat + 2^128 - b.toNat) % 2^128 :=
  ofNat_toNat _

@[simp] theorem toNat_mul (a b : U128) : (a * b).toNat = (a.toNat * b.toNat) % 2^128 :=
  ofNat_toNat _

-- Bitwise bridging lemmas
@[simp] theorem and_a0 (a b : U128) : (a &&& b).a0.val = Felt.ofNat (a.a0.val.val &&& b.a0.val.val) := rfl
@[simp] theorem and_a1 (a b : U128) : (a &&& b).a1.val = Felt.ofNat (a.a1.val.val &&& b.a1.val.val) := rfl
@[simp] theorem and_a2 (a b : U128) : (a &&& b).a2.val = Felt.ofNat (a.a2.val.val &&& b.a2.val.val) := rfl
@[simp] theorem and_a3 (a b : U128) : (a &&& b).a3.val = Felt.ofNat (a.a3.val.val &&& b.a3.val.val) := rfl
@[simp] theorem or_a0 (a b : U128) : (a ||| b).a0.val = Felt.ofNat (a.a0.val.val ||| b.a0.val.val) := rfl
@[simp] theorem or_a1 (a b : U128) : (a ||| b).a1.val = Felt.ofNat (a.a1.val.val ||| b.a1.val.val) := rfl
@[simp] theorem or_a2 (a b : U128) : (a ||| b).a2.val = Felt.ofNat (a.a2.val.val ||| b.a2.val.val) := rfl
@[simp] theorem or_a3 (a b : U128) : (a ||| b).a3.val = Felt.ofNat (a.a3.val.val ||| b.a3.val.val) := rfl
@[simp] theorem or_a0_toNat (a b : U128) : (a ||| b).a0.toNat = a.a0.toNat ||| b.a0.toNat :=
  felt_ofNat_val_lt _ (by
    have h := Nat.or_lt_two_pow a.a0.val_lt b.a0.val_lt
    unfold GOLDILOCKS_PRIME
    omega)
@[simp] theorem or_a1_toNat (a b : U128) : (a ||| b).a1.toNat = a.a1.toNat ||| b.a1.toNat :=
  felt_ofNat_val_lt _ (by
    have h := Nat.or_lt_two_pow a.a1.val_lt b.a1.val_lt
    unfold GOLDILOCKS_PRIME
    omega)
@[simp] theorem or_a2_toNat (a b : U128) : (a ||| b).a2.toNat = a.a2.toNat ||| b.a2.toNat :=
  felt_ofNat_val_lt _ (by
    have h := Nat.or_lt_two_pow a.a2.val_lt b.a2.val_lt
    unfold GOLDILOCKS_PRIME
    omega)
@[simp] theorem or_a3_toNat (a b : U128) : (a ||| b).a3.toNat = a.a3.toNat ||| b.a3.toNat :=
  felt_ofNat_val_lt _ (by
    have h := Nat.or_lt_two_pow a.a3.val_lt b.a3.val_lt
    unfold GOLDILOCKS_PRIME
    omega)
@[simp] theorem xor_a0 (a b : U128) : (a ^^^ b).a0.val = Felt.ofNat (a.a0.val.val ^^^ b.a0.val.val) := rfl
@[simp] theorem xor_a1 (a b : U128) : (a ^^^ b).a1.val = Felt.ofNat (a.a1.val.val ^^^ b.a1.val.val) := rfl
@[simp] theorem xor_a2 (a b : U128) : (a ^^^ b).a2.val = Felt.ofNat (a.a2.val.val ^^^ b.a2.val.val) := rfl
@[simp] theorem xor_a3 (a b : U128) : (a ^^^ b).a3.val = Felt.ofNat (a.a3.val.val ^^^ b.a3.val.val) := rfl
@[simp] theorem complement_a0 (a : U128) : (~~~a).a0.val = Felt.ofNat (u32Max - 1 - a.a0.val.val) := rfl
@[simp] theorem complement_a1 (a : U128) : (~~~a).a1.val = Felt.ofNat (u32Max - 1 - a.a1.val.val) := rfl
@[simp] theorem complement_a2 (a : U128) : (~~~a).a2.val = Felt.ofNat (u32Max - 1 - a.a2.val.val) := rfl
@[simp] theorem complement_a3 (a : U128) : (~~~a).a3.val = Felt.ofNat (u32Max - 1 - a.a3.val.val) := rfl

-- Equality bridging lemmas
@[simp] theorem beq_iff (a b : U128) :
    (a == b) = ((a.a0.val == b.a0.val) && (a.a1.val == b.a1.val) &&
                (a.a2.val == b.a2.val) && (a.a3.val == b.a3.val)) := rfl

theorem beq_comm (a b : U128) : (a == b) = (b == a) := by
  simp only [beq_iff, Bool.beq_comm (a := a.a0.val), Bool.beq_comm (a := a.a1.val),
    Bool.beq_comm (a := a.a2.val), Bool.beq_comm (a := a.a3.val),
    Bool.and_comm, Bool.and_left_comm]

theorem bne_iff (a b : U128) :
    (a != b) = ((a.a0.val != b.a0.val) || (a.a1.val != b.a1.val) ||
                (a.a2.val != b.a2.val) || (a.a3.val != b.a3.val)) := by
  simp only [bne, beq_iff, Bool.not_and, bne]

theorem bne_comm (a b : U128) : (a != b) = (b != a) := by
  simp only [bne, beq_comm]

-- Min/Max bridging lemmas
@[simp] theorem min_def (a b : U128) : min a b = if a ≤ b then a else b := rfl
@[simp] theorem max_def (a b : U128) : max a b = if b ≤ a then a else b := rfl

/-- `min a b = if b < a then b else a` (matches the MASM gt-then-cswap pattern). -/
theorem min_eq_ite_lt (a b : U128) : min a b = if b < a then b else a := by
  simp only [min_def, le_iff_toNat_le, lt_iff_toNat_lt]
  split_ifs <;> first | rfl | (exfalso; omega)

/-- `max a b = if a < b then b else a` (matches the MASM lt-then-cswap pattern). -/
theorem max_eq_ite_lt (a b : U128) : max a b = if a < b then b else a := by
  simp only [max_def, le_iff_toNat_le, lt_iff_toNat_lt]
  split_ifs <;> first | rfl | (exfalso; omega)

-- Bit counting operations

/-- Count leading zeros of a 128-bit value. -/
def countLeadingZeros (a : U128) : Nat :=
  if a.a3.val.val = 0 then
    if a.a2.val.val = 0 then
      if a.a1.val.val = 0 then
        u32CountLeadingZeros a.a0.val.val + 96
      else
        u32CountLeadingZeros a.a1.val.val + 64
    else
      u32CountLeadingZeros a.a2.val.val + 32
  else
    u32CountLeadingZeros a.a3.val.val

/-- Count leading ones of a 128-bit value. -/
def countLeadingOnes (a : U128) : Nat :=
  if a.a3.val.val = 2^32 - 1 then
    if a.a2.val.val = 2^32 - 1 then
      if a.a1.val.val = 2^32 - 1 then
        u32CountLeadingOnes a.a0.val.val + 96
      else
        u32CountLeadingOnes a.a1.val.val + 64
    else
      u32CountLeadingOnes a.a2.val.val + 32
  else
    u32CountLeadingOnes a.a3.val.val

/-- Count trailing zeros of a 128-bit value. -/
def countTrailingZeros (a : U128) : Nat :=
  if a.a0.val.val = 0 then
    if a.a1.val.val = 0 then
      if a.a2.val.val = 0 then
        u32CountTrailingZeros a.a3.val.val + 96
      else
        u32CountTrailingZeros a.a2.val.val + 64
    else
      u32CountTrailingZeros a.a1.val.val + 32
  else
    u32CountTrailingZeros a.a0.val.val

/-- Count trailing ones of a 128-bit value. -/
def countTrailingOnes (a : U128) : Nat :=
  if a.a0.val.val = 2^32 - 1 then
    if a.a1.val.val = 2^32 - 1 then
      if a.a2.val.val = 2^32 - 1 then
        u32CountTrailingOnes a.a3.val.val + 96
      else
        u32CountTrailingOnes a.a2.val.val + 64
    else
      u32CountTrailingOnes a.a1.val.val + 32
  else
    u32CountTrailingOnes a.a0.val.val

-- Shift and rotation operations

/-- Left-shift a u128 value by `n` bits (mod 2^128). -/
def shl (a : U128) (n : Nat) : U128 := ofNat (a.toNat * 2^n)

/-- Right-shift a u128 value by `n` bits. -/
def shr (a : U128) (n : Nat) : U128 := ofNat (a.toNat / 2^n)

/-- Left-rotate a u128 value by `n` bits. -/
def rotl (a : U128) (n : Nat) : U128 :=
  let n' := n % 128
  ofNat (a.toNat * 2^n' + a.toNat / 2^(128 - n'))

@[simp] theorem toNat_shl (a : U128) (n : Nat) :
    (a.shl n).toNat = (a.toNat * 2^n) % 2^128 := by
  simp [shl]

@[simp] theorem toNat_shr (a : U128) (n : Nat) :
    (a.shr n).toNat = a.toNat / 2^n := by
  have h : a.toNat / 2^n < 2^128 :=
    lt_of_le_of_lt (Nat.div_le_self _ _) a.toNat_lt
  unfold shr; simp only [ofNat_toNat]; exact Nat.mod_eq_of_lt h

@[simp] theorem toNat_rotl (a : U128) (n : Nat) :
    (a.rotl n).toNat =
      (a.toNat * 2^(n % 128) + a.toNat / 2^(128 - (n % 128))) % 2^128 := by
  simp [rotl]

@[simp] theorem ofNat_toNat_id (a : U128) : U128.ofNat a.toNat = a :=
  eq_of_toNat_eq (by rw [ofNat_toNat]; exact Nat.mod_eq_of_lt a.toNat_lt)

@[simp] theorem shr_zero (a : U128) : a.shr 0 = a := by
  simp [shr, Nat.div_one]

@[simp] theorem rotl_zero (a : U128) : a.rotl 0 = a := by
  apply eq_of_toNat_eq
  rw [toNat_rotl]
  change (a.toNat * 1 + a.toNat / 2 ^ 128) % 2 ^ 128 = a.toNat
  rw [Nat.mul_one, Nat.div_eq_of_lt a.toNat_lt, Nat.add_zero, Nat.mod_eq_of_lt a.toNat_lt]

@[simp] theorem ofNat_or (x y : Nat) : U128.ofNat (x ||| y) = U128.ofNat x ||| U128.ofNat y := by
  refine U128.ext (U32.eq_of_toNat_eq ?_) (U32.eq_of_toNat_eq ?_) (U32.eq_of_toNat_eq ?_) (U32.eq_of_toNat_eq ?_)
  · simpa using (Nat.or_mod_two_pow (a := x) (b := y) (n := 32))
  · simp
    rw [show (x ||| y) / 4294967296 = x / 4294967296 ||| y / 4294967296 by
      simpa using (Nat.or_div_two_pow (a := x) (b := y) (n := 32))]
    simpa using (Nat.or_mod_two_pow (a := x / 2^32) (b := y / 2^32) (n := 32))
  · simp
    rw [show (x ||| y) / 18446744073709551616 = x / 18446744073709551616 ||| y / 18446744073709551616 by
      simpa using (Nat.or_div_two_pow (a := x) (b := y) (n := 64))]
    simpa using (Nat.or_mod_two_pow (a := x / 2^64) (b := y / 2^64) (n := 32))
  · simp
    rw [show (x ||| y) / 79228162514264337593543950336 = x / 79228162514264337593543950336 ||| y / 79228162514264337593543950336 by
      simpa using (Nat.or_div_two_pow (a := x) (b := y) (n := 96))]
    simpa using (Nat.or_mod_two_pow (a := x / 2^96) (b := y / 2^96) (n := 32))

/-- For a value `v < 2^32`, `ofNat v` has `a0 = Felt.ofNat v` and the rest zero. -/
theorem ofNat_of_lt_2_32 (v : Nat) (hv : v < 2^32) :
    (U128.ofNat v).a0.val = Felt.ofNat v ∧
    (U128.ofNat v).a1.val = (0 : Felt) ∧
    (U128.ofNat v).a2.val = (0 : Felt) ∧
    (U128.ofNat v).a3.val = (0 : Felt) := by
  simp only [ofNat_a0, ofNat_a1, ofNat_a2, ofNat_a3]
  refine ⟨congrArg _ (Nat.mod_eq_of_lt hv), ?_, ?_, ?_⟩
  all_goals (
    rw [show v / _ % 2^32 = 0 from by omega]
    show Felt.ofNat 0 = 0; exact Nat.cast_zero)

/-- For a value `v = hi * 2^32 + lo` with `hi < 2^32` and `lo < 2^32`,
    `ofNat v` has `a0 = Felt.ofNat lo`, `a1 = Felt.ofNat hi`, and the rest zero. -/
theorem ofNat_of_lt_2_64 (hi lo : Nat) (hhi : hi < 2^32) (hlo : lo < 2^32) :
    (U128.ofNat (hi * 2^32 + lo)).a0.val = Felt.ofNat lo ∧
    (U128.ofNat (hi * 2^32 + lo)).a1.val = Felt.ofNat hi ∧
    (U128.ofNat (hi * 2^32 + lo)).a2.val = (0 : Felt) ∧
    (U128.ofNat (hi * 2^32 + lo)).a3.val = (0 : Felt) := by
  simp only [ofNat_a0, ofNat_a1, ofNat_a2, ofNat_a3]
  refine ⟨congrArg _ (by omega), congrArg _ (by omega), ?_, ?_⟩
  all_goals (
    rw [show (hi * 2^32 + lo) / _ % 2^32 = 0 from by omega]
    show Felt.ofNat 0 = 0; exact Nat.cast_zero)

/-- For a value `v = a2 * 2^64 + a1 * 2^32 + a0` with 32-bit limbs,
    `ofNat v` recovers those limbs and zero-extends the top limb. -/
theorem ofNat_of_lt_2_96 (a2 a1 a0 : Nat)
    (ha2 : a2 < 2^32) (ha1 : a1 < 2^32) (ha0 : a0 < 2^32) :
    (U128.ofNat (a2 * 2^64 + a1 * 2^32 + a0)).a0.val = Felt.ofNat a0 ∧
    (U128.ofNat (a2 * 2^64 + a1 * 2^32 + a0)).a1.val = Felt.ofNat a1 ∧
    (U128.ofNat (a2 * 2^64 + a1 * 2^32 + a0)).a2.val = Felt.ofNat a2 ∧
    (U128.ofNat (a2 * 2^64 + a1 * 2^32 + a0)).a3.val = (0 : Felt) := by
  simp only [ofNat_a0, ofNat_a1, ofNat_a2, ofNat_a3]
  refine ⟨congrArg _ (by omega), congrArg _ (by omega), congrArg _ (by omega), ?_⟩
  rw [show (a2 * 2^64 + a1 * 2^32 + a0) / 2^96 % 2^32 = 0 from by omega]
  exact Nat.cast_zero

/-- For a packed four-limb 128-bit value, `ofNat` recovers the original limbs. -/
theorem ofNat_of_limbs (a3 a2 a1 a0 : Nat)
    (ha3 : a3 < 2^32) (ha2 : a2 < 2^32) (ha1 : a1 < 2^32) (ha0 : a0 < 2^32) :
    (U128.ofNat (a3 * 2^96 + a2 * 2^64 + a1 * 2^32 + a0)).a0.val = Felt.ofNat a0 ∧
    (U128.ofNat (a3 * 2^96 + a2 * 2^64 + a1 * 2^32 + a0)).a1.val = Felt.ofNat a1 ∧
    (U128.ofNat (a3 * 2^96 + a2 * 2^64 + a1 * 2^32 + a0)).a2.val = Felt.ofNat a2 ∧
    (U128.ofNat (a3 * 2^96 + a2 * 2^64 + a1 * 2^32 + a0)).a3.val = Felt.ofNat a3 := by
  simp only [ofNat_a0, ofNat_a1, ofNat_a2, ofNat_a3]
  exact ⟨congrArg _ (by omega), congrArg _ (by omega), congrArg _ (by omega), congrArg _ (by omega)⟩

theorem shl_eq_mul_ofNat_pow2 (a : U128) (n : Nat) :
    a.shl n = a * U128.ofNat (2^n) := by
  apply eq_of_toNat_eq
  simp only [toNat_shl, toNat_mul, ofNat_toNat]
  conv_rhs => rw [Nat.mul_mod, Nat.mod_mod]
  rw [← Nat.mul_mod]

/-- Shifting left by `n < 128` keeps exactly the low `128 - n` bits, then appends `n` zero bits. -/
theorem mul_pow_mod_2_128 (x n : Nat) (hn : n < 128) :
    (x * 2^n) % 2^128 = (x % 2^(128 - n)) * 2^n := by
  let q := x / 2^(128 - n)
  let r := x % 2^(128 - n)
  have hx : x = q * 2^(128 - n) + r := by
    simpa [q, r, Nat.mul_comm] using (Nat.div_add_mod x (2^(128 - n))).symm
  have hr_lt : r < 2^(128 - n) := by
    dsimp [r]
    exact Nat.mod_lt _ (by positivity)
  have hpow : 2^(128 - n) * 2^n = 2^128 := by
    rw [Nat.mul_comm, ← Nat.pow_add]
    congr 1
    omega
  have hr_mul_lt : r * 2^n < 2^128 := by
    calc
      r * 2^n < 2^(128 - n) * 2^n := by
        exact Nat.mul_lt_mul_of_pos_right hr_lt (by positivity)
      _ = 2^128 := hpow
  calc
    (x * 2^n) % 2^128 = ((q * 2^(128 - n) + r) * 2^n) % 2^128 := by rw [hx]
    _ = (q * 2^128 + r * 2^n) % 2^128 := by rw [Nat.add_mul, Nat.mul_assoc, hpow]
    _ = (r * 2^n + 2^128 * q) % 2^128 := by rw [Nat.add_comm, Nat.mul_comm q (2^128)]
    _ = (r * 2^n) % 2^128 := by rw [Nat.add_mul_mod_self_left]
    _ = r * 2^n := Nat.mod_eq_of_lt hr_mul_lt
    _ = (x % 2^(128 - n)) * 2^n := by rfl

/-- For `n < 128`, rotate-left is exactly the wrapped high fragment OR the shifted body. -/
theorem rotl_eq_or_shl_shr (a : U128) (n : Nat) (hn : n < 128) :
    a.rotl n = a.shr (128 - n) ||| a.shl n := by
  set q := a.toNat / 2^(128 - n)
  set r := a.toNat % 2^(128 - n)
  have hr_lt : r < 2^(128 - n) := by
    dsimp [r]
    exact Nat.mod_lt _ (by positivity)
  have hq_lt : q < 2^n := by
    dsimp [q]
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc
      a.toNat < 2^128 := a.toNat_lt
      _ = 2^n * 2^(128 - n) := by
            rw [← Nat.pow_add]
            congr 1
            omega
  have hr_mul_lt : r * 2^n < 2^128 := by
    calc
      r * 2^n < 2^(128 - n) * 2^n := by
        exact Nat.mul_lt_mul_of_pos_right hr_lt (by positivity)
      _ = 2^128 := by
        rw [Nat.mul_comm, ← Nat.pow_add]
        congr 1
        omega
  have hq_lt128 : q < 2^128 := by
    exact lt_trans hq_lt (by simpa using (Nat.pow_lt_pow_right (by decide : 1 < 2) hn))
  have hor' : r * 2^n + q = r * 2^n ||| q := by
    simpa [Nat.mul_comm] using (Nat.two_pow_add_eq_or_of_lt (i := n) (b := q) hq_lt r)
  have hor : q + r * 2^n = q ||| (r * 2^n) := by
    rw [Nat.add_comm, hor', Nat.or_comm]
  have hshl_nat : (a.toNat * 2^n) % 2^128 = r * 2^n := by
    simpa [r] using mul_pow_mod_2_128 a.toNat n hn
  have hshl : U128.ofNat (r * 2^n) = a.shl n := by
    apply eq_of_toNat_eq
    rw [ofNat_toNat, Nat.mod_eq_of_lt hr_mul_lt, toNat_shl, hshl_nat]
  have hrotl : a.rotl n = U128.ofNat (q + r * 2^n) := by
    apply eq_of_toNat_eq
    have hq_mod : (a.toNat / 2 ^ (128 - n)) % 2 ^ 128 = q := by
      simpa [q] using (Nat.mod_eq_of_lt hq_lt128)
    rw [toNat_rotl, Nat.mod_eq_of_lt hn, ofNat_toNat, Nat.add_mod, hq_mod, hshl_nat, Nat.add_comm]
  calc
    a.rotl n = U128.ofNat (q + r * 2^n) := hrotl
    _ = U128.ofNat (q ||| (r * 2^n)) := by rw [hor]
    _ = U128.ofNat q ||| U128.ofNat (r * 2^n) := by rw [ofNat_or]
    _ = a.shr (128 - n) ||| a.shl n := by
          rw [hshl]
          apply congrArg (fun x => x ||| a.shl n)
          apply eq_of_toNat_eq
          rw [ofNat_toNat, Nat.mod_eq_of_lt hq_lt128, toNat_shr]

/-- Right-rotate a u128 value by `n` bits. -/
def rotr (a : U128) (n : Nat) : U128 :=
  let n' := n % 128
  ofNat (a.toNat / 2^n' + a.toNat * 2^(128 - n'))

@[simp] theorem toNat_rotr (a : U128) (n : Nat) :
    (a.rotr n).toNat =
      (a.toNat / 2^(n % 128) + a.toNat * 2^(128 - (n % 128))) % 2^128 := by
  simp [rotr]

@[simp] theorem rotr_zero (a : U128) : a.rotr 0 = a := by
  apply eq_of_toNat_eq
  rw [toNat_rotr]
  change (a.toNat / 1 + a.toNat * 2 ^ 128) % 2 ^ 128 = a.toNat
  rw [Nat.div_one, show a.toNat + a.toNat * 2 ^ 128 =
      a.toNat + 2 ^ 128 * a.toNat from by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt a.toNat_lt]

/-- For `n < 128`, rotate-right is exactly the shifted-left body OR the shifted-right fragment. -/
theorem rotr_eq_or_shr_shl (a : U128) (n : Nat) (hn : n < 128) :
    a.rotr n = a.shl (128 - n) ||| a.shr n := by
  set q := a.toNat / 2^n
  set r := a.toNat % 2^n
  have hr_lt : r < 2^n := by
    dsimp [r]
    exact Nat.mod_lt _ (by positivity)
  have hq_lt : q < 2^(128 - n) := by
    dsimp [q]
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc
      a.toNat < 2^128 := a.toNat_lt
      _ = 2^(128 - n) * 2^n := by
            rw [← Nat.pow_add]
            congr 1
            omega
  have hr_mul_lt : r * 2^(128 - n) < 2^128 := by
    calc
      r * 2^(128 - n) < 2^n * 2^(128 - n) := by
        exact Nat.mul_lt_mul_of_pos_right hr_lt (by positivity)
      _ = 2^128 := by
        rw [Nat.mul_comm, ← Nat.pow_add]
        congr 1
        omega
  have hq_lt128 : q < 2^128 :=
    lt_of_le_of_lt (Nat.div_le_self _ _) a.toNat_lt
  have hor' : r * 2^(128 - n) + q = r * 2^(128 - n) ||| q := by
    simpa [Nat.mul_comm] using
      (Nat.two_pow_add_eq_or_of_lt (i := 128 - n) (b := q) hq_lt r)
  have hor : q + r * 2^(128 - n) = q ||| (r * 2^(128 - n)) := by
    rw [Nat.add_comm, hor', Nat.or_comm]
  have hshl_nat : (a.toNat * 2^(128 - n)) % 2^128 = r * 2^(128 - n) := by
    by_cases hn0 : n = 0
    · subst hn0; simp [r, Nat.mod_one]
    · have h128n : 128 - n < 128 := by omega
      have := mul_pow_mod_2_128 a.toNat (128 - n) h128n
      rwa [show 128 - (128 - n) = n from by omega] at this
  have hshl : U128.ofNat (r * 2^(128 - n)) = a.shl (128 - n) := by
    apply eq_of_toNat_eq
    rw [ofNat_toNat, Nat.mod_eq_of_lt hr_mul_lt, toNat_shl, hshl_nat]
  have hrotr : a.rotr n = U128.ofNat (q + r * 2^(128 - n)) := by
    apply eq_of_toNat_eq
    have hq_mod : (a.toNat / 2 ^ n) % 2 ^ 128 = q := by
      simpa [q] using (Nat.mod_eq_of_lt hq_lt128)
    rw [toNat_rotr, Nat.mod_eq_of_lt hn, ofNat_toNat, Nat.add_mod, hq_mod, hshl_nat]
  calc
    a.rotr n = U128.ofNat (q + r * 2^(128 - n)) := hrotr
    _ = U128.ofNat (q ||| (r * 2^(128 - n))) := by rw [hor]
    _ = U128.ofNat ((r * 2^(128 - n)) ||| q) := by rw [Nat.or_comm]
    _ = U128.ofNat (r * 2^(128 - n)) ||| U128.ofNat q := by rw [ofNat_or]
    _ = a.shl (128 - n) ||| a.shr n := by
          rw [hshl]
          apply congrArg (fun x => a.shl (128 - n) ||| x)
          apply eq_of_toNat_eq
          rw [ofNat_toNat, Nat.mod_eq_of_lt hq_lt128, toNat_shr]

end U128

/-- `Felt.ofNat` distributes over addition. -/
theorem felt_ofNat_add (n m : Nat) :
    Felt.ofNat (n + m) = Felt.ofNat n + Felt.ofNat m := by
  simp [Felt.ofNat, Nat.cast_add]

/-- Reducing an addend modulo `m` before taking the outer modulo does not change the result. -/
theorem add_mod_right_mod (x y m : Nat) : (x + y % m) % m = (x + y) % m := by
  rw [Nat.add_mod, Nat.mod_mod_of_dvd _ (dvd_refl m), ← Nat.add_mod]

/-- Nested modulo reduction under two additions can be flattened before the outer modulo. -/
theorem add_add_mod_right_mod (a b c m : Nat) :
    (a + ((b + c % m) % m)) % m = (a + (b + c)) % m := by
  calc
    (a + ((b + c % m) % m)) % m = (a + (b + c % m)) % m := by
      rw [add_mod_right_mod]
    _ = ((a + b) + c % m) % m := by
      rw [Nat.add_assoc]
    _ = ((a + b) + c) % m := by
      rw [add_mod_right_mod]
    _ = (a + (b + c)) % m := by
      rw [Nat.add_assoc]

-- ============================================================================
-- Carry chain bridging lemmas for addition
-- ============================================================================

/-- The schoolbook carry-chain addition of four u32 limbs produces the correct
    decomposition of the total sum into 32-bit words. -/
theorem u128_add_carry_chain (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) :
    let total := a3 * 2^96 + a2 * 2^64 + a1 * 2^32 + a0 +
                 (b3 * 2^96 + b2 * 2^64 + b1 * 2^32 + b0)
    let sum0 := b0 + a0
    let sum1 := sum0 / 2^32 + a1 + b1
    let sum2 := sum1 / 2^32 + a2 + b2
    let sum3 := sum2 / 2^32 + a3 + b3
    sum0 % 2^32 = total % 2^32 ∧
    sum1 % 2^32 = (total / 2^32) % 2^32 ∧
    sum2 % 2^32 = (total / 2^64) % 2^32 ∧
    sum3 % 2^32 = (total / 2^96) % 2^32 := by
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- The overflow bit of the carry-chain addition equals the carry out of the full sum. -/
theorem u128_add_carry_overflow (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) :
    let total := a3 * 2^96 + a2 * 2^64 + a1 * 2^32 + a0 +
                 (b3 * 2^96 + b2 * 2^64 + b1 * 2^32 + b0)
    let sum0 := b0 + a0
    let sum1 := sum0 / 2^32 + a1 + b1
    let sum2 := sum1 / 2^32 + a2 + b2
    let sum3 := sum2 / 2^32 + a3 + b3
    sum3 / 2^32 = total / 2^128 := by
  omega

/-- Carry chain bridging at the Felt level: output limbs match U128 addition,
    and the overflow equals the carry out of the full sum. -/
theorem u128_add_carry_bridge (a b : U128) :
    let sum0 := b.a0.val.val + a.a0.val.val
    let sum1 := sum0 / 2^32 + a.a1.val.val + b.a1.val.val
    let sum2 := sum1 / 2^32 + a.a2.val.val + b.a2.val.val
    let sum3 := sum2 / 2^32 + a.a3.val.val + b.a3.val.val
    Felt.ofNat (sum0 % 2^32) = (a + b).a0.val ∧
    Felt.ofNat (sum1 % 2^32) = (a + b).a1.val ∧
    Felt.ofNat (sum2 % 2^32) = (a + b).a2.val ∧
    Felt.ofNat (sum3 % 2^32) = (a + b).a3.val ∧
    sum3 / 2^32 = (a.toNat + b.toNat) / 2^128 := by
  have cc := u128_add_carry_chain a.a0.val.val a.a1.val.val a.a2.val.val a.a3.val.val
    b.a0.val.val b.a1.val.val b.a2.val.val b.a3.val.val
  have co := u128_add_carry_overflow a.a0.val.val a.a1.val.val a.a2.val.val a.a3.val.val
    b.a0.val.val b.a1.val.val b.a2.val.val b.a3.val.val
  simp only [HAdd.hAdd, Add.add, U128.ofNat, U128.toNat] at cc co ⊢
  exact ⟨congrArg _ cc.1, congrArg _ cc.2.1, congrArg _ cc.2.2.1, congrArg _ cc.2.2.2, co⟩

-- ============================================================================
-- Carry-chain bridging lemmas for q * b + r (used by u128 divmod)
-- ============================================================================

/-- Column 0 of the `q * b + r` carry chain. -/
def u128DivmodCol0 (q0 b0 r0 : Nat) : Nat :=
  q0 * b0 + r0

/-- Column 1 of the `q * b + r` carry chain. -/
def u128DivmodCol1 (q0 q1 b0 b1 r0 r1 : Nat) : Nat :=
  q0 * b1 + q1 * b0 + r1 + u128DivmodCol0 q0 b0 r0 / 2 ^ 32

/-- Column 2 of the `q * b + r` carry chain. -/
def u128DivmodCol2 (q0 q1 q2 b0 b1 b2 r0 r1 r2 : Nat) : Nat :=
  q0 * b2 + q1 * b1 + q2 * b0 + r2 + u128DivmodCol1 q0 q1 b0 b1 r0 r1 / 2 ^ 32

/-- The carry input accumulated before the final multiply-add in column 2. -/
def u128DivmodCol2CarryIn (q0 q1 q2 b0 b1 r0 r1 : Nat) : Nat :=
  q2 * b0 + q1 * b1 + u128DivmodCol1 q0 q1 b0 b1 r0 r1 / 2 ^ 32

/-- Column 3 of the `q * b + r` carry chain. -/
def u128DivmodCol3 (q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 : Nat) : Nat :=
  q0 * b3 + q1 * b2 + q2 * b1 + q3 * b0 + r3 +
    u128DivmodCol2 q0 q1 q2 b0 b1 b2 r0 r1 r2 / 2 ^ 32

/-- Raw little-endian u128 value from four limbs. -/
def u128RawValue (a0 a1 a2 a3 : Nat) : Nat :=
  a3 * 2 ^ 96 + a2 * 2 ^ 64 + a1 * 2 ^ 32 + a0

private theorem u128DivmodCol2CarryIn_mul_pow_le
    (q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 : Nat) :
    let base := 2 ^ 32
    u128DivmodCol2CarryIn q0 q1 q2 b0 b1 r0 r1 * base ^ 2 ≤
      u128RawValue q0 q1 q2 q3 * u128RawValue b0 b1 b2 b3 +
        u128RawValue r0 r1 r2 r3 := by
  let base := 2 ^ 32
  have hcarry0 : ((q0 * b0 + r0) / base) * base ≤ q0 * b0 + r0 := by
    exact Nat.div_mul_le_self _ _
  have hcarry1 :
      (u128DivmodCol1 q0 q1 b0 b1 r0 r1 / base) * base ^ 2 ≤
        (q0 * b1 + q1 * b0 + r1) * base + (q0 * b0 + r0) := by
    have hdiv : (u128DivmodCol1 q0 q1 b0 b1 r0 r1 / base) * base ≤
        u128DivmodCol1 q0 q1 b0 b1 r0 r1 := by
      exact Nat.div_mul_le_self _ _
    have hdiv' := Nat.mul_le_mul_right base hdiv
    have hbase :
        (u128DivmodCol1 q0 q1 b0 b1 r0 r1 / base) * base ^ 2 ≤
          u128DivmodCol1 q0 q1 b0 b1 r0 r1 * base := by
      simpa [pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hdiv'
    have hrepr :
        u128DivmodCol1 q0 q1 b0 b1 r0 r1 * base =
          (q0 * b1 + q1 * b0 + r1) * base + ((q0 * b0 + r0) / base) * base := by
      unfold u128DivmodCol1 u128DivmodCol0
      ring
    rw [hrepr] at hbase
    exact le_trans hbase (by omega)
  have hpre :
      u128DivmodCol2CarryIn q0 q1 q2 b0 b1 r0 r1 * base ^ 2 ≤
        (q0 * b0 + r0) + (q0 * b1 + q1 * b0 + r1) * base + (q2 * b0 + q1 * b1) * base ^ 2 := by
    have hmain := Nat.add_le_add_left hcarry1 ((q2 * b0 + q1 * b1) * base ^ 2)
    have hsum :
        u128DivmodCol2CarryIn q0 q1 q2 b0 b1 r0 r1 * base ^ 2 =
          (q2 * b0 + q1 * b1) * base ^ 2 +
            (u128DivmodCol1 q0 q1 b0 b1 r0 r1 / base) * base ^ 2 := by
      unfold u128DivmodCol2CarryIn
      ring
    rw [hsum]
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hmain
  have hexpand :
      u128RawValue q0 q1 q2 q3 * u128RawValue b0 b1 b2 b3 + u128RawValue r0 r1 r2 r3 =
        ((q0 * b0 + r0) + (q0 * b1 + q1 * b0 + r1) * base + (q2 * b0 + q1 * b1) * base ^ 2) +
          ((q0 * b2 + r2) * base ^ 2 +
            (q0 * b3 + q1 * b2 + q2 * b1 + q3 * b0 + r3) * base ^ 3 +
            (q1 * b3 + q2 * b2 + q3 * b1) * base ^ 4 +
            (q2 * b3 + q3 * b2) * base ^ 5 +
            (q3 * b3) * base ^ 6) := by
    unfold u128RawValue
    ring
  have hextra :
      0 ≤ (q0 * b2 + r2) * base ^ 2 +
          (q0 * b3 + q1 * b2 + q2 * b1 + q3 * b0 + r3) * base ^ 3 +
          (q1 * b3 + q2 * b2 + q3 * b1) * base ^ 4 +
          (q2 * b3 + q3 * b2) * base ^ 5 +
          (q3 * b3) * base ^ 6 := by
    have h0 : 0 ≤ (q0 * b2 + r2) * base ^ 2 := Nat.zero_le _
    have h1 : 0 ≤ (q0 * b3 + q1 * b2 + q2 * b1 + q3 * b0 + r3) * base ^ 3 := Nat.zero_le _
    have h2 : 0 ≤ (q1 * b3 + q2 * b2 + q3 * b1) * base ^ 4 := Nat.zero_le _
    have h3 : 0 ≤ (q2 * b3 + q3 * b2) * base ^ 5 := Nat.zero_le _
    have h4 : 0 ≤ (q3 * b3) * base ^ 6 := Nat.zero_le _
    omega
  have hbound :
      (q0 * b0 + r0) + (q0 * b1 + q1 * b0 + r1) * base + (q2 * b0 + q1 * b1) * base ^ 2 ≤
        u128RawValue q0 q1 q2 q3 * u128RawValue b0 b1 b2 b3 + u128RawValue r0 r1 r2 r3 := by
    nlinarith [hexpand, hextra]
  exact le_trans hpre hbound

/-- The carry input accumulated before the final multiply-add in column 2 fits below `2^64`
    whenever `q * b + r` fits in 128 bits. -/
theorem u128DivmodCol2CarryIn_lt_2_64
    (q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 : Nat)
    (htotal :
      u128RawValue q0 q1 q2 q3 * u128RawValue b0 b1 b2 b3 +
        u128RawValue r0 r1 r2 r3 < 2 ^ 128) :
    u128DivmodCol2CarryIn q0 q1 q2 b0 b1 r0 r1 < 2 ^ 64 := by
  let base := 2 ^ 32
  have hmul := u128DivmodCol2CarryIn_mul_pow_le q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3
  by_contra hnot
  have hge : base ^ 2 ≤ u128DivmodCol2CarryIn q0 q1 q2 b0 b1 r0 r1 := by
    simpa [base, pow_two] using Nat.not_lt.mp hnot
  have hpow : 2 ^ 128 ≤ u128DivmodCol2CarryIn q0 q1 q2 b0 b1 r0 r1 * base ^ 2 := by
    have hmul' := Nat.mul_le_mul_right (base ^ 2) hge
    simpa [base, pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul'
  exact (not_lt_of_ge (le_trans hpow hmul)) htotal

/-- Dividing the column-2 carry input by `2^32` yields a u32 carry word. -/
theorem u128DivmodCol2CarryIn_div_lt_2_32
    (q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 : Nat)
    (htotal :
      u128RawValue q0 q1 q2 q3 * u128RawValue b0 b1 b2 b3 +
        u128RawValue r0 r1 r2 r3 < 2 ^ 128) :
    u128DivmodCol2CarryIn q0 q1 q2 b0 b1 r0 r1 / 2 ^ 32 < 2 ^ 32 := by
  have hlt := u128DivmodCol2CarryIn_lt_2_64 q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 htotal
  have hlt' : u128DivmodCol2CarryIn q0 q1 q2 b0 b1 r0 r1 < (2 ^ 32) * (2 ^ 32) := by
    simpa [pow_two] using hlt
  exact Nat.div_lt_of_lt_mul hlt'

/-- If `q * b` fits below `2^128`, every product term that contributes only above the
    low 128 bits must vanish. -/
theorem u128HighTermsZeroOfMulLt
    (q0 q1 q2 q3 b0 b1 b2 b3 : Nat)
    (hq0 : q0 < 2 ^ 32) (hq1 : q1 < 2 ^ 32) (hq2 : q2 < 2 ^ 32) (hq3 : q3 < 2 ^ 32)
    (hb0 : b0 < 2 ^ 32) (hb1 : b1 < 2 ^ 32) (hb2 : b2 < 2 ^ 32) (hb3 : b3 < 2 ^ 32)
    (hmul :
      (q3 * 2 ^ 96 + q2 * 2 ^ 64 + q1 * 2 ^ 32 + q0) *
        (b3 * 2 ^ 96 + b2 * 2 ^ 64 + b1 * 2 ^ 32 + b0) < 2 ^ 128) :
    q1 * b3 = 0 ∧
    q2 * b2 = 0 ∧
    q3 * b1 = 0 ∧
    q2 * b3 = 0 ∧
    q3 * b2 = 0 ∧
    q3 * b3 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_contra hneq
    have hpos : 0 < q1 * b3 := by omega
    have hbound :
        2 ^ 128 ≤
          (q3 * 2 ^ 96 + q2 * 2 ^ 64 + q1 * 2 ^ 32 + q0) *
            (b3 * 2 ^ 96 + b2 * 2 ^ 64 + b1 * 2 ^ 32 + b0) := by
      have hq : q1 * 2 ^ 32 ≤ q3 * 2 ^ 96 + q2 * 2 ^ 64 + q1 * 2 ^ 32 + q0 := by omega
      have hb : b3 * 2 ^ 96 ≤ b3 * 2 ^ 96 + b2 * 2 ^ 64 + b1 * 2 ^ 32 + b0 := by omega
      have hmain : 2 ^ 128 ≤ (q1 * 2 ^ 32) * (b3 * 2 ^ 96) := by
        calc
          2 ^ 128 = 1 * 1 * 2 ^ 128 := by ring
          _ ≤ q1 * b3 * 2 ^ 128 := by
            have : 1 ≤ q1 * b3 := by omega
            nlinarith
          _ = (q1 * 2 ^ 32) * (b3 * 2 ^ 96) := by ring
      exact le_trans hmain (Nat.mul_le_mul hq hb)
    omega
  · by_contra hneq
    have hpos : 0 < q2 * b2 := by omega
    have hq : q2 * 2 ^ 64 ≤ q3 * 2 ^ 96 + q2 * 2 ^ 64 + q1 * 2 ^ 32 + q0 := by omega
    have hb : b2 * 2 ^ 64 ≤ b3 * 2 ^ 96 + b2 * 2 ^ 64 + b1 * 2 ^ 32 + b0 := by omega
    have hmain : 2 ^ 128 ≤ (q2 * 2 ^ 64) * (b2 * 2 ^ 64) := by
      calc
        2 ^ 128 = 1 * 1 * 2 ^ 128 := by ring
        _ ≤ q2 * b2 * 2 ^ 128 := by
          have : 1 ≤ q2 * b2 := by omega
          nlinarith
        _ = (q2 * 2 ^ 64) * (b2 * 2 ^ 64) := by ring
    exact (not_lt_of_ge (le_trans hmain (Nat.mul_le_mul hq hb))) hmul |> False.elim
  · by_contra hneq
    have hpos : 0 < q3 * b1 := by omega
    have hq : q3 * 2 ^ 96 ≤ q3 * 2 ^ 96 + q2 * 2 ^ 64 + q1 * 2 ^ 32 + q0 := by omega
    have hb : b1 * 2 ^ 32 ≤ b3 * 2 ^ 96 + b2 * 2 ^ 64 + b1 * 2 ^ 32 + b0 := by omega
    have hmain : 2 ^ 128 ≤ (q3 * 2 ^ 96) * (b1 * 2 ^ 32) := by
      calc
        2 ^ 128 = 1 * 1 * 2 ^ 128 := by ring
        _ ≤ q3 * b1 * 2 ^ 128 := by
          have : 1 ≤ q3 * b1 := by omega
          nlinarith
        _ = (q3 * 2 ^ 96) * (b1 * 2 ^ 32) := by ring
    exact (not_lt_of_ge (le_trans hmain (Nat.mul_le_mul hq hb))) hmul |> False.elim
  · by_contra hneq
    have hpos : 0 < q2 * b3 := by omega
    have hq : q2 * 2 ^ 64 ≤ q3 * 2 ^ 96 + q2 * 2 ^ 64 + q1 * 2 ^ 32 + q0 := by omega
    have hb : b3 * 2 ^ 96 ≤ b3 * 2 ^ 96 + b2 * 2 ^ 64 + b1 * 2 ^ 32 + b0 := by omega
    have hmain : 2 ^ 160 ≤ (q2 * 2 ^ 64) * (b3 * 2 ^ 96) := by
      calc
        2 ^ 160 = 1 * 1 * 2 ^ 160 := by ring
        _ ≤ q2 * b3 * 2 ^ 160 := by
          have : 1 ≤ q2 * b3 := by omega
          nlinarith
        _ = (q2 * 2 ^ 64) * (b3 * 2 ^ 96) := by ring
    have : 2 ^ 128 ≤
        (q3 * 2 ^ 96 + q2 * 2 ^ 64 + q1 * 2 ^ 32 + q0) *
          (b3 * 2 ^ 96 + b2 * 2 ^ 64 + b1 * 2 ^ 32 + b0) := by
      exact le_trans (by omega) (le_trans hmain (Nat.mul_le_mul hq hb))
    omega
  · by_contra hneq
    have hpos : 0 < q3 * b2 := by omega
    have hq : q3 * 2 ^ 96 ≤ q3 * 2 ^ 96 + q2 * 2 ^ 64 + q1 * 2 ^ 32 + q0 := by omega
    have hb : b2 * 2 ^ 64 ≤ b3 * 2 ^ 96 + b2 * 2 ^ 64 + b1 * 2 ^ 32 + b0 := by omega
    have hmain : 2 ^ 160 ≤ (q3 * 2 ^ 96) * (b2 * 2 ^ 64) := by
      calc
        2 ^ 160 = 1 * 1 * 2 ^ 160 := by ring
        _ ≤ q3 * b2 * 2 ^ 160 := by
          have : 1 ≤ q3 * b2 := by omega
          nlinarith
        _ = (q3 * 2 ^ 96) * (b2 * 2 ^ 64) := by ring
    have : 2 ^ 128 ≤
        (q3 * 2 ^ 96 + q2 * 2 ^ 64 + q1 * 2 ^ 32 + q0) *
          (b3 * 2 ^ 96 + b2 * 2 ^ 64 + b1 * 2 ^ 32 + b0) := by
      exact le_trans (by omega) (le_trans hmain (Nat.mul_le_mul hq hb))
    omega
  · by_contra hneq
    have hpos : 0 < q3 * b3 := by omega
    have hq : q3 * 2 ^ 96 ≤ q3 * 2 ^ 96 + q2 * 2 ^ 64 + q1 * 2 ^ 32 + q0 := by omega
    have hb : b3 * 2 ^ 96 ≤ b3 * 2 ^ 96 + b2 * 2 ^ 64 + b1 * 2 ^ 32 + b0 := by omega
    have hmain : 2 ^ 192 ≤ (q3 * 2 ^ 96) * (b3 * 2 ^ 96) := by
      calc
        2 ^ 192 = 1 * 1 * 2 ^ 192 := by ring
        _ ≤ q3 * b3 * 2 ^ 192 := by
          have : 1 ≤ q3 * b3 := by omega
          nlinarith
        _ = (q3 * 2 ^ 96) * (b3 * 2 ^ 96) := by ring
    have : 2 ^ 128 ≤
        (q3 * 2 ^ 96 + q2 * 2 ^ 64 + q1 * 2 ^ 32 + q0) *
          (b3 * 2 ^ 96 + b2 * 2 ^ 64 + b1 * 2 ^ 32 + b0) := by
      exact le_trans (by omega) (le_trans hmain (Nat.mul_le_mul hq hb))
    omega

-- ============================================================================
-- Comparison bridging lemmas
-- ============================================================================

/-- Helper: val of a Felt conditional (if p then 1 else 0) -/
private theorem felt_ite_val (p : Prop) [Decidable p] :
    (if p then (1 : Felt) else (0 : Felt)).val = if p then 1 else 0 := by
  split <;> simp [Felt.val_one']

private theorem u128_borrow1_eq (a0 a1 b0 b1 : Felt)
    (ha0 : a0.isU32 = true) (hb0 : b0.isU32 = true) :
    u128Borrow1 a0 a1 b0 b1 =
    if decide (a1.val * 2^32 + a0.val < b1.val * 2^32 + b0.val) then (1 : Felt) else 0 := by
  simp only [Felt.isU32, decide_eq_true_eq] at ha0 hb0
  unfold u128Borrow1 u128Sub0 u128Sub1 u32OverflowingSub u32Max
  congr 1; apply propext
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · intro h; rcases h with h | h
    · split_ifs at h <;> omega
    · omega
  · intro h
    by_cases h1 : a1.val < b1.val
    · right; exact h1
    · left; split_ifs <;> omega

private theorem u128_borrow2_eq (a0 a1 a2 b0 b1 b2 : Felt)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true) :
    u128Borrow2 a0 a1 a2 b0 b1 b2 =
    if decide (a2.val * 2^64 + a1.val * 2^32 + a0.val <
              b2.val * 2^64 + b1.val * 2^32 + b0.val) then (1 : Felt) else 0 := by
  simp only [Felt.isU32, decide_eq_true_eq] at ha0 ha1 hb0 hb1
  unfold u128Borrow2 u128Sub2 u32OverflowingSub u32Max
  rw [u128_borrow1_eq a0 a1 b0 b1 (by simpa [Felt.isU32]) (by simpa [Felt.isU32])]
  rw [felt_ite_val]
  congr 1; apply propext
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · intro h; rcases h with h | h
    · split_ifs at h <;> omega
    · omega
  · intro h
    by_cases h2 : a2.val < b2.val
    · right; exact h2
    · left; split_ifs <;> omega

/-- The 4-limb borrow-based comparison is equivalent to `a.toNat < b.toNat`. -/
theorem u128LtBool_iff_lt (a b : U128) :
    u128LtBool a.a0.val a.a1.val a.a2.val a.a3.val b.a0.val b.a1.val b.a2.val b.a3.val =
    decide (a.toNat < b.toNat) := by
  unfold u128LtBool u128Sub3 u32OverflowingSub u32Max
  rw [u128_borrow2_eq a.a0.val a.a1.val a.a2.val b.a0.val b.a1.val b.a2.val
    a.a0.isU32 a.a1.isU32 b.a0.isU32 b.a1.isU32]
  rw [felt_ite_val]
  simp only [U128.toNat]
  have ha0' := a.a0.val_lt; have ha1' := a.a1.val_lt
  have ha2' := a.a2.val_lt; have ha3' := a.a3.val_lt
  have hb0' := b.a0.val_lt; have hb1' := b.a1.val_lt
  have hb2' := b.a2.val_lt; have hb3' := b.a3.val_lt
  -- Case-split on a3 vs b3 and the 3-limb borrow condition
  by_cases h3 : a.a3.val.val < b.a3.val.val
  · simp [decide_eq_true h3]; omega
  · by_cases h3e : a.a3.val.val = b.a3.val.val
    · simp only [h3e]
      split_ifs <;> simp_all <;> omega
    · have h3gt : a.a3.val.val > b.a3.val.val := by omega
      simp [show ¬(a.a3.val.val < b.a3.val.val) from h3]
      split_ifs <;> simp_all <;> omega

-- ============================================================================
-- Subtraction borrow-chain bridging lemmas
-- ============================================================================

set_option maxHeartbeats 64000000 in
/-- Borrow chain bridging at the Felt level: output limbs match U128 subtraction,
    and the borrow flag matches the comparison result. -/
theorem u128_sub_borrow_bridge (a b : U128) :
    let r0 := u128Sub0 a.a0.val b.a0.val
    let r1 := u32OverflowingSub (u128Sub1 a.a1.val b.a1.val).2 r0.1
    let r2 := u32OverflowingSub (u128Sub2 a.a2.val b.a2.val).2
                (u128Borrow1 a.a0.val a.a1.val b.a0.val b.a1.val).val
    let r3 := u32OverflowingSub (u128Sub3 a.a3.val b.a3.val).2
                (u128Borrow2 a.a0.val a.a1.val a.a2.val b.a0.val b.a1.val b.a2.val).val
    Felt.ofNat r0.2 = (a - b).a0.val ∧
    Felt.ofNat r1.2 = (a - b).a1.val ∧
    Felt.ofNat r2.2 = (a - b).a2.val ∧
    Felt.ofNat r3.2 = (a - b).a3.val ∧
    u128LtBool a.a0.val a.a1.val a.a2.val a.a3.val
               b.a0.val b.a1.val b.a2.val b.a3.val = decide (a < b) := by
  refine ⟨?_, ?_, ?_, ?_, u128LtBool_iff_lt a b⟩
  all_goals (
    simp only [u128Sub0, u128Sub1, u128Sub2, u128Sub3,
      u128Borrow1, u128Borrow2, u32OverflowingSub, u32Max,
      HSub.hSub, Sub.sub, U128.ofNat, U128.toNat]
    congr 1
    have ha0 := a.a0.val_lt; have ha1 := a.a1.val_lt
    have ha2 := a.a2.val_lt; have ha3 := a.a3.val_lt
    have hb0 := b.a0.val_lt; have hb1 := b.a1.val_lt
    have hb2 := b.a2.val_lt; have hb3 := b.a3.val_lt
    simp only [Nat.sub_eq])
  · split <;> omega
  · split <;> split <;> split <;> simp_all <;> omega
  · split <;> split <;> split <;> split <;> split <;> simp_all <;> omega
  · split <;> split <;> split <;> split <;> split <;> split <;> split <;> simp_all <;> omega

-- ============================================================================
-- Reusable shift-right limb decomposition lemmas
-- ============================================================================
-- These capture the core arithmetic identities used in the u128 shr proofs,
-- where a right-shift by n bits across a pair of adjacent 32-bit limbs
-- produces (lo / 2^n) ||| ((hi * 2^(32-n)) % 2^32).

/-- Dividing a two-limb value `hi * 2^32 + lo` by `2^n` gives `hi * 2^(32-n) + lo / 2^n`. -/
theorem u32_pair_div (hi lo n : Nat) (hn_pos : 0 < n) (hn : n < 32) :
    (hi * 2^32 + lo) / 2^n = hi * 2^(32 - n) + lo / 2^n := by
  conv_lhs =>
    rw [show (2 : Nat)^32 = 2^n * 2^(32 - n) from by rw [← Nat.pow_add]; congr 1; omega,
        ← mul_assoc, mul_comm hi (2^n), mul_assoc]
  rw [Nat.mul_add_div (by positivity : 2^n > 0)]

/-- `(hi * 2^(32-n)) % 2^32 = (hi % 2^n) * 2^(32-n)`: only the low `n` bits of `hi` survive. -/
theorem u32_mul_pow_mod (hi n : Nat) (hn_pos : 0 < n) (hn : n < 32) :
    (hi * 2^(32 - n)) % 2^32 = (hi % 2^n) * 2^(32 - n) := by
  rw [show (2 : Nat)^32 = 2^n * 2^(32 - n) from by rw [← Nat.pow_add]; congr 1; omega,
      Nat.mul_mod_mul_right]

/-- The non-overlapping parts of a shifted limb pair fit in 32 bits. -/
theorem u32_shr_sum_lt (hi lo n : Nat) (hlo : lo < 2^32)
    (hn_pos : 0 < n) (hn : n < 32) :
    (hi % 2^n) * 2^(32-n) + lo / 2^n < 2^32 := by
  have h_pow : 2^n * 2^(32 - n) = 2^32 := by rw [← Nat.pow_add]; congr 1; omega
  have h_div : lo / 2^n < 2^(32-n) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    have : 2^(32-n) * 2^n = 2^32 := by rw [mul_comm]; exact h_pow
    omega
  calc (hi % 2^n) * 2^(32-n) + lo / 2^n
      ≤ (2^n - 1) * 2^(32-n) + lo / 2^n :=
        Nat.add_le_add_right (Nat.mul_le_mul_right _
          (Nat.le_sub_one_of_lt (Nat.mod_lt _ (by positivity)))) _
    _ < (2^n - 1) * 2^(32-n) + 2^(32-n) := Nat.add_lt_add_left h_div _
    _ = 2^n * 2^(32-n) := by
        rw [Nat.sub_one_mul]
        exact Nat.sub_add_cancel (Nat.le_mul_of_pos_left _ (by positivity))
    _ = 2^32 := h_pow

/-- The bitwise OR of shifted limb parts equals the correct 32-bit window:
    `(lo / 2^n) ||| ((hi * 2^(32-n)) % 2^32) = ((hi * 2^32 + lo) / 2^n) % 2^32`.
    This is the core identity behind the shr limb-merging pattern in MASM. -/
theorem u32_shr_or_eq (lo hi n : Nat)
    (hlo : lo < 2^32) (hn_pos : 0 < n) (hn : n < 32) :
    (lo / 2^n) ||| ((hi * 2^(32 - n)) % 2^32) = ((hi * 2^32 + lo) / 2^n) % 2^32 := by
  rw [u32_mul_pow_mod hi n hn_pos hn]
  have h_div_bound : lo / 2^n < 2^(32-n) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    have : 2^(32-n) * 2^n = 2^32 := by rw [← Nat.pow_add]; congr 1; omega
    omega
  rw [Nat.or_comm, mul_comm (hi % 2^n) (2^(32-n)),
      ← Nat.two_pow_add_eq_or_of_lt h_div_bound,
      mul_comm (2^(32-n)) (hi % 2^n)]
  rw [u32_pair_div hi lo n hn_pos hn]
  symm
  rw [Nat.add_mod, u32_mul_pow_mod hi n hn_pos hn,
      Nat.mod_eq_of_lt (show lo / 2^n < 2^32 from
        lt_trans h_div_bound (Nat.pow_lt_pow_right (by omega) (by omega))),
      Nat.mod_eq_of_lt (u32_shr_sum_lt hi lo n hlo hn_pos hn)]

/-- The merged low limb produced by a cross-limb right shift fits in 32 bits. -/
theorem u32_shr_or_lt (lo hi n : Nat)
    (hlo : lo < 2^32) (hn_pos : 0 < n) (hn : n < 32) :
    (lo / 2^n) ||| ((hi * 2^(32 - n)) % 2^32) < 2^32 := by
  rw [u32_shr_or_eq lo hi n hlo hn_pos hn]
  exact Nat.mod_lt _ (by positivity)

/-- Decompose a shifted two-limb word into its high quotient limb and merged low limb. -/
theorem u32_pair_shr_decomp (lo hi n : Nat)
    (hlo : lo < 2^32) (hn_pos : 0 < n) (hn : n < 32) :
    (hi * 2^32 + lo) / 2^n =
      (hi / 2^n) * 2^32 + ((lo / 2^n) ||| ((hi * 2^(32 - n)) % 2^32)) := by
  have hor :
      ((lo / 2^n) ||| ((hi * 2^(32 - n)) % 2^32)) =
      lo / 2^n + (hi % 2^n) * 2^(32 - n) := by
    have hdiv : lo / 2^n < 2^(32 - n) := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]
      have : 2^(32 - n) * 2^n = 2^32 := by
        rw [← Nat.pow_add]
        congr 1
        omega
      omega
    rw [u32_mul_pow_mod hi n hn_pos hn]
    rw [Nat.or_comm, mul_comm (hi % 2^n) (2^(32 - n)),
      ← Nat.two_pow_add_eq_or_of_lt hdiv,
      mul_comm (2^(32 - n)) (hi % 2^n)]
    omega
  rw [hor, u32_pair_div hi lo n hn_pos hn]
  have hdecomp :
      hi * 2^(32 - n) =
      (hi / 2^n) * 2^32 + (hi % 2^n) * 2^(32 - n) := by
    calc
      hi * 2^(32 - n)
          = ((hi / 2^n) * 2^n + hi % 2^n) * 2^(32 - n) := by
              conv_lhs => rw [(Nat.div_add_mod hi (2^n)).symm, Nat.mul_comm (2^n) (hi / 2^n)]
      _ = (hi / 2^n) * (2^n * 2^(32 - n)) + (hi % 2^n) * 2^(32 - n) := by ring
      _ = (hi / 2^n) * 2^32 + (hi % 2^n) * 2^(32 - n) := by
        rw [show (2 : Nat)^n * 2^(32 - n) = 2^32 by
          rw [← Nat.pow_add]
          congr 1
          omega]
  simp [hdecomp, Nat.add_assoc, Nat.add_comm]

/-- Any factor `x * 2^m` with `m ≥ 32` vanishes modulo `2^32`. -/
theorem mul_pow_mod_2_32_zero (x m : Nat) (hm : 32 ≤ m) :
    (x * 2^m) % 2^32 = 0 := by
  apply Nat.dvd_iff_mod_eq_zero.mp
  exact Dvd.dvd.mul_left (Nat.pow_dvd_pow 2 hm) _

/-- Decompose the right shift of a three-limb word into three 32-bit limbs. -/
theorem u128_three_limb_shr_decomp (a1 a2 a3 n : Nat)
    (ha1 : a1 < 2^32) (ha2 : a2 < 2^32) (hn_pos : 0 < n) (hn : n < 32) :
    (a3 * 2^64 + a2 * 2^32 + a1) / 2^n =
      (a3 / 2^n) * 2^64 +
      (((a2 / 2^n) ||| ((a3 * 2^(32 - n)) % 2^32)) * 2^32) +
      ((a1 / 2^n) ||| ((a2 * 2^(32 - n)) % 2^32)) := by
  set mid := (a2 / 2^n) ||| ((a3 * 2^(32 - n)) % 2^32) with hmid
  set lo := (a1 / 2^n) ||| ((a2 * 2^(32 - n)) % 2^32) with hlo
  have hrepr : a3 * 2^64 + a2 * 2^32 + a1 = (a3 * 2^32 + a2) * 2^32 + a1 := by
    rw [show (2 : Nat)^64 = 2^32 * 2^32 by rw [← Nat.pow_add]]
    ring
  have hinner : (a3 * 2^32 + a2) / 2^n = (a3 / 2^n) * 2^32 + mid := by
    simpa [hmid] using u32_pair_shr_decomp a2 a3 n ha2 hn_pos hn
  have houter_low :
      ((a3 * 2^32 + a2) * 2^(32 - n)) % 2^32 = (a2 * 2^(32 - n)) % 2^32 := by
    rw [Nat.add_mul, Nat.add_mod]
    have hzero : (a3 * 2^32 * 2^(32 - n)) % 2^32 = 0 := by
      rw [Nat.mul_assoc, show (2 : Nat)^32 * 2^(32 - n) = 2^(64 - n) by
        rw [← Nat.pow_add]
        congr 1
        omega]
      exact mul_pow_mod_2_32_zero a3 (64 - n) (by omega)
    rw [hzero, Nat.zero_add, Nat.mod_mod]
  calc
    (a3 * 2^64 + a2 * 2^32 + a1) / 2^n
      = ((a3 * 2^32 + a2) * 2^32 + a1) / 2^n := by rw [hrepr]
    _ = ((a3 * 2^32 + a2) / 2^n) * 2^32 +
          ((a1 / 2^n) ||| (((a3 * 2^32 + a2) * 2^(32 - n)) % 2^32)) := by
        exact u32_pair_shr_decomp a1 (a3 * 2^32 + a2) n ha1 hn_pos hn
    _ = (((a3 / 2^n) * 2^32 + mid) * 2^32) + lo := by
        rw [hinner, houter_low, hlo]
    _ = (a3 / 2^n) * 2^64 + mid * 2^32 + lo := by
        rw [show (2 : Nat)^64 = 2^32 * 2^32 by rw [← Nat.pow_add]]
        ring
    _ = (a3 / 2^n) * 2^64 +
          (((a2 / 2^n) ||| ((a3 * 2^(32 - n)) % 2^32)) * 2^32) +
          ((a1 / 2^n) ||| ((a2 * 2^(32 - n)) % 2^32)) := by
        simp [hmid, hlo]

/-- Decompose the right shift of a four-limb word into four 32-bit limbs. -/
theorem u128_four_limb_shr_decomp (a0 a1 a2 a3 n : Nat)
    (ha0 : a0 < 2^32) (ha1 : a1 < 2^32) (ha2 : a2 < 2^32)
    (hn_pos : 0 < n) (hn : n < 32) :
    (a3 * 2^96 + a2 * 2^64 + a1 * 2^32 + a0) / 2^n =
      (a3 / 2^n) * 2^96 +
      (((a2 / 2^n) ||| ((a3 * 2^(32 - n)) % 2^32)) * 2^64) +
      (((a1 / 2^n) ||| ((a2 * 2^(32 - n)) % 2^32)) * 2^32) +
      ((a0 / 2^n) ||| ((a1 * 2^(32 - n)) % 2^32)) := by
  set upper := a3 * 2^64 + a2 * 2^32 + a1 with hupper_def
  set l2 := (a2 / 2^n) ||| ((a3 * 2^(32 - n)) % 2^32) with hl2
  set l1 := (a1 / 2^n) ||| ((a2 * 2^(32 - n)) % 2^32) with hl1
  set l0 := (a0 / 2^n) ||| ((a1 * 2^(32 - n)) % 2^32) with hl0
  have hrepr : a3 * 2^96 + a2 * 2^64 + a1 * 2^32 + a0 = upper * 2^32 + a0 := by
    rw [show (2 : Nat)^96 = 2^64 * 2^32 by rw [← Nat.pow_add]]
    rw [show (2 : Nat)^64 = 2^32 * 2^32 by rw [← Nat.pow_add]]
    simp [hupper_def]
    ring
  have hupper :
      upper / 2^n = (a3 / 2^n) * 2^64 + l2 * 2^32 + l1 := by
    simpa [hupper_def, hl2, hl1] using
      u128_three_limb_shr_decomp a1 a2 a3 n ha1 ha2 hn_pos hn
  have houter_low : (upper * 2^(32 - n)) % 2^32 = (a1 * 2^(32 - n)) % 2^32 := by
    rw [hupper_def, Nat.add_mul, Nat.add_mod]
    have hzero_hi : ((a3 * 2^64 + a2 * 2^32) * 2^(32 - n)) % 2^32 = 0 := by
      rw [Nat.add_mul, Nat.add_mod]
      have hzero3 : (a3 * 2^64 * 2^(32 - n)) % 2^32 = 0 := by
        rw [Nat.mul_assoc, show (2 : Nat)^64 * 2^(32 - n) = 2^(96 - n) by
          rw [← Nat.pow_add]
          congr 1
          omega]
        exact mul_pow_mod_2_32_zero a3 (96 - n) (by omega)
      have hzero2 : (a2 * 2^32 * 2^(32 - n)) % 2^32 = 0 := by
        rw [Nat.mul_assoc, show (2 : Nat)^32 * 2^(32 - n) = 2^(64 - n) by
          rw [← Nat.pow_add]
          congr 1
          omega]
        exact mul_pow_mod_2_32_zero a2 (64 - n) (by omega)
      rw [hzero3, hzero2, Nat.zero_add]
      simp
    rw [hzero_hi, Nat.zero_add, Nat.mod_mod]
  calc
    (a3 * 2^96 + a2 * 2^64 + a1 * 2^32 + a0) / 2^n
      = (upper * 2^32 + a0) / 2^n := by rw [hrepr]
    _ = (upper / 2^n) * 2^32 + ((a0 / 2^n) ||| ((upper * 2^(32 - n)) % 2^32)) := by
        exact u32_pair_shr_decomp a0 upper n ha0 hn_pos hn
    _ = (upper / 2^n) * 2^32 + l0 := by rw [houter_low, hl0]
    _ = ((a3 / 2^n) * 2^64 + l2 * 2^32 + l1) * 2^32 + l0 := by rw [hupper]
    _ = (a3 / 2^n) * 2^96 + l2 * 2^64 + l1 * 2^32 + l0 := by
        rw [show (2 : Nat)^96 = 2^64 * 2^32 by rw [← Nat.pow_add]]
        rw [show (2 : Nat)^64 = 2^32 * 2^32 by rw [← Nat.pow_add]]
        ring
    _ = (a3 / 2^n) * 2^96 +
          (((a2 / 2^n) ||| ((a3 * 2^(32 - n)) % 2^32)) * 2^64) +
          (((a1 / 2^n) ||| ((a2 * 2^(32 - n)) % 2^32)) * 2^32) +
          ((a0 / 2^n) ||| ((a1 * 2^(32 - n)) % 2^32)) := by
        simp [hl2, hl1, hl0]

/-- Adding a high-order multiple that vanishes modulo `2^32` after dividing by `2^b`:
    if `2^b | M` and `2^32 | (M / 2^b)`, then `(M + x) / 2^b % 2^32 = x / 2^b % 2^32`. -/
theorem add_high_div_mod (x M b : Nat) (hdvd_b : 2^b ∣ M) (hdvd_32 : 2^32 ∣ (M / 2^b)) :
    (M + x) / 2^b % 2^32 = x / 2^b % 2^32 := by
  have hsplit : (M + x) / 2^b = M / 2^b + x / 2^b := by
    conv_lhs => rw [Nat.add_comm]
    rw [Nat.add_div_of_dvd_left hdvd_b, Nat.add_comm]
  rw [hsplit, Nat.add_mod, Nat.dvd_iff_mod_eq_zero.mp hdvd_32, Nat.zero_add, Nat.mod_mod]

-- ============================================================================
-- U128 toNat division lemmas (used in shr_correct bridging)
-- ============================================================================
-- These express `a.toNat / 2^(k*32)` in terms of the upper limbs.

namespace U128

theorem toNat_div_2_96 (a : U128) : a.toNat / 2^96 = a.a3.val.val := by
  unfold toNat
  have h0 := a.a0.val_lt; have h1 := a.a1.val_lt
  have h2 := a.a2.val_lt; have h3 := a.a3.val_lt
  omega

theorem toNat_div_2_64 (a : U128) :
    a.toNat / 2^64 = a.a3.val.val * 2^32 + a.a2.val.val := by
  unfold toNat
  have h0 := a.a0.val_lt; have h1 := a.a1.val_lt
  have h2 := a.a2.val_lt; have h3 := a.a3.val_lt
  omega

theorem toNat_div_2_32 (a : U128) :
    a.toNat / 2^32 = a.a3.val.val * 2^64 + a.a2.val.val * 2^32 + a.a1.val.val := by
  unfold toNat
  have h0 := a.a0.val_lt; have h1 := a.a1.val_lt
  have h2 := a.a2.val_lt; have h3 := a.a3.val_lt
  omega

theorem shr_96_add_limbs (a : U128) (b_nat : Nat) :
    (a.shr (96 + b_nat)).a0.val = Felt.ofNat (a.a3.val.val / 2^b_nat) ∧
    (a.shr (96 + b_nat)).a1.val = (0 : Felt) ∧
    (a.shr (96 + b_nat)).a2.val = (0 : Felt) ∧
    (a.shr (96 + b_nat)).a3.val = (0 : Felt) := by
  have hdiv : a.toNat / 2^(96 + b_nat) = a.a3.val.val / 2^b_nat := by
    rw [show (2 : Nat)^(96 + b_nat) = 2^96 * 2^b_nat from by rw [← Nat.pow_add]]
    rw [← Nat.div_div_eq_div_mul, U128.toNat_div_2_96]
  have hlt : a.a3.val.val / 2^b_nat < 2^32 :=
    lt_of_le_of_lt (Nat.div_le_self _ _) a.a3.val_lt
  obtain ⟨h0, h1, h2, h3⟩ := U128.ofNat_of_lt_2_32 _ hlt
  simp only [U128.shr]
  rw [hdiv]
  exact ⟨h0, h1, h2, h3⟩

theorem shr_64_limbs (a : U128) :
    (a.shr 64).a0.val = a.a2.val ∧
    (a.shr 64).a1.val = a.a3.val ∧
    (a.shr 64).a2.val = (0 : Felt) ∧
    (a.shr 64).a3.val = (0 : Felt) := by
  have hdiv : a.toNat / 2^64 = a.a3.val.val * 2^32 + a.a2.val.val :=
    U128.toNat_div_2_64 a
  obtain ⟨h0, h1, h2, h3⟩ := U128.ofNat_of_lt_2_64 a.a3.val.val a.a2.val.val
    a.a3.val_lt a.a2.val_lt
  simp only [U128.shr]
  rw [hdiv]
  exact ⟨h0.trans (U32.ofNat_val a.a2), h1.trans (U32.ofNat_val a.a3), h2, h3⟩

theorem shr_64_add_limbs (a : U128) (b_nat : Nat) (hb_pos : 0 < b_nat) (hb : b_nat < 32) :
    (a.shr (64 + b_nat)).a0.val =
      Felt.ofNat ((a.a2.val.val / 2^b_nat) ||| ((a.a3.val.val * 2^(32 - b_nat)) % 2^32)) ∧
    (a.shr (64 + b_nat)).a1.val = Felt.ofNat (a.a3.val.val / 2^b_nat) ∧
    (a.shr (64 + b_nat)).a2.val = (0 : Felt) ∧
    (a.shr (64 + b_nat)).a3.val = (0 : Felt) := by
  have hdiv : a.toNat / 2^(64 + b_nat) = (a.a3.val.val * 2^32 + a.a2.val.val) / 2^b_nat := by
    rw [show (2 : Nat)^(64 + b_nat) = 2^64 * 2^b_nat from by rw [← Nat.pow_add]]
    rw [← Nat.div_div_eq_div_mul, U128.toNat_div_2_64]
  let lo := (a.a2.val.val / 2^b_nat) ||| ((a.a3.val.val * 2^(32 - b_nat)) % 2^32)
  let hi := a.a3.val.val / 2^b_nat
  have hhi_lt : hi < 2^32 := by
    dsimp [hi]
    exact lt_of_le_of_lt (Nat.div_le_self _ _) a.a3.val_lt
  have hlo_lt : lo < 2^32 := by
    dsimp [lo]
    exact Nat.or_lt_two_pow
      (lt_of_le_of_lt (Nat.div_le_self _ _) a.a2.val_lt)
      (Nat.mod_lt _ (by positivity))
  have hpair : (a.a3.val.val * 2^32 + a.a2.val.val) / 2^b_nat = hi * 2^32 + lo := by
    simpa [hi, lo] using
      u32_pair_shr_decomp a.a2.val.val a.a3.val.val b_nat a.a2.val_lt hb_pos hb
  obtain ⟨h0, h1, h2, h3⟩ := U128.ofNat_of_lt_2_64 hi lo hhi_lt hlo_lt
  simp only [U128.shr]
  rw [hdiv, hpair]
  exact ⟨h0, h1, h2, h3⟩

theorem shr_32_limbs (a : U128) :
    (a.shr 32).a0.val = a.a1.val ∧
    (a.shr 32).a1.val = a.a2.val ∧
    (a.shr 32).a2.val = a.a3.val ∧
    (a.shr 32).a3.val = (0 : Felt) := by
  have hdiv : a.toNat / 2^32 = a.a3.val.val * 2^64 + a.a2.val.val * 2^32 + a.a1.val.val :=
    U128.toNat_div_2_32 a
  obtain ⟨h0, h1, h2, h3⟩ := U128.ofNat_of_lt_2_96 a.a3.val.val a.a2.val.val a.a1.val.val
    a.a3.val_lt a.a2.val_lt a.a1.val_lt
  simp only [U128.shr]
  rw [hdiv]
  exact ⟨h0.trans (U32.ofNat_val a.a1), h1.trans (U32.ofNat_val a.a2),
    h2.trans (U32.ofNat_val a.a3), h3⟩

theorem shr_32_add_limbs (a : U128) (b_nat : Nat) (hb_pos : 0 < b_nat) (hb : b_nat < 32) :
    (a.shr (32 + b_nat)).a0.val =
      Felt.ofNat ((a.a1.val.val / 2^b_nat) ||| ((a.a2.val.val * 2^(32 - b_nat)) % 2^32)) ∧
    (a.shr (32 + b_nat)).a1.val =
      Felt.ofNat ((a.a2.val.val / 2^b_nat) ||| ((a.a3.val.val * 2^(32 - b_nat)) % 2^32)) ∧
    (a.shr (32 + b_nat)).a2.val = Felt.ofNat (a.a3.val.val / 2^b_nat) ∧
    (a.shr (32 + b_nat)).a3.val = (0 : Felt) := by
  let l0 := (a.a1.val.val / 2^b_nat) ||| ((a.a2.val.val * 2^(32 - b_nat)) % 2^32)
  let l1 := (a.a2.val.val / 2^b_nat) ||| ((a.a3.val.val * 2^(32 - b_nat)) % 2^32)
  let l2 := a.a3.val.val / 2^b_nat
  have hl0_lt : l0 < 2^32 := by
    dsimp [l0]
    exact u32_shr_or_lt a.a1.val.val a.a2.val.val b_nat a.a1.val_lt hb_pos hb
  have hl1_lt : l1 < 2^32 := by
    dsimp [l1]
    exact u32_shr_or_lt a.a2.val.val a.a3.val.val b_nat a.a2.val_lt hb_pos hb
  have hl2_lt : l2 < 2^32 := by
    dsimp [l2]
    exact lt_of_le_of_lt (Nat.div_le_self _ _) a.a3.val_lt
  have hdiv : a.toNat / 2^(32 + b_nat) =
      l2 * 2^64 + l1 * 2^32 + l0 := by
    rw [show (2 : Nat)^(32 + b_nat) = 2^32 * 2^b_nat from by rw [← Nat.pow_add]]
    rw [← Nat.div_div_eq_div_mul, U128.toNat_div_2_32]
    simpa [l0, l1, l2] using
      u128_three_limb_shr_decomp a.a1.val.val a.a2.val.val a.a3.val.val b_nat
        a.a1.val_lt a.a2.val_lt hb_pos hb
  obtain ⟨h0, h1, h2, h3⟩ := U128.ofNat_of_lt_2_96 l2 l1 l0 hl2_lt hl1_lt hl0_lt
  simp only [U128.shr]
  rw [hdiv]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [l0] using h0
  · simpa [l1] using h1
  · simpa [l2] using h2
  · exact h3

theorem shr_lt32_limbs (a : U128) (b_nat : Nat) (hb_pos : 0 < b_nat) (hb : b_nat < 32) :
    (a.shr b_nat).a0.val =
      Felt.ofNat ((a.a0.val.val / 2^b_nat) ||| ((a.a1.val.val * 2^(32 - b_nat)) % 2^32)) ∧
    (a.shr b_nat).a1.val =
      Felt.ofNat ((a.a1.val.val / 2^b_nat) ||| ((a.a2.val.val * 2^(32 - b_nat)) % 2^32)) ∧
    (a.shr b_nat).a2.val =
      Felt.ofNat ((a.a2.val.val / 2^b_nat) ||| ((a.a3.val.val * 2^(32 - b_nat)) % 2^32)) ∧
    (a.shr b_nat).a3.val = Felt.ofNat (a.a3.val.val / 2^b_nat) := by
  let l0 := (a.a0.val.val / 2^b_nat) ||| ((a.a1.val.val * 2^(32 - b_nat)) % 2^32)
  let l1 := (a.a1.val.val / 2^b_nat) ||| ((a.a2.val.val * 2^(32 - b_nat)) % 2^32)
  let l2 := (a.a2.val.val / 2^b_nat) ||| ((a.a3.val.val * 2^(32 - b_nat)) % 2^32)
  let l3 := a.a3.val.val / 2^b_nat
  have hl0_lt : l0 < 2^32 := by
    dsimp [l0]
    exact u32_shr_or_lt a.a0.val.val a.a1.val.val b_nat a.a0.val_lt hb_pos hb
  have hl1_lt : l1 < 2^32 := by
    dsimp [l1]
    exact u32_shr_or_lt a.a1.val.val a.a2.val.val b_nat a.a1.val_lt hb_pos hb
  have hl2_lt : l2 < 2^32 := by
    dsimp [l2]
    exact u32_shr_or_lt a.a2.val.val a.a3.val.val b_nat a.a2.val_lt hb_pos hb
  have hl3_lt : l3 < 2^32 := by
    dsimp [l3]
    exact lt_of_le_of_lt (Nat.div_le_self _ _) a.a3.val_lt
  have hdiv : a.toNat / 2^b_nat = l3 * 2^96 + l2 * 2^64 + l1 * 2^32 + l0 := by
    simpa [U128.toNat, l0, l1, l2, l3] using
      u128_four_limb_shr_decomp a.a0.val.val a.a1.val.val a.a2.val.val a.a3.val.val b_nat
        a.a0.val_lt a.a1.val_lt a.a2.val_lt hb_pos hb
  obtain ⟨h0, h1, h2, h3⟩ := U128.ofNat_of_limbs l3 l2 l1 l0 hl3_lt hl2_lt hl1_lt hl0_lt
  simp only [U128.shr]
  rw [hdiv]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [l0] using h0
  · simpa [l1] using h1
  · simpa [l2] using h2
  · simpa [l3] using h3

end U128

end MidenLean.Proofs
