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
    Bool.and_comm, Bool.and_assoc, Bool.and_left_comm]

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

end U128

/-- `Felt.ofNat` distributes over addition. -/
theorem felt_ofNat_add (n m : Nat) :
    Felt.ofNat (n + m) = Felt.ofNat n + Felt.ofNat m := by
  simp [Felt.ofNat, Nat.cast_add]

-- ============================================================================
-- Carry chain bridging lemmas for addition
-- ============================================================================

/-- The schoolbook carry-chain addition of four u32 limbs produces the correct
    decomposition of the total sum into 32-bit words. -/
theorem u128_add_carry_chain (a0 a1 a2 a3 b0 b1 b2 b3 : Nat)
    (ha0 : a0 < 2^32) (ha1 : a1 < 2^32) (ha2 : a2 < 2^32) (ha3 : a3 < 2^32)
    (hb0 : b0 < 2^32) (hb1 : b1 < 2^32) (hb2 : b2 < 2^32) (hb3 : b3 < 2^32) :
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
theorem u128_add_carry_overflow (a0 a1 a2 a3 b0 b1 b2 b3 : Nat)
    (ha0 : a0 < 2^32) (ha1 : a1 < 2^32) (ha2 : a2 < 2^32) (ha3 : a3 < 2^32)
    (hb0 : b0 < 2^32) (hb1 : b1 < 2^32) (hb2 : b2 < 2^32) (hb3 : b3 < 2^32) :
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
    a.a0.val_lt a.a1.val_lt a.a2.val_lt a.a3.val_lt
    b.a0.val_lt b.a1.val_lt b.a2.val_lt b.a3.val_lt
  have co := u128_add_carry_overflow a.a0.val.val a.a1.val.val a.a2.val.val a.a3.val.val
    b.a0.val.val b.a1.val.val b.a2.val.val b.a3.val.val
    a.a0.val_lt a.a1.val_lt a.a2.val_lt a.a3.val_lt
    b.a0.val_lt b.a1.val_lt b.a2.val_lt b.a3.val_lt
  simp only [HAdd.hAdd, Add.add, U128.ofNat, U128.toNat] at cc co ⊢
  exact ⟨congrArg _ cc.1, congrArg _ cc.2.1, congrArg _ cc.2.2.1, congrArg _ cc.2.2.2, co⟩

-- ============================================================================
-- Comparison bridging lemmas
-- ============================================================================

/-- Helper: val of a Felt conditional (if p then 1 else 0) -/
private theorem felt_ite_val (p : Prop) [Decidable p] :
    (if p then (1 : Felt) else (0 : Felt)).val = if p then 1 else 0 := by
  split <;> simp [Felt.val_one']

private theorem u128_borrow1_eq (a0 a1 b0 b1 : Felt)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true) :
    u128Borrow1 a0 a1 b0 b1 =
    if decide (a1.val * 2^32 + a0.val < b1.val * 2^32 + b0.val) then (1 : Felt) else 0 := by
  simp only [Felt.isU32, decide_eq_true_eq] at ha0 ha1 hb0 hb1
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
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true) (ha2 : a2.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true) (hb2 : b2.isU32 = true) :
    u128Borrow2 a0 a1 a2 b0 b1 b2 =
    if decide (a2.val * 2^64 + a1.val * 2^32 + a0.val <
              b2.val * 2^64 + b1.val * 2^32 + b0.val) then (1 : Felt) else 0 := by
  simp only [Felt.isU32, decide_eq_true_eq] at ha0 ha1 ha2 hb0 hb1 hb2
  unfold u128Borrow2 u128Sub2 u32OverflowingSub u32Max
  rw [u128_borrow1_eq a0 a1 b0 b1 (by simpa [Felt.isU32]) (by simpa [Felt.isU32])
    (by simpa [Felt.isU32]) (by simpa [Felt.isU32])]
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
    a.a0.isU32 a.a1.isU32 a.a2.isU32 b.a0.isU32 b.a1.isU32 b.a2.isU32]
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

end MidenLean.Proofs
