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

namespace U128

@[simp] theorem lt_iff_toNat_lt (a b : U128) : a < b ↔ a.toNat < b.toNat := Iff.rfl
@[simp] theorem le_iff_toNat_le (a b : U128) : a ≤ b ↔ a.toNat ≤ b.toNat := Iff.rfl

@[simp] theorem toNat_add (a b : U128) : (a + b).toNat = (a.toNat + b.toNat) % 2^128 :=
  ofNat_toNat _

@[simp] theorem toNat_sub (a b : U128) : (a - b).toNat = (a.toNat + 2^128 - b.toNat) % 2^128 :=
  ofNat_toNat _

@[simp] theorem toNat_mul (a b : U128) : (a * b).toNat = (a.toNat * b.toNat) % 2^128 :=
  ofNat_toNat _

end U128

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

end MidenLean.Proofs
