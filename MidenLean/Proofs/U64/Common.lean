import MidenLean.Proofs.U32.Common
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean

/-- Procedure environment for manual u64 proofs that call other u64 procedures. -/
def u64ProcEnv : ProcEnv := fun name =>
  match name with
  | "overflowing_add" => some Miden.Core.U64.overflowing_add
  | "gt" => some Miden.Core.U64.gt
  | "lt" => some Miden.Core.U64.lt
  | "divmod" => some Miden.Core.U64.divmod
  | "wrapping_mul" => some Miden.Core.U64.wrapping_mul
  | _ => none

-- ============================================================================
-- U64 type: a 64-bit unsigned integer as two U32 limbs
-- ============================================================================

/-- A 64-bit unsigned integer represented as two U32 limbs (little-endian).
    `lo` is the low 32-bit limb, `hi` is the high 32-bit limb. -/
structure U64 where
  lo : U32
  hi : U32

namespace U64

/-- Reconstruct the natural number value: `hi * 2^32 + lo`. -/
def toNat (x : U64) : Nat := x.hi.val.val * 2^32 + x.lo.val.val

theorem toNat_lt (x : U64) : x.toNat < 2^64 := by
  unfold toNat
  have hlo := x.lo.val_lt; have hhi := x.hi.val_lt
  omega

theorem toNat_def (x : U64) : x.toNat = x.hi.val.val * 2^32 + x.lo.val.val := rfl

/-- Construct a U64 from a natural number (taken mod 2^64). -/
def ofNat (n : Nat) : U64 where
  lo := ⟨Felt.ofNat (n % 2^32), u32_mod_isU32 n⟩
  hi := ⟨Felt.ofNat ((n / 2^32) % 2^32), u32_mod_isU32 (n / 2^32)⟩

@[simp] theorem ofNat_toNat (n : Nat) : (U64.ofNat n).toNat = n % 2^64 := by
  unfold ofNat toNat
  have h1 : (Felt.ofNat (n % 2^32)).val = n % 2^32 :=
    felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)
  have h2 : (Felt.ofNat ((n / 2^32) % 2^32)).val = (n / 2^32) % 2^32 :=
    felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)
  rw [h1, h2]; omega

@[simp] theorem ofNat_lo (n : Nat) :
    (U64.ofNat n).lo.val = Felt.ofNat (n % 2^32) := rfl

@[simp] theorem ofNat_hi (n : Nat) :
    (U64.ofNat n).hi.val = Felt.ofNat ((n / 2^32) % 2^32) := rfl

-- Extensionality: two U64s with the same lo and hi are equal.
@[ext] theorem ext {a b : U64} (hlo : a.lo = b.lo) (hhi : a.hi = b.hi) : a = b := by
  cases a; cases b; simp_all

theorem toNat_injective : Function.Injective U64.toNat := by
  intro a b hab
  have halo := a.lo.val_lt; have hahi := a.hi.val_lt
  have hblo := b.lo.val_lt; have hbhi := b.hi.val_lt
  unfold toNat at hab
  apply ext
  · exact U32.ext (ZMod.val_injective _ (by omega))
  · exact U32.ext (ZMod.val_injective _ (by omega))

theorem eq_of_toNat_eq {a b : U64} (h : a.toNat = b.toNat) : a = b :=
  toNat_injective h

end U64

-- Arithmetic instances
instance : Add U64 where add a b := U64.ofNat (a.toNat + b.toNat)
instance : Sub U64 where sub a b := U64.ofNat (a.toNat + 2^64 - b.toNat)
instance : Mul U64 where mul a b := U64.ofNat (a.toNat * b.toNat)

-- Comparison instances
instance : LT U64 where lt a b := a.toNat < b.toNat
instance : LE U64 where le a b := a.toNat ≤ b.toNat
instance (a b : U64) : Decidable (a < b) := inferInstanceAs (Decidable (a.toNat < b.toNat))
instance (a b : U64) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.toNat ≤ b.toNat))

namespace U64

@[simp] theorem lt_iff_toNat_lt (a b : U64) : a < b ↔ a.toNat < b.toNat := Iff.rfl
@[simp] theorem le_iff_toNat_le (a b : U64) : a ≤ b ↔ a.toNat ≤ b.toNat := Iff.rfl

@[simp] theorem toNat_add (a b : U64) : (a + b).toNat = (a.toNat + b.toNat) % 2^64 :=
  ofNat_toNat _

@[simp] theorem toNat_sub (a b : U64) : (a - b).toNat = (a.toNat + 2^64 - b.toNat) % 2^64 :=
  ofNat_toNat _

@[simp] theorem toNat_mul (a b : U64) : (a * b).toNat = (a.toNat * b.toNat) % 2^64 :=
  ofNat_toNat _

end U64

-- Bitwise instances
instance : AndOp U64 where and a b := {
  lo := ⟨Felt.ofNat (a.lo.val.val &&& b.lo.val.val),
    felt_ofNat_isU32_of_lt _ (Nat.lt_of_le_of_lt Nat.and_le_left a.lo.val_lt)⟩
  hi := ⟨Felt.ofNat (a.hi.val.val &&& b.hi.val.val),
    felt_ofNat_isU32_of_lt _ (Nat.lt_of_le_of_lt Nat.and_le_left a.hi.val_lt)⟩
}

instance : OrOp U64 where or a b := {
  lo := ⟨Felt.ofNat (a.lo.val.val ||| b.lo.val.val),
    felt_ofNat_isU32_of_lt _ (Nat.or_lt_two_pow a.lo.val_lt b.lo.val_lt)⟩
  hi := ⟨Felt.ofNat (a.hi.val.val ||| b.hi.val.val),
    felt_ofNat_isU32_of_lt _ (Nat.or_lt_two_pow a.hi.val_lt b.hi.val_lt)⟩
}

instance : XorOp U64 where xor a b := {
  lo := ⟨Felt.ofNat (a.lo.val.val ^^^ b.lo.val.val),
    felt_ofNat_isU32_of_lt _ (Nat.xor_lt_two_pow a.lo.val_lt b.lo.val_lt)⟩
  hi := ⟨Felt.ofNat (a.hi.val.val ^^^ b.hi.val.val),
    felt_ofNat_isU32_of_lt _ (Nat.xor_lt_two_pow a.hi.val_lt b.hi.val_lt)⟩
}

-- Equality instance
instance : BEq U64 where beq a b := (a.lo.val == b.lo.val) && (a.hi.val == b.hi.val)

-- Min/Max instances
instance : Min U64 where min a b := if a ≤ b then a else b
instance : Max U64 where max a b := if b ≤ a then a else b

namespace U64

@[simp] theorem and_lo (a b : U64) : (a &&& b).lo.val = Felt.ofNat (a.lo.val.val &&& b.lo.val.val) := rfl
@[simp] theorem and_hi (a b : U64) : (a &&& b).hi.val = Felt.ofNat (a.hi.val.val &&& b.hi.val.val) := rfl
@[simp] theorem or_lo (a b : U64) : (a ||| b).lo.val = Felt.ofNat (a.lo.val.val ||| b.lo.val.val) := rfl
@[simp] theorem or_hi (a b : U64) : (a ||| b).hi.val = Felt.ofNat (a.hi.val.val ||| b.hi.val.val) := rfl
@[simp] theorem xor_lo (a b : U64) : (a ^^^ b).lo.val = Felt.ofNat (a.lo.val.val ^^^ b.lo.val.val) := rfl
@[simp] theorem xor_hi (a b : U64) : (a ^^^ b).hi.val = Felt.ofNat (a.hi.val.val ^^^ b.hi.val.val) := rfl

@[simp] theorem beq_iff (a b : U64) : (a == b) = ((a.lo.val == b.lo.val) && (a.hi.val == b.hi.val)) := rfl

theorem beq_comm (a b : U64) : (a == b) = (b == a) := by
  simp only [beq_iff, Bool.beq_comm (a := a.lo.val), Bool.beq_comm (a := a.hi.val)]

theorem bne_iff (a b : U64) : (a != b) = ((a.lo.val != b.lo.val) || (a.hi.val != b.hi.val)) := by
  simp only [bne, beq_iff, Bool.not_and, bne]

theorem bne_comm (a b : U64) : (a != b) = (b != a) := by
  simp only [bne, beq_comm]

@[simp] theorem min_def (a b : U64) : min a b = if a ≤ b then a else b := rfl
@[simp] theorem max_def (a b : U64) : max a b = if b ≤ a then a else b := rfl

-- Bit counting operations

/-- Count leading zeros of a 64-bit value. -/
def countLeadingZeros (a : U64) : Nat :=
  if a.hi.val.val = 0 then u32CountLeadingZeros a.lo.val.val + 32
  else u32CountLeadingZeros a.hi.val.val

/-- Count leading ones of a 64-bit value. -/
def countLeadingOnes (a : U64) : Nat :=
  if a.hi.val.val = 2^32 - 1 then u32CountLeadingOnes a.lo.val.val + 32
  else u32CountLeadingOnes a.hi.val.val

/-- Count trailing zeros of a 64-bit value. -/
def countTrailingZeros (a : U64) : Nat :=
  if a.lo.val.val = 0 then u32CountTrailingZeros a.hi.val.val + 32
  else u32CountTrailingZeros a.lo.val.val

/-- Count trailing ones of a 64-bit value. -/
def countTrailingOnes (a : U64) : Nat :=
  if a.lo.val.val = 2^32 - 1 then u32CountTrailingOnes a.hi.val.val + 32
  else u32CountTrailingOnes a.lo.val.val

-- Shift and rotation operations

/-- Left-shift a u64 value by `n` bits (mod 2^64). -/
def shl (a : U64) (n : Nat) : U64 := ofNat (a.toNat * 2^n)

/-- Right-shift a u64 value by `n` bits. -/
def shr (a : U64) (n : Nat) : U64 := ofNat (a.toNat / 2^n)

/-- Left-rotate a u64 value by `n` bits. -/
def rotl (a : U64) (n : Nat) : U64 :=
  let n' := n % 64
  ofNat (a.toNat * 2^n' + a.toNat / 2^(64 - n'))

/-- Right-rotate a u64 value by `n` bits. -/
def rotr (a : U64) (n : Nat) : U64 :=
  let n' := n % 64
  ofNat (a.toNat / 2^n' + a.toNat * 2^(64 - n'))

end U64

/-- `Felt.ofNat` distributes over addition. -/
theorem felt_ofNat_add (n m : Nat) :
    Felt.ofNat (n + m) = Felt.ofNat n + Felt.ofNat m := by
  simp [Felt.ofNat, Nat.cast_add]

-- ============================================================================
-- Comparison bridging lemma
-- ============================================================================

/-- The hi_eq check in comparison formulas is equivalent to a_hi.val = b_hi.val
    for u32 inputs. -/
theorem hi_eq_iff_val_eq (a_hi b_hi : Felt)
    (ha : a_hi.isU32 = true) (hb : b_hi.isU32 = true) :
    (Felt.ofNat (u32OverflowingSub a_hi.val b_hi.val).2 == (0 : Felt)) =
    decide (a_hi.val = b_hi.val) := by
  simp only [Felt.isU32, decide_eq_true_eq] at ha hb
  -- LHS is decide (Felt.ofNat ... = 0)
  show decide _ = decide _
  apply decide_eq_decide.mpr
  constructor
  · intro h
    have hval := u32OverflowingSub_snd_val a_hi.val b_hi.val (by omega) (by omega)
    have : (Felt.ofNat (u32OverflowingSub a_hi.val b_hi.val).2).val = 0 := by
      rw [h]; rfl
    rw [hval] at this
    exact (u32OverflowingSub_snd_eq_zero_iff a_hi.val b_hi.val (by omega) (by omega)).mp this
  · intro h
    have : (u32OverflowingSub a_hi.val b_hi.val).2 = 0 :=
      (u32OverflowingSub_snd_eq_zero_iff a_hi.val b_hi.val (by omega) (by omega)).mpr h
    simp [this, Felt.ofNat]

/-- The borrow-based comparison formula is equivalent to `a.toNat < b.toNat`.

    This bridges the low-level formula used in `u64_lt_raw` to the
    high-level mathematical comparison. -/
theorem u64_borrow_iff_lt (a b : U64) :
    let borrow_lo := decide (a.lo.val.val < b.lo.val.val)
    let borrow_hi := decide (a.hi.val.val < b.hi.val.val)
    let hi_eq := Felt.ofNat (u32OverflowingSub a.hi.val.val b.hi.val.val).2 == (0 : Felt)
    (borrow_hi || (hi_eq && borrow_lo)) = decide (a.toNat < b.toNat) := by
  simp only
  rw [hi_eq_iff_val_eq a.hi.val b.hi.val a.hi.isU32 b.hi.isU32]
  simp only [U64.toNat]
  have halo := a.lo.val_lt; have hahi := a.hi.val_lt
  have hblo := b.lo.val_lt; have hbhi := b.hi.val_lt
  -- Case split on all three boolean decisions
  cases h1 : decide (a.hi.val.val < b.hi.val.val) <;>
  cases h2 : decide (a.hi.val.val = b.hi.val.val) <;>
  cases h3 : decide (a.lo.val.val < b.lo.val.val) <;>
  simp_all [decide_eq_true_eq, decide_eq_false_iff_not] <;>
  omega

-- ============================================================================
-- Arithmetic bridging lemmas
-- ============================================================================

/-- The carry-based addition formula reconstructs to `a.toNat + b.toNat`. -/
theorem u64_carry_add_spec (a_lo a_hi b_lo b_hi : Nat) :
    let lo_sum := a_lo + b_lo
    let carry := lo_sum / 2^32
    let hi_sum := a_hi + b_hi + carry
    let overflow := hi_sum / 2^32
    overflow * 2^64 + (hi_sum % 2^32) * 2^32 + lo_sum % 2^32 =
    (a_hi * 2^32 + a_lo) + (b_hi * 2^32 + b_lo) := by
  omega

/-- The overflowing_sub borrow is equivalent to `a.toNat < b.toNat`. -/
theorem u64_sub_borrow_iff_lt (a b : U64) :
    let sub_lo := u32OverflowingSub a.lo.val.val b.lo.val.val
    let sub_hi := u32OverflowingSub a.hi.val.val b.hi.val.val
    let borrow_adj := decide (sub_hi.2 < sub_lo.1)
    let borrow_hi := decide (a.hi.val.val < b.hi.val.val)
    (borrow_adj || borrow_hi) = decide (a.toNat < b.toNat) := by
  simp only [U64.toNat]
  have halo := a.lo.val_lt; have hahi := a.hi.val_lt
  have hblo := b.lo.val_lt; have hbhi := b.hi.val_lt
  unfold u32OverflowingSub u32Max
  -- Resolve all if-then-else conditions, then case-split on decides
  split_ifs <;>
  cases h1 : decide (a.hi.val.val < b.hi.val.val) <;>
  simp_all [decide_eq_true_eq, decide_eq_false_iff_not] <;>
  omega

-- ============================================================================
-- Subtraction bridging lemma
-- ============================================================================

/-- The limb-by-limb u32OverflowingSub computes the same result as
    `(a - b : U64)`, i.e. `U64.ofNat (a.toNat + 2^64 - b.toNat)`. -/
theorem u64_sub_limbs (a b : U64) :
    let sub_lo := u32OverflowingSub a.lo.val.val b.lo.val.val
    let sub_hi := u32OverflowingSub a.hi.val.val b.hi.val.val
    let sub_final := u32OverflowingSub sub_hi.2 sub_lo.1
    sub_lo.2 = (a.toNat + 2^64 - b.toNat) % 2^32 ∧
    sub_final.2 = ((a.toNat + 2^64 - b.toNat) / 2^32) % 2^32 := by
  simp only
  have halo := a.lo.val_lt; have hahi := a.hi.val_lt
  have hblo := b.lo.val_lt; have hbhi := b.hi.val_lt
  unfold u32OverflowingSub u32Max U64.toNat
  split_ifs <;> omega

/-- Corollary: the Felt values from the subtraction limb computation match
    `(a - b).lo` and `(a - b).hi`. -/
theorem u64_sub_limbs_felt (a b : U64) :
    let sub_lo := u32OverflowingSub a.lo.val.val b.lo.val.val
    let sub_hi := u32OverflowingSub a.hi.val.val b.hi.val.val
    let sub_final := u32OverflowingSub sub_hi.2 sub_lo.1
    Felt.ofNat sub_lo.2 = (a - b).lo.val ∧ Felt.ofNat sub_final.2 = (a - b).hi.val := by
  have ⟨h1, h2⟩ := u64_sub_limbs a b
  exact ⟨congrArg Felt.ofNat h1, congrArg Felt.ofNat h2⟩

-- ============================================================================
-- Schoolbook multiplication helpers (used by rotl, rotr)
-- ============================================================================

/-- Schoolbook identity: multiplying a 2-limb value (hi, lo) by P decomposes as
    (hi * P + lo / Q) * 2^32 + P * (lo % Q) when P * Q = 2^32. -/
theorem schoolbook_mul_eq (P Q hi lo : Nat) (hPQ : P * Q = 2 ^ 32) :
    (hi * 2 ^ 32 + lo) * P = (hi * P + lo / Q) * 2 ^ 32 + P * (lo % Q) := by
  suffices h : (hi * (P * Q) + lo) * P = (hi * P + lo / Q) * (P * Q) + P * (lo % Q) by
    rwa [hPQ] at h
  conv_lhs => rw [show lo = Q * (lo / Q) + lo % Q from (Nat.div_add_mod lo Q).symm]
  ring

/-- The cross remainder hi % Q * P + lo / Q < P * Q. -/
theorem cross_remainder_lt (P Q hi lo : Nat) (hQ_pos : 0 < Q)
    (h_lo_div : lo / Q < P) :
    hi % Q * P + lo / Q < P * Q := by
  have h_bound : (hi % Q + 1) * P ≤ Q * P :=
    Nat.mul_le_mul_right P (Nat.mod_lt hi hQ_pos)
  nlinarith [Nat.mul_comm Q P]

/-- The cross-term high word: (hi * P + lo / Q) / 2^32 = hi / Q. -/
theorem cross_div_eq (P Q hi lo : Nat) (hPQ : P * Q = 2 ^ 32)
    (hQ_pos : 0 < Q) (h_lo_div : lo / Q < P) :
    (hi * P + lo / Q) / 2 ^ 32 = hi / Q := by
  have h_rem := cross_remainder_lt P Q hi lo hQ_pos h_lo_div
  have h_dm := (Nat.div_add_mod hi Q).symm
  have h_eq : hi * P + lo / Q = (hi % Q * P + lo / Q) + hi / Q * 2 ^ 32 := by
    conv_lhs => rw [show hi = Q * (hi / Q) + hi % Q from h_dm]
    rw [show (Q * (hi / Q) + hi % Q) * P + lo / Q =
      (hi % Q * P + lo / Q) + hi / Q * (P * Q) from by ring, hPQ]
  rw [h_eq, Nat.add_mul_div_right _ _ (by positivity : 0 < 2 ^ 32),
      Nat.div_eq_of_lt (by rwa [hPQ] at h_rem), Nat.zero_add]

/-- Non-overlap: hi / Q + P * (lo % Q) < 2^32. -/
theorem limb_non_overlap (P Q hi lo : Nat) (hPQ : P * Q = 2 ^ 32)
    (hQ_pos : 0 < Q) (hhi : hi < 2 ^ 32) :
    hi / Q + P * (lo % Q) < 2 ^ 32 := by
  rw [← hPQ]
  have h_div_lt : hi / Q < P := by
    rw [Nat.div_lt_iff_lt_mul hQ_pos]; omega
  have h_bound : P * (lo % Q + 1) ≤ P * Q :=
    Nat.mul_le_mul_left P (Nat.mod_lt lo hQ_pos)
  nlinarith

/-- lo / Q < P when lo < 2^32 and P * Q = 2^32. -/
theorem lo_div_lt_of_u32 (P Q lo : Nat) (hPQ : P * Q = 2 ^ 32)
    (hQ_pos : 0 < Q) (hlo : lo < 2 ^ 32) :
    lo / Q < P := by
  rw [Nat.div_lt_iff_lt_mul hQ_pos]; omega

/-- Division of a 2-limb value by 2^32 * Q equals hi / Q. -/
theorem u64_div_large_pow (hi lo Q : Nat) (hlo : lo < 2 ^ 32) :
    (hi * 2 ^ 32 + lo) / (2 ^ 32 * Q) = hi / Q := by
  rw [show hi * 2 ^ 32 + lo = lo + hi * 2 ^ 32 from by omega,
      ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_right _ _ (show 0 < 2 ^ 32 from by positivity),
      Nat.div_eq_of_lt hlo, Nat.zero_add]

end MidenLean.Proofs
