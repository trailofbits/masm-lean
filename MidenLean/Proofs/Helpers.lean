import MidenLean.Semantics
import MidenLean.Proofs.SimpAttrs

namespace MidenLean

-- ============================================================================
-- MidenState projection lemmas
-- ============================================================================

@[simp, miden_simp] theorem MidenState.withStack_stack (s : MidenState) (stk : List Felt) :
    (s.withStack stk).stack = stk := rfl

@[simp, miden_simp] theorem MidenState.withStack_memory (s : MidenState) (stk : List Felt) :
    (s.withStack stk).memory = s.memory := rfl

@[simp, miden_simp] theorem MidenState.withStack_locals (s : MidenState) (stk : List Felt) :
    (s.withStack stk).locals = s.locals := rfl

@[simp, miden_simp] theorem MidenState.withStack_advice (s : MidenState) (stk : List Felt) :
    (s.withStack stk).advice = s.advice := rfl

@[simp, miden_simp] theorem MidenState.withStack_withStack (s : MidenState) (stk1 stk2 : List Felt) :
    (s.withStack stk1).withStack stk2 = s.withStack stk2 := rfl

-- ============================================================================
-- Felt value lemmas
-- ============================================================================

@[simp, miden_simp] theorem Felt.val_zero' : (0 : Felt).val = 0 := rfl

set_option maxHeartbeats 400000 in
@[simp, miden_simp] theorem Felt.val_one' : (1 : Felt).val = 1 := by native_decide

-- ============================================================================
-- Felt boolean lemmas
-- ============================================================================

@[simp, miden_simp] theorem Felt.isBool_ite_bool (p : Bool) :
    Felt.isBool (if p then (1 : Felt) else 0) = true := by
  cases p <;> simp [Felt.isBool, Felt.val_one']

@[simp, miden_simp] theorem Felt.ite_mul_ite (p q : Bool) :
    (if p then (1 : Felt) else 0) * (if q then (1 : Felt) else 0) =
    if (p && q) then (1 : Felt) else 0 := by
  cases p <;> cases q <;> simp

-- ============================================================================
-- u32OverflowingSub borrow lemma
-- ============================================================================

/-- The borrow (first component) of u32OverflowingSub is a boolean:
    1 when a < b, 0 otherwise. -/
theorem u32OverflowingSub_borrow_ite (a b : Nat) :
    Felt.ofNat (u32OverflowingSub a b).1 =
    if decide (a < b) then (1 : Felt) else 0 := by
  unfold u32OverflowingSub Felt.ofNat
  split
  · simp [decide_eq_false (show ¬(a < b) by omega)]
  · simp [decide_eq_true (show a < b by omega)]

-- ============================================================================
-- Felt.ofNat / value recovery lemmas
-- ============================================================================

/-- Felt.ofNat n has val = n when n < GOLDILOCKS_PRIME. -/
@[miden_bound] theorem felt_ofNat_val_lt (n : Nat) (h : n < GOLDILOCKS_PRIME) :
    (Felt.ofNat n).val = n := by
  unfold Felt.ofNat
  simp only [Felt, GOLDILOCKS_PRIME] at *
  rw [ZMod.val_natCast]
  exact Nat.mod_eq_of_lt h

@[miden_bound] theorem felt_val_lt_prime (a : Felt) : a.val < GOLDILOCKS_PRIME :=
  ZMod.val_lt a

-- ============================================================================
-- u32 bounds lemmas (all values < 2^32 are < GOLDILOCKS_PRIME)
-- ============================================================================

@[miden_bound] theorem u32_val_lt_prime (n : Nat) (h : n < 2^32) : n < GOLDILOCKS_PRIME := by
  unfold GOLDILOCKS_PRIME; omega

@[miden_bound] theorem u32_mod_lt_prime (n : Nat) : n % 2^32 < GOLDILOCKS_PRIME := by
  unfold GOLDILOCKS_PRIME; omega

@[miden_bound] theorem sum_div_2_32_lt_prime (a b : Felt) :
    (a.val + b.val) / 2^32 < GOLDILOCKS_PRIME := by
  have ha := felt_val_lt_prime a
  have hb := felt_val_lt_prime b
  unfold GOLDILOCKS_PRIME at *; omega

@[miden_bound] theorem u32_overflow_sub_fst_lt (a b : Nat) :
    (u32OverflowingSub a b).1 < GOLDILOCKS_PRIME := by
  unfold u32OverflowingSub
  split <;> simp [GOLDILOCKS_PRIME]

@[miden_bound] theorem u32_overflow_sub_snd_lt (a b : Nat)
    (ha : a < GOLDILOCKS_PRIME) (hb : b < GOLDILOCKS_PRIME) :
    (u32OverflowingSub a b).2 < GOLDILOCKS_PRIME := by
  unfold u32OverflowingSub
  split
  · simp; omega
  · simp [u32Max, GOLDILOCKS_PRIME] at *; omega

-- ============================================================================
-- isU32 lemmas for intermediate Felt.ofNat values
-- ============================================================================

@[miden_bound] theorem felt_ofNat_isU32_of_lt (n : Nat) (h : n < 2^32) :
    (Felt.ofNat n).isU32 = true := by
  simp only [Felt.isU32, decide_eq_true_eq]
  have hp : n < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; omega
  rw [felt_ofNat_val_lt n hp]; exact h

@[miden_bound] theorem u32OverflowingSub_fst_isU32 (a b : Nat) :
    (Felt.ofNat (u32OverflowingSub a b).1).isU32 = true := by
  unfold u32OverflowingSub
  split <;> simp [felt_ofNat_isU32_of_lt]

@[miden_bound] theorem u32OverflowingSub_snd_isU32 (a b : Nat)
    (ha : a < 2^32) (hb : b < 2^32) :
    (Felt.ofNat (u32OverflowingSub a b).2).isU32 = true := by
  apply felt_ofNat_isU32_of_lt
  unfold u32OverflowingSub u32Max; split <;> omega

@[miden_bound] theorem u32_mod_isU32 (n : Nat) :
    (Felt.ofNat (n % 2^32)).isU32 = true := by
  apply felt_ofNat_isU32_of_lt; omega

@[miden_bound] theorem u32_div_2_32_isU32 (a b : Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    (Felt.ofNat ((a.val + b.val) / 2^32)).isU32 = true := by
  apply felt_ofNat_isU32_of_lt
  simp only [Felt.isU32, decide_eq_true_eq] at ha hb; omega

@[miden_bound] theorem u32_prod_div_isU32 (a b : Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    (Felt.ofNat (a.val * b.val / 2^32)).isU32 = true := by
  apply felt_ofNat_isU32_of_lt
  simp only [Felt.isU32, decide_eq_true_eq] at ha hb
  have h3 : a.val * b.val ≤ (2^32 - 1) * (2^32 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  calc a.val * b.val / 2^32
      ≤ (2^32 - 1) * (2^32 - 1) / 2^32 := Nat.div_le_div_right h3
    _ < 2^32 := by native_decide

@[miden_bound] theorem u32_prod_div_lt_prime (a b : Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    a.val * b.val / 2^32 < GOLDILOCKS_PRIME := by
  simp only [Felt.isU32, decide_eq_true_eq] at ha hb
  have h3 : a.val * b.val ≤ (2^32 - 1) * (2^32 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  calc a.val * b.val / 2^32
      ≤ (2^32 - 1) * (2^32 - 1) / 2^32 := Nat.div_le_div_right h3
    _ < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; native_decide

end MidenLean
