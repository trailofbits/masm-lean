import MidenLean.Semantics

namespace MidenLean

-- ============================================================================
-- MidenState projection lemmas
-- ============================================================================

@[simp] theorem MidenState.withStack_stack (s : MidenState) (stk : List Felt) :
    (s.withStack stk).stack = stk := rfl

@[simp] theorem MidenState.withStack_memory (s : MidenState) (stk : List Felt) :
    (s.withStack stk).memory = s.memory := rfl

@[simp] theorem MidenState.withStack_locals (s : MidenState) (stk : List Felt) :
    (s.withStack stk).locals = s.locals := rfl

@[simp] theorem MidenState.withStack_advice (s : MidenState) (stk : List Felt) :
    (s.withStack stk).advice = s.advice := rfl

@[simp] theorem MidenState.withStack_withStack (s : MidenState) (stk1 stk2 : List Felt) :
    (s.withStack stk1).withStack stk2 = s.withStack stk2 := rfl

-- ============================================================================
-- Execution decomposition lemmas
-- ============================================================================

/-- Execute a concatenation of straight-line op lists in two phases. -/
theorem exec_append (fuel : Nat) (s : MidenState) (xs ys : List Op) :
    exec fuel s (xs ++ ys) = (do
      let s' ← exec fuel s xs
      exec fuel s' ys) := by
  unfold exec execWithEnv
  cases fuel <;> simp [List.foldlM_append]

-- ============================================================================
-- Felt value lemmas
-- ============================================================================

@[simp] theorem Felt.val_zero' : (0 : Felt).val = 0 := rfl

set_option maxHeartbeats 400000 in
@[simp] theorem Felt.val_one' : (1 : Felt).val = 1 := by native_decide

-- ============================================================================
-- Felt boolean lemmas
-- ============================================================================

@[simp] theorem Felt.isBool_ite_bool (p : Bool) :
    Felt.isBool (if p then (1 : Felt) else 0) = true := by
  cases p <;> simp [Felt.isBool, Felt.val_one']

/-- A Prop-ite of (1 : Felt) / 0 is also boolean. -/
theorem Felt.isBool_ite_prop (P : Prop) [Decidable P] :
    Felt.isBool (if P then (1 : Felt) else 0) = true := by
  unfold Felt.isBool; split_ifs <;> simp [Felt.val_one']

/-- The Nat.beq-equality of an ite-(1:Felt)/0 with 1 equals the Bool condition. -/
theorem Felt.ite_val_eq_one (p : Bool) :
    ((if p then (1 : Felt) else 0).val == 1) = p := by
  cases p <;> simp [Felt.val_one']

/-- For a Prop, (if P then (1:Felt) else 0).val == 1 = decide P. -/
theorem Felt.ite_prop_val_eq_one (P : Prop) [Decidable P] :
    ((if P then (1 : Felt) else 0).val == 1) = decide P := by
  by_cases h : P
  · simp [h, Felt.val_one']
  · simp [h]

/-- A boolean Felt equals an ite on (val == 1). -/
theorem Felt.isBool_eq_ite (a : Felt) (h : a.isBool = true) :
    a = if (a.val == 1) then (1 : Felt) else 0 := by
  simp only [Felt.isBool, Bool.or_eq_true, beq_iff_eq] at h
  have hcast : (↑(a.val) : Felt) = a := ZMod.natCast_zmod_val a
  rcases h with h | h
  · have ha0 : a = 0 := by rw [← hcast, h, Nat.cast_zero]
    simp [ha0]
  · have ha1 : a = 1 := by rw [← hcast, h, Nat.cast_one]
    simp [ha1]

/-- Converts a Prop-ite of Felt to a Bool decide-ite. -/
theorem Felt.ite_prop_eq_ite_bool (P : Prop) [Decidable P] :
    (if P then (1 : Felt) else 0) = if decide P then (1 : Felt) else 0 := by
  by_cases h : P <;> simp [h]

/-- Normalizes (if b = true then ...) to (if b then ...) for Bool b. -/
@[simp] theorem Felt.ite_beq_true (b : Bool) :
    (if (b = true) then (1 : Felt) else 0) = if b then (1 : Felt) else 0 := by
  cases b <;> simp

@[simp] theorem Felt.ite_mul_ite (p q : Bool) :
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
theorem felt_ofNat_val_lt (n : Nat) (h : n < GOLDILOCKS_PRIME) :
    (Felt.ofNat n).val = n := by
  unfold Felt.ofNat
  simp only [Felt, GOLDILOCKS_PRIME] at *
  rw [ZMod.val_natCast]
  exact Nat.mod_eq_of_lt h

theorem felt_val_lt_prime (a : Felt) : a.val < GOLDILOCKS_PRIME :=
  ZMod.val_lt a

-- ============================================================================
-- u32 bounds lemmas (all values < 2^32 are < GOLDILOCKS_PRIME)
-- ============================================================================

theorem u32_val_lt_prime (n : Nat) (h : n < 2^32) : n < GOLDILOCKS_PRIME := by
  unfold GOLDILOCKS_PRIME; omega

theorem u32_mod_lt_prime (n : Nat) : n % 2^32 < GOLDILOCKS_PRIME := by
  unfold GOLDILOCKS_PRIME; omega

theorem sum_div_2_32_lt_prime (a b : Felt) :
    (a.val + b.val) / 2^32 < GOLDILOCKS_PRIME := by
  have ha := felt_val_lt_prime a
  have hb := felt_val_lt_prime b
  unfold GOLDILOCKS_PRIME at *; omega

theorem u32_overflow_sub_fst_lt (a b : Nat) :
    (u32OverflowingSub a b).1 < GOLDILOCKS_PRIME := by
  unfold u32OverflowingSub
  split <;> simp [GOLDILOCKS_PRIME]

theorem u32_overflow_sub_snd_lt (a b : Nat)
    (ha : a < GOLDILOCKS_PRIME) (hb : b < GOLDILOCKS_PRIME) :
    (u32OverflowingSub a b).2 < GOLDILOCKS_PRIME := by
  unfold u32OverflowingSub
  split
  · simp; omega
  · simp [u32Max, GOLDILOCKS_PRIME] at *; omega

-- ============================================================================
-- isU32 lemmas for intermediate Felt.ofNat values
-- ============================================================================

theorem felt_ofNat_isU32_of_lt (n : Nat) (h : n < 2^32) :
    (Felt.ofNat n).isU32 = true := by
  simp only [Felt.isU32, decide_eq_true_eq]
  have hp : n < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; omega
  rw [felt_ofNat_val_lt n hp]; exact h

theorem u32OverflowingSub_fst_isU32 (a b : Nat) :
    (Felt.ofNat (u32OverflowingSub a b).1).isU32 = true := by
  apply felt_ofNat_isU32_of_lt
  unfold u32OverflowingSub; split <;> simp

theorem u32OverflowingSub_snd_isU32 (a b : Nat)
    (ha : a < 2^32) (hb : b < 2^32) :
    (Felt.ofNat (u32OverflowingSub a b).2).isU32 = true := by
  apply felt_ofNat_isU32_of_lt
  unfold u32OverflowingSub u32Max; split <;> omega

theorem u32_mod_isU32 (n : Nat) :
    (Felt.ofNat (n % 2^32)).isU32 = true := by
  apply felt_ofNat_isU32_of_lt; omega

theorem u32_div_2_32_isU32 (a b : Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    (Felt.ofNat ((a.val + b.val) / 2^32)).isU32 = true := by
  apply felt_ofNat_isU32_of_lt
  simp only [Felt.isU32, decide_eq_true_eq] at ha hb; omega

theorem u32_prod_div_isU32 (a b : Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    (Felt.ofNat (a.val * b.val / 2^32)).isU32 = true := by
  apply felt_ofNat_isU32_of_lt
  simp only [Felt.isU32, decide_eq_true_eq] at ha hb
  have h3 : a.val * b.val ≤ (2^32 - 1) * (2^32 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  calc a.val * b.val / 2^32
      ≤ (2^32 - 1) * (2^32 - 1) / 2^32 := Nat.div_le_div_right h3
    _ < 2^32 := by native_decide

theorem u32_prod_div_lt_prime (a b : Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    a.val * b.val / 2^32 < GOLDILOCKS_PRIME := by
  simp only [Felt.isU32, decide_eq_true_eq] at ha hb
  have h3 : a.val * b.val ≤ (2^32 - 1) * (2^32 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  calc a.val * b.val / 2^32
      ≤ (2^32 - 1) * (2^32 - 1) / 2^32 := Nat.div_le_div_right h3
    _ < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; native_decide

-- ============================================================================
-- execInstruction equation lemmas
-- ============================================================================

@[simp] theorem execInstruction_u32OverflowSub (s : MidenState) :
    execInstruction s .u32OverflowSub = execU32OverflowSub s := by
  unfold execInstruction; rfl

@[simp] theorem execInstruction_u32WrappingSub (s : MidenState) :
    execInstruction s .u32WrappingSub = execU32WrappingSub s := by
  unfold execInstruction; rfl

@[simp] theorem execInstruction_u32WidenMul (s : MidenState) :
    execInstruction s .u32WidenMul = execU32WidenMul s := by
  unfold execInstruction; rfl

@[simp] theorem execInstruction_u32WidenMadd (s : MidenState) :
    execInstruction s .u32WidenMadd = execU32WidenMadd s := by
  unfold execInstruction; rfl

/-- Concrete expansion of execU32WidenMul when isU32 guards pass. -/
theorem execU32WidenMul_concrete
    {a b : Felt} {rest : List Felt} {mem locs : Nat → Felt} {adv : List Felt}
    (ha : a.isU32 = true := by assumption) (hb : b.isU32 = true := by assumption) :
    execU32WidenMul ⟨b :: a :: rest, mem, locs, adv⟩ =
    some ⟨Felt.ofNat (a.val * b.val % 4294967296) ::
      Felt.ofNat (a.val * b.val / 4294967296) :: rest, mem, locs, adv⟩ := by
  unfold execU32WidenMul u32WideMul u32Max
  simp [ha, hb, MidenState.withStack]

/-- Concrete expansion of execU32WidenMadd when isU32 guards pass. -/
theorem execU32WidenMadd_concrete
    {a b c : Felt} {rest : List Felt} {mem locs : Nat → Felt} {adv : List Felt}
    (ha : a.isU32 = true := by assumption) (hb : b.isU32 = true := by assumption)
    (hc : c.isU32 = true := by assumption) :
    execU32WidenMadd ⟨b :: a :: c :: rest, mem, locs, adv⟩ =
    some ⟨Felt.ofNat ((a.val * b.val + c.val) % 4294967296) ::
      Felt.ofNat ((a.val * b.val + c.val) / 4294967296) :: rest, mem, locs, adv⟩ := by
  unfold execU32WidenMadd u32WideMadd u32Max
  simp [ha, hb, hc, MidenState.withStack]

end MidenLean
