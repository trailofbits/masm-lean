import MidenLean.Proofs.U256.Common
import MidenLean.Proofs.U256.Mulstep
import MidenLean.Proofs.Tactics

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

-- ============================================================================
-- Helper definitions for mulstep output
-- ============================================================================

/-- The carry output of a single mulstep call (raw computation order).
    Given carry-in `a`, value `b`, multiplier `c`, and accumulator `d`,
    mulstep computes `c * b + a` (widening multiply-add), then overflow-adds
    the low 32 bits with `d`. The carry is the sum of the two high parts. -/
noncomputable def mulstepCarry (a b c d : Felt) : Felt :=
  Felt.ofNat (((c.val * b.val + a.val) % 2 ^ 32 + d.val) / 2 ^ 32) +
  Felt.ofNat ((c.val * b.val + a.val) / 2 ^ 32)

/-- The low output of a single mulstep call:
    lo = ((c*b+a) % 2^32 + d) % 2^32. -/
noncomputable def mulstepLo (a b c d : Felt) : Felt :=
  Felt.ofNat (((c.val * b.val + a.val) % 2 ^ 32 + d.val) % 2 ^ 32)

-- ============================================================================
-- Commutativity lemmas (swap b and c positions)
-- ============================================================================

theorem mulstepLo_comm (a b c d : Felt) : mulstepLo a b c d = mulstepLo a c b d := by
  unfold mulstepLo; rw [Nat.mul_comm c.val b.val]

theorem mulstepCarry_comm (a b c d : Felt) : mulstepCarry a b c d = mulstepCarry a c b d := by
  unfold mulstepCarry; rw [Nat.mul_comm c.val b.val]

-- ============================================================================
-- Helper lemmas for carry isU32
-- ============================================================================

private theorem mulstep_carry_nat_lt (a b c d : Nat)
    (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (hc : c < 2 ^ 32) (hd : d < 2 ^ 32) :
    (c * b + a) / 2 ^ 32 + ((c * b + a) % 2 ^ 32 + d) / 2 ^ 32 < 2 ^ 32 := by
  have hcba : c * b + a ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) + (2 ^ 32 - 1) := by
    have : c * b ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  have h1 : (c * b + a) / 2 ^ 32 ≤ 2 ^ 32 - 1 := by
    calc (c * b + a) / 2 ^ 32
        ≤ ((2 ^ 32 - 1) * (2 ^ 32 - 1) + (2 ^ 32 - 1)) / 2 ^ 32 := Nat.div_le_div_right hcba
      _ ≤ 2 ^ 32 - 1 := by native_decide
  have h2 : ((c * b + a) % 2 ^ 32 + d) / 2 ^ 32 ≤ 1 := by
    calc ((c * b + a) % 2 ^ 32 + d) / 2 ^ 32
        ≤ ((2 ^ 32 - 1) + (2 ^ 32 - 1)) / 2 ^ 32 := by
          apply Nat.div_le_div_right
          have : (c * b + a) % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by positivity)
          omega
      _ ≤ 1 := by native_decide
  omega

/-- The Felt-level carry from mulstep is isU32. -/
theorem mulstep_carry_isU32 (a b c d : Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true)
    (hc : c.isU32 = true) (hd : d.isU32 = true) :
    (mulstepCarry a b c d).isU32 = true := by
  unfold mulstepCarry
  simp only [Felt.isU32, decide_eq_true_eq] at ha hb hc hd ⊢
  have hcba : c.val * b.val + a.val ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) + (2 ^ 32 - 1) := by
    have : c.val * b.val ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  have h1_lt : (c.val * b.val + a.val) / 2 ^ 32 < GOLDILOCKS_PRIME := by
    calc (c.val * b.val + a.val) / 2 ^ 32
        ≤ ((2 ^ 32 - 1) * (2 ^ 32 - 1) + (2 ^ 32 - 1)) / 2 ^ 32 := Nat.div_le_div_right hcba
      _ < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; native_decide
  have h2_lt : ((c.val * b.val + a.val) % 2 ^ 32 + d.val) / 2 ^ 32 < GOLDILOCKS_PRIME := by
    calc ((c.val * b.val + a.val) % 2 ^ 32 + d.val) / 2 ^ 32
        ≤ ((2 ^ 32 - 1) + (2 ^ 32 - 1)) / 2 ^ 32 := by
          apply Nat.div_le_div_right
          have : (c.val * b.val + a.val) % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by positivity)
          omega
      _ < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; native_decide
  have hsum_lt : ((c.val * b.val + a.val) % 2 ^ 32 + d.val) / 2 ^ 32 +
      (c.val * b.val + a.val) / 2 ^ 32 < GOLDILOCKS_PRIME := by
    have h1 : (c.val * b.val + a.val) / 2 ^ 32 ≤ 2 ^ 32 - 1 := by
      calc (c.val * b.val + a.val) / 2 ^ 32
          ≤ ((2 ^ 32 - 1) * (2 ^ 32 - 1) + (2 ^ 32 - 1)) / 2 ^ 32 := Nat.div_le_div_right hcba
        _ ≤ 2 ^ 32 - 1 := by native_decide
    have h2 : ((c.val * b.val + a.val) % 2 ^ 32 + d.val) / 2 ^ 32 ≤ 1 := by
      calc ((c.val * b.val + a.val) % 2 ^ 32 + d.val) / 2 ^ 32
          ≤ ((2 ^ 32 - 1) + (2 ^ 32 - 1)) / 2 ^ 32 := by
            apply Nat.div_le_div_right
            have : (c.val * b.val + a.val) % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by positivity)
            omega
        _ ≤ 1 := by native_decide
    unfold GOLDILOCKS_PRIME; omega
  rw [felt_add_val_no_wrap _ _
    (by rw [felt_ofNat_val_lt _ h2_lt, felt_ofNat_val_lt _ h1_lt]; exact hsum_lt)]
  rw [felt_ofNat_val_lt _ h2_lt, felt_ofNat_val_lt _ h1_lt]
  have := mulstep_carry_nat_lt a.val b.val c.val d.val ha hb hc hd
  omega

-- ============================================================================
-- mulstepLo isU32 lemma
-- ============================================================================

/-- The low output of a single mulstep call is always u32 (it's mod 2^32). -/
theorem mulstepLo_isU32 (a b c d : Felt) :
    (mulstepLo a b c d).isU32 = true := by
  unfold mulstepLo
  exact u32_mod_isU32 _

-- ============================================================================
-- Val-extraction lemmas for mulstepLo / mulstepCarry
-- ============================================================================

/-- The `.val` of `mulstepLo` is the Nat-level computation. -/
theorem mulstepLo_val (a b c d : Felt) :
    (mulstepLo a b c d).val = ((c.val * b.val + a.val) % 2 ^ 32 + d.val) % 2 ^ 32 := by
  unfold mulstepLo
  exact felt_ofNat_val_lt _ (u32_mod_lt_prime _)

/-- The `.val` of `mulstepCarry` is the Nat-level carry computation. -/
theorem mulstepCarry_val (a b c d : Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true)
    (hc : c.isU32 = true) (hd : d.isU32 = true) :
    (mulstepCarry a b c d).val =
      ((c.val * b.val + a.val) % 2 ^ 32 + d.val) / 2 ^ 32 +
      (c.val * b.val + a.val) / 2 ^ 32 := by
  unfold mulstepCarry
  simp only [Felt.isU32, decide_eq_true_eq] at ha hb hc hd
  have hcba : c.val * b.val + a.val ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) + (2 ^ 32 - 1) := by
    have : c.val * b.val ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  have h1_lt : (c.val * b.val + a.val) / 2 ^ 32 < GOLDILOCKS_PRIME := by
    calc (c.val * b.val + a.val) / 2 ^ 32
        ≤ ((2 ^ 32 - 1) * (2 ^ 32 - 1) + (2 ^ 32 - 1)) / 2 ^ 32 := Nat.div_le_div_right hcba
      _ < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; native_decide
  have h2_lt : ((c.val * b.val + a.val) % 2 ^ 32 + d.val) / 2 ^ 32 < GOLDILOCKS_PRIME := by
    calc ((c.val * b.val + a.val) % 2 ^ 32 + d.val) / 2 ^ 32
        ≤ ((2 ^ 32 - 1) + (2 ^ 32 - 1)) / 2 ^ 32 := by
          apply Nat.div_le_div_right
          have : (c.val * b.val + a.val) % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by positivity)
          omega
      _ < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; native_decide
  have hsum_lt : ((c.val * b.val + a.val) % 2 ^ 32 + d.val) / 2 ^ 32 +
      (c.val * b.val + a.val) / 2 ^ 32 < GOLDILOCKS_PRIME := by
    have h1 : (c.val * b.val + a.val) / 2 ^ 32 ≤ 2 ^ 32 - 1 := by
      calc (c.val * b.val + a.val) / 2 ^ 32
          ≤ ((2 ^ 32 - 1) * (2 ^ 32 - 1) + (2 ^ 32 - 1)) / 2 ^ 32 := Nat.div_le_div_right hcba
        _ ≤ 2 ^ 32 - 1 := by native_decide
    have h2 : ((c.val * b.val + a.val) % 2 ^ 32 + d.val) / 2 ^ 32 ≤ 1 := by
      calc ((c.val * b.val + a.val) % 2 ^ 32 + d.val) / 2 ^ 32
          ≤ ((2 ^ 32 - 1) + (2 ^ 32 - 1)) / 2 ^ 32 := by
            apply Nat.div_le_div_right
            have : (c.val * b.val + a.val) % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by positivity)
            omega
        _ ≤ 1 := by native_decide
    unfold GOLDILOCKS_PRIME; omega
  rw [felt_add_val_no_wrap _ _
    (by rw [felt_ofNat_val_lt _ h2_lt, felt_ofNat_val_lt _ h1_lt]; exact hsum_lt)]
  rw [felt_ofNat_val_lt _ h2_lt, felt_ofNat_val_lt _ h1_lt]

-- ============================================================================
-- Fundamental mulstep identity: carry * 2^32 + lo = c*b + a + d
-- ============================================================================

/-- The fundamental identity: the carry and lo outputs of mulstep
    reconstruct the full sum `c * b + a + d` at the Nat level. -/
theorem mulstep_val_sum (a b c d : Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true)
    (hc : c.isU32 = true) (hd : d.isU32 = true) :
    (mulstepCarry a b c d).val * 2 ^ 32 + (mulstepLo a b c d).val =
    c.val * b.val + a.val + d.val := by
  rw [mulstepCarry_val a b c d ha hb hc hd, mulstepLo_val a b c d]
  have hmod := Nat.div_add_mod (c.val * b.val + a.val) (2 ^ 32)
  have hmod2 := Nat.div_add_mod ((c.val * b.val + a.val) % 2 ^ 32 + d.val) (2 ^ 32)
  omega

/-- Simplified `.val` of `mulstepLo`: it is `(c*b + a + d) % 2^32`. -/
theorem mulstepLo_val_sum (a b c d : Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true)
    (hc : c.isU32 = true) (hd : d.isU32 = true) :
    (mulstepLo a b c d).val = (c.val * b.val + a.val + d.val) % 2 ^ 32 := by
  have h := mulstep_val_sum a b c d ha hb hc hd
  have hlo : (mulstepLo a b c d).val < 2 ^ 32 := by
    have := mulstepLo_isU32 a b c d
    simp only [Felt.isU32, decide_eq_true_eq] at this; exact this
  omega

/-- Simplified `.val` of `mulstepCarry`: it is `(c*b + a + d) / 2^32`. -/
theorem mulstepCarry_val_sum (a b c d : Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true)
    (hc : c.isU32 = true) (hd : d.isU32 = true) :
    (mulstepCarry a b c d).val = (c.val * b.val + a.val + d.val) / 2 ^ 32 := by
  have h := mulstep_val_sum a b c d ha hb hc hd
  have hcarry : (mulstepCarry a b c d).val < 2 ^ 32 := by
    have := mulstep_carry_isU32 a b c d ha hb hc hd
    simp only [Felt.isU32, decide_eq_true_eq] at this; exact this
  have hlo : (mulstepLo a b c d).val < 2 ^ 32 := by
    have := mulstepLo_isU32 a b c d
    simp only [Felt.isU32, decide_eq_true_eq] at this; exact this
  omega

-- ============================================================================
-- Key Nat identity for carry combining across rounds
-- ============================================================================

/-- The carry-combining identity: `(x % m + y) / m + x / m = (x + y) / m`.
    This allows us to combine carries from different multiplication rounds at the same
    limb position into a single carry-chain value. -/
theorem Nat.div_add_mod_div (x y m : Nat) (hm : 0 < m) :
    (x % m + y) / m + x / m = (x + y) / m := by
  rw [show x + y = m * (x / m) + (x % m + y) from by have := Nat.div_add_mod x m; omega,
      Nat.mul_add_div hm]; omega

-- ============================================================================
-- execWithEnv-compatible mulstep lemma
-- ============================================================================

set_option maxHeartbeats 4000000 in
/-- mulstep correctness for execWithEnv: given any env and sufficient fuel,
    mulstep produces [mulstepCarry a b c d, mulstepLo a b c d] ++ rest. -/
theorem mulstep_execWithEnv
    (env : ProcEnv) (fuel : Nat) (a b c d : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = a :: b :: c :: d :: rest)
    (ha : a.isU32 = true) (hb : b.isU32 = true)
    (hc : c.isU32 = true) (hd : d.isU32 = true) :
    execWithEnv env (fuel + 1) s Miden.Core.U256.mulstep =
    some (s.withStack (mulstepCarry a b c d :: mulstepLo a b c d :: rest)) := by
  obtain ⟨stk, mem, frames, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold mulstepCarry mulstepLo
  unfold Miden.Core.U256.mulstep execWithEnv
  simp only [List.foldlM]
  -- movdn 2
  miden_movdn
  -- u32WidenMadd
  rw [stepU32WidenMadd (ha := hc) (hb := hb) (hc := ha)]
  miden_bind
  -- movup 2
  miden_movup
  -- u32OverflowAdd
  rw [stepU32OverflowAdd (ha := u32_mod_isU32 _) (hb := hd)]
  miden_bind
  rw [felt_ofNat_val_lt _ (u32_mod_lt_prime _)]
  -- movup 2
  miden_movup
  -- add
  rw [stepAdd]; miden_bind
  simp only [pure, Pure.pure]

-- ============================================================================
-- Chunk definitions for mulstep4 decomposition
-- ============================================================================

/-- Setup and first mulstep call: movup 12, dup 1, movup 10, push 0, exec mulstep -/
private def mulstep4_chunk1 : List Op := [
  .inst (.movup 12), .inst (.dup 1), .inst (.movup 10), .inst (.push 0),
  .inst (.exec "mulstep")
]

/-- Post-call-1 shuffle and second mulstep call -/
private def mulstep4_chunk2 : List Op := [
  .inst (.swap 1), .inst (.movdn 9), .inst (.dup 1), .inst (.movup 9),
  .inst (.movup 13), .inst (.swap 3), .inst (.exec "mulstep")
]

/-- Post-call-2 shuffle and third mulstep call -/
private def mulstep4_chunk3 : List Op := [
  .inst (.swap 1), .inst (.movdn 8), .inst (.dup 1), .inst (.movup 8),
  .inst (.movup 12), .inst (.swap 3), .inst (.exec "mulstep")
]

/-- Post-call-3 shuffle and fourth mulstep call -/
private def mulstep4_chunk4 : List Op := [
  .inst (.swap 1), .inst (.movdn 7), .inst (.dup 1), .inst (.movup 7),
  .inst (.movup 11), .inst (.swap 3), .inst (.exec "mulstep")
]

/-- Final swap and movdn -/
private def mulstep4_chunk5 : List Op := [
  .inst (.swap 1), .inst (.movdn 6)
]

private theorem mulstep4_decomp :
    Miden.Core.U256.mulstep4.body =
    mulstep4_chunk1 ++ (mulstep4_chunk2 ++ (mulstep4_chunk3 ++
      (mulstep4_chunk4 ++ mulstep4_chunk5))) := by
  simp [Miden.Core.U256.mulstep4, mulstep4_chunk1, mulstep4_chunk2,
        mulstep4_chunk3, mulstep4_chunk4, mulstep4_chunk5]

-- ============================================================================
-- Chunk correctness lemmas
-- ============================================================================

set_option maxHeartbeats 8000000 in
/-- Chunk 1: setup + first mulstep.
    Stack [x0..x12] ++ rest → [carry1, lo1, x0..x7, x9..x11] ++ rest -/
private theorem mulstep4_chunk1_correct
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Felt) (rest : List Felt)
    (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (hx0 : x0.isU32 = true) (hx8 : x8.isU32 = true) (hx12 : x12.isU32 = true)
    (fuel : Nat) :
    execWithEnv u256ProcEnv (fuel + 2)
      ⟨x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest,
       mem, frames, adv⟩
      mulstep4_chunk1 =
    some ⟨mulstepCarry 0 x8 x0 x12 :: mulstepLo 0 x8 x0 x12 ::
          x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x9 :: x10 :: x11 :: rest,
          mem, frames, adv⟩ := by
  unfold mulstep4_chunk1 execWithEnv
  simp only [List.foldlM]
  miden_movup; miden_dup; miden_movup; miden_step  -- push 0
  simp only [u256ProcEnv]
  have h0u : (0 : Felt).isU32 = true := by simp [Felt.isU32]
  have hcall := mulstep_execWithEnv u256ProcEnv fuel 0 x8 x0 x12
    (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x9 :: x10 :: x11 :: rest)
    ⟨0 :: x8 :: x0 :: x12 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x9 :: x10 :: x11 :: rest,
     mem, frames, adv⟩
    rfl h0u hx8 hx0 hx12
  simp only [MidenState.withStack] at hcall
  simp only [hcall, pure, Pure.pure]

set_option maxHeartbeats 8000000 in
/-- Chunk 2: post-call-1 shuffle + second mulstep.
    Stack [carry, lo_prev, x0..x7, x9..x11] ++ rest
    → [carry', lo', x0..x6, lo_prev, x9, x10] ++ rest -/
private theorem mulstep4_chunk2_correct
    (carry lo_prev x0 x1 x2 x3 x4 x5 x6 x7 x9 x10 x11 : Felt) (rest : List Felt)
    (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (hcarry : carry.isU32 = true) (hx0 : x0.isU32 = true)
    (hx7 : x7.isU32 = true) (hx11 : x11.isU32 = true)
    (fuel : Nat) :
    execWithEnv u256ProcEnv (fuel + 2)
      ⟨carry :: lo_prev :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x9 :: x10 :: x11 :: rest,
       mem, frames, adv⟩
      mulstep4_chunk2 =
    some ⟨mulstepCarry carry x7 x0 x11 :: mulstepLo carry x7 x0 x11 ::
          x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: lo_prev :: x9 :: x10 :: rest,
          mem, frames, adv⟩ := by
  unfold mulstep4_chunk2 execWithEnv
  simp only [List.foldlM]
  miden_swap; miden_movdn; miden_dup; miden_movup; miden_movup; miden_swap
  simp only [u256ProcEnv]
  have hcall := mulstep_execWithEnv u256ProcEnv fuel carry x7 x0 x11
    (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: lo_prev :: x9 :: x10 :: rest)
    ⟨carry :: x7 :: x0 :: x11 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: lo_prev :: x9 :: x10 :: rest,
     mem, frames, adv⟩
    rfl hcarry hx7 hx0 hx11
  simp only [MidenState.withStack] at hcall
  simp only [hcall, pure, Pure.pure]

set_option maxHeartbeats 8000000 in
/-- Chunk 3: post-call-2 shuffle + third mulstep.
    Stack [carry, lo_prev, x0..x6, lo1, x9, x10] ++ rest
    → [carry', lo', x0..x5, lo_prev, lo1, x9] ++ rest -/
private theorem mulstep4_chunk3_correct
    (carry lo_prev x0 x1 x2 x3 x4 x5 x6 lo1 x9 x10 : Felt) (rest : List Felt)
    (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (hcarry : carry.isU32 = true) (hx0 : x0.isU32 = true)
    (hx6 : x6.isU32 = true) (hx10 : x10.isU32 = true)
    (fuel : Nat) :
    execWithEnv u256ProcEnv (fuel + 2)
      ⟨carry :: lo_prev :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: lo1 :: x9 :: x10 :: rest,
       mem, frames, adv⟩
      mulstep4_chunk3 =
    some ⟨mulstepCarry carry x6 x0 x10 :: mulstepLo carry x6 x0 x10 ::
          x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: lo_prev :: lo1 :: x9 :: rest,
          mem, frames, adv⟩ := by
  unfold mulstep4_chunk3 execWithEnv
  simp only [List.foldlM]
  miden_swap; miden_movdn; miden_dup; miden_movup; miden_movup; miden_swap
  simp only [u256ProcEnv]
  have hcall := mulstep_execWithEnv u256ProcEnv fuel carry x6 x0 x10
    (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: lo_prev :: lo1 :: x9 :: rest)
    ⟨carry :: x6 :: x0 :: x10 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: lo_prev :: lo1 :: x9 :: rest,
     mem, frames, adv⟩
    rfl hcarry hx6 hx0 hx10
  simp only [MidenState.withStack] at hcall
  simp only [hcall, pure, Pure.pure]

set_option maxHeartbeats 8000000 in
/-- Chunk 4: post-call-3 shuffle + fourth mulstep.
    Stack [carry, lo_prev, x0..x5, lo2, lo1, x9] ++ rest
    → [carry', lo', x0..x4, lo_prev, lo2, lo1] ++ rest -/
private theorem mulstep4_chunk4_correct
    (carry lo_prev x0 x1 x2 x3 x4 x5 lo2 lo1 x9 : Felt) (rest : List Felt)
    (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (hcarry : carry.isU32 = true) (hx0 : x0.isU32 = true)
    (hx5 : x5.isU32 = true) (hx9 : x9.isU32 = true)
    (fuel : Nat) :
    execWithEnv u256ProcEnv (fuel + 2)
      ⟨carry :: lo_prev :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: lo2 :: lo1 :: x9 :: rest,
       mem, frames, adv⟩
      mulstep4_chunk4 =
    some ⟨mulstepCarry carry x5 x0 x9 :: mulstepLo carry x5 x0 x9 ::
          x0 :: x1 :: x2 :: x3 :: x4 :: lo_prev :: lo2 :: lo1 :: rest,
          mem, frames, adv⟩ := by
  unfold mulstep4_chunk4 execWithEnv
  simp only [List.foldlM]
  miden_swap; miden_movdn; miden_dup; miden_movup; miden_movup; miden_swap
  simp only [u256ProcEnv]
  have hcall := mulstep_execWithEnv u256ProcEnv fuel carry x5 x0 x9
    (x0 :: x1 :: x2 :: x3 :: x4 :: lo_prev :: lo2 :: lo1 :: rest)
    ⟨carry :: x5 :: x0 :: x9 :: x0 :: x1 :: x2 :: x3 :: x4 :: lo_prev :: lo2 :: lo1 :: rest,
     mem, frames, adv⟩
    rfl hcarry hx5 hx0 hx9
  simp only [MidenState.withStack] at hcall
  simp only [hcall, pure, Pure.pure]

/-- Chunk 5: final swap and movdn.
    Stack [carry, lo, x0..x4, lo3, lo2, lo1] ++ rest
    → [carry, x0..x4, lo, lo3, lo2, lo1] ++ rest -/
private theorem mulstep4_chunk5_correct
    (carry lo x0 x1 x2 x3 x4 lo3 lo2 lo1 : Felt) (rest : List Felt)
    (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) :
    execWithEnv u256ProcEnv (fuel + 2)
      ⟨carry :: lo :: x0 :: x1 :: x2 :: x3 :: x4 :: lo3 :: lo2 :: lo1 :: rest,
       mem, frames, adv⟩
      mulstep4_chunk5 =
    some ⟨carry :: x0 :: x1 :: x2 :: x3 :: x4 :: lo :: lo3 :: lo2 :: lo1 :: rest,
          mem, frames, adv⟩ := by
  unfold mulstep4_chunk5 execWithEnv
  simp only [List.foldlM]
  miden_swap; miden_movdn
  simp only [pure, Pure.pure]

-- ============================================================================
-- Main theorem
-- ============================================================================

set_option maxHeartbeats 8000000 in
/-- `mulstep4` performs four sequential `mulstep` calls, threading carry through.
    Input stack:  [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12] ++ rest
    Output stack: [carry4, x0, x1, x2, x3, x4, lo4, lo3, lo2, lo1] ++ rest
    where carry_i and lo_i are the carry and low outputs of each sequential mulstep call:
      carry1 = mulstepCarry(0, x8, x0, x12),  lo1 = mulstepLo(0, x8, x0, x12)
      carry2 = mulstepCarry(carry1, x7, x0, x11), lo2 = mulstepLo(carry1, x7, x0, x11)
      carry3 = mulstepCarry(carry2, x6, x0, x10), lo3 = mulstepLo(carry2, x6, x0, x10)
      carry4 = mulstepCarry(carry3, x5, x0, x9),  lo4 = mulstepLo(carry3, x5, x0, x9) -/
theorem u256_mulstep4_correct
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest)
    (hx0 : x0.isU32 = true) (hx5 : x5.isU32 = true)
    (hx6 : x6.isU32 = true) (hx7 : x7.isU32 = true)
    (hx8 : x8.isU32 = true) (hx9 : x9.isU32 = true)
    (hx10 : x10.isU32 = true) (hx11 : x11.isU32 = true)
    (hx12 : x12.isU32 = true)
    (fuel : Nat) :
    let carry1 := mulstepCarry 0 x8 x0 x12
    let lo1    := mulstepLo    0 x8 x0 x12
    let carry2 := mulstepCarry carry1 x7 x0 x11
    let lo2    := mulstepLo    carry1 x7 x0 x11
    let carry3 := mulstepCarry carry2 x6 x0 x10
    let lo3    := mulstepLo    carry2 x6 x0 x10
    let carry4 := mulstepCarry carry3 x5 x0 x9
    let lo4    := mulstepLo    carry3 x5 x0 x9
    execWithEnv u256ProcEnv (fuel + 2) s Miden.Core.U256.mulstep4 =
    some (s.withStack (carry4 :: x0 :: x1 :: x2 :: x3 :: x4 ::
                       lo4 :: lo3 :: lo2 :: lo1 :: rest)) := by
  obtain ⟨stk, mem, frames, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  -- Decompose into chunks
  rw [execWithEnv_body_eq _ _ _ _ _ mulstep4_decomp rfl, execWithEnv_append]
  -- Chunk 1: setup + first mulstep
  rw [mulstep4_chunk1_correct (hx0 := hx0) (hx8 := hx8) (hx12 := hx12)]
  simp only [bind, Bind.bind, Option.bind]
  -- Chunk 2: shuffle + second mulstep
  rw [execWithEnv_append]
  have hc1u : (mulstepCarry 0 x8 x0 x12).isU32 = true :=
    mulstep_carry_isU32 0 x8 x0 x12 (by simp [Felt.isU32]) hx8 hx0 hx12
  rw [mulstep4_chunk2_correct (hcarry := hc1u) (hx0 := hx0) (hx7 := hx7) (hx11 := hx11)]
  simp only [bind, Bind.bind, Option.bind]
  -- Chunk 3: shuffle + third mulstep
  rw [execWithEnv_append]
  have hc2u : (mulstepCarry (mulstepCarry 0 x8 x0 x12) x7 x0 x11).isU32 = true :=
    mulstep_carry_isU32 _ x7 x0 x11 hc1u hx7 hx0 hx11
  rw [mulstep4_chunk3_correct (hcarry := hc2u) (hx0 := hx0) (hx6 := hx6) (hx10 := hx10)]
  simp only [bind, Bind.bind, Option.bind]
  -- Chunk 4: shuffle + fourth mulstep
  rw [execWithEnv_append]
  have hc3u : (mulstepCarry (mulstepCarry (mulstepCarry 0 x8 x0 x12) x7 x0 x11) x6 x0 x10).isU32 = true :=
    mulstep_carry_isU32 _ x6 x0 x10 hc2u hx6 hx0 hx10
  rw [mulstep4_chunk4_correct (hcarry := hc3u) (hx0 := hx0) (hx5 := hx5) (hx9 := hx9)]
  simp only [bind, Bind.bind, Option.bind]
  -- Chunk 5: final swap and movdn
  rw [mulstep4_chunk5_correct]

end MidenLean.Proofs
