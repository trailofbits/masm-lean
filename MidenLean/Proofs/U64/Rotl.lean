import MidenLean.Proofs.Tactics
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 16000000 in
/-- u64.rotl correctly left-rotates a u64 value.
    Input stack:  [shift, lo, hi] ++ rest
    Output stack: depends on whether shift > 31 (cswap).
    Requires shift.isU32 (for u32And) and lo.isU32 (for value recovery). -/
theorem u64_rotl_correct
    (lo hi shift : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = shift :: lo :: hi :: rest)
    (hshift_u32 : shift.isU32 = true)
    (hlo : lo.isU32 = true) :
    let eff := shift.val &&& 31
    let pow := 2 ^ eff
    let lo_prod := pow * lo.val
    let cross := hi.val * pow + lo_prod / 2 ^ 32
    let result_lo := Felt.ofNat (cross % 2 ^ 32)
    let result_hi := Felt.ofNat (cross / 2 ^ 32) + Felt.ofNat (lo_prod % 2 ^ 32)
    exec 30 s Miden.Core.U64.rotl =
    some (s.withStack (
      if decide (31 < shift.val) then
        result_lo :: result_hi :: rest
      else
        result_hi :: result_lo :: rest)) := by
  miden_setup Miden.Core.U64.rotl
  -- Step 1: movup 2
  miden_movup
  -- Step 2: swap 1
  miden_swap
  -- Step 3: push 31
  rw [stepPush]; miden_bind
  -- Step 4: dup 1
  miden_dup
  -- Step 5: u32OverflowSub
  rw [execInstruction_u32OverflowSub]; unfold execU32OverflowSub;
  dsimp only [bind, Bind.bind, Option.bind, MidenState.withStack, MidenState.stack,
    MidenState.memory, MidenState.locals, MidenState.advice]
  -- Step 6: swap 1
  miden_swap
  -- Step 7: drop
  rw [stepDrop]; miden_bind
  -- Step 8: movdn 3
  miden_movdn
  -- Step 9: push 31
  rw [stepPush]; miden_bind
  -- Prove (31 : Felt).val = 31 for value recovery
  have h31_val : (31 : Felt).val = 31 :=
    felt_ofNat_val_lt 31 (by unfold GOLDILOCKS_PRIME; omega)
  -- Prove (31 : Felt).isU32
  have h31_u32 : (31 : Felt).isU32 = true := by
    simp only [Felt.isU32, decide_eq_true_eq]
    rw [h31_val]; omega
  -- Step 10: u32And
  rw [stepU32And (ha := hshift_u32) (hb := h31_u32)]; miden_bind
  rw [h31_val]
  -- Prove the AND result is <= 31, hence its Felt.val equals itself
  have h_eff_bound : shift.val &&& 31 ≤ 31 := Nat.and_le_right
  have h_eff_lt_prime : shift.val &&& 31 < GOLDILOCKS_PRIME := by
    unfold GOLDILOCKS_PRIME; omega
  have h_eff_val : (Felt.ofNat (shift.val &&& 31)).val = shift.val &&& 31 :=
    felt_ofNat_val_lt _ h_eff_lt_prime
  -- Step 11: pow2
  rw [stepPow2 (ha := by rw [h_eff_val]; omega)]; miden_bind
  rw [h_eff_val]
  -- Prove pow is u32 (2^eff <= 2^31 < 2^32)
  have h_pow_lt_prime : 2 ^ (shift.val &&& 31) < GOLDILOCKS_PRIME := by
    have : 2 ^ (shift.val &&& 31) ≤ 2 ^ 31 := Nat.pow_le_pow_right (by omega) h_eff_bound
    unfold GOLDILOCKS_PRIME; omega
  have h_pow_val : (Felt.ofNat (2 ^ (shift.val &&& 31))).val = 2 ^ (shift.val &&& 31) :=
    felt_ofNat_val_lt _ h_pow_lt_prime
  have h_pow_u32 : (Felt.ofNat (2 ^ (shift.val &&& 31))).isU32 = true := by
    simp only [Felt.isU32, decide_eq_true_eq]
    rw [h_pow_val]
    have : 2 ^ (shift.val &&& 31) ≤ 2 ^ 31 := Nat.pow_le_pow_right (by omega) h_eff_bound
    omega
  -- Step 12: dup 0
  miden_dup
  -- Step 13: movup 3
  miden_movup
  -- Step 14: u32WidenMul
  rw [execInstruction_u32WidenMul, execU32WidenMul_concrete]
  dsimp only [bind, Bind.bind, Option.bind]
  rw [h_pow_val]
  -- Step 15: swap 1
  miden_swap
  -- Step 16: movup 3
  miden_movup
  -- Step 17: movup 3
  miden_movup
  -- Value recovery for the carry (lo_prod / 2^32)
  have h_carry_val : (Felt.ofNat (2 ^ (shift.val &&& 31) * lo.val / 2 ^ 32)).val =
      2 ^ (shift.val &&& 31) * lo.val / 2 ^ 32 := by
    apply felt_ofNat_val_lt
    have := u32_prod_div_lt_prime (Felt.ofNat (2 ^ (shift.val &&& 31))) lo h_pow_u32 hlo
    rw [h_pow_val] at this
    exact this
  -- Step 18: u32WidenMadd
  rw [execInstruction_u32WidenMadd, execU32WidenMadd_concrete]
  dsimp only [bind, Bind.bind, Option.bind]
  rw [show (4294967296 : Nat) = 2 ^ 32 from rfl]
  rw [h_pow_val, h_carry_val]
  -- Step 19: swap 1
  miden_swap
  -- Step 20: movup 2
  miden_movup
  -- Step 21: add
  rw [stepAdd]; miden_bind
  -- Step 22: swap 1
  miden_swap
  -- Step 23: movup 2
  miden_movup
  -- Rewrite borrow to if-then-else form for cswap
  rw [u32OverflowingSub_borrow_ite 31 shift.val]
  -- Step 24: cswap
  rw [stepCswapIte]; miden_bind
  -- Step 25: swap 1 - split on the boolean condition
  cases decide (31 < shift.val)
  · -- Case: shift <= 31
    simp only [Bool.false_eq_true, ↓reduceIte]
    miden_swap
  · -- Case: shift > 31
    simp only [↓reduceIte]
    miden_swap

end MidenLean.Proofs
