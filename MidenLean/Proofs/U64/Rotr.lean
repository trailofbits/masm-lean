import MidenLean.Proofs.Tactics
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

/-- Helper: convert Prop-ite to Bool-ite for boolean step lemmas. -/
private theorem ite_prop_to_decide {p : Prop} [Decidable p] (a b : Felt) :
    (if p then a else b) = if decide p then a else b := by
  cases ‹Decidable p› <;> rfl

/-- The effective shift value in rotr is ≤ 32, hence ≤ 63 for pow2. -/
private theorem rotr_eff_shift_le_63 (shift : Felt) (hshift_u32 : shift.isU32 = true) :
    (Felt.ofNat (u32OverflowingSub (32 : Felt).val
        (Felt.ofNat (shift.val &&& (31 : Felt).val)).val).2).val ≤ 63 := by
  simp only [Felt.isU32, decide_eq_true_eq] at hshift_u32
  have h31_val : (31 : Felt).val = 31 :=
    felt_ofNat_val_lt 31 (by unfold GOLDILOCKS_PRIME; omega)
  have h32_val : (32 : Felt).val = 32 :=
    felt_ofNat_val_lt 32 (by unfold GOLDILOCKS_PRIME; omega)
  rw [h31_val, h32_val]
  have hAnd_le : shift.val &&& 31 ≤ 31 := Nat.and_le_right
  have hAnd_val : (Felt.ofNat (shift.val &&& 31) : Felt).val = shift.val &&& 31 :=
    felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)
  rw [hAnd_val]
  unfold u32OverflowingSub
  split
  · have hResult_lt : 32 - (shift.val &&& 31) < GOLDILOCKS_PRIME := by
      unfold GOLDILOCKS_PRIME; omega
    rw [felt_ofNat_val_lt _ hResult_lt]; omega
  · omega

set_option maxHeartbeats 16000000 in
/-- u64.rotr correctly right-rotates a u64 value.
    Input stack:  [shift, lo, hi] ++ rest
    Output stack: [result_lo, result_hi] ++ rest
    Requires shift.isU32 (for u32Lt and u32And). -/
theorem u64_rotr_correct
    (lo hi shift : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = shift :: lo :: hi :: rest)
    (hshift_u32 : shift.isU32 = true) :
    let cmp := decide ((31 : Felt).val < shift.val)
    let shiftAnd31 := Felt.ofNat (shift.val &&& (31 : Felt).val)
    let eff_shift := Felt.ofNat (u32OverflowingSub (32 : Felt).val shiftAnd31.val).2
    let pow := Felt.ofNat (2 ^ eff_shift.val)
    let prod1 := pow * lo
    let cross := prod1.hi32 + hi * pow
    exec 35 s Miden.Core.U64.rotr =
    some (s.withStack (
      if !cmp then
        cross.lo32 :: (cross.hi32 + prod1.lo32) :: rest
      else
        (cross.hi32 + prod1.lo32) :: cross.lo32 :: rest)) := by
  miden_setup Miden.Core.U64.rotr
  -- 1-2: movup 2; swap 1
  miden_movup; miden_swap
  -- 3: push 31
  rw [stepPush]; miden_bind
  -- 4: dup 1
  miden_dup
  -- 5: u32Lt
  have h31_u32 : Felt.isU32 (31 : Felt) = true := by native_decide
  rw [stepU32Lt (ha := h31_u32) (hb := hshift_u32)]; miden_bind
  rw [ite_prop_to_decide (p := (31 : Felt).val < shift.val)]
  -- 6: movdn 3
  miden_movdn
  -- 7: push 31
  rw [stepPush]; miden_bind
  -- 8: u32And
  rw [stepU32And (ha := hshift_u32) (hb := h31_u32)]; miden_bind
  -- 9: push 32
  rw [stepPush]; miden_bind
  -- 10: swap 1
  miden_swap
  -- 11: u32WrappingSub
  rw [execInstruction_u32WrappingSub]; unfold execU32WrappingSub; miden_bind
  -- 12: pow2
  rw [stepPow2 (ha := rotr_eff_shift_le_63 shift hshift_u32)]; miden_bind
  -- 13-14: dup 0; movup 3
  miden_dup; miden_movup
  -- 15: mul
  rw [stepMul]; miden_bind
  -- 16: u32Split
  rw [stepU32Split]; miden_bind
  -- 17-19: swap 1; movup 3; movup 3
  miden_swap; miden_movup; miden_movup
  -- 20: mul
  rw [stepMul]; miden_bind
  -- 21: add
  rw [stepAdd]; miden_bind
  -- 22: u32Split
  rw [stepU32Split]; miden_bind
  -- 23-24: swap 1; movup 2
  miden_swap; miden_movup
  -- 25: add
  rw [stepAdd]; miden_bind
  -- 26-27: swap 1; movup 2
  miden_swap; miden_movup
  -- 28: not (on Bool-ite form)
  rw [stepNotIte]; miden_bind
  -- 29: cswap
  rw [stepCswapIte]; miden_bind
  -- 30: swap 1 - split on the boolean condition
  cases decide ((31 : Felt).val < shift.val)
  · miden_swap
  · miden_swap

end MidenLean.Proofs
