import MidenLean.Proofs.Tactics
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

private theorem felt31_val : (31 : Felt).val = 31 :=
  felt_ofNat_val_lt 31 (by unfold GOLDILOCKS_PRIME; omega)

private theorem felt31_isU32 : (31 : Felt).isU32 = true := by
  simp only [Felt.isU32, decide_eq_true_eq]
  rw [felt31_val]
  omega

private def rotl_chunk1 : List Op := [
  .inst (.movup 2),
  .inst (.swap 1),
  .inst (.push 31),
  .inst (.dup 1),
  .inst (.u32OverflowSub)
]

private def rotl_chunk2 : List Op := [
  .inst (.swap 1),
  .inst (.drop),
  .inst (.movdn 3),
  .inst (.push 31),
  .inst (.u32And),
  .inst (.pow2)
]

private def rotl_chunk3 : List Op := [
  .inst (.dup 0),
  .inst (.movup 3),
  .inst (.u32WidenMul),
  .inst (.swap 1),
  .inst (.movup 3),
  .inst (.movup 3),
  .inst (.u32WidenMadd),
  .inst (.swap 1),
  .inst (.movup 2),
  .inst (.add),
  .inst (.swap 1),
  .inst (.movup 2)
]

private def rotl_chunk4 : List Op := [
  .inst (.cswap),
  .inst (.swap 1)
]

private theorem rotl_decomp :
    Miden.Core.U64.rotl = rotl_chunk1 ++ (rotl_chunk2 ++ (rotl_chunk3 ++ rotl_chunk4)) := by
  simp [Miden.Core.U64.rotl, rotl_chunk1, rotl_chunk2, rotl_chunk3, rotl_chunk4]

set_option maxHeartbeats 12000000 in
private theorem rotl_chunk1_correct
    (shift lo hi : Felt) (rest : List Felt) (mem locs : Nat → Felt) (adv : List Felt)
    (hshift_u32 : shift.isU32 = true) :
    exec 30 ⟨shift :: lo :: hi :: rest, mem, locs, adv⟩ rotl_chunk1 =
      some ⟨Felt.ofNat (u32OverflowingSub 31 shift.val).1 ::
        Felt.ofNat (u32OverflowingSub 31 shift.val).2 ::
        shift :: hi :: lo :: rest, mem, locs, adv⟩ := by
  unfold exec rotl_chunk1 execWithEnv
  simp only [List.foldlM]
  miden_movup
  miden_swap
  rw [stepPush]
  miden_bind
  miden_dup
  rw [stepU32OverflowSub (ha := felt31_isU32) (hb := hshift_u32)]
  miden_bind
  rw [felt31_val]
  simp only [pure, Pure.pure]

set_option maxHeartbeats 12000000 in
private theorem rotl_chunk2_correct
    (shift lo hi : Felt) (rest : List Felt) (mem locs : Nat → Felt) (adv : List Felt)
    (hshift_u32 : shift.isU32 = true) :
    exec 30
      ⟨Felt.ofNat (u32OverflowingSub 31 shift.val).1 ::
        Felt.ofNat (u32OverflowingSub 31 shift.val).2 ::
        shift :: hi :: lo :: rest, mem, locs, adv⟩
      rotl_chunk2 =
      some ⟨Felt.ofNat (2 ^ (shift.val &&& 31)) ::
        hi :: lo :: Felt.ofNat (u32OverflowingSub 31 shift.val).1 :: rest, mem, locs, adv⟩ := by
  unfold exec rotl_chunk2 execWithEnv
  simp only [List.foldlM]
  have h_eff_bound : shift.val &&& 31 ≤ 31 := Nat.and_le_right
  have h_eff_lt_prime : shift.val &&& 31 < GOLDILOCKS_PRIME := by
    unfold GOLDILOCKS_PRIME
    omega
  have h_eff_val : (Felt.ofNat (shift.val &&& 31)).val = shift.val &&& 31 :=
    felt_ofNat_val_lt _ h_eff_lt_prime
  miden_swap
  rw [stepDrop]
  miden_bind
  miden_movdn
  rw [stepPush]
  miden_bind
  rw [stepU32And (ha := hshift_u32) (hb := felt31_isU32)]
  miden_bind
  rw [felt31_val]
  rw [stepPow2 (ha := by rw [h_eff_val]; omega)]
  miden_bind
  rw [h_eff_val]
  simp only [pure, Pure.pure]

set_option maxHeartbeats 12000000 in
private theorem rotl_chunk3_correct
    (shift lo hi : Felt) (rest : List Felt) (mem locs : Nat → Felt) (adv : List Felt)
    (hlo : lo.isU32 = true) (hhi : hi.isU32 = true) :
    let eff := shift.val &&& 31
    let pow := Felt.ofNat (2 ^ eff)
    let lo_prod_lo := Felt.ofNat ((2 ^ eff * lo.val) % 2 ^ 32)
    let cross_lo := Felt.ofNat ((hi.val * 2 ^ eff + (2 ^ eff * lo.val) / 2 ^ 32) % 2 ^ 32)
    let result_hi :=
      Felt.ofNat ((hi.val * 2 ^ eff + (2 ^ eff * lo.val) / 2 ^ 32) / 2 ^ 32) + lo_prod_lo
    exec 30
      ⟨pow :: hi :: lo :: Felt.ofNat (u32OverflowingSub 31 shift.val).1 :: rest, mem, locs, adv⟩
      rotl_chunk3 =
      some ⟨Felt.ofNat (u32OverflowingSub 31 shift.val).1 ::
        cross_lo :: result_hi :: rest, mem, locs, adv⟩ := by
  unfold exec rotl_chunk3 execWithEnv
  simp only [List.foldlM]
  have h_eff_bound : shift.val &&& 31 ≤ 31 := Nat.and_le_right
  have h_pow_lt_prime : 2 ^ (shift.val &&& 31) < GOLDILOCKS_PRIME := by
    have hpow_le : 2 ^ (shift.val &&& 31) ≤ 2 ^ 31 :=
      Nat.pow_le_pow_right (by omega) h_eff_bound
    unfold GOLDILOCKS_PRIME
    omega
  have h_pow_val : (Felt.ofNat (2 ^ (shift.val &&& 31))).val = 2 ^ (shift.val &&& 31) :=
    felt_ofNat_val_lt _ h_pow_lt_prime
  have h_pow_u32 : (Felt.ofNat (2 ^ (shift.val &&& 31))).isU32 = true := by
    simp only [Felt.isU32, decide_eq_true_eq]
    rw [h_pow_val]
    have hpow_le : 2 ^ (shift.val &&& 31) ≤ 2 ^ 31 :=
      Nat.pow_le_pow_right (by omega) h_eff_bound
    omega
  have h_carry_isU32 :
      (Felt.ofNat ((2 ^ (shift.val &&& 31) * lo.val) / 2 ^ 32)).isU32 = true := by
    have h :=
      u32_prod_div_isU32 (Felt.ofNat (2 ^ (shift.val &&& 31))) lo h_pow_u32 hlo
    rw [h_pow_val] at h
    exact h
  have h_carry_val : (Felt.ofNat ((2 ^ (shift.val &&& 31) * lo.val) / 2 ^ 32)).val =
      (2 ^ (shift.val &&& 31) * lo.val) / 2 ^ 32 := by
    have h :=
      felt_ofNat_val_lt _ (u32_prod_div_lt_prime (Felt.ofNat (2 ^ (shift.val &&& 31))) lo h_pow_u32 hlo)
    rw [h_pow_val] at h
    exact h
  miden_dup
  miden_movup
  rw [stepU32WidenMul (ha := by assumption) (hb := by assumption)]
  miden_bind
  rw [h_pow_val]
  miden_swap
  miden_movup
  miden_movup
  rw [stepU32WidenMadd (ha := by assumption) (hb := by assumption) (hc := by assumption)]
  miden_bind
  rw [h_pow_val, h_carry_val]
  miden_swap
  miden_movup
  rw [stepAdd]
  miden_bind
  miden_swap
  miden_movup
  simp only [pure, Pure.pure]

set_option maxHeartbeats 12000000 in
private theorem rotl_chunk4_correct
    (shift lo hi : Felt) (rest : List Felt) (mem locs : Nat → Felt) (adv : List Felt) :
    let eff := shift.val &&& 31
    let lo_prod := 2 ^ eff * lo.val
    let cross := hi.val * 2 ^ eff + lo_prod / 2 ^ 32
    let result_lo := Felt.ofNat (cross % 2 ^ 32)
    let result_hi := Felt.ofNat (cross / 2 ^ 32) + Felt.ofNat (lo_prod % 2 ^ 32)
    exec 30
      ⟨Felt.ofNat (u32OverflowingSub 31 shift.val).1 ::
        result_lo :: result_hi :: rest, mem, locs, adv⟩
      rotl_chunk4 =
      some ⟨(if decide (31 < shift.val) then result_lo else result_hi) ::
        (if decide (31 < shift.val) then result_hi else result_lo) ::
        rest, mem, locs, adv⟩ := by
  unfold exec rotl_chunk4 execWithEnv
  simp only [List.foldlM]
  rw [u32OverflowingSub_borrow_ite 31 shift.val]
  rw [stepCswapIte]
  miden_bind
  miden_swap
  cases decide (31 < shift.val) <;> simp only [pure, Pure.pure]

set_option maxHeartbeats 16000000 in
/-- `u64::rotl` correctly left-rotates a u64 value.
    Input stack:  [shift, lo, hi] ++ rest
    Output stack: [result_lo, result_hi] ++ rest
    Requires shift, lo, and hi to be u32 values. -/
theorem u64_rotl_correct
    (lo hi shift : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = shift :: lo :: hi :: rest)
    (hshift_u32 : shift.isU32 = true)
    (hlo : lo.isU32 = true)
    (hhi : hi.isU32 = true) :
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
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  rw [rotl_decomp, MidenLean.exec_append]
  rw [rotl_chunk1_correct shift lo hi rest mem locs adv hshift_u32]
  miden_bind
  rw [MidenLean.exec_append]
  rw [rotl_chunk2_correct shift lo hi rest mem locs adv hshift_u32]
  miden_bind
  rw [MidenLean.exec_append]
  rw [rotl_chunk3_correct shift lo hi rest mem locs adv hlo hhi]
  miden_bind
  rw [rotl_chunk4_correct shift lo hi rest mem locs adv]
  cases decide (31 < shift.val) <;> simp

end MidenLean.Proofs
