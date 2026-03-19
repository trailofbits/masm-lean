import MidenLean.Proofs.Tactics
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

private theorem exec_append (fuel : Nat) (s : MidenState)
    (xs ys : List Op) :
    exec fuel s (xs ++ ys) = (do
      let s' ← exec fuel s xs
      exec fuel s' ys) := by
  unfold exec execWithEnv
  cases fuel <;> simp [List.foldlM_append]

-- Split at instruction 15 (after u32WidenMul)
private def rotl_h1 : List Op := [
  .inst (.movup 2), .inst (.swap 1),
  .inst (.push 31), .inst (.dup 1),
  .inst (.u32OverflowSub), .inst (.swap 1),
  .inst (.drop), .inst (.movdn 3),
  .inst (.push 31), .inst (.u32And), .inst (.pow2),
  .inst (.dup 0), .inst (.movup 3),
  .inst (.u32WidenMul), .inst (.swap 1)]

private def rotl_h2 : List Op := [
  .inst (.movup 3), .inst (.movup 3),
  .inst (.u32WidenMadd), .inst (.swap 1),
  .inst (.movup 2), .inst (.add),
  .inst (.swap 1), .inst (.movup 2),
  .inst (.cswap), .inst (.swap 1)]

private theorem rotl_split :
    Miden.Core.U64.rotl = rotl_h1 ++ rotl_h2 := by
  simp [Miden.Core.U64.rotl, rotl_h1, rotl_h2]

set_option maxHeartbeats 4000000 in
private theorem rotl_h1_ok
    (lo hi shift : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
    (hshift_u32 : shift.isU32 = true)
    (hlo : lo.isU32 = true) :
    let eff := shift.val &&& 31
    let pow := 2 ^ eff
    let lo_prod := pow * lo.val
    exec 30
      ⟨shift :: lo :: hi :: rest,
       mem, locs, adv⟩ rotl_h1 =
    some ⟨Felt.ofNat (lo_prod / 2 ^ 32) ::
          Felt.ofNat (lo_prod % 2 ^ 32) ::
          Felt.ofNat pow ::
          hi ::
          Felt.ofNat
            (u32OverflowingSub 31 shift.val).1 ::
          rest,
      mem, locs, adv⟩ := by
  dsimp only []
  unfold exec rotl_h1 execWithEnv
  simp only [List.foldlM]
  miden_movup; miden_swap
  rw [stepPush]; miden_bind
  miden_dup
  have h31_u32 : Felt.isU32 (31 : Felt) = true := by
    native_decide
  rw [stepU32OverflowSub (ha := h31_u32)
    (hb := hshift_u32)]; miden_bind
  miden_swap; rw [stepDrop]; miden_bind
  miden_movdn; rw [stepPush]; miden_bind
  rw [stepU32And (ha := hshift_u32)
    (hb := h31_u32)]; miden_bind
  have h31_val : (31 : Felt).val = 31 :=
    felt_ofNat_val_lt 31
      (by unfold GOLDILOCKS_PRIME; omega)
  rw [h31_val]
  have h_eff_bound : shift.val &&& 31 ≤ 31 :=
    Nat.and_le_right
  have h_eff_val :
    (Felt.ofNat (shift.val &&& 31)).val =
      shift.val &&& 31 :=
    felt_ofNat_val_lt _
      (by unfold GOLDILOCKS_PRIME; omega)
  rw [stepPow2 (ha := by rw [h_eff_val]; omega)]
  miden_bind; rw [h_eff_val]
  miden_dup; miden_movup
  have h_pow_u32 :
    (Felt.ofNat (2 ^ (shift.val &&& 31))).isU32 =
      true := by
    simp only [Felt.isU32, decide_eq_true_eq, u32Max]
    rw [felt_ofNat_val_lt _ (by
      have : 2 ^ (shift.val &&& 31) ≤ 2 ^ 31 :=
        Nat.pow_le_pow_right (by omega) h_eff_bound
      unfold GOLDILOCKS_PRIME; omega)]
    have : 2 ^ (shift.val &&& 31) ≤ 2 ^ 31 :=
      Nat.pow_le_pow_right (by omega) h_eff_bound
    omega
  rw [execInstruction_u32WidenMul,
    execU32WidenMul_concrete (ha := h_pow_u32)
      (hb := hlo)]
  dsimp only [bind, Bind.bind, Option.bind]
  have h_pow_val :
    (Felt.ofNat (2 ^ (shift.val &&& 31))).val =
      2 ^ (shift.val &&& 31) := by
    apply felt_ofNat_val_lt
    have : 2 ^ (shift.val &&& 31) ≤ 2 ^ 31 :=
      Nat.pow_le_pow_right (by omega) h_eff_bound
    unfold GOLDILOCKS_PRIME; omega
  rw [h_pow_val, show (4294967296 : Nat) = 2 ^ 32 from rfl]
  miden_swap
  dsimp only [pure, Pure.pure]

-- Helper: carry is u32
private theorem rotl_carry_u32 (lo shift : Felt)
    (hshift_u32 : shift.isU32 = true)
    (hlo : lo.isU32 = true) :
    (Felt.ofNat (2 ^ (shift.val &&& 31) * lo.val /
      2 ^ 32)).isU32 = true := by
  have h_pow_u32 :
    (Felt.ofNat (2 ^ (shift.val &&& 31))).isU32 =
      true := by
    simp only [Felt.isU32, decide_eq_true_eq, u32Max]
    rw [felt_ofNat_val_lt _ (by
      have : 2 ^ (shift.val &&& 31) ≤ 2 ^ 31 :=
        Nat.pow_le_pow_right (by omega)
          (Nat.and_le_right)
      unfold GOLDILOCKS_PRIME; omega)]
    have : 2 ^ (shift.val &&& 31) ≤ 2 ^ 31 :=
      Nat.pow_le_pow_right (by omega) Nat.and_le_right
    omega
  have h := u32_prod_div_isU32
    (Felt.ofNat (2 ^ (shift.val &&& 31))) lo
    h_pow_u32 hlo
  have h_pow_val :
    (Felt.ofNat (2 ^ (shift.val &&& 31))).val =
      2 ^ (shift.val &&& 31) := by
    apply felt_ofNat_val_lt
    have : 2 ^ (shift.val &&& 31) ≤ 2 ^ 31 :=
      Nat.pow_le_pow_right (by omega) Nat.and_le_right
    unfold GOLDILOCKS_PRIME; omega
  rwa [h_pow_val] at h

set_option maxHeartbeats 4000000 in
private theorem rotl_h2_ok (b : Bool)
    (hi pow carry lo_mod : Felt)
    (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
    (hhi : hi.isU32 = true)
    (hpow_u32 : pow.isU32 = true)
    (hcarry_u32 : carry.isU32 = true) :
    let cross := hi.val * pow.val + carry.val
    exec 30
      ⟨carry :: lo_mod :: pow :: hi ::
        (if b then (1 : Felt) else 0) :: rest,
       mem, locs, adv⟩ rotl_h2 =
    some ⟨
      (if b then
        Felt.ofNat (cross % 2 ^ 32) ::
        (Felt.ofNat (cross / 2 ^ 32) + lo_mod) :: rest
      else
        (Felt.ofNat (cross / 2 ^ 32) + lo_mod) ::
        Felt.ofNat (cross % 2 ^ 32) :: rest),
      mem, locs, adv⟩ := by
  dsimp only []
  unfold exec rotl_h2 execWithEnv
  simp only [List.foldlM]
  miden_movup; miden_movup
  rw [execInstruction_u32WidenMadd,
    execU32WidenMadd_concrete (ha := hhi)
      (hb := hpow_u32) (hc := hcarry_u32)]
  dsimp only [bind, Bind.bind, Option.bind]
  rw [show (4294967296 : Nat) = 2 ^ 32 from rfl]
  miden_swap; miden_movup
  rw [stepAdd]; miden_bind
  miden_swap; miden_movup
  rw [stepCswapIte]; miden_bind
  cases b
  · miden_swap; dsimp only [pure, Pure.pure]; simp
  · miden_swap; dsimp only [pure, Pure.pure]; simp

set_option maxHeartbeats 4000000 in
/-- u64.rotl correctly left-rotates a u64 value. -/
theorem u64_rotl_correct
    (lo hi shift : Felt) (rest : List Felt)
    (s : MidenState)
    (hs : s.stack = shift :: lo :: hi :: rest)
    (hshift_u32 : shift.isU32 = true)
    (hlo : lo.isU32 = true)
    (hhi : hi.isU32 = true) :
    let eff := shift.val &&& 31
    let pow := 2 ^ eff
    let lo_prod := pow * lo.val
    let cross := hi.val * pow + lo_prod / 2 ^ 32
    let result_lo := Felt.ofNat (cross % 2 ^ 32)
    let result_hi :=
      Felt.ofNat (cross / 2 ^ 32) +
        Felt.ofNat (lo_prod % 2 ^ 32)
    exec 30 s Miden.Core.U64.rotl =
    some (s.withStack (
      if decide (31 < shift.val) then
        result_lo :: result_hi :: rest
      else
        result_hi :: result_lo :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  rw [rotl_split, exec_append,
    rotl_h1_ok lo hi shift rest mem locs adv
      hshift_u32 hlo]
  simp only [bind, Bind.bind, Option.bind]
  rw [u32OverflowingSub_borrow_ite 31 shift.val]
  rw [rotl_h2_ok (decide (31 < shift.val))
    hi
    (Felt.ofNat (2 ^ (shift.val &&& 31)))
    (Felt.ofNat (2 ^ (shift.val &&& 31) * lo.val /
      2 ^ 32))
    (Felt.ofNat (2 ^ (shift.val &&& 31) * lo.val %
      2 ^ 32))
    rest mem locs adv
    hhi
    (by
      simp only [Felt.isU32, decide_eq_true_eq, u32Max]
      rw [felt_ofNat_val_lt _ (by
        have : 2 ^ (shift.val &&& 31) ≤ 2 ^ 31 :=
          Nat.pow_le_pow_right (by omega)
            Nat.and_le_right
        unfold GOLDILOCKS_PRIME; omega)]
      have : 2 ^ (shift.val &&& 31) ≤ 2 ^ 31 :=
        Nat.pow_le_pow_right (by omega)
          Nat.and_le_right
      omega)
    (rotl_carry_u32 lo shift hshift_u32 hlo)]
  congr 1
  have h_pow_val :
    (Felt.ofNat (2 ^ (shift.val &&& 31))).val =
      2 ^ (shift.val &&& 31) := by
    apply felt_ofNat_val_lt
    have : 2 ^ (shift.val &&& 31) ≤ 2 ^ 31 :=
      Nat.pow_le_pow_right (by omega) Nat.and_le_right
    unfold GOLDILOCKS_PRIME; omega
  have h_carry_val :
    (Felt.ofNat (2 ^ (shift.val &&& 31) * lo.val /
      2 ^ 32)).val =
    2 ^ (shift.val &&& 31) * lo.val / 2 ^ 32 := by
    apply felt_ofNat_val_lt
    have h_pow_u32 :
      (Felt.ofNat (2 ^ (shift.val &&& 31))).isU32 =
        true := by
      simp only [Felt.isU32, decide_eq_true_eq, u32Max]
      rw [h_pow_val]
      have : 2 ^ (shift.val &&& 31) ≤ 2 ^ 31 :=
        Nat.pow_le_pow_right (by omega) Nat.and_le_right
      omega
    have h := u32_prod_div_lt_prime
      (Felt.ofNat (2 ^ (shift.val &&& 31))) lo
      h_pow_u32 hlo
    rwa [h_pow_val] at h
  rw [h_pow_val, h_carry_val]

end MidenLean.Proofs
