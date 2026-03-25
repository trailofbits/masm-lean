import MidenLean.Proofs.U128.Common
import MidenLean.Proofs.Tactics
import MidenLean.Generated.U128

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

-- ============================================================================
-- Helper lemmas
-- ============================================================================

private theorem felt32_val : (32 : Felt).val = 32 :=
  felt_ofNat_val_lt 32 (by unfold GOLDILOCKS_PRIME; omega)

private theorem shift_sub32_val
    (shift : Felt) (hshift : shift.val ≤ 31) :
    (Felt.ofNat (u32OverflowingSub 32 shift.val).2).val = 32 - shift.val := by
  unfold u32OverflowingSub
  simp [show shift.val ≤ 32 by omega]
  rw [felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)]

private theorem pow32_sub_val
    (shift : Felt) (hshift_pos : 0 < shift.val) (hshift : shift.val ≤ 31) :
    (Felt.ofNat (2 ^ (32 - shift.val))).val = 2 ^ (32 - shift.val) := by
  apply felt_ofNat_val_lt
  have hpow_le : 2 ^ (32 - shift.val) ≤ 2 ^ 31 := by
    apply Nat.pow_le_pow_right
    omega
    omega
  unfold GOLDILOCKS_PRIME
  omega

private theorem pow32_sub_isU32
    (shift : Felt) (hshift_pos : 0 < shift.val) (hshift : shift.val ≤ 31) :
    (Felt.ofNat (2 ^ (32 - shift.val))).isU32 = true := by
  apply felt_ofNat_isU32_of_lt
  have hpow_le : 2 ^ (32 - shift.val) ≤ 2 ^ 31 := by
    apply Nat.pow_le_pow_right
    omega
    omega
  omega

-- ============================================================================
-- Chunk definitions for the nonzero (else) branch
-- ============================================================================

/-- Setup: push 32, compute 32−shift, pow2. -/
private def shr_k1_setup : List Op := [
  .inst (.push 32), .inst (.dup 1), .inst (.u32WrappingSub), .inst (.pow2)]

/-- Compute block 1: shift a3 and a2, widen-multiply a3 by pow, OR with shifted a2. -/
private def shr_k1_compute1 : List Op := [
  .inst (.dup 5), .inst (.dup 2), .inst (.u32Shr),
  .inst (.dup 5), .inst (.dup 3), .inst (.u32Shr),
  .inst (.dup 7), .inst (.dup 3), .inst (.u32WidenMul),
  .inst (.swap 1), .inst (.drop), .inst (.u32Or)]

/-- Compute block 2: shift a1, widen-multiply a2 by pow, OR with shifted a1. -/
private def shr_k1_compute2 : List Op := [
  .inst (.dup 5), .inst (.dup 4), .inst (.u32Shr),
  .inst (.dup 7), .inst (.dup 4), .inst (.u32WidenMul),
  .inst (.swap 1), .inst (.drop), .inst (.u32Or)]

/-- Cleanup: move results down, drop temporaries. -/
private def shr_k1_cleanup : List Op := [
  .inst (.movdn 8), .inst (.movdn 8), .inst (.movdn 8),
  .inst (.drop), .inst (.drop), .inst (.drop),
  .inst (.drop), .inst (.drop), .inst (.drop)]

-- ============================================================================
-- Chunk correctness lemmas
-- ============================================================================

set_option maxHeartbeats 1600000 in
private theorem shr_k1_setup_correct
    (shift a0 a1 a2 a3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
    (hshift_u32 : shift.isU32 = true)
    (hshift : shift.val ≤ 31) (hshift_pos : 0 < shift.val) :
    exec 42 ⟨shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv⟩ shr_k1_setup =
    some ⟨Felt.ofNat (2 ^ (32 - shift.val)) :: shift :: a0 :: a1 :: a2 :: a3 :: rest,
      mem, locs, adv⟩ := by
  unfold exec shr_k1_setup execWithEnv
  simp only [List.foldlM]
  rw [stepPush]
  miden_bind
  miden_dup
  rw [stepU32WrappingSubLocal (ha := U32.felt32_isU32) (hb := hshift_u32)]
  miden_bind
  simp only [felt32_val]
  have hpow_input_le63 : (Felt.ofNat (u32OverflowingSub 32 shift.val).2).val ≤ 63 := by
    rw [shift_sub32_val shift hshift]; omega
  rw [stepPow2 (ha := hpow_input_le63)]
  miden_bind
  have hpow_eq :
      Felt.ofNat (2 ^ (Felt.ofNat (u32OverflowingSub 32 shift.val).2).val) =
        Felt.ofNat (2 ^ (32 - shift.val)) := by
    congr 1; congr 1; exact shift_sub32_val shift hshift
  rw [hpow_eq]; rfl

set_option maxHeartbeats 2000000 in
private theorem shr_k1_compute1_correct
    (shift a0 a1 a2 a3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
    (hshift_u32 : shift.isU32 = true)
    (ha2_u32 : a2.isU32 = true) (ha3_u32 : a3.isU32 = true)
    (hshift : shift.val ≤ 31) (hshift_pos : 0 < shift.val) :
    let pow := Felt.ofNat (2 ^ (32 - shift.val))
    exec 42
      ⟨pow :: shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv⟩
      shr_k1_compute1 =
    some ⟨Felt.ofNat ((a2.val / 2 ^ shift.val) ||| ((a3.val * 2 ^ (32 - shift.val)) % 2 ^ 32)) ::
      Felt.ofNat (a3.val / 2 ^ shift.val) ::
      pow :: shift :: a0 :: a1 :: a2 :: a3 :: rest,
      mem, locs, adv⟩ := by
  unfold exec shr_k1_compute1 execWithEnv
  simp only [List.foldlM]
  have hpow_u32 : (Felt.ofNat (2 ^ (32 - shift.val))).isU32 = true :=
    pow32_sub_isU32 shift hshift_pos hshift
  have hpow_val : (Felt.ofNat (2 ^ (32 - shift.val))).val = 2 ^ (32 - shift.val) :=
    pow32_sub_val shift hshift_pos hshift
  have ha3_shr_u32 : (Felt.ofNat (a3.val / 2 ^ shift.val)).isU32 = true :=
    U32.u32Shr_result_isU32 a3 shift ha3_u32
  have ha2_shr_u32 : (Felt.ofNat (a2.val / 2 ^ shift.val)).isU32 = true :=
    U32.u32Shr_result_isU32 a2 shift ha2_u32
  miden_dup
  miden_dup
  rw [stepU32ShrLocal (ha := ha3_u32) (hb := hshift_u32) (hshift := hshift)]
  miden_bind
  miden_dup
  miden_dup
  rw [stepU32ShrLocal (ha := ha2_u32) (hb := hshift_u32) (hshift := hshift)]
  miden_bind
  miden_dup
  miden_dup
  rw [stepU32WidenMul
    (a := a3) (b := Felt.ofNat (2 ^ (32 - shift.val)))
    (ha := ha3_u32) (hb := hpow_u32)]
  miden_bind
  rw [hpow_val]
  miden_swap
  rw [stepDrop]
  miden_bind
  rw [stepU32Or (ha := ha2_shr_u32) (hb := u32_mod_isU32 _)]
  miden_bind
  rw [felt_ofNat_val_lt _ (lt_of_le_of_lt (Nat.div_le_self _ _) (felt_val_lt_prime a2))]
  rw [felt_ofNat_val_lt _ (u32_mod_lt_prime _)]
  dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]

set_option maxHeartbeats 2000000 in
private theorem shr_k1_compute2_correct
    (shift a0 a1 a2 a3 : Felt) (rest : List Felt)
    (r0 r1 : Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
    (hshift_u32 : shift.isU32 = true)
    (ha1_u32 : a1.isU32 = true) (ha2_u32 : a2.isU32 = true)
    (hshift : shift.val ≤ 31) (hshift_pos : 0 < shift.val) :
    let pow := Felt.ofNat (2 ^ (32 - shift.val))
    exec 42
      ⟨r0 :: r1 :: pow :: shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv⟩
      shr_k1_compute2 =
    some ⟨Felt.ofNat ((a1.val / 2 ^ shift.val) ||| ((a2.val * 2 ^ (32 - shift.val)) % 2 ^ 32)) ::
      r0 :: r1 :: pow :: shift :: a0 :: a1 :: a2 :: a3 :: rest,
      mem, locs, adv⟩ := by
  unfold exec shr_k1_compute2 execWithEnv
  simp only [List.foldlM]
  have hpow_u32 : (Felt.ofNat (2 ^ (32 - shift.val))).isU32 = true :=
    pow32_sub_isU32 shift hshift_pos hshift
  have hpow_val : (Felt.ofNat (2 ^ (32 - shift.val))).val = 2 ^ (32 - shift.val) :=
    pow32_sub_val shift hshift_pos hshift
  have ha1_shr_u32 : (Felt.ofNat (a1.val / 2 ^ shift.val)).isU32 = true :=
    U32.u32Shr_result_isU32 a1 shift ha1_u32
  miden_dup
  miden_dup
  rw [stepU32ShrLocal (ha := ha1_u32) (hb := hshift_u32) (hshift := hshift)]
  miden_bind
  miden_dup
  miden_dup
  rw [stepU32WidenMul
    (a := a2) (b := Felt.ofNat (2 ^ (32 - shift.val)))
    (ha := ha2_u32) (hb := hpow_u32)]
  miden_bind
  rw [hpow_val]
  miden_swap
  rw [stepDrop]
  miden_bind
  rw [stepU32Or (ha := ha1_shr_u32) (hb := u32_mod_isU32 _)]
  miden_bind
  rw [felt_ofNat_val_lt _ (lt_of_le_of_lt (Nat.div_le_self _ _) (felt_val_lt_prime a1))]
  rw [felt_ofNat_val_lt _ (u32_mod_lt_prime _)]
  dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]

set_option maxHeartbeats 2000000 in
private theorem shr_k1_cleanup_correct
    (a b c pow shift x0 x1 x2 x3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt) :
    exec 42 ⟨a :: b :: c :: pow :: shift :: x0 :: x1 :: x2 :: x3 :: rest, mem, locs, adv⟩
      shr_k1_cleanup =
    some ⟨a :: b :: c :: rest, mem, locs, adv⟩ := by
  unfold exec shr_k1_cleanup execWithEnv
  simp only [List.foldlM]
  miden_movdn
  miden_movdn
  miden_movdn
  rw [stepDrop]
  miden_bind
  rw [stepDrop]
  miden_bind
  rw [stepDrop]
  miden_bind
  rw [stepDrop]
  miden_bind
  rw [stepDrop]
  miden_bind
  rw [stepDrop]
  dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]

-- ============================================================================
-- Nonzero path: compose chunks via exec_append
-- ============================================================================

set_option maxHeartbeats 2000000 in
private theorem shr_k1_nonzero
    (shift a0 a1 a2 a3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
    (hshift_u32 : shift.isU32 = true)
    (ha1_u32 : a1.isU32 = true) (ha2_u32 : a2.isU32 = true) (ha3_u32 : a3.isU32 = true)
    (hshift : shift.val ≤ 31) (hshift_pos : 0 < shift.val) :
    exec 42 ⟨shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv⟩
      (shr_k1_setup ++ (shr_k1_compute1 ++ (shr_k1_compute2 ++ shr_k1_cleanup))) =
    some ⟨Felt.ofNat ((a1.val / 2 ^ shift.val) ||| ((a2.val * 2 ^ (32 - shift.val)) % 2 ^ 32)) ::
      Felt.ofNat ((a2.val / 2 ^ shift.val) ||| ((a3.val * 2 ^ (32 - shift.val)) % 2 ^ 32)) ::
      Felt.ofNat (a3.val / 2 ^ shift.val) :: rest, mem, locs, adv⟩ := by
  rw [exec_append]
  rw [shr_k1_setup_correct shift a0 a1 a2 a3 rest mem locs adv hshift_u32 hshift hshift_pos]
  simp only [bind, Bind.bind, Option.bind]
  rw [exec_append]
  rw [shr_k1_compute1_correct shift a0 a1 a2 a3 rest mem locs adv hshift_u32 ha2_u32 ha3_u32
    hshift hshift_pos]
  simp only [bind, Bind.bind, Option.bind]
  rw [exec_append]
  rw [shr_k1_compute2_correct shift a0 a1 a2 a3 rest
    (Felt.ofNat ((a2.val / 2 ^ shift.val) ||| ((a3.val * 2 ^ (32 - shift.val)) % 2 ^ 32)))
    (Felt.ofNat (a3.val / 2 ^ shift.val))
    mem locs adv hshift_u32 ha1_u32 ha2_u32 hshift hshift_pos]
  simp only [bind, Bind.bind, Option.bind]
  exact shr_k1_cleanup_correct
    (Felt.ofNat ((a1.val / 2 ^ shift.val) ||| ((a2.val * 2 ^ (32 - shift.val)) % 2 ^ 32)))
    (Felt.ofNat ((a2.val / 2 ^ shift.val) ||| ((a3.val * 2 ^ (32 - shift.val)) % 2 ^ 32)))
    (Felt.ofNat (a3.val / 2 ^ shift.val))
    (Felt.ofNat (2 ^ (32 - shift.val))) shift a0 a1 a2 a3 rest mem locs adv

-- ============================================================================
-- Main theorem
-- ============================================================================

set_option maxHeartbeats 4000000 in
/-- `u128::shr_k1` right-shifts a 128-bit value by one whole limb plus an
    additional bit count smaller than one limb.
    Input stack:  [shift, a0, a1, a2, a3] ++ rest
    Output stack: [r0, r1, r2] ++ rest
    where `r0..r2` are the low-to-high u32 limbs of `(a3:a2:a1:a0) >> (32 + shift)`. -/
theorem u128_shr_k1_correct
    (shift a0 a1 a2 a3 : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = shift :: a0 :: a1 :: a2 :: a3 :: rest)
    (hshift_u32 : shift.isU32 = true)
    (ha1_u32 : a1.isU32 = true) (ha2_u32 : a2.isU32 = true)
    (ha3_u32 : a3.isU32 = true)
    (hshift : shift.val ≤ 31) :
    let pow := 2 ^ (32 - shift.val)
    exec 43 s Miden.Core.U128.shr_k1 =
    some (s.withStack (
      if shift == (0 : Felt) then
        a1 :: a2 :: a3 :: rest
      else
        Felt.ofNat ((a1.val / 2 ^ shift.val) ||| ((a2.val * pow) % 4294967296)) ::
        Felt.ofNat ((a2.val / 2 ^ shift.val) ||| ((a3.val * pow) % 4294967296)) ::
        Felt.ofNat (a3.val / 2 ^ shift.val) :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.U128.shr_k1 execWithEnv
  simp only [List.foldlM]
  miden_dup
  rw [stepEqImm]
  miden_bind
  by_cases hzero : shift == (0 : Felt)
  · simp [hzero, MidenState.withStack]
    unfold execWithEnv
    simp only [List.foldlM]
    rw [stepDrop]
    miden_bind
    rw [stepDrop]
  · simp [hzero, MidenState.withStack]
    have hshift_ne_zero : shift.val ≠ 0 := by
      intro hval
      apply hzero
      apply beq_iff_eq.mpr
      exact (ZMod.val_eq_zero shift).mp hval
    have hshift_pos : 0 < shift.val := by omega
    have h := shr_k1_nonzero shift a0 a1 a2 a3 rest mem locs adv
      hshift_u32 ha1_u32 ha2_u32 ha3_u32 hshift hshift_pos
    simp only [exec, shr_k1_setup, shr_k1_compute1, shr_k1_compute2, shr_k1_cleanup,
      List.nil_append, List.cons_append] at h
    rw [h]; rfl

end MidenLean.Proofs
