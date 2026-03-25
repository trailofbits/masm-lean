import MidenLean.Proofs.U128.WrappingMul
import MidenLean.Proofs.Tactics
import MidenLean.Generated.U128

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

-- ============================================================================
-- Helper lemmas
-- ============================================================================

private theorem felt128_val : (128 : Felt).val = 128 :=
  felt_ofNat_val_lt 128 (by unfold GOLDILOCKS_PRIME; omega)

private theorem felt64_val : (64 : Felt).val = 64 :=
  felt_ofNat_val_lt 64 (by unfold GOLDILOCKS_PRIME; omega)

private theorem pow2_lt_prime (n : Nat) (h : n < 64) :
    2 ^ n < GOLDILOCKS_PRIME := by
  have h1 : 2 ^ n ≤ 2 ^ 63 := by
    apply Nat.pow_le_pow_right <;> omega
  have h2 : (2 : Nat) ^ 63 < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; norm_num
  omega

private theorem pow2_val (n : Nat) (h : n < 64) :
    (Felt.ofNat (2 ^ n)).val = 2 ^ n :=
  felt_ofNat_val_lt _ (pow2_lt_prime n h)

private theorem pow2_val_lt_2_64 (n : Nat) (h : n < 64) :
    (Felt.ofNat (2 ^ n)).val < 2 ^ 64 := by
  rw [pow2_val n h]; exact Nat.pow_lt_pow_right (by omega) h

private theorem u32OverflowingSub_snd_of_ge (a b : Nat) (h : a ≥ b) :
    (u32OverflowingSub a b).2 = a - b := by
  unfold u32OverflowingSub; simp [h]

private theorem sub64_val (shift : Felt)
    (hshift_u32 : shift.isU32 = true)
    (hge : ¬(shift.val < 64)) :
    (Felt.ofNat (u32OverflowingSub shift.val 64).2).val =
    shift.val - 64 := by
  rw [u32OverflowingSub_snd_of_ge _ _ (by omega)]
  apply felt_ofNat_val_lt
  simp [Felt.isU32, decide_eq_true_eq] at hshift_u32
  unfold GOLDILOCKS_PRIME; omega

private theorem sub64_le63 (shift : Felt)
    (hshift_u32 : shift.isU32 = true)
    (hge : ¬(shift.val < 64)) (hlt : shift.val < 128) :
    (Felt.ofNat (u32OverflowingSub shift.val 64).2).val ≤ 63 := by
  rw [sub64_val shift hshift_u32 hge]; omega

private theorem sub64_lt64 (shift : Felt)
    (hshift_u32 : shift.isU32 = true)
    (hge : ¬(shift.val < 64)) (hlt : shift.val < 128) :
    (Felt.ofNat (u32OverflowingSub shift.val 64).2).val < 64 := by
  rw [sub64_val shift hshift_u32 hge]; omega

-- ============================================================================
-- Chunk definitions
-- ============================================================================

/-- Validation and condition: dup, push 128, u32Lt, assert, dup, push 64, u32Lt -/
private def shl_prefix : List Op := [
  .inst (.dup 0), .inst (.push 128), .inst (.u32Lt),
  .inst (.assertWithError "shift amount must be in the range [0, 128)"),
  .inst (.dup 0), .inst (.push 64), .inst (.u32Lt)]

/-- True branch setup (shift < 64): pow2, u32Split, push 0, push 0, movup 3, movup 3 -/
private def shl_true_setup : List Op := [
  .inst (.pow2), .inst (.u32Split),
  .inst (.push 0), .inst (.push 0),
  .inst (.movup 3), .inst (.movup 3)]

/-- False branch setup (shift >= 64): push 64, u32WrappingSub, pow2, u32Split, push 0, push 0 -/
private def shl_false_setup : List Op := [
  .inst (.push 64), .inst (.u32WrappingSub),
  .inst (.pow2), .inst (.u32Split),
  .inst (.push 0), .inst (.push 0)]

private def shl_true_branch : List Op :=
  shl_true_setup ++ [.inst (.exec "wrapping_mul")]

private def shl_false_branch : List Op :=
  shl_false_setup ++ [.inst (.exec "wrapping_mul")]

-- ============================================================================
-- Decomposition
-- ============================================================================

private theorem shl_decomp :
    Miden.Core.U128.shl = shl_prefix ++ [.ifElse shl_true_branch shl_false_branch] := by
  simp [Miden.Core.U128.shl, shl_prefix, shl_true_branch, shl_true_setup,
        shl_false_branch, shl_false_setup]

-- ============================================================================
-- Prefix correctness
-- ============================================================================

set_option maxHeartbeats 4000000 in
private theorem shl_prefix_correct (env : ProcEnv) (fuel : Nat)
    (shift a0 a1 a2 a3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
    (hshift_u32 : shift.isU32 = true)
    (hshift_lt128 : shift.val < 128) :
    execWithEnv env (fuel + 1)
      ⟨shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv⟩
      shl_prefix =
    some ⟨(if shift.val < 64 then (1 : Felt) else 0) ::
          shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv⟩ := by
  unfold shl_prefix execWithEnv
  simp only [List.foldlM]
  dsimp only [bind, Bind.bind, Option.bind]
  miden_dup
  miden_step -- push 128
  rw [stepU32Lt (ha := hshift_u32) (hb := U32.felt128_isU32)]
  miden_bind
  simp only [felt128_val]
  rw [stepAssertWithError (h := by simp [hshift_lt128, Felt.val_one'])]
  miden_bind
  miden_dup
  miden_step -- push 64
  rw [stepU32Lt (ha := hshift_u32) (hb := U32.felt64_isU32)]
  miden_bind
  simp only [felt64_val]
  simp [pure, Pure.pure]

-- ============================================================================
-- True branch setup correctness (shift < 64)
-- ============================================================================

set_option maxHeartbeats 4000000 in
private theorem shl_true_setup_correct (env : ProcEnv) (fuel : Nat)
    (shift a0 a1 a2 a3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
    (hshift_lt64 : shift.val < 64) :
    let p := Felt.ofNat (2 ^ shift.val)
    execWithEnv env (fuel + 1)
      ⟨shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv⟩
      shl_true_setup =
    some ⟨p.lo32 :: p.hi32 :: 0 :: 0 :: a0 :: a1 :: a2 :: a3 :: rest,
          mem, locs, adv⟩ := by
  unfold shl_true_setup execWithEnv
  simp only [List.foldlM]
  dsimp only [bind, Bind.bind, Option.bind]
  rw [stepPow2 (ha := by omega)]
  miden_bind
  rw [stepU32Split]
  miden_bind
  miden_step  -- push 0
  miden_step  -- push 0
  miden_movup  -- movup 3
  miden_movup  -- movup 3
  simp [pure, Pure.pure]

-- ============================================================================
-- False branch setup correctness (shift >= 64)
-- ============================================================================

set_option maxHeartbeats 4000000 in
private theorem shl_false_setup_correct (env : ProcEnv) (fuel : Nat)
    (shift a0 a1 a2 a3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
    (hshift_u32 : shift.isU32 = true)
    (hshift_ge64 : ¬(shift.val < 64))
    (hshift_lt128 : shift.val < 128) :
    let s64 := Felt.ofNat (u32OverflowingSub shift.val 64).2
    let q := Felt.ofNat (2 ^ s64.val)
    execWithEnv env (fuel + 1)
      ⟨shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv⟩
      shl_false_setup =
    some ⟨0 :: 0 :: q.lo32 :: q.hi32 :: a0 :: a1 :: a2 :: a3 :: rest,
          mem, locs, adv⟩ := by
  unfold shl_false_setup execWithEnv
  simp only [List.foldlM]
  dsimp only [bind, Bind.bind, Option.bind]
  miden_step  -- push 64
  rw [stepU32WrappingSubLocal (ha := hshift_u32) (hb := U32.felt64_isU32)]
  miden_bind
  simp only [felt64_val]
  rw [stepPow2 (ha := sub64_le63 shift hshift_u32 hshift_ge64 hshift_lt128)]
  miden_bind
  rw [stepU32Split]
  miden_bind
  miden_step  -- push 0
  miden_step  -- push 0
  simp [pure, Pure.pure]

-- ============================================================================
-- True branch full correctness
-- ============================================================================

set_option maxHeartbeats 8000000 in
private theorem shl_true_branch_correct (fuel : Nat)
    (shift a0 a1 a2 a3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
    (hshift_lt64 : shift.val < 64)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (ha2 : a2.isU32 = true) (ha3 : a3.isU32 = true) :
    let p := Felt.ofNat (2 ^ shift.val)
    execWithEnv u128ProcEnv (fuel + 2)
      ⟨shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv⟩
      shl_true_branch =
    some ⟨u128MulC0 a0 p.lo32 ::
          u128MulC1 a0 a1 p.lo32 p.hi32 ::
          u128MulC2 a0 a1 a2 p.lo32 p.hi32 0 ::
          u128MulC3 a0 a1 a2 a3 p.lo32 p.hi32 0 0 ::
          rest, mem, locs, adv⟩ := by
  show execWithEnv u128ProcEnv (fuel + 2) _ (shl_true_setup ++ [.inst (.exec "wrapping_mul")]) = _
  rw [execWithEnv_append]
  rw [shl_true_setup_correct u128ProcEnv (fuel + 1) shift a0 a1 a2 a3 rest mem locs adv hshift_lt64]
  simp only [bind, Bind.bind, Option.bind]
  -- Now execute [.inst (.exec "wrapping_mul")]
  unfold execWithEnv
  simp only [List.foldlM, u128ProcEnv, bind, Bind.bind, Option.bind, pure, Pure.pure]
  rw [u128_wrapping_mul_run u128ProcEnv fuel a0 a1 a2 a3
    (Felt.ofNat (2 ^ shift.val)).lo32
    (Felt.ofNat (2 ^ shift.val)).hi32
    0 0
    rest mem locs adv ha0 ha1 ha2 ha3
    (U32.lo32_isU32 _)
    (U32.hi32_isU32_of_val_lt_2_64 _ (pow2_val_lt_2_64 shift.val hshift_lt64))
    (by apply felt_ofNat_isU32_of_lt; norm_num)
    (by apply felt_ofNat_isU32_of_lt; norm_num)]

-- ============================================================================
-- False branch full correctness
-- ============================================================================

set_option maxHeartbeats 8000000 in
private theorem shl_false_branch_correct (fuel : Nat)
    (shift a0 a1 a2 a3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
    (hshift_u32 : shift.isU32 = true)
    (hshift_ge64 : ¬(shift.val < 64))
    (hshift_lt128 : shift.val < 128)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (ha2 : a2.isU32 = true) (ha3 : a3.isU32 = true) :
    let s64 := Felt.ofNat (u32OverflowingSub shift.val 64).2
    let q := Felt.ofNat (2 ^ s64.val)
    execWithEnv u128ProcEnv (fuel + 2)
      ⟨shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv⟩
      shl_false_branch =
    some ⟨u128MulC0 a0 0 ::
          u128MulC1 a0 a1 0 0 ::
          u128MulC2 a0 a1 a2 0 0 q.lo32 ::
          u128MulC3 a0 a1 a2 a3 0 0 q.lo32 q.hi32 ::
          rest, mem, locs, adv⟩ := by
  show execWithEnv u128ProcEnv (fuel + 2) _ (shl_false_setup ++ [.inst (.exec "wrapping_mul")]) = _
  rw [execWithEnv_append]
  rw [shl_false_setup_correct u128ProcEnv (fuel + 1) shift a0 a1 a2 a3 rest mem locs adv
    hshift_u32 hshift_ge64 hshift_lt128]
  simp only [bind, Bind.bind, Option.bind]
  -- Now execute [.inst (.exec "wrapping_mul")]
  unfold execWithEnv
  simp only [List.foldlM, u128ProcEnv, bind, Bind.bind, Option.bind, pure, Pure.pure]
  rw [u128_wrapping_mul_run u128ProcEnv fuel a0 a1 a2 a3
    0 0
    (Felt.ofNat (2 ^ (Felt.ofNat (u32OverflowingSub shift.val 64).2).val)).lo32
    (Felt.ofNat (2 ^ (Felt.ofNat (u32OverflowingSub shift.val 64).2).val)).hi32
    rest mem locs adv ha0 ha1 ha2 ha3
    (by apply felt_ofNat_isU32_of_lt; norm_num)
    (by apply felt_ofNat_isU32_of_lt; norm_num)
    (U32.lo32_isU32 _)
    (U32.hi32_isU32_of_val_lt_2_64 _
      (pow2_val_lt_2_64 _ (sub64_lt64 shift hshift_u32 hshift_ge64 hshift_lt128)))]

-- ============================================================================
-- ifElse dispatch helpers
-- ============================================================================

private theorem execWithEnv_ifElse_one
    (env : ProcEnv) (fuel : Nat)
    (rest : List Felt) (mem locs : Nat → Felt) (adv : List Felt)
    (thenBlk elseBlk : List Op) :
    execWithEnv env (fuel + 2)
      ⟨(1 : Felt) :: rest, mem, locs, adv⟩
      [.ifElse thenBlk elseBlk] =
    execWithEnv env (fuel + 1) ⟨rest, mem, locs, adv⟩ thenBlk := by
  conv_lhs => unfold execWithEnv
  simp only [List.foldlM, MidenState.withStack]
  dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
  have hv1 : (1 : Felt).val = 1 := Felt.val_one'
  have hbeq : ((1 : Nat) == 1) = true := by decide
  simp only [hv1, hbeq, ↓reduceIte]
  cases execWithEnv env (fuel + 1) ⟨rest, mem, locs, adv⟩ thenBlk <;> rfl

private theorem execWithEnv_ifElse_zero
    (env : ProcEnv) (fuel : Nat)
    (rest : List Felt) (mem locs : Nat → Felt) (adv : List Felt)
    (thenBlk elseBlk : List Op) :
    execWithEnv env (fuel + 2)
      ⟨(0 : Felt) :: rest, mem, locs, adv⟩
      [.ifElse thenBlk elseBlk] =
    execWithEnv env (fuel + 1) ⟨rest, mem, locs, adv⟩ elseBlk := by
  conv_lhs => unfold execWithEnv
  simp only [List.foldlM, MidenState.withStack]
  dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
  have hv0 : (0 : Felt).val = 0 := Felt.val_zero'
  have hneq : ((0 : Nat) == 1) = false := by decide
  have hbeq : ((0 : Nat) == 0) = true := by decide
  simp only [hv0, hneq, hbeq, ↓reduceIte]
  cases execWithEnv env (fuel + 1) ⟨rest, mem, locs, adv⟩ elseBlk <;> rfl

-- ============================================================================
-- Composition: u128_shl_run
-- ============================================================================

set_option maxHeartbeats 8000000 in
theorem u128_shl_run
    (fuel : Nat)
    (shift a0 a1 a2 a3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
    (hshift_u32 : shift.isU32 = true)
    (hshift_lt128 : shift.val < 128)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (ha2 : a2.isU32 = true) (ha3 : a3.isU32 = true) :
    execWithEnv u128ProcEnv (fuel + 3)
      ⟨shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv⟩
      Miden.Core.U128.shl =
    (if shift.val < 64 then
      let p := Felt.ofNat (2 ^ shift.val)
      some ⟨u128MulC0 a0 p.lo32 ::
            u128MulC1 a0 a1 p.lo32 p.hi32 ::
            u128MulC2 a0 a1 a2 p.lo32 p.hi32 0 ::
            u128MulC3 a0 a1 a2 a3 p.lo32 p.hi32 0 0 ::
            rest, mem, locs, adv⟩
    else
      let s64 := Felt.ofNat (u32OverflowingSub shift.val 64).2
      let q := Felt.ofNat (2 ^ s64.val)
      some ⟨u128MulC0 a0 0 ::
            u128MulC1 a0 a1 0 0 ::
            u128MulC2 a0 a1 a2 0 0 q.lo32 ::
            u128MulC3 a0 a1 a2 a3 0 0 q.lo32 q.hi32 ::
            rest, mem, locs, adv⟩) := by
  rw [shl_decomp, execWithEnv_append]
  rw [shl_prefix_correct u128ProcEnv (fuel + 2) shift a0 a1 a2 a3 rest mem locs adv
    hshift_u32 hshift_lt128]
  simp only [bind, Bind.bind, Option.bind]
  -- Case split on shift < 64
  by_cases hlt : shift.val < 64
  · -- shift < 64: condition is 1, take true branch
    simp only [hlt, ↓reduceIte]
    rw [execWithEnv_ifElse_one]
    exact shl_true_branch_correct fuel shift a0 a1 a2 a3 rest mem locs adv
      hlt ha0 ha1 ha2 ha3
  · -- shift >= 64: condition is 0, take false branch
    simp only [hlt, ↓reduceIte]
    rw [execWithEnv_ifElse_zero]
    exact shl_false_branch_correct fuel shift a0 a1 a2 a3 rest mem locs adv
      hshift_u32 hlt hshift_lt128 ha0 ha1 ha2 ha3

-- ============================================================================
-- Main correctness theorem
-- ============================================================================

set_option maxHeartbeats 8000000 in
/-- `u128::shl` correctly computes the left shift of a 128-bit value by a given amount.
    Input stack:  [shift, a0, a1, a2, a3] ++ rest  (shift < 128, a0..a3 are u32 limbs)
    Output stack: [r0, r1, r2, r3] ++ rest
    where `r0..r3` are the u32 limbs of `(a << shift) mod 2^128`, computed via
    multiplication by `2^shift` using `wrapping_mul`. -/
theorem u128_shl_correct
    (shift a0 a1 a2 a3 : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = shift :: a0 :: a1 :: a2 :: a3 :: rest)
    (hshift_u32 : shift.isU32 = true)
    (hshift_lt128 : shift.val < 128)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (ha2 : a2.isU32 = true) (ha3 : a3.isU32 = true) :
    execWithEnv u128ProcEnv 70 s Miden.Core.U128.shl =
    (if shift.val < 64 then
      let p := Felt.ofNat (2 ^ shift.val)
      some (s.withStack (
        u128MulC0 a0 p.lo32 ::
        u128MulC1 a0 a1 p.lo32 p.hi32 ::
        u128MulC2 a0 a1 a2 p.lo32 p.hi32 0 ::
        u128MulC3 a0 a1 a2 a3 p.lo32 p.hi32 0 0 ::
        rest))
    else
      let s64 := Felt.ofNat (u32OverflowingSub shift.val 64).2
      let q := Felt.ofNat (2 ^ s64.val)
      some (s.withStack (
        u128MulC0 a0 0 ::
        u128MulC1 a0 a1 0 0 ::
        u128MulC2 a0 a1 a2 0 0 q.lo32 ::
        u128MulC3 a0 a1 a2 a3 0 0 q.lo32 q.hi32 ::
        rest))) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  have h := u128_shl_run 67 shift a0 a1 a2 a3 rest mem locs adv
    hshift_u32 hshift_lt128 ha0 ha1 ha2 ha3
  simpa using h

end MidenLean.Proofs
