import MidenLean.Proofs.U128.Shl
import MidenLean.Proofs.U128.Shr
import MidenLean.Proofs.Tactics
import MidenLean.Generated.U128

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

-- ============================================================================
-- Helper lemmas
-- ============================================================================

private theorem felt128_val' : (128 : Felt).val = 128 :=
  felt_ofNat_val_lt 128 (by unfold GOLDILOCKS_PRIME; omega)

private theorem complement_val (shift : Felt) (hshift_lt128 : shift.val < 128)
    (hshift_pos : 0 < shift.val) :
    (Felt.ofNat (u32OverflowingSub 128 shift.val).2).val = 128 - shift.val := by
  unfold u32OverflowingSub
  simp [show shift.val ≤ 128 by omega]
  rw [felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)]

private theorem complement_isU32 (shift : Felt) (hshift_lt128 : shift.val < 128)
    (hshift_pos : 0 < shift.val) :
    (Felt.ofNat (u32OverflowingSub 128 shift.val).2).isU32 = true := by
  apply felt_ofNat_isU32_of_lt
  unfold u32OverflowingSub
  simp [show shift.val ≤ 128 by omega]
  omega

private theorem complement_lt128 (shift : Felt) (hshift_lt128 : shift.val < 128)
    (hshift_pos : 0 < shift.val) :
    (Felt.ofNat (u32OverflowingSub 128 shift.val).2).val < 128 := by
  rw [complement_val shift hshift_lt128 hshift_pos]; omega

-- ============================================================================
-- isU32 for shl output limbs (u128MulC values)
-- ============================================================================

private theorem u128MulC0_isU32 (a0 b0 : Felt) : (u128MulC0 a0 b0).isU32 = true := by
  unfold u128MulC0; exact felt_ofNat_isU32_of_lt _ (Nat.mod_lt _ (by omega))

private theorem u128MulC1_isU32 (a0 a1 b0 b1 : Felt) :
    (u128MulC1 a0 a1 b0 b1).isU32 = true := by
  unfold u128MulC1; exact felt_ofNat_isU32_of_lt _ (Nat.mod_lt _ (by omega))

private theorem u128MulC2_isU32 (a0 a1 a2 b0 b1 b2 : Felt) :
    (u128MulC2 a0 a1 a2 b0 b1 b2).isU32 = true := by
  unfold u128MulC2; exact felt_ofNat_isU32_of_lt _ (Nat.mod_lt _ (by omega))

private theorem u128MulC3_isU32 (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) :
    (u128MulC3 a0 a1 a2 a3 b0 b1 b2 b3).isU32 = true := by
  unfold u128MulC3; exact felt_ofNat_isU32_of_lt _ (Nat.mod_lt _ (by omega))

-- ============================================================================
-- isU32 for shr output limbs
-- ============================================================================

private theorem shr_div_isU32 (a : Felt) (b : Nat) (ha : a.isU32 = true) :
    (Felt.ofNat (a.val / 2 ^ b)).isU32 = true := by
  apply felt_ofNat_isU32_of_lt
  exact lt_of_le_of_lt (Nat.div_le_self _ _)
    (by simpa [Felt.isU32, decide_eq_true_eq] using ha)

private theorem shr_or_mod_isU32 (x y : Nat) (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    (Felt.ofNat (x ||| y)).isU32 = true := by
  apply felt_ofNat_isU32_of_lt
  exact Nat.or_lt_two_pow hx hy

-- ============================================================================
-- Chunk definitions
-- ============================================================================

private def rotl_prefix : List Op := [.inst (.dup 0), .inst (.eqImm 0)]

/-- Duplicate shift and a0..a3, then move shift to top for shl call. -/
private def rotl_dup_setup : List Op := [
  .inst (.dup 0), .inst (.dup 5), .inst (.dup 5),
  .inst (.dup 5), .inst (.dup 5), .inst (.movup 4)]

/-- Move shl results below original args, compute 128-shift for shr call. -/
private def rotl_mid_setup : List Op := [
  .inst (.movdn 8), .inst (.movdn 8), .inst (.movdn 8), .inst (.movdn 8),
  .inst (.push 128), .inst (.swap 1), .inst (.u32WrappingSub)]

/-- Combine shr and shl limbs with elementwise u32Or. -/
private def rotl_combine : List Op := [
  .inst (.movup 4), .inst (.u32Or),
  .inst (.swap 1), .inst (.movup 4), .inst (.u32Or),
  .inst (.swap 1), .inst (.movup 2), .inst (.movup 4), .inst (.u32Or),
  .inst (.movdn 2), .inst (.movup 3), .inst (.movup 4), .inst (.u32Or),
  .inst (.movdn 3)]

private def rotl_nonzero : List Op :=
  rotl_dup_setup ++ [.inst (.exec "shl")] ++
  rotl_mid_setup ++ [.inst (.exec "shr")] ++
  rotl_combine

-- ============================================================================
-- Decomposition
-- ============================================================================

private theorem rotl_decomp :
    Miden.Core.U128.rotl =
    rotl_prefix ++ [.ifElse [.inst (.drop)] rotl_nonzero] := by
  simp [Miden.Core.U128.rotl, rotl_prefix, rotl_nonzero,
        rotl_dup_setup, rotl_mid_setup, rotl_combine]

-- ============================================================================
-- Prefix correctness
-- ============================================================================

private theorem rotl_prefix_correct (env : ProcEnv) (fuel : Nat)
    (shift a0 a1 a2 a3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt) :
    execWithEnv env (fuel + 1)
      ⟨shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv⟩
      rotl_prefix =
    some ⟨(if shift == (0 : Felt) then (1 : Felt) else 0) ::
          shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv⟩ := by
  unfold rotl_prefix execWithEnv
  simp only [List.foldlM]
  dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
  miden_dup
  rw [stepEqImm]

-- ============================================================================
-- Dup setup correctness
-- ============================================================================

set_option maxHeartbeats 4000000 in
private theorem rotl_dup_setup_correct (env : ProcEnv) (fuel : Nat)
    (shift a0 a1 a2 a3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt) :
    execWithEnv env (fuel + 1)
      ⟨shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv⟩
      rotl_dup_setup =
    some ⟨shift :: a0 :: a1 :: a2 :: a3 ::
          shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv⟩ := by
  unfold rotl_dup_setup execWithEnv
  simp only [List.foldlM]
  dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
  miden_dup   -- dup 0
  miden_dup   -- dup 5
  miden_dup   -- dup 5
  miden_dup   -- dup 5
  miden_dup   -- dup 5
  miden_movup -- movup 4

-- ============================================================================
-- Mid setup correctness (generic in shl result limbs)
-- ============================================================================

set_option maxHeartbeats 4000000 in
private theorem rotl_mid_setup_correct (env : ProcEnv) (fuel : Nat)
    (s0 s1 s2 s3 shift a0 a1 a2 a3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
    (hshift_u32 : shift.isU32 = true) :
    execWithEnv env (fuel + 1)
      ⟨s0 :: s1 :: s2 :: s3 :: shift :: a0 :: a1 :: a2 :: a3 :: rest,
       mem, locs, adv⟩
      rotl_mid_setup =
    some ⟨Felt.ofNat (u32OverflowingSub 128 shift.val).2 ::
          a0 :: a1 :: a2 :: a3 :: s0 :: s1 :: s2 :: s3 :: rest,
          mem, locs, adv⟩ := by
  unfold rotl_mid_setup execWithEnv
  simp only [List.foldlM]
  dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
  miden_movdn  -- movdn 8
  miden_movdn  -- movdn 8
  miden_movdn  -- movdn 8
  miden_movdn  -- movdn 8
  rw [stepPush]
  miden_bind
  miden_swap
  rw [stepU32WrappingSubLocal (ha := U32.felt128_isU32) (hb := hshift_u32)]
  miden_bind
  simp only [felt128_val']

-- ============================================================================
-- Combine correctness (generic in shr and shl result limbs)
-- ============================================================================

set_option maxHeartbeats 4000000 in
private theorem rotl_combine_correct (env : ProcEnv) (fuel : Nat)
    (r0 r1 r2 r3 s0 s1 s2 s3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
    (hr0 : r0.isU32 = true) (hr1 : r1.isU32 = true)
    (hr2 : r2.isU32 = true) (hr3 : r3.isU32 = true)
    (hs0 : s0.isU32 = true) (hs1 : s1.isU32 = true)
    (hs2 : s2.isU32 = true) (hs3 : s3.isU32 = true) :
    execWithEnv env (fuel + 1)
      ⟨r0 :: r1 :: r2 :: r3 :: s0 :: s1 :: s2 :: s3 :: rest, mem, locs, adv⟩
      rotl_combine =
    some ⟨Felt.ofNat (r0.val ||| s0.val) :: Felt.ofNat (r1.val ||| s1.val) ::
          Felt.ofNat (r2.val ||| s2.val) :: Felt.ofNat (r3.val ||| s3.val) :: rest,
          mem, locs, adv⟩ := by
  unfold rotl_combine execWithEnv
  simp only [List.foldlM]
  dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
  miden_movup -- movup 4
  rw [stepU32Or (ha := hr0) (hb := hs0)]
  miden_bind
  miden_swap
  miden_movup -- movup 4
  rw [stepU32Or (ha := hr1) (hb := hs1)]
  miden_bind
  miden_swap
  miden_movup -- movup 2
  miden_movup -- movup 4
  rw [stepU32Or (ha := hr2) (hb := hs2)]
  miden_bind
  miden_movdn -- movdn 2
  miden_movup -- movup 3
  miden_movup -- movup 4
  rw [stepU32Or (ha := hr3) (hb := hs3)]
  miden_bind
  miden_movdn -- movdn 3

-- ============================================================================
-- ifElse dispatch helpers (reused from Shl/Shr)
-- ============================================================================

private theorem execWithEnv_append' (env : ProcEnv) (fuel : Nat)
    (s : MidenState) (xs ys : List Op) :
    execWithEnv env fuel s (xs ++ ys) = (do
      let s' ← execWithEnv env fuel s xs
      execWithEnv env fuel s' ys) := by
  unfold execWithEnv
  cases fuel <;> simp [List.foldlM_append]

private theorem execWithEnv_ifElse_one'
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

private theorem execWithEnv_ifElse_zero'
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
-- Nonzero branch: parametric composition
-- ============================================================================

set_option maxHeartbeats 8000000 in
/-- The nonzero branch of rotl, parametric in the shl and shr output limbs.
    Takes hypotheses that shl and shr produce the given limbs, and that
    all limbs are u32. -/
private theorem rotl_nonzero_correct (fuel : Nat)
    (shift a0 a1 a2 a3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
    (s0 s1 s2 s3 r0 r1 r2 r3 : Felt)
    (hshift_u32 : shift.isU32 = true)
    (hs0 : s0.isU32 = true) (hs1 : s1.isU32 = true)
    (hs2 : s2.isU32 = true) (hs3 : s3.isU32 = true)
    (hr0 : r0.isU32 = true) (hr1 : r1.isU32 = true)
    (hr2 : r2.isU32 = true) (hr3 : r3.isU32 = true)
    (hshl : execWithEnv u128ProcEnv (fuel + 7)
      ⟨shift :: a0 :: a1 :: a2 :: a3 ::
       shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv⟩
      Miden.Core.U128.shl =
      some ⟨s0 :: s1 :: s2 :: s3 ::
            shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv⟩)
    (hshr : execWithEnv u128ProcEnv (fuel + 7)
      ⟨Felt.ofNat (u32OverflowingSub 128 shift.val).2 ::
       a0 :: a1 :: a2 :: a3 :: s0 :: s1 :: s2 :: s3 :: rest, mem, locs, adv⟩
      Miden.Core.U128.shr =
      some ⟨r0 :: r1 :: r2 :: r3 ::
            s0 :: s1 :: s2 :: s3 :: rest, mem, locs, adv⟩) :
    execWithEnv u128ProcEnv (fuel + 8)
      ⟨shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv⟩
      rotl_nonzero =
    some ⟨Felt.ofNat (r0.val ||| s0.val) :: Felt.ofNat (r1.val ||| s1.val) ::
          Felt.ofNat (r2.val ||| s2.val) :: Felt.ofNat (r3.val ||| s3.val) :: rest,
          mem, locs, adv⟩ := by
  unfold rotl_nonzero
  simp only [List.append_assoc]
  -- Step 1: dup setup
  rw [execWithEnv_append']
  rw [rotl_dup_setup_correct u128ProcEnv (fuel + 7) shift a0 a1 a2 a3 rest mem locs adv]
  simp only [bind, Bind.bind, Option.bind]
  -- Step 2: exec "shl"
  rw [execWithEnv_append']
  conv_lhs =>
    arg 1
    unfold execWithEnv
    simp only [List.foldlM, u128ProcEnv]
    dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
  rw [hshl]
  simp only [bind, Bind.bind, Option.bind]
  -- Step 3: mid setup
  rw [execWithEnv_append']
  rw [rotl_mid_setup_correct u128ProcEnv (fuel + 7) s0 s1 s2 s3 shift a0 a1 a2 a3 rest
    mem locs adv hshift_u32]
  simp only [bind, Bind.bind, Option.bind]
  -- Step 4: exec "shr"
  rw [execWithEnv_append']
  conv_lhs =>
    arg 1
    unfold execWithEnv
    simp only [List.foldlM, u128ProcEnv]
    dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
  rw [hshr]
  simp only [bind, Bind.bind, Option.bind]
  -- Step 5: combine
  exact rotl_combine_correct u128ProcEnv (fuel + 7) r0 r1 r2 r3 s0 s1 s2 s3 rest
    mem locs adv hr0 hr1 hr2 hr3 hs0 hs1 hs2 hs3

-- ============================================================================
-- Main correctness theorem
-- ============================================================================

set_option maxHeartbeats 8000000 in
/-- `u128::rotl` correctly left-rotates a 128-bit value by `shift` positions (0 ≤ shift < 128).
    When shift = 0, the output is identity. When shift ≠ 0, the output limbs are the
    bitwise OR of the corresponding `u128::shl(shift)` and `u128::shr(128−shift)` output limbs.
    The shl and shr sub-procedure results are provided as parametric hypotheses; their
    individual correctness is proved in `u128_shl_raw` and `u128_shr_raw`. -/
theorem u128_rotl_raw (fuel : Nat)
    (shift a0 a1 a2 a3 : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = shift :: a0 :: a1 :: a2 :: a3 :: rest)
    (hshift_u32 : shift.isU32 = true)
    (s0 s1 s2 s3 r0 r1 r2 r3 : Felt)
    (hs0 : s0.isU32 = true) (hs1 : s1.isU32 = true)
    (hs2 : s2.isU32 = true) (hs3 : s3.isU32 = true)
    (hr0 : r0.isU32 = true) (hr1 : r1.isU32 = true)
    (hr2 : r2.isU32 = true) (hr3 : r3.isU32 = true)
    (hshl : execWithEnv u128ProcEnv (fuel + 7)
      ⟨shift :: a0 :: a1 :: a2 :: a3 ::
       shift :: a0 :: a1 :: a2 :: a3 :: rest,
       s.memory, s.locals, s.advice⟩
      Miden.Core.U128.shl =
      some ⟨s0 :: s1 :: s2 :: s3 ::
            shift :: a0 :: a1 :: a2 :: a3 :: rest,
            s.memory, s.locals, s.advice⟩)
    (hshr : execWithEnv u128ProcEnv (fuel + 7)
      ⟨Felt.ofNat (u32OverflowingSub 128 shift.val).2 ::
       a0 :: a1 :: a2 :: a3 :: s0 :: s1 :: s2 :: s3 :: rest,
       s.memory, s.locals, s.advice⟩
      Miden.Core.U128.shr =
      some ⟨r0 :: r1 :: r2 :: r3 ::
            s0 :: s1 :: s2 :: s3 :: rest,
            s.memory, s.locals, s.advice⟩) :
    execWithEnv u128ProcEnv (fuel + 9) s Miden.Core.U128.rotl =
    some (s.withStack (
      if shift == (0 : Felt) then
        a0 :: a1 :: a2 :: a3 :: rest
      else
        Felt.ofNat (r0.val ||| s0.val) :: Felt.ofNat (r1.val ||| s1.val) ::
        Felt.ofNat (r2.val ||| s2.val) :: Felt.ofNat (r3.val ||| s3.val) :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs hshl hshr ⊢
  subst hs
  rw [rotl_decomp, execWithEnv_append']
  rw [rotl_prefix_correct u128ProcEnv (fuel + 8) shift a0 a1 a2 a3 rest mem locs adv]
  simp only [bind, Bind.bind, Option.bind]
  by_cases hzero : shift == (0 : Felt)
  · -- shift == 0: identity
    simp only [hzero, ↓reduceIte]
    rw [execWithEnv_ifElse_one' u128ProcEnv (fuel + 7)]
    conv_lhs => unfold execWithEnv
    simp only [List.foldlM]
    dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
    rw [stepDrop]
  · -- shift ≠ 0: nonzero branch
    simp only [hzero, ↓reduceIte, Bool.false_eq_true]
    rw [execWithEnv_ifElse_zero' u128ProcEnv (fuel + 7)]
    have hshift_pos : 0 < shift.val := by
      have : shift.val ≠ 0 := fun hval =>
        hzero (beq_iff_eq.mpr ((ZMod.val_eq_zero shift).mp hval))
      omega
    exact rotl_nonzero_correct fuel shift a0 a1 a2 a3 rest mem locs adv
      s0 s1 s2 s3 r0 r1 r2 r3
      hshift_u32 hs0 hs1 hs2 hs3 hr0 hr1 hr2 hr3
      hshl hshr

end MidenLean.Proofs
