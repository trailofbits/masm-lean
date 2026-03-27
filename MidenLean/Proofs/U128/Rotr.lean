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

private theorem felt128_val_rotr : (128 : Felt).val = 128 :=
  felt_ofNat_val_lt 128 (by unfold GOLDILOCKS_PRIME; omega)

private theorem rotr_complement_val (shift : Felt) (hshift_lt128 : shift.val < 128)
    (hshift_pos : 0 < shift.val) :
    (Felt.ofNat (u32OverflowingSub 128 shift.val).2).val = 128 - shift.val := by
  unfold u32OverflowingSub
  simp [show shift.val ≤ 128 by omega]
  rw [felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)]

private theorem rotr_complement_isU32 (shift : Felt) (hshift_lt128 : shift.val < 128)
    (hshift_pos : 0 < shift.val) :
    (Felt.ofNat (u32OverflowingSub 128 shift.val).2).isU32 = true := by
  apply felt_ofNat_isU32_of_lt
  unfold u32OverflowingSub
  simp [show shift.val ≤ 128 by omega]
  omega

private theorem rotr_complement_lt128 (shift : Felt) (hshift_lt128 : shift.val < 128)
    (hshift_pos : 0 < shift.val) :
    (Felt.ofNat (u32OverflowingSub 128 shift.val).2).val < 128 := by
  rw [rotr_complement_val shift hshift_lt128 hshift_pos]; omega

-- ============================================================================
-- Chunk definitions
-- ============================================================================

private def rotr_prefix : List Op := [.inst (.dup 0), .inst (.eqImm 0)]

/-- Duplicate shift and a0..a3, then move shift to top for shr call. -/
private def rotr_dup_setup : List Op := [
  .inst (.dup 0), .inst (.dup 5), .inst (.dup 5),
  .inst (.dup 5), .inst (.dup 5), .inst (.movup 4)]

/-- Move shr results below original args, compute 128-shift for shl call. -/
private def rotr_mid_setup : List Op := [
  .inst (.movdn 8), .inst (.movdn 8), .inst (.movdn 8), .inst (.movdn 8),
  .inst (.push 128), .inst (.swap 1), .inst (.u32WrappingSub)]

/-- Combine shl and shr limbs with elementwise u32Or. -/
private def rotr_combine : List Op := [
  .inst (.movup 4), .inst (.u32Or),
  .inst (.swap 1), .inst (.movup 4), .inst (.u32Or),
  .inst (.swap 1), .inst (.movup 2), .inst (.movup 4), .inst (.u32Or),
  .inst (.movdn 2), .inst (.movup 3), .inst (.movup 4), .inst (.u32Or),
  .inst (.movdn 3)]

private def rotr_nonzero : List Op :=
  rotr_dup_setup ++ [.inst (.exec "shr")] ++
  rotr_mid_setup ++ [.inst (.exec "shl")] ++
  rotr_combine

-- ============================================================================
-- Decomposition
-- ============================================================================

private theorem rotr_decomp :
    Miden.Core.U128.rotr =
    rotr_prefix ++ [.ifElse [.inst (.drop)] rotr_nonzero] := by
  simp [Miden.Core.U128.rotr, rotr_prefix, rotr_nonzero,
        rotr_dup_setup, rotr_mid_setup, rotr_combine]

-- ============================================================================
-- Prefix correctness
-- ============================================================================

private theorem rotr_prefix_correct (env : ProcEnv) (fuel : Nat)
    (shift a0 a1 a2 a3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt) :
    execWithEnv env (fuel + 1)
      ⟨shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv⟩
      rotr_prefix =
    some ⟨(if shift == (0 : Felt) then (1 : Felt) else 0) ::
          shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv⟩ := by
  unfold rotr_prefix execWithEnv
  simp only [List.foldlM]
  dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
  miden_dup
  rw [stepEqImm]

-- ============================================================================
-- Dup setup correctness
-- ============================================================================

set_option maxHeartbeats 4000000 in
private theorem rotr_dup_setup_correct (env : ProcEnv) (fuel : Nat)
    (shift a0 a1 a2 a3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt) :
    execWithEnv env (fuel + 1)
      ⟨shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv⟩
      rotr_dup_setup =
    some ⟨shift :: a0 :: a1 :: a2 :: a3 ::
          shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv⟩ := by
  unfold rotr_dup_setup execWithEnv
  simp only [List.foldlM]
  dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
  miden_dup   -- dup 0
  miden_dup   -- dup 5
  miden_dup   -- dup 5
  miden_dup   -- dup 5
  miden_dup   -- dup 5
  miden_movup -- movup 4

-- ============================================================================
-- Mid setup correctness
-- ============================================================================

set_option maxHeartbeats 4000000 in
private theorem rotr_mid_setup_correct (env : ProcEnv) (fuel : Nat)
    (r0 r1 r2 r3 shift a0 a1 a2 a3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
    (hshift_u32 : shift.isU32 = true) :
    execWithEnv env (fuel + 1)
      ⟨r0 :: r1 :: r2 :: r3 :: shift :: a0 :: a1 :: a2 :: a3 :: rest,
       mem, locs, adv⟩
      rotr_mid_setup =
    some ⟨Felt.ofNat (u32OverflowingSub 128 shift.val).2 ::
          a0 :: a1 :: a2 :: a3 :: r0 :: r1 :: r2 :: r3 :: rest,
          mem, locs, adv⟩ := by
  unfold rotr_mid_setup execWithEnv
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
  simp only [felt128_val_rotr]

-- ============================================================================
-- Combine correctness
-- ============================================================================

set_option maxHeartbeats 4000000 in
private theorem rotr_combine_correct (env : ProcEnv) (fuel : Nat)
    (s0 s1 s2 s3 r0 r1 r2 r3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
    (hs0 : s0.isU32 = true) (hs1 : s1.isU32 = true)
    (hs2 : s2.isU32 = true) (hs3 : s3.isU32 = true)
    (hr0 : r0.isU32 = true) (hr1 : r1.isU32 = true)
    (hr2 : r2.isU32 = true) (hr3 : r3.isU32 = true) :
    execWithEnv env (fuel + 1)
      ⟨s0 :: s1 :: s2 :: s3 :: r0 :: r1 :: r2 :: r3 :: rest, mem, locs, adv⟩
      rotr_combine =
    some ⟨Felt.ofNat (s0.val ||| r0.val) :: Felt.ofNat (s1.val ||| r1.val) ::
          Felt.ofNat (s2.val ||| r2.val) :: Felt.ofNat (s3.val ||| r3.val) :: rest,
          mem, locs, adv⟩ := by
  unfold rotr_combine execWithEnv
  simp only [List.foldlM]
  dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
  miden_movup -- movup 4
  rw [stepU32Or (ha := hs0) (hb := hr0)]
  miden_bind
  miden_swap
  miden_movup -- movup 4
  rw [stepU32Or (ha := hs1) (hb := hr1)]
  miden_bind
  miden_swap
  miden_movup -- movup 2
  miden_movup -- movup 4
  rw [stepU32Or (ha := hs2) (hb := hr2)]
  miden_bind
  miden_movdn -- movdn 2
  miden_movup -- movup 3
  miden_movup -- movup 4
  rw [stepU32Or (ha := hs3) (hb := hr3)]
  miden_bind
  miden_movdn -- movdn 3

-- ============================================================================
-- ifElse dispatch helpers
-- ============================================================================

private theorem execWithEnv_append_rotr (env : ProcEnv) (fuel : Nat)
    (s : MidenState) (xs ys : List Op) :
    execWithEnv env fuel s (xs ++ ys) = (do
      let s' ← execWithEnv env fuel s xs
      execWithEnv env fuel s' ys) := by
  unfold execWithEnv
  cases fuel <;> simp [List.foldlM_append]

private theorem execWithEnv_ifElse_one_rotr
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

private theorem execWithEnv_ifElse_zero_rotr
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
/-- The nonzero branch of rotr, parametric in the shr and shl output limbs.
    Takes hypotheses that shr and shl produce the given limbs, and that
    all limbs are u32. -/
private theorem rotr_nonzero_correct (fuel : Nat)
    (shift a0 a1 a2 a3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
    (r0 r1 r2 r3 s0 s1 s2 s3 : Felt)
    (hshift_u32 : shift.isU32 = true)
    (hr0 : r0.isU32 = true) (hr1 : r1.isU32 = true)
    (hr2 : r2.isU32 = true) (hr3 : r3.isU32 = true)
    (hs0 : s0.isU32 = true) (hs1 : s1.isU32 = true)
    (hs2 : s2.isU32 = true) (hs3 : s3.isU32 = true)
    (hshr : execWithEnv u128ProcEnv (fuel + 7)
      ⟨shift :: a0 :: a1 :: a2 :: a3 ::
       shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv⟩
      Miden.Core.U128.shr =
      some ⟨r0 :: r1 :: r2 :: r3 ::
            shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv⟩)
    (hshl : execWithEnv u128ProcEnv (fuel + 7)
      ⟨Felt.ofNat (u32OverflowingSub 128 shift.val).2 ::
       a0 :: a1 :: a2 :: a3 :: r0 :: r1 :: r2 :: r3 :: rest, mem, locs, adv⟩
      Miden.Core.U128.shl =
      some ⟨s0 :: s1 :: s2 :: s3 ::
            r0 :: r1 :: r2 :: r3 :: rest, mem, locs, adv⟩) :
    execWithEnv u128ProcEnv (fuel + 8)
      ⟨shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv⟩
      rotr_nonzero =
    some ⟨Felt.ofNat (s0.val ||| r0.val) :: Felt.ofNat (s1.val ||| r1.val) ::
          Felt.ofNat (s2.val ||| r2.val) :: Felt.ofNat (s3.val ||| r3.val) :: rest,
          mem, locs, adv⟩ := by
  unfold rotr_nonzero
  simp only [List.append_assoc]
  -- Step 1: dup setup
  rw [execWithEnv_append_rotr]
  rw [rotr_dup_setup_correct u128ProcEnv (fuel + 7) shift a0 a1 a2 a3 rest mem locs adv]
  simp only [bind, Bind.bind, Option.bind]
  -- Step 2: exec "shr"
  rw [execWithEnv_append_rotr]
  conv_lhs =>
    arg 1
    unfold execWithEnv
    simp only [List.foldlM, u128ProcEnv]
    dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
  rw [hshr]
  simp only [bind, Bind.bind, Option.bind]
  -- Step 3: mid setup
  rw [execWithEnv_append_rotr]
  rw [rotr_mid_setup_correct u128ProcEnv (fuel + 7) r0 r1 r2 r3 shift a0 a1 a2 a3 rest
    mem locs adv hshift_u32]
  simp only [bind, Bind.bind, Option.bind]
  -- Step 4: exec "shl"
  rw [execWithEnv_append_rotr]
  conv_lhs =>
    arg 1
    unfold execWithEnv
    simp only [List.foldlM, u128ProcEnv]
    dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
  rw [hshl]
  simp only [bind, Bind.bind, Option.bind]
  -- Step 5: combine
  exact rotr_combine_correct u128ProcEnv (fuel + 7) s0 s1 s2 s3 r0 r1 r2 r3 rest
    mem locs adv hs0 hs1 hs2 hs3 hr0 hr1 hr2 hr3

-- ============================================================================
-- Main correctness theorem (raw)
-- ============================================================================

set_option maxHeartbeats 8000000 in
/-- `u128::rotr` right-rotates a 128-bit value by `shift` positions (0 ≤ shift < 128).
    When shift = 0, the output is identity. When shift ≠ 0, the output limbs are the
    bitwise OR of the corresponding `u128::shl(128−shift)` and `u128::shr(shift)` output limbs.
    The shl and shr sub-procedure results are provided as parametric hypotheses; their
    individual correctness is proved in `u128_shl_correct` and `u128_shr_correct_run`. -/
theorem u128_rotr_raw (fuel : Nat)
    (shift a0 a1 a2 a3 : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = shift :: a0 :: a1 :: a2 :: a3 :: rest)
    (hshift_u32 : shift.isU32 = true)
    (r0 r1 r2 r3 s0 s1 s2 s3 : Felt)
    (hr0 : r0.isU32 = true) (hr1 : r1.isU32 = true)
    (hr2 : r2.isU32 = true) (hr3 : r3.isU32 = true)
    (hs0 : s0.isU32 = true) (hs1 : s1.isU32 = true)
    (hs2 : s2.isU32 = true) (hs3 : s3.isU32 = true)
    (hshr : execWithEnv u128ProcEnv (fuel + 7)
      ⟨shift :: a0 :: a1 :: a2 :: a3 ::
       shift :: a0 :: a1 :: a2 :: a3 :: rest,
       s.memory, s.locals, s.advice⟩
      Miden.Core.U128.shr =
      some ⟨r0 :: r1 :: r2 :: r3 ::
            shift :: a0 :: a1 :: a2 :: a3 :: rest,
            s.memory, s.locals, s.advice⟩)
    (hshl : execWithEnv u128ProcEnv (fuel + 7)
      ⟨Felt.ofNat (u32OverflowingSub 128 shift.val).2 ::
       a0 :: a1 :: a2 :: a3 :: r0 :: r1 :: r2 :: r3 :: rest,
       s.memory, s.locals, s.advice⟩
      Miden.Core.U128.shl =
      some ⟨s0 :: s1 :: s2 :: s3 ::
            r0 :: r1 :: r2 :: r3 :: rest,
            s.memory, s.locals, s.advice⟩) :
    execWithEnv u128ProcEnv (fuel + 9) s Miden.Core.U128.rotr =
    some (s.withStack (
      if shift == (0 : Felt) then
        a0 :: a1 :: a2 :: a3 :: rest
      else
        Felt.ofNat (s0.val ||| r0.val) :: Felt.ofNat (s1.val ||| r1.val) ::
        Felt.ofNat (s2.val ||| r2.val) :: Felt.ofNat (s3.val ||| r3.val) :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs hshr hshl ⊢
  subst hs
  rw [rotr_decomp, execWithEnv_append_rotr]
  rw [rotr_prefix_correct u128ProcEnv (fuel + 8) shift a0 a1 a2 a3 rest mem locs adv]
  simp only [bind, Bind.bind, Option.bind]
  by_cases hzero : shift == (0 : Felt)
  · -- shift == 0: identity
    simp only [hzero, ↓reduceIte]
    rw [execWithEnv_ifElse_one_rotr u128ProcEnv (fuel + 7)]
    conv_lhs => unfold execWithEnv
    simp only [List.foldlM]
    dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
    rw [stepDrop]
  · -- shift ≠ 0: nonzero branch
    simp only [hzero, ↓reduceIte, Bool.false_eq_true]
    rw [execWithEnv_ifElse_zero_rotr u128ProcEnv (fuel + 7)]
    exact rotr_nonzero_correct fuel shift a0 a1 a2 a3 rest mem locs adv
      r0 r1 r2 r3 s0 s1 s2 s3
      hshift_u32 hr0 hr1 hr2 hr3 hs0 hs1 hs2 hs3
      hshr hshl

-- ============================================================================
-- Concrete correctness theorem
-- ============================================================================

set_option maxHeartbeats 16000000 in
/-- `u128::rotr` right-rotates a u128 value by `shift` bits.
    Input stack:  [shift, a.a0, a.a1, a.a2, a.a3] ++ rest
    Output stack: [(a.rotr shift).a0, (a.rotr shift).a1, (a.rotr shift).a2, (a.rotr shift).a3] ++ rest -/
theorem u128_rotr_correct (a : U128) (shift : U32) (rest : List Felt) (s : MidenState)
    (hs : s.stack = shift.val :: a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val :: rest)
    (hshift_lt128 : shift.toNat < 128) :
    execWithEnv u128ProcEnv 72 s Miden.Core.U128.rotr =
    some (s.withStack (
      (a.rotr shift.toNat).a0.val :: (a.rotr shift.toNat).a1.val ::
      (a.rotr shift.toNat).a2.val :: (a.rotr shift.toNat).a3.val :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  by_cases hzero : shift.toNat = 0
  · have hshift0 : shift.val = (0 : Felt) := by
      apply ZMod.val_injective
      simpa [U32.toNat, Felt.val_zero'] using hzero
    have hshift0b : (shift.val == (0 : Felt)) = true := by
      exact beq_iff_eq.mpr hshift0
    rw [rotr_decomp, execWithEnv_append_rotr]
    rw [rotr_prefix_correct u128ProcEnv 71 shift.val a.a0.val a.a1.val a.a2.val a.a3.val rest mem locs adv]
    simp only [bind, Bind.bind, Option.bind, hshift0b, ↓reduceIte]
    rw [execWithEnv_ifElse_one_rotr u128ProcEnv 70]
    conv_lhs => unfold execWithEnv
    simp only [List.foldlM]
    dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
    rw [stepDrop]
    simp [hzero, U128.rotr_zero]
  · have hpos : 0 < shift.toNat := Nat.pos_of_ne_zero hzero
    have hshift_ne0 : shift.val ≠ (0 : Felt) := by
      intro h
      apply hzero
      simpa [U32.toNat, Felt.val_zero'] using congrArg ZMod.val h
    have hshift0b : (shift.val == (0 : Felt)) = false := by
      exact Bool.eq_false_iff.mpr (fun h => hshift_ne0 (beq_iff_eq.mp h))
    let shiftComp : U32 := ⟨Felt.ofNat (u32OverflowingSub 128 shift.toNat).2,
      rotr_complement_isU32 shift.val hshift_lt128 hpos⟩
    have hshiftComp_toNat : shiftComp.toNat = 128 - shift.toNat := by
      dsimp [shiftComp, U32.toNat]
      exact rotr_complement_val shift.val hshift_lt128 hpos
    have hshiftComp_lt128 : shiftComp.toNat < 128 := by
      dsimp [shiftComp, U32.toNat]
      exact rotr_complement_lt128 shift.val hshift_lt128 hpos
    -- shr is called first with the original shift
    have hshr :
        execWithEnv u128ProcEnv 70
          ⟨shift.val :: a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val ::
            shift.val :: a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val :: rest,
            mem, locs, adv⟩
          Miden.Core.U128.shr =
        some ⟨(a.shr shift.toNat).a0.val :: (a.shr shift.toNat).a1.val ::
              (a.shr shift.toNat).a2.val :: (a.shr shift.toNat).a3.val ::
              shift.val :: a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val :: rest,
              mem, locs, adv⟩ := by
      simpa [MidenState.withStack] using
        (u128_shr_correct_run 63 a shift
          (shift.val :: a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val :: rest)
          ⟨shift.val :: a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val ::
            shift.val :: a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val :: rest,
            mem, locs, adv⟩
          rfl hshift_lt128)
    -- shl is called second with (128 - shift)
    have hshl :
        execWithEnv u128ProcEnv 70
          ⟨shiftComp.val :: a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val ::
            (a.shr shift.toNat).a0.val :: (a.shr shift.toNat).a1.val ::
            (a.shr shift.toNat).a2.val :: (a.shr shift.toNat).a3.val :: rest,
            mem, locs, adv⟩
          Miden.Core.U128.shl =
        some ⟨(a.shl (128 - shift.toNat)).a0.val :: (a.shl (128 - shift.toNat)).a1.val ::
              (a.shl (128 - shift.toNat)).a2.val :: (a.shl (128 - shift.toNat)).a3.val ::
              (a.shr shift.toNat).a0.val :: (a.shr shift.toNat).a1.val ::
              (a.shr shift.toNat).a2.val :: (a.shr shift.toNat).a3.val :: rest,
              mem, locs, adv⟩ := by
      simpa [MidenState.withStack, hshiftComp_toNat] using
        (u128_shl_correct a shiftComp
          ((a.shr shift.toNat).a0.val :: (a.shr shift.toNat).a1.val ::
            (a.shr shift.toNat).a2.val :: (a.shr shift.toNat).a3.val :: rest)
          ⟨shiftComp.val :: a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val ::
            (a.shr shift.toNat).a0.val :: (a.shr shift.toNat).a1.val ::
            (a.shr shift.toNat).a2.val :: (a.shr shift.toNat).a3.val :: rest,
            mem, locs, adv⟩
          rfl hshiftComp_lt128)
    have hraw := u128_rotr_raw 63 shift.val a.a0.val a.a1.val a.a2.val a.a3.val rest
      ⟨shift.val :: a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val :: rest, mem, locs, adv⟩
      rfl shift.isU32
      (a.shr shift.toNat).a0.val (a.shr shift.toNat).a1.val
      (a.shr shift.toNat).a2.val (a.shr shift.toNat).a3.val
      (a.shl (128 - shift.toNat)).a0.val (a.shl (128 - shift.toNat)).a1.val
      (a.shl (128 - shift.toNat)).a2.val (a.shl (128 - shift.toNat)).a3.val
      (a.shr shift.toNat).a0.isU32 (a.shr shift.toNat).a1.isU32
      (a.shr shift.toNat).a2.isU32 (a.shr shift.toNat).a3.isU32
      (a.shl (128 - shift.toNat)).a0.isU32 (a.shl (128 - shift.toNat)).a1.isU32
      (a.shl (128 - shift.toNat)).a2.isU32 (a.shl (128 - shift.toNat)).a3.isU32
      hshr hshl
    simpa [hshift0b, U128.rotr_eq_or_shr_shl a shift.toNat hshift_lt128]
      using hraw

end MidenLean.Proofs
