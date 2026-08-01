import MidenLean.Proofs.U128.Shl
import MidenLean.Proofs.U128.Shr
import MidenLean.Proofs.Tactics
import MidenLean.Symbolic.Tactic
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
    Miden.Core.U128.rotr.body =
    rotr_prefix ++ [.ifElse [.inst (.drop)] rotr_nonzero] := by
  simp [Miden.Core.U128.rotr, rotr_prefix, rotr_nonzero,
        rotr_dup_setup, rotr_mid_setup, rotr_combine]

-- ============================================================================
-- Prefix correctness
-- ============================================================================

private theorem rotr_prefix_correct (env : ProcEnv) (fuel : Nat)
    (shift a0 a1 a2 a3 : Felt) (rest : List Felt)
    (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt) :
    execProcedure env (fuel + 1)
      ⟨shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, frames, adv⟩
      rotr_prefix =
    some ⟨(if shift == (0 : Felt) then (1 : Felt) else 0) ::
          shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, frames, adv⟩ := by
  unfold rotr_prefix execProcedure
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
    (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt) :
    execProcedure env (fuel + 1)
      ⟨shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, frames, adv⟩
      rotr_dup_setup =
    some ⟨shift :: a0 :: a1 :: a2 :: a3 ::
          shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, frames, adv⟩ := by
  unfold rotr_dup_setup execProcedure
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
    (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (hshift_u32 : shift.isU32 = true) :
    execProcedure env (fuel + 1)
      ⟨r0 :: r1 :: r2 :: r3 :: shift :: a0 :: a1 :: a2 :: a3 :: rest,
       mem, frames, adv⟩
      rotr_mid_setup =
    some ⟨Felt.ofNat (u32OverflowingSub 128 shift.val).2 ::
          a0 :: a1 :: a2 :: a3 :: r0 :: r1 :: r2 :: r3 :: rest,
          mem, frames, adv⟩ := by
  unfold rotr_mid_setup execProcedure
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
    (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (hs0 : s0.isU32 = true) (hs1 : s1.isU32 = true)
    (hs2 : s2.isU32 = true) (hs3 : s3.isU32 = true)
    (hr0 : r0.isU32 = true) (hr1 : r1.isU32 = true)
    (hr2 : r2.isU32 = true) (hr3 : r3.isU32 = true) :
    execProcedure env (fuel + 1)
      ⟨s0 :: s1 :: s2 :: s3 :: r0 :: r1 :: r2 :: r3 :: rest, mem, frames, adv⟩
      rotr_combine =
    some ⟨Felt.ofNat (s0.val ||| r0.val) :: Felt.ofNat (s1.val ||| r1.val) ::
          Felt.ofNat (s2.val ||| r2.val) :: Felt.ofNat (s3.val ||| r3.val) :: rest,
          mem, frames, adv⟩ := by
  unfold rotr_combine execProcedure
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
-- Nonzero branch: parametric composition
-- ============================================================================

set_option maxHeartbeats 8000000 in
/-- The nonzero branch of rotr, parametric in the shr and shl output limbs.
    Takes hypotheses that shr and shl produce the given limbs, and that
    all limbs are u32. -/
private theorem rotr_nonzero_correct (fuel : Nat)
    (shift a0 a1 a2 a3 : Felt) (rest : List Felt)
    (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (r0 r1 r2 r3 s0 s1 s2 s3 : Felt)
    (hshift_u32 : shift.isU32 = true)
    (hr0 : r0.isU32 = true) (hr1 : r1.isU32 = true)
    (hr2 : r2.isU32 = true) (hr3 : r3.isU32 = true)
    (hs0 : s0.isU32 = true) (hs1 : s1.isU32 = true)
    (hs2 : s2.isU32 = true) (hs3 : s3.isU32 = true)
    (hshr : execProcedure u128ProcEnv (fuel + 7)
      ⟨shift :: a0 :: a1 :: a2 :: a3 ::
       shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, frames, adv⟩
      Miden.Core.U128.shr =
      some ⟨r0 :: r1 :: r2 :: r3 ::
            shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, frames, adv⟩)
    (hshl : execProcedure u128ProcEnv (fuel + 7)
      ⟨Felt.ofNat (u32OverflowingSub 128 shift.val).2 ::
       a0 :: a1 :: a2 :: a3 :: r0 :: r1 :: r2 :: r3 :: rest, mem, frames, adv⟩
      Miden.Core.U128.shl =
      some ⟨s0 :: s1 :: s2 :: s3 ::
            r0 :: r1 :: r2 :: r3 :: rest, mem, frames, adv⟩) :
    execProcedure u128ProcEnv (fuel + 8)
      ⟨shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, frames, adv⟩
      rotr_nonzero =
    some ⟨Felt.ofNat (s0.val ||| r0.val) :: Felt.ofNat (s1.val ||| r1.val) ::
          Felt.ofNat (s2.val ||| r2.val) :: Felt.ofNat (s3.val ||| r3.val) :: rest,
          mem, frames, adv⟩ := by
  unfold rotr_nonzero
  simp only [List.append_assoc]
  -- Step 1: dup setup
  rw [execProcedure_append]
  rw [rotr_dup_setup_correct u128ProcEnv (fuel + 7) shift a0 a1 a2 a3 rest mem frames adv]
  simp only [bind, Bind.bind, Option.bind]
  -- Step 2: execProcedure emptyEnv "shr"
  rw [execProcedure_append]
  miden_exec_step [hshr]
  -- Step 3: mid setup
  rw [execProcedure_append]
  rw [rotr_mid_setup_correct u128ProcEnv (fuel + 7) r0 r1 r2 r3 shift a0 a1 a2 a3 rest
    mem frames adv hshift_u32]
  simp only [bind, Bind.bind, Option.bind]
  -- Step 4: execProcedure emptyEnv "shl"
  change execProcedure u128ProcEnv (fuel + 8)
      ⟨Felt.ofNat (u32OverflowingSub 128 shift.val).2 ::
        a0 :: a1 :: a2 :: a3 :: r0 :: r1 :: r2 :: r3 :: rest,
        mem, frames, adv⟩
      ([Op.inst (.exec "shl")] ++ rotr_combine) =
    some ⟨Felt.ofNat (s0.val ||| r0.val) :: Felt.ofNat (s1.val ||| r1.val) ::
          Felt.ofNat (s2.val ||| r2.val) :: Felt.ofNat (s3.val ||| r3.val) :: rest,
          mem, frames, adv⟩
  rw [execProcedure_append]
  miden_exec_step [hshl]
  -- Step 5: combine
  exact rotr_combine_correct u128ProcEnv (fuel + 7) s0 s1 s2 s3 r0 r1 r2 r3 rest
    mem frames adv hs0 hs1 hs2 hs3 hr0 hr1 hr2 hr3

-- ============================================================================
-- Low-level exec theorem
-- ============================================================================

set_option maxHeartbeats 8000000 in
/-- `u128::rotr` computes the right rotation of a 128-bit value by `shift` bits.
    Input stack:  [shift, a0, a1, a2, a3] ++ rest  (shift < 128, a0..a3 are u32 limbs)
    Output stack: [r0, r1, r2, r3] ++ rest
    where `r0..r3` are the u32 limbs of `rotr(a, shift)`, computed as the
    elementwise `u32Or` of `u128::shr(shift)` and `u128::shl(128-shift)`.
    Parametric in `fuel` so this lemma can serve as a registered callee summary
    and as the basis for `u128_rotr_correct`. -/
@[miden_exec_summary]
theorem u128_rotr_exec (fuel : Nat)
    (shift a0 a1 a2 a3 : Felt) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = shift :: a0 :: a1 :: a2 :: a3 :: rest)
    (hshift_u32 : shift.isU32 = true)
    (r0 r1 r2 r3 s0 s1 s2 s3 : Felt)
    (hr0 : r0.isU32 = true) (hr1 : r1.isU32 = true)
    (hr2 : r2.isU32 = true) (hr3 : r3.isU32 = true)
    (hs0 : s0.isU32 = true) (hs1 : s1.isU32 = true)
    (hs2 : s2.isU32 = true) (hs3 : s3.isU32 = true)
    (hshr : execProcedure u128ProcEnv (fuel + 7)
      ⟨shift :: a0 :: a1 :: a2 :: a3 ::
       shift :: a0 :: a1 :: a2 :: a3 :: rest,
       s.memory, s.frames, s.advice⟩
      Miden.Core.U128.shr =
      some ⟨r0 :: r1 :: r2 :: r3 ::
            shift :: a0 :: a1 :: a2 :: a3 :: rest,
            s.memory, s.frames, s.advice⟩)
    (hshl : execProcedure u128ProcEnv (fuel + 7)
      ⟨Felt.ofNat (u32OverflowingSub 128 shift.val).2 ::
       a0 :: a1 :: a2 :: a3 :: r0 :: r1 :: r2 :: r3 :: rest,
       s.memory, s.frames, s.advice⟩
      Miden.Core.U128.shl =
      some ⟨s0 :: s1 :: s2 :: s3 ::
            r0 :: r1 :: r2 :: r3 :: rest,
            s.memory, s.frames, s.advice⟩) :
    execProcedure u128ProcEnv (fuel + 9) s Miden.Core.U128.rotr =
    some (s.withStack (
      if shift == (0 : Felt) then
        a0 :: a1 :: a2 :: a3 :: rest
      else
        Felt.ofNat (s0.val ||| r0.val) :: Felt.ofNat (s1.val ||| r1.val) ::
        Felt.ofNat (s2.val ||| r2.val) :: Felt.ofNat (s3.val ||| r3.val) :: rest)) := by
  obtain ⟨stk, mem, frames, adv⟩ := s
  simp only [Concrete.State.withStack] at hs hshr hshl ⊢
  subst hs
  rw [execProcedure_body_eq _ _ _ _ _ rotr_decomp rfl, execProcedure_append]
  rw [rotr_prefix_correct u128ProcEnv (fuel + 8) shift a0 a1 a2 a3 rest mem frames adv]
  simp only [bind, Bind.bind, Option.bind]
  by_cases hzero : shift == (0 : Felt)
  · -- shift == 0: identity
    simp only [hzero, ↓reduceIte]
    rw [execProcedure_ifElse_one u128ProcEnv (fuel + 7)]
    conv_lhs => unfold execProcedure
    simp only [List.foldlM]
    dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
    rw [stepDrop]
  · -- shift ≠ 0: nonzero branch
    simp only [hzero, ↓reduceIte, Bool.false_eq_true]
    rw [execProcedure_ifElse_zero u128ProcEnv (fuel + 7)]
    exact rotr_nonzero_correct fuel shift a0 a1 a2 a3 rest mem frames adv
      r0 r1 r2 r3 s0 s1 s2 s3
      hshift_u32 hr0 hr1 hr2 hr3 hs0 hs1 hs2 hs3
      hshr hshl

-- ============================================================================
-- High-level correctness theorem
-- ============================================================================

set_option maxHeartbeats 16000000 in
/-- `u128::rotr` right-rotates a u128 value by `shift` bits.
    Input stack:  [shift, a.a0, a.a1, a.a2, a.a3] ++ rest
    Output stack: [(a.rotr shift).a0, (a.rotr shift).a1, (a.rotr shift).a2, (a.rotr shift).a3] ++ rest -/
theorem u128_rotr_correct (a : U128) (shift : U32) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = shift.val :: a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val :: rest)
    (hshift_lt128 : shift.toNat < 128) :
    execProcedure u128ProcEnv 72 s Miden.Core.U128.rotr =
    some (s.withStack (
      (a.rotr shift.toNat).a0.val :: (a.rotr shift.toNat).a1.val ::
      (a.rotr shift.toNat).a2.val :: (a.rotr shift.toNat).a3.val :: rest)) := by
  obtain ⟨stk, mem, frames, adv⟩ := s
  simp only [Concrete.State.withStack] at hs ⊢
  subst hs
  by_cases hzero : shift.toNat = 0
  · have hshift0 : shift.val = (0 : Felt) := by
      apply ZMod.val_injective
      simpa [U32.toNat, Felt.val_zero'] using hzero
    have hshift0b : (shift.val == (0 : Felt)) = true := by
      exact beq_iff_eq.mpr hshift0
    rw [execProcedure_body_eq _ _ _ _ _ rotr_decomp rfl, execProcedure_append]
    rw [rotr_prefix_correct u128ProcEnv 71 shift.val a.a0.val a.a1.val a.a2.val a.a3.val rest mem frames adv]
    simp only [bind, Bind.bind, Option.bind, hshift0b, ↓reduceIte]
    rw [execProcedure_ifElse_one u128ProcEnv 70]
    conv_lhs => unfold execProcedure
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
    have hshr : execProcedure u128ProcEnv 70
        ⟨shift.val :: a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val ::
          shift.val :: a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val :: rest,
          mem, frames, adv⟩
        Miden.Core.U128.shr =
        some ⟨(a.shr shift.toNat).a0.val :: (a.shr shift.toNat).a1.val ::
              (a.shr shift.toNat).a2.val :: (a.shr shift.toNat).a3.val ::
              shift.val :: a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val :: rest,
              mem, frames, adv⟩ := by
      simpa [Concrete.State.withStack] using
        (u128_shr_correct_run 63 a shift
          (shift.val :: a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val :: rest)
          ⟨shift.val :: a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val ::
            shift.val :: a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val :: rest,
            mem, frames, adv⟩
          rfl hshift_lt128)
    have hshl : execProcedure u128ProcEnv 70
        ⟨shiftComp.val :: a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val ::
          (a.shr shift.toNat).a0.val :: (a.shr shift.toNat).a1.val ::
          (a.shr shift.toNat).a2.val :: (a.shr shift.toNat).a3.val :: rest,
          mem, frames, adv⟩
        Miden.Core.U128.shl =
        some ⟨(a.shl (128 - shift.toNat)).a0.val :: (a.shl (128 - shift.toNat)).a1.val ::
              (a.shl (128 - shift.toNat)).a2.val :: (a.shl (128 - shift.toNat)).a3.val ::
              (a.shr shift.toNat).a0.val :: (a.shr shift.toNat).a1.val ::
              (a.shr shift.toNat).a2.val :: (a.shr shift.toNat).a3.val :: rest,
              mem, frames, adv⟩ := by
      simpa [Concrete.State.withStack, hshiftComp_toNat] using
        (u128_shl_correct a shiftComp
          ((a.shr shift.toNat).a0.val :: (a.shr shift.toNat).a1.val ::
            (a.shr shift.toNat).a2.val :: (a.shr shift.toNat).a3.val :: rest)
          ⟨shiftComp.val :: a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val ::
            (a.shr shift.toNat).a0.val :: (a.shr shift.toNat).a1.val ::
            (a.shr shift.toNat).a2.val :: (a.shr shift.toNat).a3.val :: rest,
            mem, frames, adv⟩
          rfl hshiftComp_lt128)
    have hexec := u128_rotr_exec 63 shift.val a.a0.val a.a1.val a.a2.val a.a3.val
      rest ⟨shift.val :: a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val :: rest, mem, frames, adv⟩
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
      using hexec

end MidenLean.Proofs
