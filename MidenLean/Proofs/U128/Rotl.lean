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
    Miden.Core.U128.rotl.body =
    rotl_prefix ++ [.ifElse [.inst (.drop)] rotl_nonzero] := by
  simp [Miden.Core.U128.rotl, rotl_prefix, rotl_nonzero,
        rotl_dup_setup, rotl_mid_setup, rotl_combine]

-- ============================================================================
-- Prefix correctness
-- ============================================================================

private theorem rotl_prefix_correct (env : ProcEnv) (fuel : Nat)
    (shift a0 a1 a2 a3 : Felt) (rest : List Felt)
    (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt) :
    execProcedure env (fuel + 1)
      ⟨shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, frames, adv⟩
      rotl_prefix =
    some ⟨(if shift == (0 : Felt) then (1 : Felt) else 0) ::
          shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, frames, adv⟩ := by
  unfold rotl_prefix execProcedure
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
    (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt) :
    execProcedure env (fuel + 1)
      ⟨shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, frames, adv⟩
      rotl_dup_setup =
    some ⟨shift :: a0 :: a1 :: a2 :: a3 ::
          shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, frames, adv⟩ := by
  unfold rotl_dup_setup execProcedure
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
    (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (hshift_u32 : shift.isU32 = true) :
    execProcedure env (fuel + 1)
      ⟨s0 :: s1 :: s2 :: s3 :: shift :: a0 :: a1 :: a2 :: a3 :: rest,
       mem, frames, adv⟩
      rotl_mid_setup =
    some ⟨Felt.ofNat (u32OverflowingSub 128 shift.val).2 ::
          a0 :: a1 :: a2 :: a3 :: s0 :: s1 :: s2 :: s3 :: rest,
          mem, frames, adv⟩ := by
  unfold rotl_mid_setup execProcedure
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
    (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (hr0 : r0.isU32 = true) (hr1 : r1.isU32 = true)
    (hr2 : r2.isU32 = true) (hr3 : r3.isU32 = true)
    (hs0 : s0.isU32 = true) (hs1 : s1.isU32 = true)
    (hs2 : s2.isU32 = true) (hs3 : s3.isU32 = true) :
    execProcedure env (fuel + 1)
      ⟨r0 :: r1 :: r2 :: r3 :: s0 :: s1 :: s2 :: s3 :: rest, mem, frames, adv⟩
      rotl_combine =
    some ⟨Felt.ofNat (r0.val ||| s0.val) :: Felt.ofNat (r1.val ||| s1.val) ::
          Felt.ofNat (r2.val ||| s2.val) :: Felt.ofNat (r3.val ||| s3.val) :: rest,
          mem, frames, adv⟩ := by
  unfold rotl_combine execProcedure
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
-- Nonzero branch: parametric composition
-- ============================================================================

set_option maxHeartbeats 8000000 in
/-- The nonzero branch of rotl, parametric in the shl and shr output limbs.
    Takes hypotheses that shl and shr produce the given limbs, and that
    all limbs are u32. -/
private theorem rotl_nonzero_correct (fuel : Nat)
    (shift a0 a1 a2 a3 : Felt) (rest : List Felt)
    (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (s0 s1 s2 s3 r0 r1 r2 r3 : Felt)
    (hshift_u32 : shift.isU32 = true)
    (hs0 : s0.isU32 = true) (hs1 : s1.isU32 = true)
    (hs2 : s2.isU32 = true) (hs3 : s3.isU32 = true)
    (hr0 : r0.isU32 = true) (hr1 : r1.isU32 = true)
    (hr2 : r2.isU32 = true) (hr3 : r3.isU32 = true)
    (hshl : execProcedure u128ProcEnv (fuel + 7)
      ⟨shift :: a0 :: a1 :: a2 :: a3 ::
       shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, frames, adv⟩
      Miden.Core.U128.shl =
      some ⟨s0 :: s1 :: s2 :: s3 ::
            shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, frames, adv⟩)
    (hshr : execProcedure u128ProcEnv (fuel + 7)
      ⟨Felt.ofNat (u32OverflowingSub 128 shift.val).2 ::
       a0 :: a1 :: a2 :: a3 :: s0 :: s1 :: s2 :: s3 :: rest, mem, frames, adv⟩
      Miden.Core.U128.shr =
      some ⟨r0 :: r1 :: r2 :: r3 ::
            s0 :: s1 :: s2 :: s3 :: rest, mem, frames, adv⟩) :
    execProcedure u128ProcEnv (fuel + 8)
      ⟨shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, frames, adv⟩
      rotl_nonzero =
    some ⟨Felt.ofNat (r0.val ||| s0.val) :: Felt.ofNat (r1.val ||| s1.val) ::
          Felt.ofNat (r2.val ||| s2.val) :: Felt.ofNat (r3.val ||| s3.val) :: rest,
          mem, frames, adv⟩ := by
  unfold rotl_nonzero
  simp only [List.append_assoc]
  -- Step 1: dup setup
  rw [execProcedure_append]
  rw [rotl_dup_setup_correct u128ProcEnv (fuel + 7) shift a0 a1 a2 a3 rest mem frames adv]
  simp only [bind, Bind.bind, Option.bind]
  -- Step 2: execProcedure emptyEnv "shl"
  rw [execProcedure_append]
  miden_exec_step [hshl]
  -- Step 3: mid setup
  rw [execProcedure_append]
  rw [rotl_mid_setup_correct u128ProcEnv (fuel + 7) s0 s1 s2 s3 shift a0 a1 a2 a3 rest
    mem frames adv hshift_u32]
  simp only [bind, Bind.bind, Option.bind]
  -- Step 4: execProcedure emptyEnv "shr"
  change execProcedure u128ProcEnv (fuel + 8)
      ⟨Felt.ofNat (u32OverflowingSub 128 shift.val).2 ::
        a0 :: a1 :: a2 :: a3 :: s0 :: s1 :: s2 :: s3 :: rest,
        mem, frames, adv⟩
      ([Op.inst (.exec "shr")] ++ rotl_combine) =
    some ⟨Felt.ofNat (r0.val ||| s0.val) :: Felt.ofNat (r1.val ||| s1.val) ::
          Felt.ofNat (r2.val ||| s2.val) :: Felt.ofNat (r3.val ||| s3.val) :: rest,
          mem, frames, adv⟩
  rw [execProcedure_append]
  miden_exec_step [hshr]
  -- Step 5: combine
  exact rotl_combine_correct u128ProcEnv (fuel + 7) r0 r1 r2 r3 s0 s1 s2 s3 rest
    mem frames adv hr0 hr1 hr2 hr3 hs0 hs1 hs2 hs3

-- ============================================================================
-- Low-level exec theorem
-- ============================================================================

set_option maxHeartbeats 8000000 in
/-- `u128::rotl` computes the left rotation of a 128-bit value by `shift` bits.
    Input stack:  [shift, a0, a1, a2, a3] ++ rest  (shift < 128, a0..a3 are u32 limbs)
    Output stack: [r0, r1, r2, r3] ++ rest
    where `r0..r3` are the u32 limbs of `rotl(a, shift)`, computed as the
    elementwise `u32Or` of `u128::shl(shift)` and `u128::shr(128-shift)`.
    Parametric in `fuel` so this lemma can serve as a registered callee summary
    and as the basis for `u128_rotl_correct`. -/
@[miden_exec_summary]
theorem u128_rotl_exec (fuel : Nat)
    (shift a0 a1 a2 a3 : Felt) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = shift :: a0 :: a1 :: a2 :: a3 :: rest)
    (hshift_u32 : shift.isU32 = true)
    (s0 s1 s2 s3 r0 r1 r2 r3 : Felt)
    (hs0 : s0.isU32 = true) (hs1 : s1.isU32 = true)
    (hs2 : s2.isU32 = true) (hs3 : s3.isU32 = true)
    (hr0 : r0.isU32 = true) (hr1 : r1.isU32 = true)
    (hr2 : r2.isU32 = true) (hr3 : r3.isU32 = true)
    (hshl : execProcedure u128ProcEnv (fuel + 7)
      ⟨shift :: a0 :: a1 :: a2 :: a3 ::
       shift :: a0 :: a1 :: a2 :: a3 :: rest,
       s.memory, s.frames, s.advice⟩
      Miden.Core.U128.shl =
      some ⟨s0 :: s1 :: s2 :: s3 ::
            shift :: a0 :: a1 :: a2 :: a3 :: rest,
            s.memory, s.frames, s.advice⟩)
    (hshr : execProcedure u128ProcEnv (fuel + 7)
      ⟨Felt.ofNat (u32OverflowingSub 128 shift.val).2 ::
       a0 :: a1 :: a2 :: a3 :: s0 :: s1 :: s2 :: s3 :: rest,
       s.memory, s.frames, s.advice⟩
      Miden.Core.U128.shr =
      some ⟨r0 :: r1 :: r2 :: r3 ::
            s0 :: s1 :: s2 :: s3 :: rest,
            s.memory, s.frames, s.advice⟩) :
    execProcedure u128ProcEnv (fuel + 9) s Miden.Core.U128.rotl =
    some (s.withStack (
      if shift == (0 : Felt) then
        a0 :: a1 :: a2 :: a3 :: rest
      else
        Felt.ofNat (r0.val ||| s0.val) :: Felt.ofNat (r1.val ||| s1.val) ::
        Felt.ofNat (r2.val ||| s2.val) :: Felt.ofNat (r3.val ||| s3.val) :: rest)) := by
  obtain ⟨stk, mem, frames, adv⟩ := s
  simp only [Concrete.State.withStack] at hs hshl hshr ⊢
  subst hs
  rw [execProcedure_body_eq _ _ _ _ _ rotl_decomp rfl, execProcedure_append]
  rw [rotl_prefix_correct u128ProcEnv (fuel + 8) shift a0 a1 a2 a3 rest mem frames adv]
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
    have hshift_pos : 0 < shift.val := by
      have : shift.val ≠ 0 := fun hval =>
        hzero (beq_iff_eq.mpr ((ZMod.val_eq_zero shift).mp hval))
      omega
    exact rotl_nonzero_correct fuel shift a0 a1 a2 a3 rest mem frames adv
      s0 s1 s2 s3 r0 r1 r2 r3
      hshift_u32 hs0 hs1 hs2 hs3 hr0 hr1 hr2 hr3
      hshl hshr

set_option maxHeartbeats 16000000 in
/-- `u128::rotl` left-rotates a u128 value by `shift` bits.
    Input stack:  [shift, a.a0, a.a1, a.a2, a.a3] ++ rest
    Output stack: [(a.rotl shift).a0, (a.rotl shift).a1, (a.rotl shift).a2, (a.rotl shift).a3] ++ rest -/
theorem u128_rotl_correct (a : U128) (shift : U32) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = shift.val :: a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val :: rest)
    (hshift_lt128 : shift.toNat < 128) :
    execProcedure u128ProcEnv 72 s Miden.Core.U128.rotl =
    some (s.withStack (
      (a.rotl shift.toNat).a0.val :: (a.rotl shift.toNat).a1.val ::
      (a.rotl shift.toNat).a2.val :: (a.rotl shift.toNat).a3.val :: rest)) := by
  obtain ⟨stk, mem, frames, adv⟩ := s
  simp only [Concrete.State.withStack] at hs ⊢
  subst hs
  by_cases hzero : shift.toNat = 0
  · have hshift0 : shift.val = (0 : Felt) := by
      apply ZMod.val_injective
      simpa [U32.toNat, Felt.val_zero'] using hzero
    have hshift0b : (shift.val == (0 : Felt)) = true := by
      exact beq_iff_eq.mpr hshift0
    rw [execProcedure_body_eq _ _ _ _ _ rotl_decomp rfl, execProcedure_append]
    rw [rotl_prefix_correct u128ProcEnv 71 shift.val a.a0.val a.a1.val a.a2.val a.a3.val rest mem frames adv]
    simp only [bind, Bind.bind, Option.bind, hshift0b, ↓reduceIte]
    rw [execProcedure_ifElse_one u128ProcEnv 70]
    conv_lhs => unfold execProcedure
    simp only [List.foldlM]
    dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
    rw [stepDrop]
    simp [hzero, U128.rotl_zero]
  · have hpos : 0 < shift.toNat := Nat.pos_of_ne_zero hzero
    have hshift_ne0 : shift.val ≠ (0 : Felt) := by
      intro h
      apply hzero
      simpa [U32.toNat, Felt.val_zero'] using congrArg ZMod.val h
    have hshift0b : (shift.val == (0 : Felt)) = false := by
      exact Bool.eq_false_iff.mpr (fun h => hshift_ne0 (beq_iff_eq.mp h))
    let shiftComp : U32 := ⟨Felt.ofNat (u32OverflowingSub 128 shift.toNat).2,
      complement_isU32 shift.val hshift_lt128 hpos⟩
    have hshiftComp_toNat : shiftComp.toNat = 128 - shift.toNat := by
      dsimp [shiftComp, U32.toNat]
      exact complement_val shift.val hshift_lt128 hpos
    have hshiftComp_lt128 : shiftComp.toNat < 128 := by
      dsimp [shiftComp, U32.toNat]
      exact complement_lt128 shift.val hshift_lt128 hpos
    have hshl : execProcedure u128ProcEnv 70
        ⟨shift.val :: a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val ::
          shift.val :: a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val :: rest,
          mem, frames, adv⟩
        Miden.Core.U128.shl =
        some ⟨(a.shl shift.toNat).a0.val :: (a.shl shift.toNat).a1.val ::
              (a.shl shift.toNat).a2.val :: (a.shl shift.toNat).a3.val ::
              shift.val :: a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val :: rest,
              mem, frames, adv⟩ := by
      simpa [Concrete.State.withStack] using
        (u128_shl_correct a shift
          (shift.val :: a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val :: rest)
          ⟨shift.val :: a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val ::
            shift.val :: a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val :: rest,
            mem, frames, adv⟩
          rfl hshift_lt128)
    have hshr : execProcedure u128ProcEnv 70
        ⟨shiftComp.val :: a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val ::
          (a.shl shift.toNat).a0.val :: (a.shl shift.toNat).a1.val ::
          (a.shl shift.toNat).a2.val :: (a.shl shift.toNat).a3.val :: rest,
          mem, frames, adv⟩
        Miden.Core.U128.shr =
        some ⟨(a.shr (128 - shift.toNat)).a0.val :: (a.shr (128 - shift.toNat)).a1.val ::
              (a.shr (128 - shift.toNat)).a2.val :: (a.shr (128 - shift.toNat)).a3.val ::
              (a.shl shift.toNat).a0.val :: (a.shl shift.toNat).a1.val ::
              (a.shl shift.toNat).a2.val :: (a.shl shift.toNat).a3.val :: rest,
              mem, frames, adv⟩ := by
      simpa [Concrete.State.withStack, hshiftComp_toNat] using
        (u128_shr_correct_run 63 a shiftComp
          ((a.shl shift.toNat).a0.val :: (a.shl shift.toNat).a1.val ::
            (a.shl shift.toNat).a2.val :: (a.shl shift.toNat).a3.val :: rest)
          ⟨shiftComp.val :: a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val ::
            (a.shl shift.toNat).a0.val :: (a.shl shift.toNat).a1.val ::
            (a.shl shift.toNat).a2.val :: (a.shl shift.toNat).a3.val :: rest,
            mem, frames, adv⟩
          rfl hshiftComp_lt128)
    have hexec := u128_rotl_exec 63 shift.val a.a0.val a.a1.val a.a2.val a.a3.val
      rest ⟨shift.val :: a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val :: rest, mem, frames, adv⟩
      rfl shift.isU32
      (a.shl shift.toNat).a0.val (a.shl shift.toNat).a1.val
      (a.shl shift.toNat).a2.val (a.shl shift.toNat).a3.val
      (a.shr (128 - shift.toNat)).a0.val (a.shr (128 - shift.toNat)).a1.val
      (a.shr (128 - shift.toNat)).a2.val (a.shr (128 - shift.toNat)).a3.val
      (a.shl shift.toNat).a0.isU32 (a.shl shift.toNat).a1.isU32
      (a.shl shift.toNat).a2.isU32 (a.shl shift.toNat).a3.isU32
      (a.shr (128 - shift.toNat)).a0.isU32 (a.shr (128 - shift.toNat)).a1.isU32
      (a.shr (128 - shift.toNat)).a2.isU32 (a.shr (128 - shift.toNat)).a3.isU32
      hshl hshr
    simpa [hshift0b, U128.rotl_eq_or_shl_shr a shift.toNat hshift_lt128]
      using hexec

end MidenLean.Proofs
