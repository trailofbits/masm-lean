import MidenLean.Proofs.Tactics
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 8000000 in
/-- u64.overflowing_sub correctly computes subtraction of two u64 values with borrow.
    Input stack:  [b_lo, b_hi, a_lo, a_hi] ++ rest
    Output stack: [borrow, diff_lo, diff_hi] ++ rest
    where (diff_hi, diff_lo) is the u64 difference a - b,
    and borrow = 1 iff the subtraction underflowed. -/
theorem u64_overflowing_sub_correct
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest) :
    exec 20 s Miden.Core.Math.U64.overflowing_sub =
    some (s.withStack (
      let sub_lo := u32OverflowingSub a_lo.val b_lo.val
      let sub_hi := u32OverflowingSub a_hi.val b_hi.val
      let sub_adj := u32OverflowingSub sub_hi.2 sub_lo.1
      let borrow_hi := decide (a_hi.val < b_hi.val)
      let borrow_adj := decide (sub_hi.2 < sub_lo.1)
      (if borrow_adj || borrow_hi then (1 : Felt) else 0) ::
      Felt.ofNat sub_lo.2 :: Felt.ofNat sub_adj.2 :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.Math.U64.overflowing_sub execWithEnv
  simp only [List.foldlM]
  change (do
    let s' ← execInstruction ⟨b_lo :: b_hi :: a_lo :: a_hi :: rest, mem, locs, adv⟩ (.movup 3)
    let s' ← execInstruction s' (.movup 3)
    let s' ← execInstruction s' (.movup 2)
    let s' ← execInstruction s' (.u32OverflowSub)
    let s' ← execInstruction s' (.movup 2)
    let s' ← execInstruction s' (.movup 3)
    let s' ← execInstruction s' (.u32OverflowSub)
    let s' ← execInstruction s' (.swap 1)
    let s' ← execInstruction s' (.movup 2)
    let s' ← execInstruction s' (.u32OverflowSub)
    let s' ← execInstruction s' (.movup 2)
    let s' ← execInstruction s' Instruction.or
    let s' ← execInstruction s' (.movup 2)
    let s' ← execInstruction s' (.swap 1)
    pure s') = _
  miden_movup; miden_movup; miden_movup
  rw [stepU32OverflowSub]; miden_bind
  miden_movup; miden_movup
  rw [stepU32OverflowSub]; miden_bind
  miden_swap
  miden_movup
  -- The third u32OverflowSub operates on Felt.ofNat values
  have h_val_snd : (Felt.ofNat (u32OverflowingSub a_hi.val b_hi.val).2).val =
      (u32OverflowingSub a_hi.val b_hi.val).2 :=
    felt_ofNat_val_lt _ (u32_overflow_sub_snd_lt _ _ (ZMod.val_lt a_hi) (ZMod.val_lt b_hi))
  have h_val_fst : (Felt.ofNat (u32OverflowingSub a_lo.val b_lo.val).1).val =
      (u32OverflowingSub a_lo.val b_lo.val).1 :=
    felt_ofNat_val_lt _ (u32_overflow_sub_fst_lt _ _)
  rw [stepU32OverflowSub]; miden_bind
  rw [h_val_snd, h_val_fst]
  miden_movup
  -- Convert both borrows to boolean ite form for stepOrIte
  rw [u32OverflowingSub_borrow_ite (u32OverflowingSub a_hi.val b_hi.val).2
      (u32OverflowingSub a_lo.val b_lo.val).1]
  rw [u32OverflowingSub_borrow_ite a_hi.val b_hi.val]
  rw [stepOrIte]; miden_bind
  miden_movup
  miden_swap
  dsimp only [pure, Pure.pure]

end MidenLean.Proofs
