import MidenLean.Proofs.U64.Common
import MidenLean.Proofs.Tactics
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

-- Based on generated skeleton: SEMI | Instructions: 10 | Calls: true (gt)
set_option maxHeartbeats 16000000 in
/-- `u64::min` correctly computes the minimum of two u64 values.
    Input stack:  [b_lo, b_hi, a_lo, a_hi] ++ rest
    Output stack: [min_lo, min_hi] ++ rest
    If b > a (as u64), returns a; otherwise returns b. -/
theorem u64_min_correct
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest)
    (ha_lo : a_lo.isU32 = true) (ha_hi : a_hi.isU32 = true)
    (hb_lo : b_lo.isU32 = true) (hb_hi : b_hi.isU32 = true) :
    execWithEnv u64ProcEnv 20 s Miden.Core.U64.min =
    some (s.withStack (
      let borrow_lo := decide (a_lo.val < b_lo.val)
      let borrow_hi := decide (a_hi.val < b_hi.val)
      let hi_eq := Felt.ofNat (u32OverflowingSub a_hi.val b_hi.val).2 == (0 : Felt)
      let is_gt := borrow_hi || (hi_eq && borrow_lo)
      (if is_gt then a_lo else b_lo) ::
      (if is_gt then a_hi else b_hi) :: rest)) := by
  -- Setup: unfold min, resolve ProcEnv, unfold gt body
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold Miden.Core.U64.min execWithEnv
  simp only [List.foldlM, u64ProcEnv]
  dsimp only [bind, Bind.bind, Option.bind]
  unfold Miden.Core.U64.gt execWithEnv
  simp only [List.foldlM, bind, Bind.bind, Option.bind, pure, Pure.pure]
  -- Instruction 1: movup 3
  miden_step
  -- Instruction 2: movup 3
  miden_step
  -- Instruction 3: dupw 0
  miden_step
  -- gt body (13 instructions)
  miden_step  -- movup 3
  miden_step  -- movup 3
  miden_step  -- movup 2
  miden_step  -- swap 1
  miden_step  -- u32OverflowSub
  miden_step  -- movdn 3
  miden_step  -- drop
  miden_step  -- u32OverflowSub
  miden_step  -- swap 1
  miden_step  -- eqImm 0
  miden_step  -- movup 2
  -- and: need to rewrite borrow first
  rw [u32OverflowingSub_borrow_ite a_lo.val b_lo.val]
  miden_step  -- and
  rw [u32OverflowingSub_borrow_ite a_hi.val b_hi.val]
  miden_step  -- or
  -- Instruction 5: movup 4
  miden_step
  -- Instruction 6: movup 3
  miden_step
  -- Instruction 7: dup 2
  miden_step
  -- Instruction 8: cdrop
  miden_step
  -- Instruction 9: movdn 3
  miden_step
  -- Instruction 10: cdrop
  rw [stepCdropIte]

end MidenLean.Proofs
