import MidenLean.Proofs.U64
import MidenLean.Proofs.Tactics
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 8000000 in
/-- u64.lte correctly compares two u64 values.
    Input stack:  [b_lo, b_hi, a_lo, a_hi] ++ rest
    Output stack: [result] ++ rest
    where result = 1 iff a ≤ b (as u64), else 0.
    Computed as !(a > b). -/
theorem u64_lte_correct
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest) :
    execWithEnv u64ProcEnv 20 s Miden.Core.Math.U64.lte =
    some (s.withStack (
      let borrow_lo := decide (b_lo.val < a_lo.val)
      let borrow_hi := decide (b_hi.val < a_hi.val)
      let hi_eq := Felt.ofNat (u32OverflowingSub b_hi.val a_hi.val).2 == (0 : Felt)
      (if !(borrow_hi || (hi_eq && borrow_lo)) then (1 : Felt) else 0) :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  -- Unfold lte and resolve ProcEnv
  unfold Miden.Core.Math.U64.lte execWithEnv
  simp only [List.foldlM, u64ProcEnv]
  dsimp only [bind, Bind.bind, Option.bind]
  -- Unfold gt body
  unfold Miden.Core.Math.U64.gt execWithEnv
  simp only [List.foldlM, bind, Bind.bind, Option.bind, pure, Pure.pure]
  -- Step through gt body
  miden_movup; miden_movup; miden_movup
  miden_swap
  rw [stepU32OverflowSub]; dsimp only []
  miden_movdn
  rw [stepDrop]; dsimp only []
  rw [stepU32OverflowSub]; dsimp only []
  miden_swap
  rw [stepEqImm]; dsimp only []
  miden_movup
  -- Convert borrow_lo to boolean ite form for stepAndIte
  rw [u32OverflowingSub_borrow_ite b_lo.val a_lo.val]
  rw [stepAndIte]; dsimp only []
  -- Convert borrow_hi to boolean ite form for stepOrIte
  rw [u32OverflowingSub_borrow_ite b_hi.val a_hi.val]
  rw [stepOrIte]; dsimp only []
  -- not
  rw [stepNotIte]

end MidenLean.Proofs
