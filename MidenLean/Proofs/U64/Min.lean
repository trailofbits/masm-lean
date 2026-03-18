import MidenLean.Proofs.U64
import MidenLean.Proofs.Tactics
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean

set_option maxHeartbeats 16000000 in
/-- u64.min correctly computes the minimum of two u64 values.
    Input stack:  [b_lo, b_hi, a_lo, a_hi] ++ rest
    Output stack: [min_lo, min_hi] ++ rest
    If b > a (as u64), returns a; otherwise returns b. -/
theorem u64_min_correct
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest) :
    execWithEnv u64ProcEnv 20 s Miden.Core.U64.min =
    some (s.withStack (
      let borrow_lo := decide (a_lo.val < b_lo.val)
      let borrow_hi := decide (a_hi.val < b_hi.val)
      let hi_eq := Felt.ofNat (u32OverflowingSub a_hi.val b_hi.val).2 == (0 : Felt)
      let is_gt := borrow_hi || (hi_eq && borrow_lo)
      (if is_gt then a_lo else b_lo) ::
      (if is_gt then a_hi else b_hi) :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  -- Unfold min, resolve ProcEnv, then unfold gt body
  unfold Miden.Core.U64.min execWithEnv
  simp only [List.foldlM, u64ProcEnv]
  dsimp only [bind, Bind.bind, Option.bind]
  unfold Miden.Core.U64.gt execWithEnv
  simp only [List.foldlM, bind, Bind.bind, Option.bind, pure, Pure.pure]
  -- Now we have a flat chain of execInstruction calls.
  -- min preamble: movup 3; movup 3; dupw 0
  miden_movup; miden_movup
  rw [execInstruction_dupw]; unfold execDupw; dsimp [MidenState.withStack, MidenState.stack,
    List.getElem?_cons_succ, List.getElem?_cons_zero]
  -- gt body: movup 3; movup 3; movup 2; swap 1; u32OverflowSub; movdn 3; drop;
  --          u32OverflowSub; swap 1; eqImm 0; movup 2; and; or
  miden_movup; miden_movup; miden_movup
  miden_swap
  rw [execInstruction_u32OverflowSub]; unfold execU32OverflowSub; dsimp only [MidenState.withStack]
  miden_movdn
  rw [execInstruction_drop]; unfold execDrop; dsimp only [MidenState.withStack]
  rw [execInstruction_u32OverflowSub]; unfold execU32OverflowSub; dsimp only [MidenState.withStack]
  miden_swap
  rw [execInstruction_eqImm]; unfold execEqImm; dsimp only [MidenState.withStack]
  miden_movup
  rw [u32OverflowingSub_borrow_ite a_lo.val b_lo.val]
  rw [execInstruction_and, execAnd_ite]; dsimp only [MidenState.withStack]
  rw [u32OverflowingSub_borrow_ite a_hi.val b_hi.val]
  rw [execInstruction_or, execOr_ite]; dsimp only [MidenState.withStack]
  -- min postamble: movup 4; movup 3; dup 2; cdrop; movdn 3; cdrop
  miden_movup; miden_movup
  miden_dup
  rw [execInstruction_cdrop, execCdrop_ite]; miden_bind
  miden_movdn
  rw [execInstruction_cdrop, execCdrop_ite]

end MidenLean.Proofs
