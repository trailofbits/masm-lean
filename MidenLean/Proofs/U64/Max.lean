import MidenLean.Proofs.U64
import MidenLean.Proofs.Tactics
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean

set_option maxHeartbeats 16000000 in
/-- u64.max correctly computes the maximum of two u64 values.
    Input stack:  [b_lo, b_hi, a_lo, a_hi] ++ rest
    Output stack: [max_lo, max_hi] ++ rest
    lt is called on [a_lo, a_hi, b_lo, b_hi], computing b < a.
    If b < a, returns a; otherwise returns b. -/
theorem u64_max_correct
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest) :
    execWithEnv u64ProcEnv 20 s Miden.Core.U64.max =
    some (s.withStack (
      let borrow_lo := decide (b_lo.val < a_lo.val)
      let borrow_hi := decide (b_hi.val < a_hi.val)
      let hi_eq := Felt.ofNat (u32OverflowingSub b_hi.val a_hi.val).2 == (0 : Felt)
      let is_lt := borrow_hi || (hi_eq && borrow_lo)
      (if is_lt then a_lo else b_lo) ::
      (if is_lt then a_hi else b_hi) :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  -- Unfold max, resolve ProcEnv, then unfold lt body
  unfold Miden.Core.U64.max execWithEnv
  simp only [List.foldlM, u64ProcEnv]
  dsimp only [bind, Bind.bind, Option.bind]
  unfold Miden.Core.U64.lt execWithEnv
  simp only [List.foldlM, bind, Bind.bind, Option.bind, pure, Pure.pure]
  -- max preamble: movup 3; movup 3; dupw 0
  miden_movup; miden_movup
  rw [execInstruction_dupw]; unfold execDupw; dsimp [MidenState.withStack, MidenState.stack,
    List.getElem?_cons_succ, List.getElem?_cons_zero]
  -- lt body: movup 3; movup 3; movup 2; u32OverflowSub; movdn 3; drop;
  --          swap 1; u32OverflowSub; swap 1; eqImm 0; movup 2; and; or
  miden_movup; miden_movup; miden_movup
  rw [execInstruction_u32OverflowSub]; unfold execU32OverflowSub; dsimp only [MidenState.withStack]
  miden_movdn
  rw [execInstruction_drop]; unfold execDrop; dsimp only [MidenState.withStack]
  miden_swap
  rw [execInstruction_u32OverflowSub]; unfold execU32OverflowSub; dsimp only [MidenState.withStack]
  miden_swap
  rw [execInstruction_eqImm]; unfold execEqImm; dsimp only [MidenState.withStack]
  miden_movup
  rw [u32OverflowingSub_borrow_ite b_lo.val a_lo.val]
  rw [execInstruction_and, execAnd_ite]; dsimp only [MidenState.withStack]
  rw [u32OverflowingSub_borrow_ite b_hi.val a_hi.val]
  rw [execInstruction_or, execOr_ite]; dsimp only [MidenState.withStack]
  -- max postamble: movup 4; movup 3; dup 2; cdrop; movdn 3; cdrop
  miden_movup; miden_movup
  miden_dup
  rw [execInstruction_cdrop, execCdrop_ite]; miden_bind
  miden_movdn
  rw [execInstruction_cdrop, execCdrop_ite]

end MidenLean.Proofs
