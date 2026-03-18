import MidenLean.Proofs.U64
import MidenLean.Proofs.Tactics
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 8000000 in
/-- u64.gte correctly compares two u64 values.
    Input stack:  [b_lo, b_hi, a_lo, a_hi] ++ rest
    Output stack: [result] ++ rest
    where result = 1 iff a ≥ b (as u64), else 0.
    Computed as !(a < b). -/
theorem u64_gte_correct
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest)
    (ha_lo : a_lo.isU32 = true) (ha_hi : a_hi.isU32 = true)
    (hb_lo : b_lo.isU32 = true) (hb_hi : b_hi.isU32 = true) :
    execWithEnv u64ProcEnv 20 s Miden.Core.U64.gte =
    some (s.withStack (
      let borrow_lo := decide (a_lo.val < b_lo.val)
      let borrow_hi := decide (a_hi.val < b_hi.val)
      let hi_eq := Felt.ofNat (u32OverflowingSub a_hi.val b_hi.val).2 == (0 : Felt)
      (if !(borrow_hi || (hi_eq && borrow_lo)) then (1 : Felt) else 0) :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  -- Unfold gte and resolve ProcEnv
  unfold Miden.Core.U64.gte execWithEnv
  simp only [List.foldlM, u64ProcEnv]
  dsimp only [bind, Bind.bind, Option.bind]
  -- Unfold lt body
  unfold Miden.Core.U64.lt execWithEnv
  simp only [List.foldlM, bind, Bind.bind, Option.bind, pure, Pure.pure]
  -- Step through lt body
  miden_movup; miden_movup; miden_movup
  rw [stepU32OverflowSub (ha := by assumption) (hb := by assumption)]; dsimp only []
  miden_movdn
  rw [stepDrop]; dsimp only []
  miden_swap
  rw [stepU32OverflowSub (ha := by assumption) (hb := by assumption)]; dsimp only []
  miden_swap
  rw [stepEqImm]; dsimp only []
  miden_movup
  -- Convert borrow_lo to boolean ite form for stepAndIte
  rw [u32OverflowingSub_borrow_ite a_lo.val b_lo.val]
  rw [stepAndIte]; dsimp only []
  -- Convert borrow_hi to boolean ite form for stepOrIte
  rw [u32OverflowingSub_borrow_ite a_hi.val b_hi.val]
  rw [stepOrIte]; dsimp only []
  -- not
  rw [stepNotIte]

end MidenLean.Proofs
