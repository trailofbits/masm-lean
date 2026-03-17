import MidenLean.Proofs.Tactics
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 8000000 in
/-- u64.lt correctly compares two u64 values.
    Input stack:  [b_lo, b_hi, a_lo, a_hi] ++ rest
    Output stack: [result] ++ rest
    where result = 1 iff a < b (as u64), else 0.
    The comparison is: a_hi < b_hi, or (a_hi == b_hi and a_lo < b_lo). -/
theorem u64_lt_correct
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest) :
    exec 20 s Miden.Core.Math.U64.lt =
    some (s.withStack (
      let borrow_lo := decide (a_lo.val < b_lo.val)
      let borrow_hi := decide (a_hi.val < b_hi.val)
      let hi_eq := Felt.ofNat (u32OverflowingSub a_hi.val b_hi.val).2 == (0 : Felt)
      (if borrow_hi || (hi_eq && borrow_lo) then (1 : Felt) else 0) :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.Math.U64.lt execWithEnv
  simp only [List.foldlM]
  change (do
    let s' ← execInstruction ⟨b_lo :: b_hi :: a_lo :: a_hi :: rest, mem, locs, adv⟩ (.movup 3)
    let s' ← execInstruction s' (.movup 3)
    let s' ← execInstruction s' (.movup 2)
    let s' ← execInstruction s' (.u32OverflowSub)
    let s' ← execInstruction s' (.movdn 3)
    let s' ← execInstruction s' (.drop)
    let s' ← execInstruction s' (.swap 1)
    let s' ← execInstruction s' (.u32OverflowSub)
    let s' ← execInstruction s' (.swap 1)
    let s' ← execInstruction s' (.eqImm 0)
    let s' ← execInstruction s' (.movup 2)
    let s' ← execInstruction s' Instruction.and
    let s' ← execInstruction s' Instruction.or
    pure s') = _
  miden_movup; miden_movup; miden_movup
  rw [stepU32OverflowSub]; miden_bind
  miden_movdn
  rw [stepDrop]; miden_bind
  miden_swap
  rw [stepU32OverflowSub]; miden_bind
  miden_swap
  rw [stepEqImm]; miden_bind
  miden_movup
  -- Convert borrow_lo to boolean ite form for stepAndIte
  rw [u32OverflowingSub_borrow_ite a_lo.val b_lo.val]
  rw [stepAndIte]; miden_bind
  -- Convert borrow_hi to boolean ite form for stepOrIte
  rw [u32OverflowingSub_borrow_ite a_hi.val b_hi.val]
  rw [stepOrIte]; dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]

end MidenLean.Proofs
