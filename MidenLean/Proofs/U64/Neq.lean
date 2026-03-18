import MidenLean.Proofs.Tactics
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 4000000 in
/-- u64.neq correctly tests inequality of two u64 values.
    Input stack:  [b_lo, b_hi, a_lo, a_hi] ++ rest
    Output stack: [result] ++ rest
    where result = 1 iff b_lo != a_lo || b_hi != a_hi, else 0. -/
theorem u64_neq_correct (b_lo b_hi a_lo a_hi : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest) :
    exec 10 s Miden.Core.U64.neq =
    some (s.withStack (
      (if (b_lo != a_lo) || (b_hi != a_hi)
       then (1 : Felt) else 0) :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.U64.neq execWithEnv
  simp only [List.foldlM]
  change (do
    let s' ← execInstruction ⟨b_lo :: b_hi :: a_lo :: a_hi :: rest, mem, locs, adv⟩ (.movup 2)
    let s' ← execInstruction s' (.neq)
    let s' ← execInstruction s' (.swap 2)
    let s' ← execInstruction s' (.neq)
    let s' ← execInstruction s' Instruction.or
    pure s') = _
  miden_movup
  rw [stepNeq]; miden_bind
  miden_swap
  rw [stepNeq]; miden_bind
  rw [stepOrIte]; dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]

end MidenLean.Proofs
