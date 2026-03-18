import MidenLean.Proofs.Tactics
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 4000000 in
/-- u64.eq correctly tests equality of two u64 values.
    Input stack:  [b_lo, b_hi, a_lo, a_hi] ++ rest
    Output stack: [result] ++ rest
    where result = 1 iff b_lo == a_lo && b_hi == a_hi, else 0. -/
theorem u64_eq_correct (b_lo b_hi a_lo a_hi : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest) :
    exec 10 s Miden.Core.U64.eq =
    some (s.withStack (
      (if (b_lo == a_lo) && (b_hi == a_hi)
       then (1 : Felt) else 0) :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.U64.eq execWithEnv
  simp only [List.foldlM]
  change (do
    let s' ← execInstruction ⟨b_lo :: b_hi :: a_lo :: a_hi :: rest, mem, locs, adv⟩ (.movup 2)
    let s' ← execInstruction s' (.eq)
    let s' ← execInstruction s' (.swap 2)
    let s' ← execInstruction s' (.eq)
    let s' ← execInstruction s' Instruction.and
    pure s') = _
  miden_movup
  rw [stepEq]; miden_bind
  miden_swap
  rw [stepEq]; miden_bind
  rw [stepAndIte]; dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]

end MidenLean.Proofs
