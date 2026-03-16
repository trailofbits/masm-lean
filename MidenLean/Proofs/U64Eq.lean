import MidenLean.Proofs.StepLemmas
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas

set_option maxHeartbeats 4000000 in
/-- u64.eq correctly tests equality of two u64 values.
    Input stack:  [b_lo, b_hi, a_lo, a_hi] ++ rest
    Output stack: [result] ++ rest
    where result = 1 iff b_lo == a_lo && b_hi == a_hi, else 0. -/
theorem u64_eq_correct (b_lo b_hi a_lo a_hi : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest) :
    exec 10 s Miden.Core.Math.U64.eq =
    some (s.withStack (
      (if (b_lo == a_lo) && (b_hi == a_hi)
       then (1 : Felt) else 0) :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.Math.U64.eq execOps
  simp only [List.foldlM]
  change (do
    let s' ← stepInstruction ⟨b_lo :: b_hi :: a_lo :: a_hi :: rest, mem, locs, adv⟩ (.movup 2)
    let s' ← stepInstruction s' (.eq)
    let s' ← stepInstruction s' (.swap 2)
    let s' ← stepInstruction s' (.eq)
    let s' ← stepInstruction s' Instruction.and
    pure s') = _
  rw [stepMovup2]; dsimp only [bind, Bind.bind, Option.bind]
  rw [stepEq]; dsimp only [bind, Bind.bind, Option.bind]
  rw [stepSwap (hn := by decide) (htop := rfl) (hnth := rfl)]
  dsimp only [bind, Bind.bind, Option.bind, List.set]
  rw [stepEq]; dsimp only [bind, Bind.bind, Option.bind]
  rw [stepAndIte]; dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]

end MidenLean.Proofs
