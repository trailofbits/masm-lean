import MidenLean.Proofs.Tactics
import MidenLean.Generated.Word

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 4000000 in
theorem word_eq_correct (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 :: rest) :
    exec 13 s Miden.Core.Word.eq =
    some (s.withStack (
      (if a0 == b0 && a1 == b1 && a2 == b2 && b3 == a3 then (1 : Felt) else 0) :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.Word.eq execWithEnv
  simp only [List.foldlM]
  change (do
    let s' ← execInstruction ⟨a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 :: rest, mem, locs, adv⟩ (.movup 4)
    let s' ← execInstruction s' (.eq)
    let s' ← execInstruction s' (.swap 1)
    let s' ← execInstruction s' (.movup 4)
    let s' ← execInstruction s' (.eq)
    let s' ← execInstruction s' (.and)
    let s' ← execInstruction s' (.swap 1)
    let s' ← execInstruction s' (.movup 3)
    let s' ← execInstruction s' (.eq)
    let s' ← execInstruction s' (.and)
    let s' ← execInstruction s' (.movdn 2)
    let s' ← execInstruction s' (.eq)
    let s' ← execInstruction s' (.and)
    pure s') = _
  miden_movup
  rw [stepEq]; miden_bind
  miden_swap
  miden_movup
  rw [stepEq]; miden_bind
  rw [stepAndIte]; miden_bind
  miden_swap
  miden_movup
  rw [stepEq]; miden_bind
  rw [stepAndIte]; miden_bind
  miden_movdn
  rw [stepEq]; miden_bind
  rw [stepAndIte]; miden_bind
  dsimp only [pure, Pure.pure]

end MidenLean.Proofs
