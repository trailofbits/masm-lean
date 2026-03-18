import MidenLean.Proofs.Tactics
import MidenLean.Generated.Word

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 4000000 in
theorem word_test_eq_correct (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 :: rest) :
    exec 15 s Miden.Core.Word.test_eq =
    some (s.withStack (
      (if b3 == a3 && b2 == a2 && b1 == a1 && b0 == a0 then (1 : Felt) else 0) ::
      a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.Word.test_eq execWithEnv
  simp only [List.foldlM]
  change (do
    let s' ← execInstruction ⟨a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 :: rest, mem, locs, adv⟩ (.dup 7)
    let s' ← execInstruction s' (.dup 4)
    let s' ← execInstruction s' (.eq)
    let s' ← execInstruction s' (.dup 7)
    let s' ← execInstruction s' (.dup 4)
    let s' ← execInstruction s' (.eq)
    let s' ← execInstruction s' (.and)
    let s' ← execInstruction s' (.dup 6)
    let s' ← execInstruction s' (.dup 3)
    let s' ← execInstruction s' (.eq)
    let s' ← execInstruction s' (.and)
    let s' ← execInstruction s' (.dup 5)
    let s' ← execInstruction s' (.dup 2)
    let s' ← execInstruction s' (.eq)
    let s' ← execInstruction s' (.and)
    pure s') = _
  miden_dup
  miden_dup
  rw [stepEq]; miden_bind
  miden_dup
  miden_dup
  rw [stepEq]; miden_bind
  rw [stepAndIte]; miden_bind
  miden_dup
  miden_dup
  rw [stepEq]; miden_bind
  rw [stepAndIte]; miden_bind
  miden_dup
  miden_dup
  rw [stepEq]; miden_bind
  rw [stepAndIte]; miden_bind
  dsimp only [pure, Pure.pure]

end MidenLean.Proofs
