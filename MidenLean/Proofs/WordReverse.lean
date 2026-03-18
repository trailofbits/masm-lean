import MidenLean.Proofs.StepLemmas
import MidenLean.Generated.Word

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas

set_option maxHeartbeats 400000 in
theorem word_reverse_correct (a b c d : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = a :: b :: c :: d :: rest) :
    exec 4 s Miden.Core.Word.reverse =
    some (s.withStack (d :: c :: b :: a :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.Word.reverse execWithEnv
  simp only [List.foldlM]
  rw [stepReverseW]; rfl

end MidenLean.Proofs
