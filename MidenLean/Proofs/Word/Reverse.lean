import MidenLean.Proofs.Tactics
import MidenLean.Generated.Word

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

/-- word.reverse correctly reverses the first four stack elements.
    Input stack:  [a, b, c, d] ++ rest
    Output stack: [d, c, b, a] ++ rest -/
theorem word_reverse_correct (a b c d : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = a :: b :: c :: d :: rest) :
    exec 10 s Miden.Core.Word.reverse =
    some (s.withStack (d :: c :: b :: a :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.Word.reverse execWithEnv
  simp only [List.foldlM]
  rw [stepReversew]
  dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]

end MidenLean.Proofs
