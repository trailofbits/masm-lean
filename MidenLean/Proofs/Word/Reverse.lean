import MidenLean.Generated.Word
import MidenLean.Proofs.StepLemmas

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas

/-- `word::reverse` reverses the first four stack elements.
    Input stack:  [a, b, c, d] ++ rest
    Output stack: [d, c, b, a] ++ rest -/
theorem word_reverse_correct (a b c d : Felt) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = a :: b :: c :: d :: rest) :
    execProcedure emptyEnv 10 s Miden.Core.Word.reverse =
    some (s.withStack (d :: c :: b :: a :: rest)) := by
  obtain ⟨stk, mem, frames, adv⟩ := s
  simp only [Concrete.State.withStack] at hs ⊢
  subst hs
  unfold Miden.Core.Word.reverse execProcedure
  simp only [List.foldlM]
  rw [stepReversew]
  dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]

end MidenLean.Proofs
