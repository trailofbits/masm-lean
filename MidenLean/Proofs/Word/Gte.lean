import MidenLean.Proofs.Word.Lt

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

/-- `word::gte` correctly checks whether one word is greater than or equal to another. -/
theorem word_gte_correct
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 :: rest) :
    let result := decide (a3.val > b3.val)
                  || ((b3 == a3) && decide (a2.val > b2.val))
                  || ((b3 == a3) && (b2 == a2) && decide (a1.val > b1.val))
                  || ((b3 == a3) && (b2 == a2) && (b1 == a1) && decide (a0.val > b0.val))
    execWithEnv wordProcEnv 4 s Miden.Core.Word.gte =
    some (s.withStack ((if !result then (1:Felt) else 0) :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold Miden.Core.Word.gte execWithEnv
  simp only [List.foldlM, wordProcEnv]
  dsimp only [bind, Bind.bind, Option.bind]
  rw [show execWithEnv wordProcEnv 3
    ⟨a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 :: rest, mem, locs, adv⟩
    Miden.Core.Word.lt =
    some ⟨(if decide (a3.val > b3.val)
            || ((b3 == a3) && decide (a2.val > b2.val))
            || ((b3 == a3) && (b2 == a2) && decide (a1.val > b1.val))
            || ((b3 == a3) && (b2 == a2) && (b1 == a1) && decide (a0.val > b0.val))
           then (1:Felt) else 0) :: rest, mem, locs, adv⟩
    from word_lt_correct a0 a1 a2 a3 b0 b1 b2 b3 rest
      ⟨_, mem, locs, adv⟩ rfl]
  dsimp only [bind, Bind.bind, Option.bind]
  rw [stepNotIte]
  dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]

end MidenLean.Proofs
