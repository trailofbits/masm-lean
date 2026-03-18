import MidenLean.Proofs.Tactics
import MidenLean.Generated.Word

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 4000000 in
/-- word.arrange_words_adjacent_le correctly interleaves two words for comparison.
    Input stack:  [a0, a1, a2, a3, b0, b1, b2, b3] ++ rest
    Output stack: [b3, a3, b2, a2, b1, a1, b0, a0] ++ rest -/
theorem word_arrange_words_adjacent_le_correct
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 :: rest) :
    exec 20 s Miden.Core.Word.arrange_words_adjacent_le =
    some (s.withStack (b3 :: a3 :: b2 :: a2 :: b1 :: a1 :: b0 :: a0 :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.Word.arrange_words_adjacent_le execWithEnv
  simp only [List.foldlM]
  miden_step  -- movup 7
  miden_step  -- movup 4
  miden_step  -- swap 1
  miden_step  -- movup 7
  miden_step  -- movdn 2
  miden_step  -- movup 5
  miden_step  -- movdn 3
  miden_step  -- movup 7
  miden_step  -- movdn 4
  miden_step  -- movup 6
  miden_step  -- movdn 5
  miden_step  -- movup 7
  miden_step  -- movdn 6
  dsimp only [pure, Pure.pure]

end MidenLean.Proofs
