import MidenLean.Proofs.Tactics
import MidenLean.Generated.Word

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

-- Trace through arrange_words_adjacent_le
-- Input stack layout: [b0, b1, b2, b3, a0, a1, a2, a3] ++ rest
-- (where b is the lower word, a is the upper word)
--
-- The sequence performs 13 stack operations to rearrange to
-- output format needed by word::gt/lt which is:
-- [a0, b3, a2, b2, a3, a1, b1, b0] ++ rest

set_option maxHeartbeats 4000000 in
theorem word_arrange_words_adjacent_le_correct
    (b0 b1 b2 b3 a0 a1 a2 a3 : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest) :
    exec 13 s Miden.Core.Word.arrange_words_adjacent_le =
    some (s.withStack (a3 :: b3 :: a2 :: b2 :: a1 :: b1 :: a0 :: b0 :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.Word.arrange_words_adjacent_le execWithEnv
  simp only [List.foldlM]
  change (do
    let s' ← execInstruction ⟨b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv⟩ (.movup 7)
    let s' ← execInstruction s' (.movup 4)
    let s' ← execInstruction s' (.swap 1)
    let s' ← execInstruction s' (.movup 7)
    let s' ← execInstruction s' (.movdn 2)
    let s' ← execInstruction s' (.movup 5)
    let s' ← execInstruction s' (.movdn 3)
    let s' ← execInstruction s' (.movup 7)
    let s' ← execInstruction s' (.movdn 4)
    let s' ← execInstruction s' (.movup 6)
    let s' ← execInstruction s' (.movdn 5)
    let s' ← execInstruction s' (.movup 7)
    let s' ← execInstruction s' (.movdn 6)
    pure s') = _
  miden_movup
  miden_movup
  miden_swap
  miden_movup
  miden_movdn
  miden_movup
  miden_movdn
  miden_movup
  miden_movdn
  miden_movup
  miden_movdn
  miden_movup
  miden_movdn
  dsimp only [pure, Pure.pure]

end MidenLean.Proofs
