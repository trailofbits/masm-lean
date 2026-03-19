import MidenLean.Proofs.Tactics
import MidenLean.Generated.Word

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 4000000 in
/-- `word::test_eq` correctly tests equality of two words without consuming inputs.
    Input stack:  [a0, a1, a2, a3, b0, b1, b2, b3] ++ rest
    Output stack: [result, a0, a1, a2, a3, b0, b1, b2, b3] ++ rest
    where result = 1 iff all corresponding elements are equal, else 0. -/
theorem word_test_eq_correct (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt)
    (s : MidenState)
    (hs : s.stack = a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 :: rest) :
    exec 20 s Miden.Core.Word.test_eq =
    some (s.withStack (
      (if (b3 == a3) && (b2 == a2) && (b1 == a1) && (b0 == a0)
       then (1 : Felt) else 0) ::
      a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.Word.test_eq execWithEnv
  simp only [List.foldlM]
  miden_step  -- dup 7
  miden_step  -- dup 4
  miden_step  -- eq
  miden_step  -- dup 7
  miden_step  -- dup 4
  miden_step  -- eq
  miden_step  -- and
  miden_step  -- dup 6
  miden_step  -- dup 3
  miden_step  -- eq
  miden_step  -- and
  miden_step  -- dup 5
  miden_step  -- dup 2
  miden_step  -- eq
  miden_step  -- and
  dsimp only [pure, Pure.pure]

end MidenLean.Proofs
