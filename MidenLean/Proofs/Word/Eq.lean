import MidenLean.Proofs.Tactics
import MidenLean.Generated.Word

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 4000000 in
/-- `word::eq` correctly tests equality of two words.
    Input stack:  [a0, a1, a2, a3, b0, b1, b2, b3] ++ rest
    Output stack: [result] ++ rest
    where result = 1 iff a0=b0 /\ a1=b1 /\ a2=b2 /\ a3=b3, else 0. -/
theorem word_eq_correct (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 :: rest) :
    exec 20 s Miden.Core.Word.eq =
    some (s.withStack (
      (if (a0 == b0) && (a1 == b1) && (a2 == b2) && (b3 == a3)
       then (1 : Felt) else 0) :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.Word.eq execWithEnv
  simp only [List.foldlM]
  miden_step  -- movup 4
  miden_step  -- eq
  miden_step  -- swap 1
  miden_step  -- movup 4
  miden_step  -- eq
  miden_step  -- and
  miden_step  -- swap 1
  miden_step  -- movup 3
  miden_step  -- eq
  miden_step  -- and
  miden_step  -- movdn 2
  miden_step  -- eq
  miden_step  -- and
  dsimp only [pure, Pure.pure]

end MidenLean.Proofs
