import MidenLean.Proofs.Tactics
import MidenLean.Generated.Word

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 4000000 in
/-- `word::eqz` correctly tests whether a word is zero.
    Input stack:  [a, b, c, d] ++ rest
    Output stack: [is_zero] ++ rest
    where is_zero = 1 iff all four input elements are zero. -/
theorem word_eqz_correct
    (a b c d : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = a :: b :: c :: d :: rest) :
    exec 25 s Miden.Core.Word.eqz =
    some (s.withStack (
      (if (a == (0 : Felt)) && (b == (0 : Felt)) && (c == (0 : Felt)) && (d == (0 : Felt))
       then (1 : Felt) else 0) :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.Word.eqz execWithEnv
  simp only [List.foldlM]
  rw [stepEqImm]
  miden_bind
  miden_loop
  miden_swap
  rw [stepEqImm]
  miden_bind
  rw [stepAndIte]
  miden_bind
  miden_loop
  miden_swap
  rw [stepEqImm]
  miden_bind
  rw [stepAndIte]
  miden_bind
  miden_loop
  miden_swap
  rw [stepEqImm]
  miden_bind
  rw [stepAndIte]
  miden_bind
  miden_loop
  simp only [pure, Pure.pure]

end MidenLean.Proofs
