import MidenLean.Proofs.Tactics
import MidenLean.Generated.U128

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

/-- `u128::neq` correctly tests inequality of two 128-bit values.
    Input stack:  [b0, b1, b2, b3, a0, a1, a2, a3] ++ rest
    Output stack: [result] ++ rest
    where result = 1 iff some limb of `a` differs from the corresponding limb of `b`. -/
theorem u128_neq_correct
    (b0 b1 b2 b3 a0 a1 a2 a3 : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest) :
    exec 19 s Miden.Core.U128.neq =
    some (s.withStack (
      (if (b0 != a0) || (a1 != b1) || (a2 != b2) || (a3 != b3)
       then (1 : Felt) else 0) :: rest)) := by
  obtain ⟨stk, mem, locs, adv, evts⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.U128.neq execWithEnv
  simp only [List.foldlM]
  miden_movup
  rw [stepNeq]
  miden_bind
  miden_movup
  miden_movup
  rw [stepNeq]
  miden_bind
  rw [stepOrIte]
  miden_bind
  miden_movup
  miden_movup
  rw [stepNeq]
  miden_bind
  rw [stepOrIte]
  miden_bind
  miden_movup
  miden_movup
  rw [stepNeq]
  miden_bind
  rw [stepOrIte]
  dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]

end MidenLean.Proofs
