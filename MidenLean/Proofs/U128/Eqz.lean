import MidenLean.Proofs.Tactics
import MidenLean.Generated.U128

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 4000000 in
/-- u128.eqz correctly tests whether a 128-bit value is zero.
    Input stack:  [a, b, c, d] ++ rest
    Output stack: [is_zero] ++ rest
    where is_zero = 1 iff all four input limbs are zero. -/
theorem u128_eqz_correct
    (a b c d : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = a :: b :: c :: d :: rest) :
    exec 15 s Miden.Core.U128.eqz =
    some (s.withStack (
      (if (a == (0 : Felt)) && (b == (0 : Felt)) && (c == (0 : Felt)) && (d == (0 : Felt))
       then (1 : Felt) else 0) :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.U128.eqz execWithEnv
  simp only [List.foldlM]
  rw [stepEqImm]
  miden_bind
  miden_swap
  rw [stepEqImm]
  miden_bind
  rw [stepAndIte]
  miden_bind
  miden_swap
  rw [stepEqImm]
  miden_bind
  rw [stepAndIte]
  miden_bind
  miden_swap
  rw [stepEqImm]
  miden_bind
  rw [stepAndIte]
  dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]

end MidenLean.Proofs
