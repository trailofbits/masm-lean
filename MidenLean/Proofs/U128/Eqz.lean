import MidenLean.Proofs.U128.Common
import MidenLean.Proofs.Tactics
import MidenLean.Generated.U128

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 4000000 in
theorem u128_eqz_raw
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

/-- `u128::eqz` tests whether a 128-bit value is zero.
    Input stack:  [a.a0, a.a1, a.a2, a.a3] ++ rest
    Output stack: [(if a == 0 then 1 else 0)] ++ rest -/
theorem u128_eqz_correct (a : U128) (rest : List Felt) (s : MidenState)
    (hs : s.stack = a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val :: rest) :
    exec 15 s Miden.Core.U128.eqz =
    some (s.withStack (
      (if a == U128.ofNat 0 then (1 : Felt) else 0) :: rest)) := by
  simp only [U128.beq_iff, U128.ofNat]
  exact u128_eqz_raw a.a0.val a.a1.val a.a2.val a.a3.val rest s hs

end MidenLean.Proofs
