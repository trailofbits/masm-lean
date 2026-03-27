import MidenLean.Proofs.U128.Common
import MidenLean.Proofs.Tactics
import MidenLean.Generated.U128

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 4000000 in
theorem u128_eq_raw
    (b0 b1 b2 b3 a0 a1 a2 a3 : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest) :
    exec 19 s Miden.Core.U128.eq =
    some (s.withStack (
      (if (b0 == a0) && (a1 == b1) && (a2 == b2) && (a3 == b3)
       then (1 : Felt) else 0) :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.U128.eq execWithEnv
  simp only [List.foldlM]
  miden_movup
  rw [stepEq]
  miden_bind
  miden_movup
  miden_movup
  rw [stepEq]
  miden_bind
  rw [stepAndIte]
  miden_bind
  miden_movup
  miden_movup
  rw [stepEq]
  miden_bind
  rw [stepAndIte]
  miden_bind
  miden_movup
  miden_movup
  rw [stepEq]
  miden_bind
  rw [stepAndIte]
  dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]

/-- `u128::eq` tests equality of two 128-bit values.
    Input stack:  [b.a0, b.a1, b.a2, b.a3, a.a0, a.a1, a.a2, a.a3] ++ rest
    Output stack: [(if a == b then 1 else 0)] ++ rest -/
theorem u128_eq_correct (a b : U128) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val ::
                    a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val :: rest) :
    exec 19 s Miden.Core.U128.eq =
    some (s.withStack (
      (if (a == b) then (1 : Felt) else 0) :: rest)) := by
  rw [u128_eq_raw b.a0.val b.a1.val b.a2.val b.a3.val
    a.a0.val a.a1.val a.a2.val a.a3.val rest s hs]
  simp only [U128.beq_iff, Bool.beq_comm (a := b.a0.val), Bool.and_comm,
    Bool.and_left_comm]

end MidenLean.Proofs
