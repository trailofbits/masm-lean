import Mathlib.Data.Nat.Bitwise
import MidenLean.Proofs.Tactics
import MidenLean.Generated.U128

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 4000000 in
/-- `u128::and` correctly computes bitwise AND of two 128-bit values.
    Input stack:  [b0, b1, b2, b3, a0, a1, a2, a3] ++ rest
    Output stack: [b0 &&& a0, b1 &&& a1, b2 &&& a2, b3 &&& a3] ++ rest. -/
theorem u128_and_correct
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (ha2 : a2.isU32 = true) (ha3 : a3.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true)
    (hb2 : b2.isU32 = true) (hb3 : b3.isU32 = true) :
    exec 17 s Miden.Core.U128.and =
    some (s.withStack (
      Felt.ofNat (b0.val &&& a0.val) ::
      Felt.ofNat (b1.val &&& a1.val) ::
      Felt.ofNat (b2.val &&& a2.val) ::
      Felt.ofNat (b3.val &&& a3.val) :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.U128.and execWithEnv
  simp only [List.foldlM]
  miden_movup
  rw [stepU32And (ha := hb0) (hb := ha0)]
  miden_bind
  miden_movup
  miden_movup
  rw [stepU32And (ha := ha1) (hb := hb1)]
  miden_bind
  miden_movup
  miden_movup
  rw [stepU32And (ha := ha2) (hb := hb2)]
  miden_bind
  miden_movup
  miden_movup
  rw [stepU32And (ha := ha3) (hb := hb3)]
  miden_bind
  rw [stepReversew]
  dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
  congr 1
  simp [Nat.land_comm]

end MidenLean.Proofs
