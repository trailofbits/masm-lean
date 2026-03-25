import MidenLean.Proofs.U128.Common
import MidenLean.Proofs.Tactics
import MidenLean.Generated.U128

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 4000000 in
theorem u128_xor_raw
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (ha2 : a2.isU32 = true) (ha3 : a3.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true)
    (hb2 : b2.isU32 = true) (hb3 : b3.isU32 = true) :
    exec 17 s Miden.Core.U128.xor =
    some (s.withStack (
      Felt.ofNat (b0.val ^^^ a0.val) ::
      Felt.ofNat (b1.val ^^^ a1.val) ::
      Felt.ofNat (b2.val ^^^ a2.val) ::
      Felt.ofNat (b3.val ^^^ a3.val) :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.U128.xor execWithEnv
  simp only [List.foldlM]
  miden_movup
  rw [stepU32Xor (ha := hb0) (hb := ha0)]
  miden_bind
  miden_movup
  miden_movup
  rw [stepU32Xor (ha := ha1) (hb := hb1)]
  miden_bind
  miden_movup
  miden_movup
  rw [stepU32Xor (ha := ha2) (hb := hb2)]
  miden_bind
  miden_movup
  miden_movup
  rw [stepU32Xor (ha := ha3) (hb := hb3)]
  miden_bind
  rw [stepReversew]
  dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
  simp [Nat.xor_comm]

/-- `u128::xor` correctly computes bitwise XOR of two 128-bit values.
    Input stack:  [b.a0, b.a1, b.a2, b.a3, a.a0, a.a1, a.a2, a.a3] ++ rest
    Output stack: [(a ^^^ b).a0, (a ^^^ b).a1, (a ^^^ b).a2, (a ^^^ b).a3] ++ rest -/
theorem u128_xor_correct (a b : U128) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val ::
                    a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val :: rest) :
    exec 17 s Miden.Core.U128.xor =
    some (s.withStack (
      (a ^^^ b).a0.val :: (a ^^^ b).a1.val ::
      (a ^^^ b).a2.val :: (a ^^^ b).a3.val :: rest)) := by
  simp only [U128.xor_a0, U128.xor_a1, U128.xor_a2, U128.xor_a3,
    Nat.xor_comm a.a0.val.val, Nat.xor_comm a.a1.val.val,
    Nat.xor_comm a.a2.val.val, Nat.xor_comm a.a3.val.val]
  exact u128_xor_raw a.a0.val a.a1.val a.a2.val a.a3.val
    b.a0.val b.a1.val b.a2.val b.a3.val rest s hs
    a.a0.isU32 a.a1.isU32 a.a2.isU32 a.a3.isU32
    b.a0.isU32 b.a1.isU32 b.a2.isU32 b.a3.isU32

end MidenLean.Proofs
