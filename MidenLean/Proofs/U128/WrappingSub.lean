import MidenLean.Proofs.U128.Common
import MidenLean.Proofs.U128.OverflowingSub
import MidenLean.Proofs.Tactics
import MidenLean.Generated.U128

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 8000000 in
/-- `u128::wrapping_sub` correctly computes wrapping subtraction of two 128-bit values (raw limb version).
    Input stack:  [b0, b1, b2, b3, a0, a1, a2, a3] ++ rest
    Output stack: [d0, d1, d2, d3] ++ rest
    where `d0..d3` are the low-to-high limbs of `(a - b) mod 2^128`. -/
theorem u128_wrapping_sub_raw
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (ha2 : a2.isU32 = true) (ha3 : a3.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true)
    (hb2 : b2.isU32 = true) (hb3 : b3.isU32 = true) :
    execWithEnv u128ProcEnv 31 s Miden.Core.U128.wrapping_sub =
    some (s.withStack (u128WrappingSubResult a0 a1 a2 a3 b0 b1 b2 b3 rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold Miden.Core.U128.wrapping_sub execWithEnv
  simp only [List.foldlM, u128ProcEnv]
  dsimp only [bind, Bind.bind, Option.bind]
  rw [show execWithEnv u128ProcEnv 30
      ⟨b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv⟩
      Miden.Core.U128.overflowing_sub =
      some ⟨u128OverflowingSubResult a0 a1 a2 a3 b0 b1 b2 b3 rest, mem, locs, adv⟩
      from u128_overflowing_sub_run u128ProcEnv 29 a0 a1 a2 a3 b0 b1 b2 b3 rest mem locs adv
        ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3]
  miden_bind
  unfold u128OverflowingSubResult u128WrappingSubResult
  rw [stepDrop]
  dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]

/-- `u128::wrapping_sub` correctly computes `(a - b) mod 2^128` for two 128-bit values.
    Input stack:  [b.a0, b.a1, b.a2, b.a3, a.a0, a.a1, a.a2, a.a3] ++ rest
    Output stack: [(a−b).a0, (a−b).a1, (a−b).a2, (a−b).a3] ++ rest -/
theorem u128_wrapping_sub_correct (a b : U128) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val ::
                    a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val :: rest) :
    execWithEnv u128ProcEnv 31 s Miden.Core.U128.wrapping_sub =
    some (s.withStack (
      (a - b).a0.val :: (a - b).a1.val :: (a - b).a2.val :: (a - b).a3.val :: rest)) := by
  have h := u128_wrapping_sub_raw a.a0.val a.a1.val a.a2.val a.a3.val
    b.a0.val b.a1.val b.a2.val b.a3.val rest s hs
    a.a0.isU32 a.a1.isU32 a.a2.isU32 a.a3.isU32
    b.a0.isU32 b.a1.isU32 b.a2.isU32 b.a3.isU32
  rw [h]; congr 1; congr 1
  exact u128WrappingSubResult_eq a b rest

end MidenLean.Proofs
