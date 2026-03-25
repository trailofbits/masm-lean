import MidenLean.Proofs.U128.Common
import MidenLean.Proofs.U128.OverflowingMul
import MidenLean.Proofs.Tactics
import MidenLean.Generated.U128

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 8000000 in
/-- `u128::widening_mul` correctly computes the low 128 bits of the product and moves the overflow flag to the end (raw limb version).
    Input stack:  [b0, b1, b2, b3, a0, a1, a2, a3] ++ rest
    Output stack: [c0, c1, c2, c3, overflow] ++ rest
    where `c0..c3` are the low-to-high limbs of `(a * b) mod 2^128`
    and `overflow` is `1` exactly when the discarded high part is nonzero. -/
theorem u128_widening_mul_raw
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (ha2 : a2.isU32 = true) (ha3 : a3.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true)
    (hb2 : b2.isU32 = true) (hb3 : b3.isU32 = true) :
    execWithEnv u128ProcEnv 31 s Miden.Core.U128.widening_mul =
    some (s.withStack (
      u128MulC0 a0 b0 ::
      u128MulC1 a0 a1 b0 b1 ::
      u128MulC2 a0 a1 a2 b0 b1 b2 ::
      u128MulC3 a0 a1 a2 a3 b0 b1 b2 b3 ::
      (if u128MulOverflowBool a0 a1 a2 a3 b0 b1 b2 b3 then (1 : Felt) else 0) ::
      rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold Miden.Core.U128.widening_mul execWithEnv
  simp only [List.foldlM, u128ProcEnv]
  dsimp only [bind, Bind.bind, Option.bind]
  rw [show execWithEnv u128ProcEnv 30
      ⟨b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv⟩
      Miden.Core.U128.overflowing_mul =
      some ⟨
        (if u128MulOverflowBool a0 a1 a2 a3 b0 b1 b2 b3 then (1 : Felt) else 0) ::
        u128MulC0 a0 b0 ::
        u128MulC1 a0 a1 b0 b1 ::
        u128MulC2 a0 a1 a2 b0 b1 b2 ::
        u128MulC3 a0 a1 a2 a3 b0 b1 b2 b3 ::
        rest,
        mem, locs, adv⟩
      from u128_overflowing_mul_run u128ProcEnv 29 a0 a1 a2 a3 b0 b1 b2 b3 rest mem locs adv
        ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3]
  miden_bind
  miden_movdn
  dsimp only [pure, Pure.pure]

set_option maxHeartbeats 8000000 in
/-- `u128::widening_mul` correctly computes `(a * b) mod 2^128` and an overflow flag.
    Input stack:  [b.a0, b.a1, b.a2, b.a3, a.a0, a.a1, a.a2, a.a3] ++ rest
    Output stack: [(a*b).a0, (a*b).a1, (a*b).a2, (a*b).a3, overflow] ++ rest -/
theorem u128_widening_mul_correct (a b : U128) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val ::
                    a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val :: rest) :
    execWithEnv u128ProcEnv 31 s Miden.Core.U128.widening_mul =
    some (s.withStack (
      (a * b).a0.val :: (a * b).a1.val :: (a * b).a2.val :: (a * b).a3.val ::
      (if u128MulOverflowBool a.a0.val a.a1.val a.a2.val a.a3.val
          b.a0.val b.a1.val b.a2.val b.a3.val then (1 : Felt) else 0) ::
      rest)) := by
  have h := u128_widening_mul_raw a.a0.val a.a1.val a.a2.val a.a3.val
    b.a0.val b.a1.val b.a2.val b.a3.val rest s hs
    a.a0.isU32 a.a1.isU32 a.a2.isU32 a.a3.isU32
    b.a0.isU32 b.a1.isU32 b.a2.isU32 b.a3.isU32
  rw [h]; congr 1; congr 1
  exact u128MulResult_eq a b _

end MidenLean.Proofs
