import MidenLean.Proofs.U128.Common
import MidenLean.Proofs.U128.OverflowingSub
import MidenLean.Symbolic.Tactic
import MidenLean.Generated.U128

namespace MidenLean.Proofs

open MidenLean
open MidenLean.Tactics

set_option maxHeartbeats 8000000 in
/-- `u128::wrapping_sub` computes wrapping subtraction of two 128-bit values (raw limb version).
    Input stack:  [b0, b1, b2, b3, a0, a1, a2, a3] ++ rest
    Output stack: [d0, d1, d2, d3] ++ rest
    where `d0..d3` are the low-to-high limbs of `(a - b) mod 2^128`.
    Parametric in `fuel` so this lemma serves both as a callee summary for
    reflective callers and as the basis for `u128_wrapping_sub_correct`. -/
@[miden_exec_summary]
theorem u128_wrapping_sub_exec
    (fuel : Nat)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (ha2 : a2.isU32 = true) (ha3 : a3.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true)
    (hb2 : b2.isU32 = true) (hb3 : b3.isU32 = true) :
    execProcedure u128ProcEnv (fuel + 2) s Miden.Core.U128.wrapping_sub =
    some (s.withStack (u128WrappingSubResult a0 a1 a2 a3 b0 b1 b2 b3 rest)) := by
  miden_vcg

/-- `u128::wrapping_sub` computes `(a - b) mod 2^128` for two 128-bit values.
    Input stack:  [b.a0, b.a1, b.a2, b.a3, a.a0, a.a1, a.a2, a.a3] ++ rest
    Output stack: [(a−b).a0, (a−b).a1, (a−b).a2, (a−b).a3] ++ rest -/
theorem u128_wrapping_sub_correct (a b : U128) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val ::
                    a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val :: rest) :
    execProcedure u128ProcEnv 31 s Miden.Core.U128.wrapping_sub =
    some (s.withStack (
      (a - b).a0.val :: (a - b).a1.val :: (a - b).a2.val :: (a - b).a3.val :: rest)) := by
  have h := u128_wrapping_sub_exec 29 a.a0.val a.a1.val a.a2.val a.a3.val
    b.a0.val b.a1.val b.a2.val b.a3.val rest s hs
    a.a0.isU32 a.a1.isU32 a.a2.isU32 a.a3.isU32
    b.a0.isU32 b.a1.isU32 b.a2.isU32 b.a3.isU32
  rw [h]; congr 1; congr 1
  exact u128WrappingSubResult_eq a b rest

end MidenLean.Proofs
