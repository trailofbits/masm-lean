import MidenLean.Proofs.U128.Common
import MidenLean.Proofs.Tactics
import MidenLean.Symbolic.Tactic
import MidenLean.Generated.U128

namespace MidenLean.Proofs

open MidenLean
open MidenLean.Tactics

set_option maxHeartbeats 4000000 in
/-- `u128::and` computes bitwise AND of two 128-bit values, limb by limb.
    Input stack:  [b0, b1, b2, b3, a0, a1, a2, a3] ++ rest
    Output stack: [b0 &&& a0, a1 &&& b1, a2 &&& b2, a3 &&& b3] ++ rest
    Parametric in `env` and `fuel` so this lemma serves both as a callee
    summary for reflective callers and as the basis for `u128_and_correct`. -/
@[miden_exec_summary]
theorem u128_and_exec
    (env : ProcEnv) (fuel : Nat)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (ha2 : a2.isU32 = true) (ha3 : a3.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true)
    (hb2 : b2.isU32 = true) (hb3 : b3.isU32 = true) :
    execProcedure env (fuel + 1) s Miden.Core.U128.and =
    some (s.withStack (
      Felt.ofNat (b0.val &&& a0.val) ::
      Felt.ofNat (a1.val &&& b1.val) ::
      Felt.ofNat (a2.val &&& b2.val) ::
      Felt.ofNat (a3.val &&& b3.val) :: rest)) := by
  miden_vcg

/-- `u128::and` computes bitwise AND of two 128-bit values.
    Input stack:  [b.a0, b.a1, b.a2, b.a3, a.a0, a.a1, a.a2, a.a3] ++ rest
    Output stack: [(a &&& b).a0, (a &&& b).a1, (a &&& b).a2, (a &&& b).a3] ++ rest -/
theorem u128_and_correct (a b : U128) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val ::
                    a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val :: rest) :
    execProcedure emptyEnv 17 s Miden.Core.U128.and =
    some (s.withStack (
      (a &&& b).a0.val :: (a &&& b).a1.val ::
      (a &&& b).a2.val :: (a &&& b).a3.val :: rest)) := by
  simp only [U128.and_a0, U128.and_a1, U128.and_a2, U128.and_a3,
    Nat.and_comm a.a0.val.val]
  exact u128_and_exec emptyEnv 16 a.a0.val a.a1.val a.a2.val a.a3.val
    b.a0.val b.a1.val b.a2.val b.a3.val rest s hs
    a.a0.isU32 a.a1.isU32 a.a2.isU32 a.a3.isU32
    b.a0.isU32 b.a1.isU32 b.a2.isU32 b.a3.isU32

end MidenLean.Proofs
