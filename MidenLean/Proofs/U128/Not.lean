import MidenLean.Proofs.U128.Common
import MidenLean.Proofs.Tactics
import MidenLean.Symbolic.Tactic
import MidenLean.Generated.U128

namespace MidenLean.Proofs

open MidenLean
open MidenLean.Tactics

set_option maxHeartbeats 4000000 in
/-- `u128::not` computes the bitwise complement of a 128-bit value, limb by limb.
    Input stack:  [a0, a1, a2, a3] ++ rest
    Output stack: [~~~a0, ~~~a1, ~~~a2, ~~~a3] ++ rest, limbwise over u32 values.
    Parametric in `env` and `fuel` so this lemma serves both as a callee
    summary for reflective callers and as the basis for `u128_not_correct`. -/
@[miden_exec_summary]
theorem u128_not_exec
    (env : ProcEnv) (fuel : Nat)
    (a0 a1 a2 a3 : Felt) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = a0 :: a1 :: a2 :: a3 :: rest)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (ha2 : a2.isU32 = true) (ha3 : a3.isU32 = true) :
    execProcedure env (fuel + 1) s Miden.Core.U128.not =
    some (s.withStack (
      Felt.ofNat (u32Max - 1 - a0.val) ::
      Felt.ofNat (u32Max - 1 - a1.val) ::
      Felt.ofNat (u32Max - 1 - a2.val) ::
      Felt.ofNat (u32Max - 1 - a3.val) :: rest)) := by
  miden_vcg

/-- `u128::not` pushes the limbs of `~~~a` (bitwise complement).
    Input stack:  [a.a0, a.a1, a.a2, a.a3] ++ rest
    Output stack: [(~~~a).a0, (~~~a).a1, (~~~a).a2, (~~~a).a3] ++ rest -/
theorem u128_not_correct (a : U128) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val :: rest) :
    execProcedure emptyEnv 13 s Miden.Core.U128.not =
    some (s.withStack (
      (~~~a).a0.val :: (~~~a).a1.val ::
      (~~~a).a2.val :: (~~~a).a3.val :: rest)) := by
  simp only [U128.complement_a0, U128.complement_a1, U128.complement_a2, U128.complement_a3]
  exact u128_not_exec emptyEnv 12 a.a0.val a.a1.val a.a2.val a.a3.val rest s hs
    a.a0.isU32 a.a1.isU32 a.a2.isU32 a.a3.isU32

end MidenLean.Proofs
