import MidenLean.Proofs.U256.Common
import MidenLean.Proofs.Tactics
import MidenLean.Symbolic.Tactic

namespace MidenLean.Proofs

open MidenLean
open MidenLean.Tactics

set_option maxHeartbeats 4000000 in
/-- `u256::eqz` tests whether a 256-bit value is zero, limb by limb.
    Parametric in `env` and `fuel` so this lemma serves both as a callee summary
    for reflective callers and as the basis for `u256_eqz_correct`. -/
@[miden_exec_summary]
theorem u256_eqz_exec
    (env : ProcEnv) (fuel : Nat)
    (x0 x1 x2 x3 x4 x5 x6 x7 : Felt) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: rest) :
    execProcedure env (fuel + 2) s Miden.Core.U256.eqz =
    some (s.withStack (
      (if (x0 == (0 : Felt)) && (x1 == (0 : Felt)) && (x2 == (0 : Felt)) &&
          (x3 == (0 : Felt)) && (x4 == (0 : Felt)) && (x5 == (0 : Felt)) &&
          (x6 == (0 : Felt)) && (x7 == (0 : Felt))
       then (1 : Felt) else 0) :: rest)) := by
  miden_vcg

/-- `u256::eqz` tests whether a u256 value equals zero.
    Input stack:  [a.a0, a.a1, a.a2, a.a3, a.a4, a.a5, a.a6, a.a7] ++ rest
    Output stack: [result] ++ rest
    where result = 1 if all limbs equal 0, otherwise 0. -/
theorem u256_eqz_correct (a : U256) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val ::
                    a.a4.val :: a.a5.val :: a.a6.val :: a.a7.val :: rest) :
    execProcedure emptyEnv 37 s Miden.Core.U256.eqz =
    some (s.withStack (
      (if a == U256.ofNat 0 then (1 : Felt) else 0) :: rest)) := by
  simp only [U256.beq_iff, U256.ofNat]
  exact u256_eqz_exec emptyEnv 35 a.a0.val a.a1.val a.a2.val a.a3.val
    a.a4.val a.a5.val a.a6.val a.a7.val rest s hs

end MidenLean.Proofs
