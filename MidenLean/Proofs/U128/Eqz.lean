import MidenLean.Proofs.U128.Common
import MidenLean.Proofs.Tactics
import MidenLean.Symbolic.Tactic
import MidenLean.Generated.U128

namespace MidenLean.Proofs

open MidenLean
open MidenLean.Tactics

set_option maxHeartbeats 4000000 in
/-- `u128::eqz` tests whether a 128-bit value is zero, limb by limb.
    Input stack:  [a, b, c, d] ++ rest
    Output stack: [is_zero] ++ rest
    where is_zero = 1 iff all four input limbs are zero.
    Parametric in `env` and `fuel` so this lemma serves both as a callee
    summary for reflective callers and as the basis for `u128_eqz_correct`. -/
@[miden_exec_summary]
theorem u128_eqz_exec
    (env : ProcEnv) (fuel : Nat)
    (a b c d : Felt) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = a :: b :: c :: d :: rest) :
    execProcedure env (fuel + 1) s Miden.Core.U128.eqz =
    some (s.withStack (
      (if (a == (0 : Felt)) && (b == (0 : Felt)) && (c == (0 : Felt)) && (d == (0 : Felt))
       then (1 : Felt) else 0) :: rest)) := by
  miden_vcg
  all_goals miden_finish_reflection

/-- `u128::eqz` tests whether a 128-bit value is zero.
    Input stack:  [a.a0, a.a1, a.a2, a.a3] ++ rest
    Output stack: [(if a == 0 then 1 else 0)] ++ rest -/
theorem u128_eqz_correct (a : U128) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val :: rest) :
    execProcedure emptyEnv 15 s Miden.Core.U128.eqz =
    some (s.withStack (
      (if a == U128.ofNat 0 then (1 : Felt) else 0) :: rest)) := by
  simp only [U128.beq_iff, U128.ofNat]
  exact u128_eqz_exec emptyEnv 14 a.a0.val a.a1.val a.a2.val a.a3.val rest s hs

end MidenLean.Proofs
