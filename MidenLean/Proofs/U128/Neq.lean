import MidenLean.Proofs.U128.Common
import MidenLean.Proofs.Tactics
import MidenLean.Symbolic.Tactic
import MidenLean.Generated.U128

namespace MidenLean.Proofs

open MidenLean
open MidenLean.Tactics

set_option maxHeartbeats 4000000 in
/-- `u128::neq` tests inequality of two 128-bit values, limb by limb.
    Input stack:  [b0, b1, b2, b3, a0, a1, a2, a3] ++ rest
    Output stack: [result] ++ rest
    where result = 1 iff some limb pair differs, else 0.
    Parametric in `env` and `fuel` so this lemma serves both as a callee
    summary for reflective callers and as the basis for `u128_neq_correct`. -/
@[miden_exec_summary]
theorem u128_neq_exec
    (env : ProcEnv) (fuel : Nat)
    (b0 b1 b2 b3 a0 a1 a2 a3 : Felt) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest) :
    execProcedure env (fuel + 1) s Miden.Core.U128.neq =
    some (s.withStack (
      (if (b0 != a0) || (a1 != b1) || (a2 != b2) || (a3 != b3)
       then (1 : Felt) else 0) :: rest)) := by
  miden_vcg
  all_goals miden_finish_reflection

/-- `u128::neq` tests inequality of two 128-bit values.
    Input stack:  [b.a0, b.a1, b.a2, b.a3, a.a0, a.a1, a.a2, a.a3] ++ rest
    Output stack: [(if a != b then 1 else 0)] ++ rest -/
theorem u128_neq_correct (a b : U128) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val ::
                    a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val :: rest) :
    execProcedure emptyEnv 19 s Miden.Core.U128.neq =
    some (s.withStack (
      (if (a != b) then (1 : Felt) else 0) :: rest)) := by
  have h := u128_neq_exec emptyEnv 18 b.a0.val b.a1.val b.a2.val b.a3.val
    a.a0.val a.a1.val a.a2.val a.a3.val rest s hs
  simp only [U128.bne_iff, show (a.a0.val != b.a0.val) = (b.a0.val != a.a0.val) from bne_comm ..]
  exact h

end MidenLean.Proofs
