import MidenLean.Proofs.U256.Common
import MidenLean.Proofs.Tactics
import MidenLean.Symbolic.Tactic

namespace MidenLean.Proofs

open MidenLean
open MidenLean.Tactics

set_option maxHeartbeats 4000000 in
/-- `u256::u256_le_to_be` reverses the order of eight stack elements.
    Input stack:  [x0, x1, x2, x3, x4, x5, x6, x7] ++ rest
    Output stack: [x7, x6, x5, x4, x3, x2, x1, x0] ++ rest
    Parametric in `env` and `fuel` so this lemma serves both as a callee
    summary for reflective callers and as the basis for `u256_u256_le_to_be_correct`. -/
@[miden_exec_summary]
theorem u256_u256_le_to_be_exec
    (env : ProcEnv) (fuel : Nat)
    (x0 x1 x2 x3 x4 x5 x6 x7 : Felt) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: rest) :
    execProcedure env (fuel + 1) s Miden.Core.U256.u256_le_to_be =
    some (s.withStack (x7 :: x6 :: x5 :: x4 :: x3 :: x2 :: x1 :: x0 :: rest)) := by
  miden_vcg

/-- `u256::u256_le_to_be` reverses the order of eight stack elements.
    Input stack:  [a.a0, a.a1, a.a2, a.a3, a.a4, a.a5, a.a6, a.a7] ++ rest
    Output stack: [a.a7, a.a6, a.a5, a.a4, a.a3, a.a2, a.a1, a.a0] ++ rest -/
theorem u256_u256_le_to_be_correct (a : U256) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val ::
                    a.a4.val :: a.a5.val :: a.a6.val :: a.a7.val :: rest) :
    execProcedure emptyEnv 8 s Miden.Core.U256.u256_le_to_be =
    some (s.withStack (a.a7.val :: a.a6.val :: a.a5.val :: a.a4.val ::
                       a.a3.val :: a.a2.val :: a.a1.val :: a.a0.val :: rest)) :=
  u256_u256_le_to_be_exec emptyEnv 7 a.a0.val a.a1.val a.a2.val a.a3.val
    a.a4.val a.a5.val a.a6.val a.a7.val rest s hs

end MidenLean.Proofs
