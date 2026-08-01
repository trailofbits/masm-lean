import MidenLean.Proofs.Tactics
import MidenLean.Symbolic.Tactic
import MidenLean.Generated.Word

namespace MidenLean.Proofs

open MidenLean
open MidenLean.Tactics

set_option maxHeartbeats 4000000 in
/-- `word::test_eq` tests equality of two words without consuming inputs, element by element.
    Input stack:  [a0, a1, a2, a3, b0, b1, b2, b3] ++ rest
    Output stack: [result, a0, a1, a2, a3, b0, b1, b2, b3] ++ rest
    where result = 1 iff all corresponding elements are equal, else 0.
    Parametric in `env` and `fuel` so this lemma serves both as a callee
    summary for reflective callers and as the basis for `word_test_eq_correct`. -/
@[miden_exec_summary]
theorem word_test_eq_exec
    (env : ProcEnv) (fuel : Nat)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 :: rest) :
    execProcedure env (fuel + 1) s Miden.Core.Word.test_eq =
    some (s.withStack (
      (if (b3 == a3) && (b2 == a2) && (b1 == a1) && (b0 == a0)
       then (1 : Felt) else 0) ::
      a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 :: rest)) := by
  miden_vcg
  all_goals miden_finish_reflection

/-- `word::test_eq` tests equality of two words without consuming inputs.
    Input stack:  [a0, a1, a2, a3, b0, b1, b2, b3] ++ rest
    Output stack: [result, a0, a1, a2, a3, b0, b1, b2, b3] ++ rest
    where result = 1 iff all corresponding elements are equal, else 0. -/
theorem word_test_eq_correct (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt)
    (s : Concrete.State)
    (hs : s.stack = a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 :: rest) :
    execProcedure emptyEnv 20 s Miden.Core.Word.test_eq =
    some (s.withStack (
      (if (b3 == a3) && (b2 == a2) && (b1 == a1) && (b0 == a0)
       then (1 : Felt) else 0) ::
      a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 :: rest)) := by
  exact word_test_eq_exec emptyEnv 19 a0 a1 a2 a3 b0 b1 b2 b3 rest s hs

end MidenLean.Proofs
