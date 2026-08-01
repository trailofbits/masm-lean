import MidenLean.Proofs.Tactics
import MidenLean.Symbolic.Tactic
import MidenLean.Generated.Word

namespace MidenLean.Proofs

open MidenLean
open MidenLean.Tactics

set_option maxHeartbeats 4000000 in
/-- `word::eq` tests equality of two words, element by element.
    Input stack:  [a0, a1, a2, a3, b0, b1, b2, b3] ++ rest
    Output stack: [result] ++ rest
    where result = 1 iff a0=b0 /\ a1=b1 /\ a2=b2 /\ a3=b3, else 0.
    Parametric in `env` and `fuel` so this lemma serves both as a callee
    summary for reflective callers and as the basis for `word_eq_correct`. -/
@[miden_exec_summary]
theorem word_eq_exec
    (env : ProcEnv) (fuel : Nat)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 :: rest) :
    execProcedure env (fuel + 1) s Miden.Core.Word.eq =
    some (s.withStack (
      (if (a0 == b0) && (a1 == b1) && (a2 == b2) && (b3 == a3)
       then (1 : Felt) else 0) :: rest)) := by
  miden_vcg
  all_goals miden_finish_reflection

/-- `word::eq` tests equality of two words.
    Input stack:  [a0, a1, a2, a3, b0, b1, b2, b3] ++ rest
    Output stack: [result] ++ rest
    where result = 1 iff a0=b0 /\ a1=b1 /\ a2=b2 /\ a3=b3, else 0. -/
theorem word_eq_correct (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 :: rest) :
    execProcedure emptyEnv 20 s Miden.Core.Word.eq =
    some (s.withStack (
      (if (a0 == b0) && (a1 == b1) && (a2 == b2) && (b3 == a3)
       then (1 : Felt) else 0) :: rest)) := by
  exact word_eq_exec emptyEnv 19 a0 a1 a2 a3 b0 b1 b2 b3 rest s hs

end MidenLean.Proofs
