import MidenLean.Proofs.Tactics
import MidenLean.Symbolic.Tactic
import MidenLean.Generated.Word

namespace MidenLean.Proofs

open MidenLean
open MidenLean.Tactics

/-- `word::reverse` reverses the first four stack elements.
    Input stack:  [a, b, c, d] ++ rest
    Output stack: [d, c, b, a] ++ rest
    Parametric in `env` and `fuel` so this lemma serves both as a callee
    summary for reflective callers and as the basis for `word_reverse_correct`. -/
@[miden_exec_summary]
theorem word_reverse_exec
    (env : ProcEnv) (fuel : Nat)
    (a b c d : Felt) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = a :: b :: c :: d :: rest) :
    execProcedure env (fuel + 1) s Miden.Core.Word.reverse =
    some (s.withStack (d :: c :: b :: a :: rest)) := by
  miden_vcg

/-- `word::reverse` reverses the first four stack elements.
    Input stack:  [a, b, c, d] ++ rest
    Output stack: [d, c, b, a] ++ rest -/
theorem word_reverse_correct (a b c d : Felt) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = a :: b :: c :: d :: rest) :
    execProcedure emptyEnv 10 s Miden.Core.Word.reverse =
    some (s.withStack (d :: c :: b :: a :: rest)) := by
  exact word_reverse_exec emptyEnv 9 a b c d rest s hs

end MidenLean.Proofs
