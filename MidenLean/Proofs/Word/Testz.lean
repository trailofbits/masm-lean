import MidenLean.Proofs.Tactics
import MidenLean.Symbolic.Tactic
import MidenLean.Generated.Word

namespace MidenLean.Proofs

open MidenLean
open MidenLean.Tactics

set_option maxHeartbeats 8000000 in
/-- `word::testz` tests whether a word is zero without consuming the input. -/
theorem word_testz_correct (a b c d : Felt) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = a :: b :: c :: d :: rest) :
    execProcedure emptyEnv 20 s Miden.Core.Word.testz =
    some (s.withStack (
      (if (d == (0:Felt)) && ((c == (0:Felt)) && ((b == (0:Felt)) && (a == (0:Felt))))
       then (1 : Felt) else 0) :: a :: b :: c :: d :: rest)) := by
  miden_vcg
  all_goals miden_finish_reflection

end MidenLean.Proofs
