import MidenLean.Proofs.Tactics
import MidenLean.Symbolic.Tactic
import MidenLean.Generated.Word

namespace MidenLean.Proofs

open MidenLean
open MidenLean.Tactics

set_option maxHeartbeats 4000000 in
/-- `word::eqz` tests whether a word is zero.
    Input stack:  [a, b, c, d] ++ rest
    Output stack: [is_zero] ++ rest
    where is_zero = 1 iff all four input elements are zero. -/
theorem word_eqz_correct
    (a b c d : Felt) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = a :: b :: c :: d :: rest) :
    execProcedure emptyEnv 25 s Miden.Core.Word.eqz =
    some (s.withStack (
      (if (a == (0 : Felt)) && (b == (0 : Felt)) && (c == (0 : Felt)) && (d == (0 : Felt))
       then (1 : Felt) else 0) :: rest)) := by
  miden_vcg

end MidenLean.Proofs
