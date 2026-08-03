import MidenLean.Proofs.Word.Common
import MidenLean.Proofs.Tactics
import MidenLean.Symbolic.Tactic
import MidenLean.Generated.Word

namespace MidenLean.Proofs

open MidenLean
open MidenLean.Tactics

set_option maxHeartbeats 4000000 in
/-- `word::gt` pushes 1 iff the deeper word (pushed first, limbs `b0..b3`) is
    lexicographically greater than the top word, comparing limbs from the most
    significant (index 3) downward.
    Parametric in `fuel` so this lemma serves both as a callee summary for
    reflective callers and as the basis for `word_gt_correct`. The env is fixed
    to `wordProcEnv` because `miden_vcg` resolves the
    `exec arrange_words_adjacent_le` call through that environment. -/
@[miden_exec_summary]
theorem word_gt_exec (fuel : Nat)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 :: rest) :
    execProcedure wordProcEnv (fuel + 3) s Miden.Core.Word.gt =
    some (s.withStack ((if decide (a3.val < b3.val)
                  || ((b3 == a3) && decide (a2.val < b2.val))
                  || ((b3 == a3) && (b2 == a2) && decide (a1.val < b1.val))
                  || ((b3 == a3) && (b2 == a2) && (b1 == a1) && decide (a0.val < b0.val))
                then (1:Felt) else 0) :: rest)) := by
  miden_vcg
  -- The residual goals are the contradictory limb orderings left by the
  -- case split on each `repeat` iteration's comparison flags.
  all_goals omega

/-- `word::gt` pushes 1 iff the deeper word (pushed first, limbs `b0..b3`) is
    lexicographically greater than the top word, comparing limbs from the most
    significant (index 3) downward. -/
theorem word_gt_correct
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 :: rest) :
    let result := decide (a3.val < b3.val)
                  || ((b3 == a3) && decide (a2.val < b2.val))
                  || ((b3 == a3) && (b2 == a2) && decide (a1.val < b1.val))
                  || ((b3 == a3) && (b2 == a2) && (b1 == a1) && decide (a0.val < b0.val))
    execProcedure wordProcEnv 3 s Miden.Core.Word.gt =
    some (s.withStack ((if result then (1:Felt) else 0) :: rest)) :=
  word_gt_exec 0 a0 a1 a2 a3 b0 b1 b2 b3 rest s hs

end MidenLean.Proofs
