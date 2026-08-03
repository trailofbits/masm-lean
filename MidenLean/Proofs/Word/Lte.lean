import MidenLean.Proofs.Word.Common
import MidenLean.Proofs.Word.Gt
import MidenLean.Symbolic.Tactic
import MidenLean.Generated.Word

namespace MidenLean.Proofs

open MidenLean
open MidenLean.Tactics

set_option maxHeartbeats 16000000 in
/-- `word::lte` checks whether one word is less than or equal to another. -/
theorem word_lte_correct
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 :: rest) :
    let result := decide (a3.val < b3.val)
                  || ((b3 == a3) && decide (a2.val < b2.val))
                  || ((b3 == a3) && (b2 == a2) && decide (a1.val < b1.val))
                  || ((b3 == a3) && (b2 == a2) && (b1 == a1) && decide (a0.val < b0.val))
    execProcedure wordProcEnv 4 s Miden.Core.Word.lte =
    some (s.withStack ((if !result then (1:Felt) else 0) :: rest)) := by
  dsimp only
  miden_vcg
  all_goals by_cases hb3 : b3 = a3 <;> by_cases hb2 : b2 = a2 <;> by_cases hb1 : b1 = a1 <;>
    simp_all <;> omega

end MidenLean.Proofs
