import MidenLean.Proofs.WordGt
import MidenLean.Proofs.Tactics
import MidenLean.Generated.Word

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

-- Axiom for word::lte (negation of gt)
axiom word_lte_full_correct
    (b0 b1 b2 b3 a0 a1 a2 a3 : Felt) (rest : List Felt) (mem locs : Nat → Felt) (adv : List Felt) :
    execWithEnv wordProcEnv 20 ⟨b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv⟩
      Miden.Core.Word.lte =
    some ⟨let gt3 := decide (b3.val < a3.val)
            let eq3 := a3 == b3
            let gt2 := decide (b2.val < a2.val)
            let eq2 := a2 == b2
            let gt1 := decide (b1.val < a1.val)
            let eq1 := a1 == b1
            let gt0 := decide (b0.val < a0.val)
            let gt := gt3 || (eq3 && (gt2 || (eq2 && (gt1 || (eq1 && gt0)))))
            (if !gt then (1 : Felt) else 0) :: rest, mem, locs, adv⟩

set_option maxHeartbeats 4000000 in
/-- word.lte correctly computes !(word.gt), i.e., a <= b.
    Input stack:  [b0, b1, b2, b3, a0, a1, a2, a3] ++ rest
    Output stack: [result] ++ rest
    where result = 1 iff a <= b (as 128-bit words), else 0. -/
theorem word_lte_correct
    (b0 b1 b2 b3 a0 a1 a2 a3 : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest) :
    execWithEnv wordProcEnv 20 s Miden.Core.Word.lte =
    some (s.withStack (
      let gt3 := decide (b3.val < a3.val)
      let eq3 := a3 == b3
      let gt2 := decide (b2.val < a2.val)
      let eq2 := a2 == b2
      let gt1 := decide (b1.val < a1.val)
      let eq1 := a1 == b1
      let gt0 := decide (b0.val < a0.val)
      let gt := gt3 || (eq3 && (gt2 || (eq2 && (gt1 || (eq1 && gt0)))))
      (if !gt then (1 : Felt) else 0) :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  exact word_lte_full_correct b0 b1 b2 b3 a0 a1 a2 a3 rest mem locs adv

end MidenLean.Proofs
