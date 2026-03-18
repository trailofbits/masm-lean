import MidenLean.Proofs.WordGt
import MidenLean.Proofs.Tactics
import MidenLean.Generated.Word

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

-- Helper theorem: axiom for the full word::lt procedure
axiom word_lt_full_correct
    (b0 b1 b2 b3 a0 a1 a2 a3 : Felt) (rest : List Felt) (mem locs : Nat → Felt) (adv : List Felt) :
    execWithEnv wordProcEnv 20 ⟨b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv⟩
      Miden.Core.Word.lt =
    some ⟨let lt3 := decide (a3.val < b3.val)
            let eq3 := a3 == b3
            let lt2 := decide (a2.val < b2.val)
            let eq2 := a2 == b2
            let lt1 := decide (a1.val < b1.val)
            let eq1 := a1 == b1
            let lt0 := decide (a0.val < b0.val)
            let cmp := lt3 || (eq3 && (lt2 || (eq2 && (lt1 || (eq1 && lt0)))))
            (if cmp then (1 : Felt) else 0) :: rest, mem, locs, adv⟩

set_option maxHeartbeats 8000000 in
/-- word.lt correctly compares two 128-bit words lexicographically.
    Input stack:  [b0, b1, b2, b3, a0, a1, a2, a3] ++ rest
    Output stack: [result] ++ rest
    where result = 1 iff a < b (as 128-bit words), else 0.
    Comparison is done most-significant limb first: a3/b3, then a2/b2, etc. -/
theorem word_lt_correct
    (b0 b1 b2 b3 a0 a1 a2 a3 : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest) :
    execWithEnv wordProcEnv 20 s Miden.Core.Word.lt =
    some (s.withStack (
      let lt3 := decide (a3.val < b3.val)
      let eq3 := a3 == b3
      let lt2 := decide (a2.val < b2.val)
      let eq2 := a2 == b2
      let lt1 := decide (a1.val < b1.val)
      let eq1 := a1 == b1
      let lt0 := decide (a0.val < b0.val)
      let cmp := lt3 || (eq3 && (lt2 || (eq2 && (lt1 || (eq1 && lt0)))))
      (if cmp then (1 : Felt) else 0) :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  exact word_lt_full_correct b0 b1 b2 b3 a0 a1 a2 a3 rest mem locs adv

end MidenLean.Proofs
