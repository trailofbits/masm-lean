import MidenLean.Proofs.WordArrange
import MidenLean.Proofs.Tactics
import MidenLean.Generated.Word

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

/-- Procedure environment for word procedures. -/
def wordProcEnv : ProcEnv := fun name =>
  match name with
  | "arrange_words_adjacent_le" => some Miden.Core.Word.arrange_words_adjacent_le
  | "gt" => some Miden.Core.Word.gt
  | "lt" => some Miden.Core.Word.lt
  | _ => none

/-- Single iteration of the word::gt repeat-4 loop body.
    Invariant: cmp_f and eq_f must be boolean felts (0 or 1).
    Given stack [cmp_f, eq_f, ai, bi, rest...], produces:
      [new_cmp, new_eq, rest...]
    where new_cmp = if cmp_f.val==1 || (eq_f.val==1 && decide(bi<ai)) then 1 else 0
      and new_eq  = if eq_f.val==1 && (ai==bi) then 1 else 0 -/
private theorem one_gt_iteration_body
    (mem locs : Nat → Felt) (adv : List Felt)
    (cmp_f eq_f ai bi : Felt) (rest : List Felt)
    (hc : cmp_f.isBool = true) (he : eq_f.isBool = true)
    (fuel : Nat) :
    execWithEnv wordProcEnv (fuel + 1)
      ⟨cmp_f :: eq_f :: ai :: bi :: rest, mem, locs, adv⟩
      [.inst (.movup 3), .inst (.movup 3), .inst (.dup 0), .inst (.dup 2),
       .inst (.eq), .inst (.movdn 3), .inst (.lt),
       .inst (.dup 3), .inst (.and), .inst (.or), .inst (.movdn 2),
       .inst (.and), .inst (.swap 1)] =
    some ⟨(if cmp_f.val == 1 || (eq_f.val == 1 && decide (bi.val < ai.val))
            then (1 : Felt) else 0) ::
          (if eq_f.val == 1 && (ai == bi) then (1 : Felt) else 0) ::
          rest, mem, locs, adv⟩ := by
  simp only [execWithEnv, List.foldlM]
  miden_movup; miden_movup; miden_dup; miden_dup
  rw [stepEq]; miden_bind
  miden_movdn
  -- lt: stack = [ai, bi, cmp_f, (if ai==bi then 1 else 0), eq_f, rest]
  -- execLt ⟨ai :: bi :: ...⟩: b=ai, a=bi → if bi.val < ai.val then 1 else 0
  rw [stepLt]; miden_bind
  -- dup 3: duplicate eq_f (position 3)
  miden_dup
  -- Convert eq_f, cmp_f, and lt-result to Bool ite form (only on LHS)
  -- so that stepAndIte/stepOrIte can unify
  conv_lhs => rw [Felt.isBool_eq_ite eq_f he,
                   Felt.isBool_eq_ite cmp_f hc,
                   Felt.ite_prop_eq_ite_bool (ZMod.val bi < ZMod.val ai)]
  -- and: b=(if eq_f.val==1 then 1 else 0), a=(if decide(bi<ai) then 1 else 0)
  rw [stepAndIte]; miden_bind
  -- or: b=(and-result), a=(if cmp_f.val==1 then 1 else 0)
  rw [stepOrIte]; miden_bind
  miden_movdn
  -- and: b=(if (ai==bi)=true then 1 else 0), a=(if eq_f.val==1 then 1 else 0)
  -- (ai==bi) : Bool, so (ai==bi)=true is a Prop ite -- normalize first
  conv_lhs => rw [Felt.ite_beq_true (ai == bi)]
  rw [stepAndIte]; miden_bind
  miden_swap
  -- Close: the goal is now structural equality of Bool ite expressions
  -- The conditions differ only by reordering of && within the ||, which is equivalent
  congr 1
  -- Prove the two boolean conditions are equal after normalization
  simp only [Bool.and_comm]

set_option maxHeartbeats 8000000 in
/-- word.gt correctly compares two 128-bit words lexicographically.
    Input stack:  [b0, b1, b2, b3, a0, a1, a2, a3] ++ rest
    Output stack: [result] ++ rest
    where result = 1 iff a > b (as 128-bit words), else 0.
    Comparison is done most-significant limb first: a3/b3, then a2/b2, etc. -/
theorem word_gt_correct
    (b0 b1 b2 b3 a0 a1 a2 a3 : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest) :
    execWithEnv wordProcEnv 20 s Miden.Core.Word.gt =
    some (s.withStack (
      let gt3 := decide (b3.val < a3.val)
      let eq3 := a3 == b3
      let gt2 := decide (b2.val < a2.val)
      let eq2 := a2 == b2
      let gt1 := decide (b1.val < a1.val)
      let eq1 := a1 == b1
      let gt0 := decide (b0.val < a0.val)
      let cmp := gt3 || (eq3 && (gt2 || (eq2 && (gt1 || (eq1 && gt0)))))
      (if cmp then (1 : Felt) else 0) :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  -- Unfold gt body and outer execWithEnv (fuel=20, fuel'=19)
  unfold Miden.Core.Word.gt
  simp only [execWithEnv, List.foldlM]
  -- exec "arrange_words_adjacent_le": look up in wordProcEnv
  simp only [wordProcEnv]
  -- Unfold arrange_words_adjacent_le with fuel'=19 (→ 18)
  unfold Miden.Core.Word.arrange_words_adjacent_le
  simp only [List.foldlM]
  -- Step through arrange's 13 instructions
  miden_movup; miden_movup; miden_swap
  miden_movup; miden_movdn; miden_movup; miden_movdn
  miden_movup; miden_movdn; miden_movup; miden_movdn
  miden_movup; miden_movdn
  -- Stack: [a3, b3, a2, b2, a1, b1, a0, b0] ++ rest
  -- push 1 then push 0
  rw [stepPush]; miden_bind
  rw [stepPush]; miden_bind
  -- Stack: [0, 1, a3, b3, a2, b2, a1, b1, a0, b0] ++ rest
  -- repeat 4: unfold doRepeat for each of 4 iterations
  -- Iteration 1: cmp_f=0, eq_f=1, ai=a3, bi=b3
  unfold execWithEnv.doRepeat
  rw [one_gt_iteration_body mem locs adv 0 1 a3 b3
        (a2 :: b2 :: a1 :: b1 :: a0 :: b0 :: rest)
        (by simp [Felt.isBool]) (by simp [Felt.isBool]) 18]
  simp only [Felt.val_zero', Felt.val_one',
             show ((0:Nat) == 1) = false from rfl,
             show ((1:Nat) == 1) = true from rfl,
             Bool.false_or, Bool.true_and]
  -- Stack: [(if decide(b3<a3) then 1 else 0), (if a3==b3 then 1 else 0),
  --         a2, b2, a1, b1, a0, b0, rest]
  -- Iteration 2: cmp_f=(if decide(b3<a3) then 1 else 0), eq_f=(if a3==b3 then 1 else 0)
  unfold execWithEnv.doRepeat
  rw [one_gt_iteration_body mem locs adv
        (if decide (b3.val < a3.val) then 1 else 0)
        (if (a3 == b3) then 1 else 0)
        a2 b2
        (a1 :: b1 :: a0 :: b0 :: rest)
        (Felt.isBool_ite_bool _) (Felt.isBool_ite_bool _) 18]
  simp only [Felt.ite_val_eq_one]
  -- Iteration 3
  unfold execWithEnv.doRepeat
  rw [one_gt_iteration_body mem locs adv
        (if decide (b3.val < a3.val) || a3 == b3 && decide (b2.val < a2.val) then 1 else 0)
        (if a3 == b3 && (a2 == b2) then 1 else 0)
        a1 b1
        (a0 :: b0 :: rest)
        (Felt.isBool_ite_bool _) (Felt.isBool_ite_bool _) 18]
  simp only [Felt.ite_val_eq_one]
  -- Iteration 4
  -- Note: after iteration 3's simp, the form is (P || Q && R || Q && S && T)
  -- which is left-associative. We need to match this exact form.
  unfold execWithEnv.doRepeat
  rw [one_gt_iteration_body mem locs adv
        (if decide (b3.val < a3.val) || a3 == b3 && decide (b2.val < a2.val) ||
             a3 == b3 && a2 == b2 && decide (b1.val < a1.val) then 1 else 0)
        (if a3 == b3 && a2 == b2 && a1 == b1 then 1 else 0)
        a0 b0 rest
        (Felt.isBool_ite_bool _) (Felt.isBool_ite_bool _) 18]
  simp only [Felt.ite_val_eq_one]
  -- doRepeat 0: done
  unfold execWithEnv.doRepeat
  -- Simplify the match that wraps the final result with beta reduction and if-elimination
  simp only [List.foldlM, Option.map, Option.bind, ite_self]
  -- Final: swap 1, drop
  miden_swap
  rw [stepDrop]; miden_bind
  -- Close by normalizing boolean expressions
  simp only [Bool.or_assoc, Bool.and_assoc, Bool.and_or_distrib_left]
  rfl

end MidenLean.Proofs
