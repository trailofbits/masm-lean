import MidenLean.Proofs.Tactics
import MidenLean.Proofs.Word.Arrange
import MidenLean.Generated.Word

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

/-- Procedure environment for word comparison procedures. -/
def wordProcEnv : ProcEnv := fun name =>
  match name with
  | "arrange_words_adjacent_le" => some Miden.Core.Word.arrange_words_adjacent_le
  | "lt" => some Miden.Core.Word.lt
  | "gt" => some Miden.Core.Word.gt
  | _ => none

/-- Convert Prop-level `if a < b` to Bool-level `if decide (a < b)` for Felt values. -/
private theorem felt_ite_lt_decide (a b : Felt) :
    (if a.val < b.val then (1:Felt) else 0) =
    (if decide (a.val < b.val) then (1:Felt) else 0) := by
  cases h : decide (a.val < b.val) <;> simp_all [decide_eq_true_eq, decide_eq_false_iff_not]

/-- Convert Prop-level `if a > b` to Bool-level `if decide (a > b)` for Felt values. -/
private theorem felt_ite_gt_decide (a b : Felt) :
    (if a.val > b.val then (1:Felt) else 0) =
    (if decide (a.val > b.val) then (1:Felt) else 0) := by
  cases h : decide (a.val > b.val) <;> simp_all [decide_eq_true_eq, decide_eq_false_iff_not]

theorem arrange_for_wordProcEnv
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt) :
    execWithEnv wordProcEnv 2
      ⟨a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 :: rest, mem, locs, adv, evts⟩
      Miden.Core.Word.arrange_words_adjacent_le =
    some ⟨b3 :: a3 :: b2 :: a2 :: b1 :: a1 :: b0 :: a0 :: rest, mem, locs, adv, evts⟩ := by
  unfold Miden.Core.Word.arrange_words_adjacent_le execWithEnv
  simp only [List.foldlM]
  miden_step; miden_step; miden_step; miden_step; miden_step  -- movup 7, movup 4, swap, movup 7, movdn 2
  miden_step; miden_step; miden_step; miden_step; miden_step  -- movup 5, movdn 3, movup 7, movdn 4, movup 6
  rw [stepMovdn (hn := rfl)]; miden_bind  -- movdn 5
  miden_step  -- movup 7
  rw [stepMovdn (hn := rfl)]  -- movdn 6
  dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure, insertAt, List.take, List.drop,
    List.cons_append, List.nil_append, List.append_nil]

-- One iteration of the word.gt comparison loop.
private theorem gt_iteration
    (result undecided : Bool) (b_i a_i : Felt) (tail : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt) :
    let eq_flag := (b_i == a_i)
    let lt_flag := decide (a_i.val < b_i.val)
    let new_result := result || (undecided && lt_flag)
    let new_undecided := undecided && eq_flag
    execWithEnv wordProcEnv 2
      ⟨(if result then (1:Felt) else 0) :: (if undecided then (1:Felt) else 0) ::
        b_i :: a_i :: tail, mem, locs, adv, evts⟩
      [.inst (.movup 3), .inst (.movup 3), .inst (.dup 0), .inst (.dup 2),
       .inst (.eq), .inst (.movdn 3), .inst (.lt), .inst (.dup 3),
       .inst (.and), .inst (.or), .inst (.movdn 2), .inst (.and), .inst (.swap 1)] =
    some ⟨(if new_result then (1:Felt) else 0) ::
          (if new_undecided then (1:Felt) else 0) :: tail, mem, locs, adv, evts⟩ := by
  unfold execWithEnv
  simp only [List.foldlM]
  miden_step; miden_step  -- movup 3, movup 3
  miden_step; miden_step  -- dup 0, dup 2
  miden_step              -- eq
  miden_step              -- movdn 3
  rw [stepLt]; miden_bind  -- lt
  rw [felt_ite_lt_decide]
  miden_step  -- dup 3
  miden_step  -- and
  miden_step  -- or
  miden_step  -- movdn 2
  miden_step  -- and
  miden_step  -- swap 1
  rw [Bool.and_comm (decide (a_i.val < b_i.val)) undecided]
  dsimp only [pure, Pure.pure]

-- First iteration specialized for concrete 0/1 stack values.
private theorem gt_iteration_init
    (b_i a_i : Felt) (tail : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt) :
    execWithEnv wordProcEnv 2
      ⟨(0:Felt) :: (1:Felt) :: b_i :: a_i :: tail, mem, locs, adv, evts⟩
      [.inst (.movup 3), .inst (.movup 3), .inst (.dup 0), .inst (.dup 2),
       .inst (.eq), .inst (.movdn 3), .inst (.lt), .inst (.dup 3),
       .inst (.and), .inst (.or), .inst (.movdn 2), .inst (.and), .inst (.swap 1)] =
    some ⟨(if decide (a_i.val < b_i.val) then (1:Felt) else 0) ::
          (if (b_i == a_i) then (1:Felt) else 0) :: tail, mem, locs, adv, evts⟩ :=
  gt_iteration false true b_i a_i tail mem locs adv

/-- `word::gt` correctly compares two words lexicographically. -/
theorem word_gt_correct
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 :: rest) :
    let result := decide (a3.val < b3.val)
                  || ((b3 == a3) && decide (a2.val < b2.val))
                  || ((b3 == a3) && (b2 == a2) && decide (a1.val < b1.val))
                  || ((b3 == a3) && (b2 == a2) && (b1 == a1) && decide (a0.val < b0.val))
    execWithEnv wordProcEnv 3 s Miden.Core.Word.gt =
    some (s.withStack ((if result then (1:Felt) else 0) :: rest)) := by
  obtain ⟨stk, mem, locs, adv, evts⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  -- Unfold procedure and resolve arrange call
  unfold Miden.Core.Word.gt execWithEnv
  simp only [List.foldlM, wordProcEnv]
  dsimp only [bind, Bind.bind, Option.bind]
  rw [arrange_for_wordProcEnv a0 a1 a2 a3 b0 b1 b2 b3 rest mem locs adv]
  dsimp only [bind, Bind.bind, Option.bind]
  -- push 1, push 0
  rw [stepPush]; miden_bind
  rw [stepPush]; miden_bind
  -- Iteration 1: result=false, undecided=true, b_i=b3, a_i=a3
  unfold execWithEnv.doRepeat
  rw [gt_iteration_init b3 a3 (b2 :: a2 :: b1 :: a1 :: b0 :: a0 :: rest) mem locs adv]
  dsimp only []
  -- Iteration 2
  unfold execWithEnv.doRepeat
  rw [gt_iteration _ _ b2 a2 (b1 :: a1 :: b0 :: a0 :: rest) mem locs adv]
  dsimp only []
  -- Iteration 3
  unfold execWithEnv.doRepeat
  rw [gt_iteration _ _ b1 a1 (b0 :: a0 :: rest) mem locs adv]
  dsimp only []
  -- Iteration 4
  unfold execWithEnv.doRepeat
  rw [gt_iteration _ _ b0 a0 rest mem locs adv]
  dsimp only []
  -- doRepeat base case
  unfold execWithEnv.doRepeat
  dsimp only [bind, Bind.bind, Option.bind]
  -- swap and drop
  miden_step  -- swap 1
  rw [stepDrop]
  dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]

end MidenLean.Proofs
