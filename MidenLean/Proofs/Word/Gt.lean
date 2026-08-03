import MidenLean.Proofs.Word.Common
import MidenLean.Proofs.Tactics
import MidenLean.Symbolic.Tactic
import MidenLean.Generated.Word

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

-- One iteration of the word.gt comparison loop.
set_option maxHeartbeats 4000000 in
private theorem gt_iteration
    (result undecided : Bool) (b_i a_i : Felt) (tail : List Felt)
    (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt) :
    let eq_flag := (b_i == a_i)
    let lt_flag := decide (a_i.val < b_i.val)
    let new_result := result || (undecided && lt_flag)
    let new_undecided := undecided && eq_flag
    execProcedure wordProcEnv 2
      ⟨(if result then (1:Felt) else 0) :: (if undecided then (1:Felt) else 0) ::
        b_i :: a_i :: tail, mem, frames, adv⟩
      (Procedure.ofOps
        [.inst (.movup 3), .inst (.movup 3), .inst (.dup 0), .inst (.dup 2),
         .inst (.eq), .inst (.movdn 3), .inst (.lt), .inst (.dup 3),
         .inst (.and), .inst (.or), .inst (.movdn 2), .inst (.and), .inst (.swap 1)]) =
    some ⟨(if new_result then (1:Felt) else 0) ::
          (if new_undecided then (1:Felt) else 0) :: tail, mem, frames, adv⟩ := by
  unfold execProcedure
  simp [Procedure.ofOps]
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
  simp [decide_eq_true_eq]

-- First iteration specialized for concrete 0/1 stack values.
private theorem gt_iteration_init
    (b_i a_i : Felt) (tail : List Felt)
    (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt) :
    execProcedure wordProcEnv 2
      ⟨(0:Felt) :: (1:Felt) :: b_i :: a_i :: tail, mem, frames, adv⟩
      (Procedure.ofOps
        [.inst (.movup 3), .inst (.movup 3), .inst (.dup 0), .inst (.dup 2),
         .inst (.eq), .inst (.movdn 3), .inst (.lt), .inst (.dup 3),
         .inst (.and), .inst (.or), .inst (.movdn 2), .inst (.and), .inst (.swap 1)]) =
    some ⟨(if decide (a_i.val < b_i.val) then (1:Felt) else 0) ::
          (if (b_i == a_i) then (1:Felt) else 0) :: tail, mem, frames, adv⟩ :=
  gt_iteration false true b_i a_i tail mem frames adv

set_option maxHeartbeats 16000000 in
private theorem word_gt_exec_concrete
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 :: rest) :
    execProcedure wordProcEnv 3 s Miden.Core.Word.gt =
    some (s.withStack ((if decide (a3.val < b3.val)
                  || ((b3 == a3) && decide (a2.val < b2.val))
                  || ((b3 == a3) && (b2 == a2) && decide (a1.val < b1.val))
                  || ((b3 == a3) && (b2 == a2) && (b1 == a1) && decide (a0.val < b0.val))
                then (1:Felt) else 0) :: rest)) := by
  obtain ⟨stk, mem, frames, adv⟩ := s
  simp only [Concrete.State.withStack] at hs ⊢
  subst hs
  -- Unfold procedure and resolve arrange call
  unfold Miden.Core.Word.gt execProcedure
  simp [Procedure.ofOps, wordProcEnv]
  dsimp only [bind, Bind.bind, Option.bind]
  rw [arrange_for_wordProcEnv a0 a1 a2 a3 b0 b1 b2 b3 rest mem frames adv]
  dsimp only [bind, Bind.bind, Option.bind]
  -- push 1, push 0
  rw [stepPush]; miden_bind
  rw [stepPush]; miden_bind
  -- Iteration 1: result=false, undecided=true, b_i=b3, a_i=a3
  unfold execProcedure.doRepeat
  rw [gt_iteration_init b3 a3 (b2 :: a2 :: b1 :: a1 :: b0 :: a0 :: rest) mem frames adv]
  dsimp only []
  -- Iteration 2
  unfold execProcedure.doRepeat
  rw [gt_iteration _ _ b2 a2 (b1 :: a1 :: b0 :: a0 :: rest) mem frames adv]
  dsimp only []
  -- Iteration 3
  unfold execProcedure.doRepeat
  rw [gt_iteration _ _ b1 a1 (b0 :: a0 :: rest) mem frames adv]
  dsimp only []
  -- Iteration 4
  unfold execProcedure.doRepeat
  rw [gt_iteration _ _ b0 a0 rest mem frames adv]
  dsimp only []
  -- doRepeat base case
  unfold execProcedure.doRepeat
  dsimp only [bind, Bind.bind, Option.bind]
  -- swap and drop
  miden_step  -- swap 1
  rw [stepDrop]
  simp

/-- `word::gt` pushes 1 iff the deeper word (pushed first, limbs `b0..b3`) is
    lexicographically greater than the top word, comparing limbs from the most
    significant (index 3) downward.
    Parametric in `fuel` (derived from the concrete-fuel proof by fuel
    monotonicity) so this lemma serves both as a callee summary for reflective
    callers and as the basis for `word_gt_correct`. The env is fixed to
    `wordProcEnv` because the proof resolves the `exec arrange_words_adjacent_le`
    call by unfolding that environment. -/
@[miden_exec_summary]
theorem word_gt_exec (fuel : Nat)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 :: rest) :
    execProcedure wordProcEnv (fuel + 3) s Miden.Core.Word.gt =
    some (s.withStack ((if decide (a3.val < b3.val)
                  || ((b3 == a3) && decide (a2.val < b2.val))
                  || ((b3 == a3) && (b2 == a2) && decide (a1.val < b1.val))
                  || ((b3 == a3) && (b2 == a2) && (b1 == a1) && decide (a0.val < b0.val))
                then (1:Felt) else 0) :: rest)) :=
  execProcedure_fuel_mono (by omega)
    (word_gt_exec_concrete a0 a1 a2 a3 b0 b1 b2 b3 rest s hs)

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
