import MidenLean.Proofs.Tactics
import MidenLean.Generated.Word

/-!
# Shared definitions for the `word` proof module

This file collects the pieces that several `word` proofs need:

* `wordProcEnv`, the procedure environment used by the word comparison
  procedures (`gt`, `lt`, `gte`, `lte`), which call each other and
  `arrange_words_adjacent_le`.
* `felt_ite_lt_decide` / `felt_ite_gt_decide`, which normalize the
  `Prop`-level `if` produced by the `lt`/`gt` step lemmas into the
  `Bool`-level `decide` form used in the correctness statements.
* `arrange_for_wordProcEnv`, the `arrange_words_adjacent_le` summary at the
  fuel and environment used by the `gt` and `lt` proofs.
-/

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
theorem felt_ite_lt_decide (a b : Felt) :
    (if a.val < b.val then (1:Felt) else 0) =
    (if decide (a.val < b.val) then (1:Felt) else 0) := by
  cases h : decide (a.val < b.val) <;> simp_all [decide_eq_true_eq, decide_eq_false_iff_not]

/-- Convert Prop-level `if a > b` to Bool-level `if decide (a > b)` for Felt values. -/
theorem felt_ite_gt_decide (a b : Felt) :
    (if a.val > b.val then (1:Felt) else 0) =
    (if decide (a.val > b.val) then (1:Felt) else 0) := by
  cases h : decide (a.val > b.val) <;> simp_all [decide_eq_true_eq, decide_eq_false_iff_not]

set_option maxHeartbeats 4000000 in
/-- `arrange_words_adjacent_le` interleaves the two input words, at the fuel and
    environment used by the `word::gt` and `word::lt` proofs. -/
theorem arrange_for_wordProcEnv
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt)
    (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt) :
    execProcedure wordProcEnv 2
      ⟨a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 :: rest, mem, frames, adv⟩
      Miden.Core.Word.arrange_words_adjacent_le =
    some ⟨b3 :: a3 :: b2 :: a2 :: b1 :: a1 :: b0 :: a0 :: rest, mem, frames, adv⟩ := by
  unfold Miden.Core.Word.arrange_words_adjacent_le execProcedure
  simp [Procedure.ofOps]
  miden_step; miden_step; miden_step; miden_step; miden_step  -- movup 7, movup 4, swap, movup 7, movdn 2
  miden_step; miden_step; miden_step; miden_step; miden_step  -- movup 5, movdn 3, movup 7, movdn 4, movup 6
  rw [stepMovdn (hn := rfl)]; miden_bind  -- movdn 5
  miden_step  -- movup 7
  rw [stepMovdn (hn := rfl)]  -- movdn 6
  dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure, insertAt, List.take, List.drop,
    List.cons_append, List.nil_append, List.append_nil]

end MidenLean.Proofs
