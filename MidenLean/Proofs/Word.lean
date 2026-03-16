import MidenLean.Proofs.Helpers
import MidenLean.Generated.Word

namespace MidenLean.Proofs

open MidenLean

-- Helper: stepInstruction for eqImm on a cons stack
private theorem step_eqImm_cons (s : MidenState) (v a : Felt) (rest : List Felt)
    (hs : s.stack = a :: rest) :
    stepInstruction s (Instruction.eqImm v) =
    some (s.withStack ((if a == v then (1 : Felt) else 0) :: rest)) := by
  unfold stepInstruction; rw [hs]

-- Helper: stepInstruction for swap 1 on a two-element-or-more stack
private theorem step_swap1_cons (s : MidenState) (x y : Felt) (rest : List Felt)
    (hs : s.stack = x :: y :: rest) :
    stepInstruction s (Instruction.swap 1) =
    some (s.withStack (y :: x :: rest)) := by
  unfold stepInstruction; rw [hs]; simp

-- Helper: stepInstruction for and on two boolean felts
private theorem step_and_bools (s : MidenState) (p q : Bool) (rest : List Felt)
    (hs : s.stack = (if p then (1:Felt) else 0) :: (if q then (1:Felt) else 0) :: rest) :
    stepInstruction s (Instruction.and) =
    some (s.withStack ((if (q && p) then (1 : Felt) else 0) :: rest)) := by
  unfold stepInstruction; rw [hs]
  simp [Felt.isBool_ite_bool]
  cases p <;> cases q <;> simp

-- Helper: one iteration of [swap 1, eqImm 0, and]
private theorem one_iteration_body
    (s : MidenState) (acc : Bool) (x : Felt) (tail : List Felt) (n : Nat)
    (hs : s.stack = (if acc then (1:Felt) else 0) :: x :: tail) :
    execOps (fun _ => none) (n + 1) s
      [.inst (.swap 1), .inst (.eqImm 0), .inst (.and)] =
    some (s.withStack ((if (acc && (x == (0:Felt))) then (1:Felt) else 0) :: tail)) := by
  unfold execOps
  simp only [List.foldlM]
  have h_swap := step_swap1_cons s _ _ _ hs
  rw [h_swap]; dsimp only [bind, Option.bind]
  have h_eq := step_eqImm_cons (s.withStack (x :: (if acc then (1:Felt) else 0) :: tail)) 0 x
    ((if acc then (1:Felt) else 0) :: tail)
    (MidenState.withStack_stack s _)
  rw [h_eq]; dsimp only [bind, Option.bind]
  have h_and := step_and_bools
    ((s.withStack (x :: (if acc then (1 : Felt) else 0) :: tail)).withStack
      ((if x == (0 : Felt) then (1 : Felt) else 0) :: (if acc then (1 : Felt) else 0) :: tail))
    (x == (0:Felt)) acc tail
    (MidenState.withStack_stack _ _)
  rw [h_and]
  simp [MidenState.withStack_withStack]

set_option maxHeartbeats 4000000 in
theorem word_eqz_correct (a b c d : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = a :: b :: c :: d :: rest) :
    exec 10 s Miden.Core.Word.eqz =
    some (s.withStack (
      (if (a == (0:Felt)) && (b == (0:Felt)) && (c == (0:Felt)) && (d == (0:Felt))
       then (1 : Felt) else 0) :: rest)) := by
  -- Unfold the top-level definitions
  unfold exec Miden.Core.Word.eqz
  unfold execOps
  simp only [List.foldlM]
  -- First instruction: eqImm 0
  have h_eq0 := step_eqImm_cons s 0 a (b :: c :: d :: rest) hs
  rw [h_eq0]; dsimp only [bind, Option.bind]
  -- doRepeat 9 3 body state: unroll 3 iterations
  -- Iteration 1: acc = (a == 0), x = b
  unfold execOps.doRepeat
  rw [one_iteration_body _ (a == (0:Felt)) b (c :: d :: rest) 8 (MidenState.withStack_stack s _)]
  simp only [MidenState.withStack_withStack]
  -- Iteration 2: acc = (a == 0) && (b == 0), x = c
  unfold execOps.doRepeat
  rw [one_iteration_body _ ((a == (0:Felt)) && (b == (0:Felt))) c (d :: rest) 8
    (MidenState.withStack_stack s _)]
  simp only [MidenState.withStack_withStack]
  -- Iteration 3: acc = (a == 0) && (b == 0) && (c == 0), x = d
  unfold execOps.doRepeat
  rw [one_iteration_body _ ((a == (0:Felt)) && (b == (0:Felt)) && (c == (0:Felt))) d rest 8
    (MidenState.withStack_stack s _)]
  simp only [MidenState.withStack_withStack]
  -- doRepeat 9 0 = some st
  unfold execOps.doRepeat
  simp

end MidenLean.Proofs
