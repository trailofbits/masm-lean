import MidenLean.Proofs.Helpers
import MidenLean.Proofs.StepLemmas
import MidenLean.Generated.Word

namespace MidenLean.Proofs

open MidenLean

set_option maxHeartbeats 8000000 in
/-- `word::testz` correctly tests whether a word is zero without consuming the input. -/
theorem word_testz_correct (a b c d : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = a :: b :: c :: d :: rest) :
    exec 20 s Miden.Core.Word.testz =
    some (s.withStack (
      (if (d == (0:Felt)) && ((c == (0:Felt)) && ((b == (0:Felt)) && (a == (0:Felt))))
       then (1 : Felt) else 0) :: a :: b :: c :: d :: rest)) := by
  -- Destructure the state to work with concrete fields
  obtain ⟨stk, mem, locs, adv⟩ := s
  subst hs
  -- Unfold top-level definitions
  unfold exec Miden.Core.Word.testz
  -- Unfold execWithEnv to process the foldlM over the 4-element op list
  unfold execWithEnv
  simp only [List.foldlM]
  -- The first op is repeat 4 [dup 3, eqImm 0]
  -- This calls doRepeat with fuel=19, n=4
  -- Iteration 1: stack = [a, b, c, d, ...rest]
  unfold execWithEnv.doRepeat
  unfold execWithEnv
  simp only [List.foldlM]
  -- dup 3 on [a, b, c, d, ...rest] → [d, a, b, c, d, ...rest]
  rw [StepLemmas.stepDup (h := rfl)]
  dsimp only [bind, Option.bind]
  -- eqImm 0 on [d, a, b, c, d, ...rest] → [(d==0?), a, b, c, d, ...rest]
  rw [StepLemmas.stepEqImm]
  dsimp only [bind, Option.bind]
  -- Iteration 2: stack = [(d==0?), a, b, c, d, ...rest]
  unfold execWithEnv.doRepeat
  unfold execWithEnv
  simp only [List.foldlM]
  -- dup 3 copies index 3 = c
  rw [StepLemmas.stepDup (h := rfl)]
  dsimp only [bind, Option.bind]
  -- eqImm 0 on [c, (d==0?), a, b, c, d, ...rest]
  rw [StepLemmas.stepEqImm]
  dsimp only [bind, Option.bind]
  -- Iteration 3: stack = [(c==0?), (d==0?), a, b, c, d, ...rest]
  unfold execWithEnv.doRepeat
  unfold execWithEnv
  simp only [List.foldlM]
  -- dup 3 copies index 3 = b
  rw [StepLemmas.stepDup (h := rfl)]
  dsimp only [bind, Option.bind]
  -- eqImm 0 on [b, (c==0?), (d==0?), a, b, c, d, ...rest]
  rw [StepLemmas.stepEqImm]
  dsimp only [bind, Option.bind]
  -- Iteration 4: stack = [(b==0?), (c==0?), (d==0?), a, b, c, d, ...rest]
  unfold execWithEnv.doRepeat
  unfold execWithEnv
  simp only [List.foldlM]
  -- dup 3 copies index 3 = a
  rw [StepLemmas.stepDup (h := rfl)]
  dsimp only [bind, Option.bind]
  -- eqImm 0 on [a, (b==0?), (c==0?), (d==0?), a, b, c, d, ...rest]
  rw [StepLemmas.stepEqImm]
  dsimp only [bind, Option.bind]
  -- doRepeat base case (n = 0)
  unfold execWithEnv.doRepeat
  dsimp only [bind, Option.bind]
  -- Now stack: [(a==0?), (b==0?), (c==0?), (d==0?), a, b, c, d, ...rest]
  -- Process the three and instructions
  -- and 1: [(a==0?), (b==0?), ...] → [(b==0?) && (a==0?), ...]
  rw [StepLemmas.stepAndIte]
  dsimp only [bind, Option.bind]
  -- and 2: [(b==0?) && (a==0?), (c==0?), ...] → [(c==0?) && ((b==0?) && (a==0?)), ...]
  rw [StepLemmas.stepAndIte]
  dsimp only [bind, Option.bind]
  -- and 3: result → [(d==0?) && ((c==0?) && ((b==0?) && (a==0?))), a, b, c, d, ...rest]
  rw [StepLemmas.stepAndIte]
  simp only [MidenState.withStack]
  rfl

end MidenLean.Proofs
