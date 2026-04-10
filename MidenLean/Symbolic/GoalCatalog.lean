import MidenLean.Proofs.Tactics
import MidenLean.Symbolic.Tactic
import MidenLean.Generated.Word

/-!
# Goal Catalog — VCG Regression Tests

Captures regression tests for `miden_vcg` + `miden_finish_reflection` on
pilot procedures. All theorems should close without `sorry`.

## Status

### `word::eqz` — PASSING
Fixed by `decidable_rec_const` + `split_ifs <;> simp_all <;> tauto` in
`miden_finish_reflection`. The `Decidable.rec` kernel forms are normalized
to `if-then-else` by the `miden_reflect_norm` simp set, then the residual
nested-if and `em'` goals are closed by `split_ifs` and `tauto`.

### `word::testz` — PASSING (32M heartbeats)
Same normalization path as `eqz`. Needs high heartbeats due to 10-iteration
repeat decomposition in `miden_vcg`.

Do not import this file from production code.
-/

namespace MidenLean.Symbolic.GoalCatalog

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

-- Regression test: word::eqz — was broken by Decidable.rec, fixed by decidable_rec_const
set_option maxHeartbeats 4000000 in
theorem eqz_vcg_regression
    (a b c d : Felt) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = a :: b :: c :: d :: rest) :
    execProcedure emptyEnv 25 s Miden.Core.Word.eqz =
    some (s.withStack (
      (if (a == (0 : Felt)) && (b == (0 : Felt)) && (c == (0 : Felt)) && (d == (0 : Felt))
       then (1 : Felt) else 0) :: rest)) := by
  miden_vcg
  all_goals miden_finish_reflection

-- Target: word::testz — 10 identical hpreconds goals after miden_vcg
-- miden_vcg needs >16M heartbeats for 10-iteration repeat decomposition
set_option maxHeartbeats 32000000 in
theorem testz_vcg_test
    (a b c d : Felt) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = a :: b :: c :: d :: rest) :
    execProcedure emptyEnv 25 s Miden.Core.Word.testz =
    some (s.withStack (
      (if (d == (0:Felt)) && ((c == (0:Felt)) && ((b == (0:Felt)) && (a == (0:Felt))))
       then (1 : Felt) else 0) :: a :: b :: c :: d :: rest)) := by
  miden_vcg
  all_goals miden_finish_reflection

end MidenLean.Symbolic.GoalCatalog
