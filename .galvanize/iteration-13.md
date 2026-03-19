## Iteration 13
**Date:** 2026-03-19
**Vivisect run:** #13 (full mode)

### Vivisect Findings (Phase 1)
| Category | Count |
|----------|-------|
| Broken   | 0     |
| Absurd   | 0     |
| Bad      | 1     |
| Good     | 17    |

Bad-1: Stack depth not enforced per-instruction
(now addressed by AC-50 through AC-53).

### Changes Made (Phases 2-3)
- Semantics.lean: added overflow guards to 11
  handlers with net positive stack effect (execPadw,
  execPush, execPushList, execDup, execDupw,
  execU32Test, execU32TestW, execU32Split,
  execMemLoadImm, execLocLoad, execAdvPush). Each
  checks `s.stack.length + N > MAX_STACK_DEPTH`
  and returns `none` on overflow.
- StepLemmas.lean: added `hov` hypotheses to
  stepPush, stepDup, stepDupw, stepU32Split,
  stepAdvPush2. Proofs use `have : not ... := by
  omega` pattern.
- Tactics.lean: miden_step discharges overflow
  hypotheses via `(hov := by simp [List.length_cons];
  omega)`. Fixed pre-existing `ha_align` bug.
- 30+ proof files: added `(hlen : rest.length + 30
  <= MAX_STACK_DEPTH)` hypothesis to all correctness
  theorems that use stack-growing instructions.
  Propagated through helper theorems and callers.
- Tests/Semantics.lean: 8 new edge case tests for
  stack overflow (push/dup/padw/advPush/u32Split on
  full stack) and underflow (drop on empty stack).
- CLAUDE.md: fixed stale `-j 2` flag (Lake 5.0.0
  does not support -j). Added exit code check to
  build command examples.
- .vivisect/guidelines.md: same `-j 2` fix.
- Build: 1913 jobs, 0 errors, 0 warnings, 0 sorry.

### Tarot Log
None

### Convergence Status
Pending Phase 4 check.
