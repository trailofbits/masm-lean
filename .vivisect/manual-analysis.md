# Vivisect Manual Analysis: masm-lean

## Run 14 findings (post-AC-50-53, 2026-03-19)

AC-50 through AC-53 implemented. Verification pass
confirms overflow guards in all net-positive-stack
handlers, step lemma hov hypotheses, proof file hlen
hypotheses, and edge case tests.

### Verified: overflow guards complete

11 overflow guards added to Semantics.lean:
- L158: execPadw (+4 net stack)
- L162: execPush (+1)
- L166: execPushList (+N)
- L173: execDup (+1)
- L179: execDupw (+4)
- L465: execU32Test (+1)
- L471: execU32TestW (+1)
- L486: execU32Split (+1)
- L828: execMemLoadImm (+1)
- L935: execLocLoad (+1)
- L964: execAdvPush (+N)

All handlers with net zero or negative stack effect
(arithmetic, comparison, boolean, swap, movup, movdn,
assert, drop, memory load/store where address consumed)
correctly do NOT have overflow guards -- they cannot
increase stack depth.

### Verified: step lemmas updated

5 step lemmas in StepLemmas.lean have hov hypotheses:
- stepPush (L22): hov : stk.length + 1 <= MAX
- stepDup (L22): hov : stk.length + 1 <= MAX
- stepDupw (L391): hov : stk.length + 4 <= MAX
- stepU32Split (L337): hov : rest.length + 2 <= MAX
- stepAdvPush2 (L451): hov : stk.length + 2 <= MAX

### Verified: proof files updated

67 hov/hlen references across 20 proof files. All
correctness theorems carry `hlen : rest.length + 30
<= MAX_STACK_DEPTH` hypotheses ensuring sufficient
headroom for intermediate stack growth.

### Verified: edge case tests

Tests/Semantics.lean lines 1413-1479 test:
- push on full stack -> none (L1418-1423)
- push on stack with room -> some (L1426-1431)
- dup on full stack -> none (L1434-1439)
- padw when only 3 slots left -> none (L1442-1447)
- padw with exactly 4 slots -> some (L1450-1455)
- advPush on full stack -> none (L1458-1463)
- u32Split on full stack -> none (L1466-1471)
- drop on empty stack -> none (L1474-1478)

### Verified: diagnostics clean

Lean LSP reports 0 errors, 0 warnings for:
- Semantics.lean
- StepLemmas.lean
- Tests/Semantics.lean

### Previous Bad finding resolution

The run 12/13 Bad finding "stack depth not enforced
per-instruction" is now resolved:
- MAX_STACK_DEPTH overflow guards on all handlers
  with net positive stack effect
- wellFormed predicate at State.lean:122-124
- padStack function at State.lean:117-118
- Step lemmas carry hov hypotheses
- Proofs carry hlen hypotheses
- Edge case tests verify guard behavior

Remaining intentional simplification: Lean returns
none on short stacks (< required elements) where
Rust would auto-pad with zeros. This is the correct
modeling choice because:
1. wellFormed requires 16 <= len as hypothesis
2. All proofs carry sufficient-depth hypotheses
3. padStack available for creating well-formed states
4. Pattern matching on insufficient elements is
   standard for optional semantics

This is not a divergence from Rust -- it is a
different enforcement mechanism. Rust pads lazily;
Lean requires well-formed input via hypotheses.

### Spec divergence check (updated)

1. AC-50 (overflow guards): RESOLVED. 11 guards
   added to all net-positive-stack handlers.
2. AC-51 (step lemma hov): RESOLVED. 5 step lemmas
   updated.
3. AC-52 (proof hlen): RESOLVED. 20 proof files
   updated with 67 hov/hlen references.
4. AC-53 (edge case tests): RESOLVED. 8 tests at
   Tests/Semantics.lean:1413-1479.
5. Stale spec text (spec.md lines 155-156, 236-240):
   still describes element-addressed memory. Not a
   code bug.
6. Stale spec text (spec.md section 7 assert):
   describes "top != 0" but code requires top == 1.
   Not a code bug.

---
