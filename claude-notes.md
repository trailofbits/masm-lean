# Claude Notes: audit-0xmiden/masm-lean

## 2026-03-19: Galvanize iteration 10

### Completed
- AC-34/35/36: shr/rotl/rotr semantic theorems (iter 9)
- StepLemmas.lean: 45 maxHeartbeats removed via
  EquationLemmas.lean (O(1) dispatch lemmas)
- Helpers.lean: removed @[simp] from equation lemmas
  to prevent eager rewriting in downstream proofs
- Build: EXIT 0, 0 errors, 0 warnings, 46/49 ACs

### In progress: AC-47 (remove all maxHeartbeats)
- StepLemmas.lean: DONE (0 remaining)
- Helpers.lean: 1 remaining (line 42)
- Felt.lean: 1 remaining (line 12)
- ~70 proof files still have maxHeartbeats
  Strategy: most will just work once the foundation
  (StepLemmas) is fast. Try removing in batch.

### Remaining ACs
- AC-47: Remove maxHeartbeats from non-Generated files
- AC-48: [ongoing] No maxHeartbeats in non-Generated
- AC-45: Emit event ID (structural MidenState change)
- AC-43: Bounded stack model
- AC-44: Word-addressed memory

### Key technique: equation lemmas
Each instruction gets a theorem:
  execInstruction s .foo = execFoo s := rfl
This is O(1) because rfl on a specific constructor
match. Then step lemmas do:
  simp only [execInstruction_foo]; unfold execFoo; ...
The equation lemma handles the dispatch; unfold handles
the small handler function. Total cost: O(1) + O(handler).
DO NOT mark equation lemmas @[simp] -- that causes eager
rewriting that breaks proofs using rw [stepFoo].

### Prior sessions (condensed)
See git log for full history.
