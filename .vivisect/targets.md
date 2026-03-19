# Vivisect Targets: masm-lean

**Date:** 2026-03-18
**Source files:** 44, **Functions:** 302
**Total targets:** 3

| # | Target | Scope | Priority | Phase | Findings |
|---|--------|-------|----------|-------|----------|
| 1 | core-semantics | Felt.lean, State.lean, Instruction.lean, Op.lean, Semantics.lean | Must | Pending | |
| 2 | generated-procs | Generated/U64.lean, Generated/Word.lean | Must | Pending | |
| 3 | proofs | Proofs/*.lean | Must | Pending | |

## Target Details

### Target 1: core-semantics
The execution engine: field element type (Felt),
machine state (MidenState), instruction definitions,
and the main dispatch + handler functions in
Semantics.lean. This is the highest-value target
because all semantic correctness depends on it.

Files:
- MidenLean/Felt.lean (39 lines)
- MidenLean/State.lean (43 lines)
- MidenLean/Instruction.lean (170 lines)
- MidenLean/Op.lean (33 lines)
- MidenLean/Semantics.lean (1105 lines)

### Target 2: generated-procs
Rust-translated procedure bodies for u64 and word
operations. These are the "programs" that run on top
of the core semantics.

Files:
- MidenLean/Generated/U64.lean (458 lines)
- MidenLean/Generated/Word.lean (154 lines)

### Target 3: proofs
Correctness theorems for generated procedures.
Validates that the generated code computes the
intended mathematical function.

Files:
- MidenLean/Proofs/*.lean (all 28 proof files)
- MidenLean/Proofs/Helpers.lean (194 lines)
- MidenLean/Proofs/StepLemmas.lean (397 lines)
- MidenLean/Proofs/Tactics.lean (91 lines)
