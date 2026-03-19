# Galvanize Goal: Semantics Reference Mapping & Test
# Coverage

**Date:** 2026-03-18
**Initial prompt:** Do the mapping before more proving. The
mapping should be incorporated as comments in the files
defining semantics. Also investigate why the existing test
suite didn't catch the advPush ordering bug. Extend tests.

## Clarified Goal

Add inline reference comments to Semantics.lean mapping
each instruction handler to its miden-vm Rust source, so
that semantic correctness can be verified by inspection
against the reference implementation. Then investigate the
test gap that allowed the divmod advPush ordering bug to
ship, and extend the test suite to catch such issues.

The divmod bug was: advPush.2 reverses elements from the
advice tape, but the theorem assumed they weren't reversed.
The existing #eval tests in Tests/Semantics.lean didn't
exercise advPush with multi-element pushes in a way that
would expose ordering errors.

## Acceptance Criteria

### Tier 1: Semantics Reference Comments

- [x] AC-1: Each instruction handler in Semantics.lean has
  a comment citing the miden-vm source file and line range
  for its reference implementation
- [x] AC-2: advPush handler comment explicitly documents
  the reversal semantics with a concrete example
- [x] AC-3: Any semantic discrepancy found during the
  mapping is documented in a comment (even if not fixed,
  the discrepancy is visible)

### Tier 2: Test Gap Investigation

- [x] AC-4: Root cause documented: why the existing
  Tests/Semantics.lean #eval tests did not catch the
  advPush ordering issue in divmod
- [x] AC-5: Classification of which instructions have
  order-sensitive semantics (advPush, advLoadW, movup,
  movdn, swap, etc.) vs order-insensitive

### Tier 3: Extended Tests

- [x] AC-6: advPush ordering test: #eval test that pushes
  [a, b] from advice and verifies stack order is [b, a]
  (the reversal)
- [x] AC-7: advPush N>2 ordering test if advPush supports
  N>2 in the model
- [x] AC-8: For each order-sensitive instruction, at least
  one #eval test that would fail if the operand order were
  swapped
- [x] AC-9: All tests pass (`lake build MidenLean` clean)

## Default Quality Requirements

- [x] lake build passes with 0 errors
- [x] 0 lint warnings
- [x] No sorry in any proof file

## Scope Boundaries

**In scope:** Reference comments in Semantics.lean,
test investigation and extension in Tests/Semantics.lean.

**Out of scope:** Fixing semantic discrepancies found
during mapping (document only); new proofs; refactoring
Semantics.lean structure.

## Revision History

- 2026-03-18: Initial goal (semantics mapping + tests)
- 2026-03-18: All ACs completed
