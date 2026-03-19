# Vivisect Patches: masm-lean

Date: 2026-03-18

## Absurd: Replace axioms with proofs

### Patch 1: Prove word_lt_full_correct

The word::lt loop body is structurally identical to
word::gt but uses `.gt` instead of `.lt` (comparing
in the opposite direction). The proof technique from
`one_gt_iteration_body` can be adapted:

1. Write `one_lt_iteration_body` analogous to
   `one_gt_iteration_body` (WordGt.lean:25-68).
   The only difference: the loop uses `.gt` for
   the comparison, so the condition becomes
   `decide (ai.val < bi.val)` instead of
   `decide (bi.val < ai.val)`.

2. Write `word_lt_correct` by 4-iteration induction
   (same pattern as WordGt.lean:76-158).

3. Remove `axiom word_lt_full_correct` from
   WordLt.lean.

### Patch 2: Derive word_lte_correct from word_gt

word::lte is `exec "gt"; not`. Given
`word_gt_correct`, the proof is:
1. Unfold lte body.
2. Apply word_gt_correct for the exec "gt" step.
3. Apply stepNot for the not step.
4. Remove `axiom word_lte_full_correct` from
   WordLte.lean.

### Patch 3: Derive word_gte_correct from word_lt

Same as Patch 2 but using word_lt_correct (from
Patch 1) and negating. Remove
`axiom word_gte_full_correct` from WordGte.lean.

## Bad: Normalize NOT style

### Patch 4: Use consistent NOT in count functions

Change u32CountLeadingOnes (Semantics.lean:91) from:
```lean
u32CountLeadingZeros (u32Max - 1 - n)
```
to:
```lean
u32CountLeadingZeros (n ^^^ (u32Max - 1))
```

Or vice versa (change u32CountTrailingOnes line 95).
Both are equivalent for u32 values. This is cosmetic
only.
