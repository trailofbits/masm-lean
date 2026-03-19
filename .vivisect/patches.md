# Vivisect Patches: masm-lean

Date: 2026-03-19

## Previously Applied Patches

All patches from the 2026-03-18 run have been
applied:

1. word_lt_full_correct: proved (WordLt.lean)
2. word_lte_full_correct: proved (WordLte.lean)
3. word_gte_full_correct: proved (WordGte.lean)
4. NOT style normalization: applied
   (u32CountLeadingOnes uses XOR)

## Current Findings

### Bad: Element-addressed memory

No patch proposed. This is an intentional modeling
simplification. Changing to word-addressed memory
(Nat -> Word) would require updating all memory
handlers and all proofs that reference memory.
This is tracked as galvanize AC-44.

### Bad: Stack depth not enforced per-instruction

No patch proposed. The bounded stack
infrastructure (wellFormed, padStack) is in place.
Enforcing depth per-instruction would require
wrapping each handler with depth checks. This is
tracked as galvanize AC-43, partially implemented
(definitions exist, enforcement is Prop-level).

## No Broken/Absurd Patches Needed

No Broken or Absurd findings exist in this run.
