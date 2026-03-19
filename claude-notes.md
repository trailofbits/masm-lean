# claude-notes.md

## 2026-03-19: Galvanize iteration 3-4 (semantic theorems)

### Completed in iteration 3
- AC-19: u64_neq_semantic (Neq.lean)
- AC-30: u64_and_toU64 (And.lean) via toU64_and bridge
- AC-31: u64_or_toU64 (Or.lean) via toU64_or bridge
- AC-32: u64_xor_toU64 (Xor.lean) via toU64_xor bridge
- AC-41: u64_min_semantic (Min.lean)
- AC-42: u64_max_semantic (Max.lean)

### Bridge infrastructure added to Interp.lean
- toU64_neq_iff: neq bridge
- toU64_testBit: testBit decomposition at 32-bit
  boundary using Nat.testBit_two_pow_mul_add
- toU64_and/or/xor: bitwise bridge via
  Nat.eq_of_testBit_eq extensionality
- Helper lemmas: felt_ofNat_val, isU32_lt,
  felt_ofNat_isU32, bitwise_u32_lt_prime

### Working on (iteration 4)
Remaining 22 unchecked ACs:
- AC-20: eqz (needs _correct theorem first)
- AC-21-29: arithmetic semantic theorems
  - wrapping_add has no _correct theorem yet
  - wrapping_sub uses cascaded u32OverflowingSub
  - wrapping_mul uses cross-product chain
  - widening_add/mul: could use toU128
  - div/mod/divmod: complex advice-tape hypotheses
- AC-33-36: shift/rotation (complex theorem shapes)
- AC-37-40: counting (need u64-level counting defs)
- AC-43-46: Bad fixes (stretch)

### Key decisions
- Bitwise semantic theorems use `_toU64` naming
  (separate bridge lemma) rather than restating the
  full execution in semantic terms
- Memory cap constraint added to CLAUDE.md after
  previous session OOM'd the machine

### Build status
0 errors, 0 warnings, 0 sorry

## Previous sessions
(see below for detailed history from earlier sessions)
