# claude-notes.md

## 2026-03-19: Galvanize semantic theorems session

### Summary
33/49 ACs completed (67%). Added 15 semantic theorems
and bridge lemmas for u64 procedures.

### Key bridge infrastructure (Interp.lean)
- toU64_neq_iff, toU64_testBit (32-bit boundary)
- toU64_and/or/xor (via Nat.eq_of_testBit_eq)
- cross_product_mod_2_64: carry chain identity for
  limb-level multiplication (manual Nat.div_add_mod
  decomposition). Unblocks wrapping_mul, shl, and
  potentially shr/rotl/rotr.
- felt_lo32_hi32_toU64: lo32/hi32 split-rejoin = id
- u64_lt_condition_eq: comparison bridge (pre-existing)

### Semantic theorems added
- Tier 5: neq_semantic
- Tier 6: wrapping_sub, overflowing_sub, widening_add,
  wrapping_mul
- Tier 7: and/or/xor_toU64, shl_semantic
- Tier 8: min/max_semantic
- Tier 9: NOT style fix (AC-46)

### Remaining (16 ACs)
- AC-20: eqz (needs _correct theorem)
- AC-21: wrapping_add (needs _correct theorem)
- AC-26: widening_mul (128-bit carry chain)
- AC-27-29: div/mod/divmod (advice tape extraction)
- AC-34: shr (uses field inverse, complex)
- AC-35-36: rotl/rotr (conditional cross-product)
- AC-37-40: counting (needs u64-level definitions)
- AC-43-45: stretch (structural changes)

### Build constraints
- MANDATORY: all lake build commands must use
  systemd-run --user --scope -p MemoryMax=10G
- Previous session OOM'd machine by removing this
