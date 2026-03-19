# Galvanize Goal: masm-lean Semantic Correctness

**Date:** 2026-03-18 (restored 2026-03-19)
**Initial prompt:** Semantics reference mapping, test
coverage, and semantic theorem strengthening for all
proved MASM procedures.

## Clarified Goal

Ensure the masm-lean formal verification project has:
(1) inline reference comments mapping each instruction
to its miden-vm Rust source, (2) comprehensive test
coverage including order-sensitive instructions, and
(3) semantic correctness theorems that state results
in terms of mathematical operations on interpreted
types (toU64, toU128) rather than raw field elements.

## Acceptance Criteria

### Tier 1: Semantics Reference Comments (complete)

- [x] AC-1: Instruction handler reference comments
- [x] AC-2: advPush reversal semantics documented
- [x] AC-3: Semantic discrepancies documented

### Tier 2: Test Gap Investigation (complete)

- [x] AC-4: advPush root cause documented
- [x] AC-5: Order-sensitive instruction classification

### Tier 3: Extended Tests (complete)

- [x] AC-6: advPush ordering test
- [x] AC-7: advPush N>2 ordering test
- [x] AC-8: Order-sensitive instruction tests
- [x] AC-9: All tests pass

### Tier 4: Interpretation Layer (complete)

- [x] AC-10: toU64 interpretation function
- [x] AC-11: toU128 interpretation function
- [x] AC-12: Bridge lemmas (toU64_eq_iff, toU64_lt_iff)
- [x] AC-13: toU128 bridge lemma (toU128_lt_iff)

### Tier 5: Semantic U64 Comparison & Equality

- [x] AC-14: u64_lt_semantic (toU64 a < toU64 b)
- [x] AC-15: u64_gt_semantic (toU64 b < toU64 a)
- [x] AC-16: u64_lte_semantic (not (toU64 b < toU64 a))
- [x] AC-17: u64_gte_semantic (not (toU64 a < toU64 b))
- [x] AC-18: u64_eq_semantic (toU64 a = toU64 b)
- [x] AC-19: u64_neq_semantic
- [ ] AC-20: u64_eqz_semantic (needs _correct first)

### Tier 6: Semantic U64 Arithmetic

- [ ] AC-21: u64_wrapping_add_semantic [blocked:
  needs wrapping_add _correct theorem first]
- [x] AC-22: u64_wrapping_sub_semantic
- [x] AC-23: u64_wrapping_mul_semantic (via
  cross_product_mod_2_64 bridge)
- [x] AC-24: u64_overflowing_sub_semantic
- [x] AC-25: u64_widening_add_semantic
- [ ] AC-26: u64_widening_mul_semantic (toU128 result)
- [ ] AC-27: u64_div_semantic
- [ ] AC-28: u64_mod_semantic
- [ ] AC-29: u64_divmod_semantic

### Tier 7: Semantic U64 Bitwise & Shifts

- [x] AC-30: u64_and_toU64 (bridge lemma)
- [x] AC-31: u64_or_toU64 (bridge lemma)
- [x] AC-32: u64_xor_toU64 (bridge lemma)
- [x] AC-33: u64_shl_semantic
- [ ] AC-34: u64_shr_semantic
- [ ] AC-35: u64_rotl_semantic
- [ ] AC-36: u64_rotr_semantic

### Tier 8: Semantic U64 Counting & Min/Max

- [ ] AC-37: u64_clz_semantic [blocked: needs u64
  clz definition]
- [ ] AC-38: u64_ctz_semantic [blocked: needs u64
  ctz definition]
- [ ] AC-39: u64_clo_semantic [blocked: needs u64
  clo definition]
- [ ] AC-40: u64_cto_semantic [blocked: needs u64
  cto definition]
- [x] AC-41: u64_min_semantic
- [x] AC-42: u64_max_semantic

### Tier 9: Fix Bad Findings (stretch)

- [ ] AC-43: Bounded stack model -- add minimum depth
  of 16 (zero-padded) and/or maximum depth of 2^16
  to match Rust VM semantics
- [ ] AC-44: Word-addressed memory -- refactor memory
  model from Nat -> Felt to Nat -> Word (4-element)
  to match Rust BTreeMap<u32, [Felt; 4]>
- [ ] AC-45: Emit reads event ID -- execEmit should
  read top stack element as event ID (not just check
  non-empty), and emitImm should use its argument
- [x] AC-46: Consistent NOT style -- unified to XOR

## Default Quality Requirements

- [x] lake build passes with 0 errors
- [x] 0 lint warnings
- [x] No sorry in any proof file

## Scope Boundaries

**In scope:** Reference comments, tests, semantic
theorems for all u64 procedures with existing proofs.

**Out of scope:** Word-level semantic theorems (deferred
until word axioms are fully eliminated), new procedure
proofs, modifying miden-vm.

## Revision History

- 2026-03-18: Initial goal (Tiers 1-3)
- 2026-03-18: Additive: Tiers 5-8 for semantic theorems
- 2026-03-18: Tiers 1-3 completed
- 2026-03-19: Restored lost Tiers 5-8 from iteration 2
  goal revision. Renumbered ACs. Added Tier 4 for
  already-completed interpretation layer. Marked
  completed semantic theorems (lt/gt/lte/gte/eq).
- 2026-03-19: Additive: Tier 9 (AC-43 to AC-46) for
  fixing the 4 Bad vivisect findings (stretch goal)
