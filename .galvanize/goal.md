# Galvanize Goal: u64.divmod Correctness Proof

**Date:** 2026-03-18
**Initial prompt:** Prove u64.divmod correct, then re-enable
Divmod/Div/Mod imports so the build includes them with zero
sorry.

## Clarified Goal

The u64.divmod procedure is a 50-instruction advice-tape
procedure that performs 64-bit unsigned division. Given
dividend a = (a_hi, a_lo) and divisor b = (b_lo, b_hi) on
the stack, it reads quotient q and remainder r from the
advice tape, then verifies:

1. b * q fits in 64 bits (cross-term checks)
2. r < b (via exec "lt")
3. b * q + r == a (wide addition + equality assertions)

The output stack is [r_lo, r_hi, q_lo, q_hi | rest].

The proof is elementary number theory over u32 limbs -- no
advanced math, just careful tracking of carries and cross
products through 50 instructions.

## Acceptance Criteria

### Tier 1: Infrastructure

- [ ] AC-1: Step lemma `stepEmitImm` added
  (emitImm is a no-op: `some s`)
- [ ] AC-2: Step lemma `stepAdvPush2` added for advPush 2
  (takes 2 values from advice, reverses onto stack;
  requires `advice.length >= 2` hypothesis)
- [ ] AC-3: Step lemma `stepU32Assert2` added
  (asserts top two stack elements are u32; requires
  isU32 hypotheses)
- [ ] AC-4: Step lemma `stepAssertWithError` added
  (same as assert: pops top, requires val == 1)
- [ ] AC-5: Step lemma `stepAssertEqWithError` added
  (same as assertEq: pops two, requires equality)
- [ ] AC-6: All new step lemmas added to `miden_step`
  tactic

### Tier 2: Theorem Statement

- [ ] AC-7: `u64_divmod_correct` theorem statement
  completed with:
  - Correct output stack: `r_lo :: r_hi :: q_lo ::
    q_hi :: rest`
  - All necessary hypotheses (isU32 for all 8 limbs,
    cross-product carry conditions, r < b, a == b*q+r
    decomposition)
  - Advice stack hypothesis
  - Match the hypothesis set from Div.lean/Mod.lean

### Tier 3: Proof Body

- [ ] AC-8: Phase 1 proved (instructions 1-13):
  read q from advice, verify first cross product
  b_lo * q_hi and accumulate b_hi * q_hi + carry,
  assert high word is zero
- [ ] AC-9: Phase 2 proved (instructions 14-24):
  verify second cross product b_lo * q_lo + cross_lo,
  assert high word is zero; verify b_hi * q_lo == 0
- [ ] AC-10: Phase 3 proved (instructions 25-35):
  read r from advice, rearrange stack, exec "lt" to
  verify r < b, assert result
- [ ] AC-11: Phase 4 proved (instructions 36-50):
  wide-add r + (b*q cross terms), assert no carry
  overflow, assert equality with a_hi and a_lo

### Tier 4: Integration

- [ ] AC-12: Div.lean and Mod.lean build successfully
  (they already have complete proofs that call
  u64_divmod_correct)
- [ ] AC-13: All three files re-imported in
  MidenLean.lean; `lake build MidenLean` passes
  with 0 errors, 0 warnings, 0 sorry

## Default Quality Requirements

- [ ] No sorry in any proof file
- [ ] lake build passes with 0 errors
- [ ] 0 lint warnings

## Scope Boundaries

**In scope:** u64.divmod proof, supporting step lemmas,
Div/Mod integration.

**Out of scope:** Semantic theorem strengthening (toU64
interpretation of divmod result); other unproved procedures.

## Revision History

- 2026-03-18: Initial goal (focused divmod session)
