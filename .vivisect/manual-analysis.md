# Vivisect Manual Analysis: masm-lean

Date:  2026-03-18
Scope: All .lean files in MidenLean/

## Target: core-semantics

### Finding: execAdvPush reverses, execAdvLoadW does not
File: MidenLean/Semantics.lean:892-906
Category: Good (after fix)

`execAdvPush` (line 897) reverses the taken advice
elements before prepending to stack. `execAdvLoadW`
(line 906) does NOT reverse. This asymmetry is
intentional and correct:
- advPush pops elements one at a time from advice
  (FIFO) onto stack (LIFO), so the first advice
  element ends up deepest. Equivalent to reverse.
- advLoadW replaces the top 4 stack elements with
  4 advice elements in order. No reversal needed.

This was previously a bug (advLoadW DID reverse)
and was fixed per spec section 6, AC-14. The test
at Tests/Semantics.lean:786-790 is a regression
test for this fix.

### Finding: u32 ops all have isU32 precondition checks
File: MidenLean/Semantics.lean:453-751
Category: Good (after fix)

The spec (section 6, AC-7/8/9/11) documented that
28+ u32 ops lacked isU32 precondition checks.
Reviewing the current code, ALL u32 arithmetic,
comparison, bitwise, shift, rotate, and count
operations now include `if !a.isU32 ...` or
`if !a.isU32 || !b.isU32 ...` guards. Examples:
- execU32WidenAdd: line 456
- execU32Shl: line 613
- execU32Clz: line 684
- execU32Lt: line 714

Regression tests at Tests/Semantics.lean:519-573
verify rejection of non-u32 inputs.

### Finding: Memory model is element-addressed
File: MidenLean/State.lean:9-10, Semantics.lean:780-878
Category: Bad (intentional design divergence)

Lean uses `Nat -> Felt` (element-addressed).
Rust uses `BTreeMap<u32, [Felt; 4]>` (word-addressed).
The Be/Le variants compensate: memStorewBe stores
elements in reverse order within the word address
range, while memStorewLe stores in natural order.

This is documented as intentional in the spec
(section 6, AC-13).

### Finding: Stack model has no depth enforcement
File: MidenLean/State.lean:8
Category: Bad (intentional design divergence)

Lean uses unbounded `List Felt`. Rust enforces:
- Minimum depth 16 (auto-padded with zeros)
- Maximum depth 2^16

Operations that would underflow on a short stack
return `none` in Lean (safe failure), but Rust would
have auto-padded zeros available. For example,
`dup.15` on a 10-element stack fails in Lean but
succeeds in Rust (accessing a zero-padded element).

This is documented as intentional in the spec
(section 6, AC-5).

### Finding: emit is a no-op without reading top
File: MidenLean/Semantics.lean:911-914
Category: Bad (intentional simplification)

`execEmit` checks stack non-empty but does not read
or consume the top element. Rust's emit reads the
top element as an event ID. This is documented in
the spec (section 6, AC-12).

### Finding: emitImm ignores the event ID parameter
File: MidenLean/Semantics.lean:1037
Category: Bad (intentional simplification)

Line 1037: `| .emitImm _ => some s`
The emitImm instruction completely ignores its event
ID argument. This is consistent with emit being a
semantic no-op.

## Target: proofs

### Finding: 3 axioms remain unproved
Files: WordLt.lean:12, WordLte.lean:12, WordGte.lean:12
Category: Bad

Three word comparison theorems use Lean `axiom`
declarations instead of proofs:
1. `word_lt_full_correct` (WordLt.lean:12)
2. `word_lte_full_correct` (WordLte.lean:12)
3. `word_gte_full_correct` (WordGte.lean:12)

`word_gt_correct` (WordGt.lean:76) IS fully proved.
The lt proof should be achievable by the same
technique (identical loop structure, just using
`.gt` instead of `.lt` in the loop body for the
reversed comparison). The lte/gte proofs should be
derivable from gt/lt + not.

The axioms create a soundness gap: if the axiom
statements contain errors (e.g., wrong comparison
direction, wrong associativity of boolean
expressions), those errors would be invisible to
the proof checker. However, the axiom statements
appear correct upon manual inspection, and the test
suite exercises all four operations with concrete
values.

### Finding: u64_min/max theorem statements are complex
Files: U64MinMax.lean:16-29, 72-89
Category: Good

The min/max theorems express their results in terms
of `u32OverflowingSub` intermediate values rather
than direct mathematical min/max. This is correct
but makes the theorem statements harder to interpret.
The relationship between the overflow-sub-based
comparison and mathematical ordering is established
by the proof itself.

## Target: generated-procs

### Finding: Generated code is not hand-editable
Files: Generated/U64.lean, Generated/Word.lean
Category: Good

All procedure definitions are pure lists of Op values.
They are produced by a Rust translator and match the
MASM source. The Lean proofs verify these exact
instruction sequences, so any manual edit would
invalidate the proofs. This is the correct design.

## Spec Divergence Check

Comparing .galvanize/spec.md against implementation:

1. AC-14 (advLoadW reversal): FIXED. Code no longer
   reverses. Regression test present.
2. AC-7/8/9/11 (u32 preconditions): FIXED. All u32
   ops now check isU32. Regression tests present.
3. AC-5 (stack depth): Documented divergence.
   No enforcement, as specified.
4. AC-13 (memory model): Documented divergence.
   Element-addressed, as specified.
5. AC-12 (emit): Documented as no-op, as specified.

No impl-vs-spec divergences found beyond what the
spec itself documents as intentional.

---
## Run 3 findings


## Run 4 findings (incremental, 2026-03-19)

### Finding: NOT style inconsistency RESOLVED
File: MidenLean/Semantics.lean:90-91
Category: Good (fixed)

u32CountLeadingOnes changed from
`u32CountLeadingZeros (u32Max - 1 - n)` to
`u32CountLeadingZeros (n ^^^ (u32Max - 1))`,
matching u32CountTrailingOnes. The "Inconsistent
NOT implementation style" Bad finding is resolved.

### Finding: Semantic interpretation layer added
File: MidenLean/Proofs/Interp.lean (NEW, 385 lines)
Category: Good

New file introduces:
- toU64, toU128: limb pair -> Nat interpretation
- Bridge lemmas: toU64_eq_iff, toU64_lt_iff,
  toU128_lt_iff, u64_lt_condition_eq, toU64_neq_iff
- Bitwise: toU64_and, toU64_or, toU64_xor (proved
  via Nat.testBit decomposition)
- cross_product_mod_2_64: carry chain correctness
- Counting: u64CountLeading/TrailingZeros/Ones
- felt_lo32_hi32_toU64: Felt decomposition roundtrip

All lemmas are sorry-free and axiom-free. Clean
mathematical layer.

### Finding: 16 semantic corollaries added
Files: Proofs/U64/{And,Or,Xor,Clz,Ctz,Clo,Min,Max,
       Neq,Sub,WideningAdd,WrappingMul,
       OverflowingSub,Shl}.lean
Category: Good

Each file gained a _semantic or _toU64 corollary
that connects the _correct theorem to a toU64-level
statement. Pattern: rw [original_correct]; apply
bridge_lemma. All are sorry-free.

### Finding: Cross-validation test suite added
File: MidenLean/Tests/CrossValidation.lean (NEW)
Category: Good

30+ tests exercising MASM library procedures through
Lean semantics against miden-vm Rust test vectors.
Includes a complete u64 ProcEnv covering all 27 u64
procedures. Tests use #eval with panic! on mismatch.

### Finding: StepLemmas updated for clo change
File: MidenLean/Proofs/StepLemmas.lean
Category: Good

stepU32Clo lemma updated to match the XOR-based
u32CountLeadingOnes definition. No functional change
to the step lemma's behavior, just tracks the
definition update.
