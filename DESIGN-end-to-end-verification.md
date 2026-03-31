# End-to-End Formal Verification of MidenVM

Design document for MidenVM formal verification. Current scope: MASM/stdlib
correctness plus Layer 3 AIR soundness/completeness ("not over- or
under-constrained"). Layer 4 STARK proof-system soundness remains future work.

## 1. Proof Taxonomy

There are three fundamentally distinct proof categories. The first two share a
model (instruction semantics). The third requires formalizing the algebraic
constraint system.

### 1.1 Functional Correctness

**Question**: Does MASM procedure P compute function f on valid inputs?

```
For all x in D:  P(x) = f(x)
```

Where:
- I = all possible stack states (full input space)
- D c I = inputs satisfying preconditions (e.g., a.isU32 /\ b.isU32)
- f : D -> O = the specification function (only defined on valid inputs)
- P : I -> O u {fail} = the MASM procedure (defined on everything, may trap)

In the Lean development we do not want the domain `D` to live only in prose.
For helper-level proofs we usually factor the spec into:

- `f_pure` = the typed mathematical or Rust-reference spec on typed inputs
- `spec_io` = a partial IO relation on machine values that *internalizes* the
  validity preconditions
- `spec_state` = the lifted machine-state relation induced by `spec_io`

Then the machine-level domain is recovered from the spec itself:

```
D_machine = { s : ∃ s', spec_state s s' }
```

This avoids a proof interface where the domain is carried separately from the
code-level spec.

This proves graph(f) c graph(P|_D). The spec's behavior is *contained in* the
MASM procedure's behavior on valid inputs.

**Gap**: Says nothing about inputs outside D. The MASM procedure still runs on
I \ D and may silently produce wrong results.

### 1.2 Spec Equivalence

**Question**: Does MASM procedure P compute the same function as reference
implementation R?

Two implementations live in different worlds:
- P : I_masm -> O u {fail}  (MASM, operates on stack of field elements)
- R : I_rust -> O u {fail}  (Rust, operates on typed values)

Bridge functions:
- encode : I_rust -> I_masm  (e.g., u64 becomes two u32 felts on stack)
- decode : O_masm -> O_rust  (read stack back as typed value)

Each implementation has a domain where it's defined:
- D_rust = inputs where R doesn't panic
- D_masm = inputs where P doesn't trap

Spec equivalence proves:

```
For all x in D_rust /\ D_masm:  decode(P(encode(x))) = R(x)
```

For helper-level Lean proofs, the equivalent formulation is usually:

```
local_sem_P(s, s') -> spec_state_P(s, s')
```

where `spec_state_P` is already the lifted partial machine-state spec. The
typed Rust or pure mathematical spec is used to *define* `spec_state_P`; the
theorem itself is then stated directly at the code boundary.

The interesting security regions are:
- D_masm \ D_rust: MASM accepts inputs Rust would reject (MISSING VALIDATION)
- D_rust \ D_masm: MASM traps on inputs Rust accepts (OVER-RESTRICTION)

Most stdlib findings fall in D_masm \ D_rust.

### 1.3 Constraint Soundness

**Question**: Do the AIR constraints characterize exactly the valid execution
traces?

Different universe -- not functions, but execution traces:
- T = a candidate execution trace (sequence of VM state rows)
- V = { T : T follows instruction semantics correctly }  (valid traces)
- S = { T : all AIR constraints evaluate to 0 on T }     (constraint-satisfying traces)

Soundness:    S c V   (every constrained trace is valid)
Completeness: V c S   (every valid trace satisfies constraints)

The two dangerous gaps are:
- Under-constrained AIR: S \ V is non-empty
- Over-constrained AIR: V \ S is non-empty

Layer 3 is exactly the claim that both gaps are empty.

**Fundamentally requires**: formalizing the AIR constraint system, which is a
completely different kind of Lean development from instruction semantics.

## 2. Relationship Between Proof Types

### 2.1 Set-Theoretic View

```
Functional correctness:    graph(f) c graph(P|_D)
                           "spec fits inside MASM on valid inputs"

Spec equivalence:          graph(P|_{D/\D'}) = graph(R|_{D/\D'})
                           "MASM and Rust agree where both defined"

Constraint soundness:      S c V
                           "every constrained trace is valid"
```

The first two are complementary views of "is the code correct?" -- they share
the same foundation (instruction semantics model). The third is about "does the
AIR exactly capture valid execution traces?" and requires an additional
formalization of the algebraic constraint system.

### 2.2 Composition

The Layer 3 execution-correctness argument chains the first three:

1. Spec equivalence: P_masm computes the same function as R_rust
   (the code is correct)
2. Functional correctness: P_masm computes f on valid inputs
   (we know WHAT it computes)
3. Constraint soundness/completeness: the AIR is neither under-constrained nor
   over-constrained

Together: the specified valid traces are exactly the traces admitted by the AIR,
and those traces implement the intended computation.

In the helper proofs we package (1)+(2) as adjacent-semantics theorems:

- Layer 1: `exec P s = some s' ↔ dom_P s ∧ local_sem_P s s'`
- Layer 2: `local_sem_P s s' -> spec_state_P s s'`
- Combined: `exec P s = some s' ↔ spec_state_P s s'`

with `dom_P s := ∃ s', spec_state_P s s'`.

Without (3), invalid traces may satisfy the AIR or valid traces may be
rejected. Without (1)+(2), the code might compute the wrong function even when
the AIR is exact.

## 3. Complete Theorem Set for a Single Routine

Using u32wrapping_add as the concrete example.

### 3.0 Setup

```
Inputs:
  I       = Felt x Felt x Stack          -- all possible stack states with >= 2 elements
  D       = { (a, b, rest) in I : a < 2^32 /\ b < 2^32 }

Functions:
  P       : I -> (Felt x Stack) u {fail} -- MASM procedure
  f       : D -> Felt x Stack            -- spec: f(a, b, rest) = ((a+b) mod 2^32, rest)
  R       : u32 x u32 -> u32            -- Rust: u32::wrapping_add

Encoding:
  encode  : (u32, u32) -> (Felt, Felt)
  decode  : Felt -> u32

Traces:
  T       = list of TraceRow
  V       = { T : T follows instruction semantics }
  S       = { T : all AIR constraints evaluate to 0 on T }
```

Actual Lean packaging for helper proofs:

```
f_pure       : typed input -> typed output
local_sem    : MidenState -> MidenState -> Prop
spec_io      : machine input -> machine output -> Prop
spec_state   : MidenState -> MidenState -> Prop
dom          : MidenState -> Prop := fun s => ∃ s', spec_state s s'
```

The important point is that `spec_io` / `spec_state` already include the
validity preconditions (for example `x.isU32 = true`), so the machine-side
domain is derived from the spec rather than duplicated next to it.

### 3.1 Theorem: Functional Correctness

"On valid inputs, P computes f."

```
THEOREM fc_u32wrapping_add:
  forall (a b : Felt) (rest : Stack),
    a.val < 2^32 ->
    b.val < 2^32 ->
    P(a :: b :: rest) = some (Felt.ofNat ((a.val + b.val) % 2^32) :: rest)
```

What it gives: The happy path works.
What it misses: Says nothing about inputs outside D.

### 3.2 Theorem: Input Rejection

"On invalid inputs, P fails."

```
THEOREM reject_u32wrapping_add:
  forall (a b : Felt) (rest : Stack),
    a.val >= 2^32 \/ b.val >= 2^32 ->
    P(a :: b :: rest) = none
```

What it gives: Invalid inputs can't silently produce a result.

IMPORTANT NOTE: This theorem is often FALSE in practice. Many MASM procedures
do NOT reject invalid inputs -- they lack sufficient assertions. Attempting to
prove this and failing is itself a security finding. If P silently computes on
I \ D, the procedure has a missing validation gap.

### 3.3 Theorem: Total Correctness

"P computes f on D and fails everywhere else."

```
THEOREM total_u32wrapping_add:
  forall (a b : Felt) (rest : Stack),
    P(a :: b :: rest) = some result
    <->
    (a.val < 2^32 /\ b.val < 2^32 /\
     result = Felt.ofNat ((a.val + b.val) % 2^32) :: rest)
```

This is the biconditional -- the strongest statement about P as a function:

  { x : P(x) != fail } = D      (domain equality)
  forall x in D, P(x) = f(x)    (output equality)

Theorems 3.1 + 3.2 together imply Theorem 3.3.

### 3.4 Theorem: Spec Equivalence / Code-Level Spec Bridge

"P computes the same function as Rust's wrapping_add."

```
THEOREM spec_equiv_u32wrapping_add:
  forall (a b : Nat),
    a < 2^32 ->
    b < 2^32 ->
    let masm_result := P(Felt.ofNat a :: Felt.ofNat b :: rest)
    let rust_result := Nat.wrapping_add_u32(a, b)
    masm_result = some (Felt.ofNat rust_result :: rest)
```

Relationship to Theorem 3.1: If f = R composed with decode, then 3.1 and 3.4
are the same theorem with different presentation. They diverge when the spec
and the Rust reference disagree (rare but possible).

In the actual helper files, this layer is preferably stated directly against a
lifted partial machine-state spec:

```
THEOREM spec_bridge_u32wrapping_add:
  forall (s s'),
    dom s ->
    local_sem s s' ->
    spec_state s s'

THEOREM code_matches_spec_u32wrapping_add:
  forall (s s'),
    P(s) = some s' <-> spec_state s s'
```

Here `spec_state` already internalizes the `u32` preconditions via the
underlying `spec_io`.

### 3.5 Theorem: Constraint Soundness (per instruction)

"Any trace row satisfying the u32add AIR constraint is a valid u32add execution."

Now in a completely different world -- algebraic constraints over trace columns.

```
-- A trace row for the u32add operation
RECORD U32AddRow :=
  s0      : Felt    -- stack top before
  s1      : Felt    -- stack second before
  s0'     : Felt    -- stack top after (overflow bit)
  s1'     : Felt    -- stack second after (sum mod 2^32)

-- The trusted Lean AIR predicate for this phase
DEF air_u32add(row : U32AddRow) : Prop :=
  s0.val + s1.val = s0'.val * 2^32 + s1'.val
  /\ s0' * (s0' - 1) = 0                          -- s0' is boolean
  /\ s1'.val < 2^32                                -- s1' is u32 (range check)

-- The semantic specification
DEF valid_u32add(row : U32AddRow) : Prop :=
  s1'.val = (s0.val + s1.val) % 2^32
  /\ s0'.val = (s0.val + s1.val) / 2^32

THEOREM constraint_sound_u32add:
  forall (row : U32AddRow),
    s0.val < 2^32 ->
    s1.val < 2^32 ->
    air_u32add(row) ->
    valid_u32add(row)
```

What this proves: the local AIR does not admit invalid u32add rows.

CURRENT TRUST BOUNDARY: for this Layer 3 effort, `air_u32add` is the trusted
Lean AIR predicate for the instruction. Ideally it is validated against the
Rust AIR, but Rust-AIR fidelity is not part of the theorem goal in this phase.

### 3.6 Theorem: Constraint Completeness (per instruction)

"Every valid u32add execution satisfies the AIR constraint."

```
THEOREM constraint_complete_u32add:
  forall (row : U32AddRow),
    valid_u32add(row) ->
    air_u32add(row)
```

What this proves: the local AIR does not reject valid u32add rows.

### 3.7 Future Theorem: End-to-End

"A valid STARK proof implies the program computed correctly."

```
THEOREM end_to_end_u32wrapping_add:
  forall (proof : StarkProof) (pub_inputs : PublicInputs),
    stark_verify(proof, pub_inputs) = true ->
    let (a, b) := decode_inputs(pub_inputs)
    let result := decode_output(pub_inputs)
    a < 2^32 /\ b < 2^32 ->
    result = (a + b) % 2^32
```

This is Layer 4. It requires ALL of the above plus STARK proof-system
soundness (polynomial commitments, Fiat-Shamir transform). It is not required
for the current Layer 3 objective.

## 4. Architecture Layers

```
Layer 4 (end-to-end):     STARK proof accepted -> correct result
                               | requires all below

Layer 3 (constraints):    S c V  (Thm 3.5: soundness)
                          V c S  (Thm 3.6: completeness)
                               | requires AIR formalization

Layer 2 (spec bridge):   local_sem_P -> spec_state_P
                          Combined: exec P s = some s' <-> spec_state_P s s'
                               | `spec_state_P` is the lifted partial code-level
                               | spec derived from the pure math / Rust spec

Layer 1 (code correct):  exec P s = some s' <-> dom_P s /\ local_sem_P s s'
                          rejection outside dom_P
                               | requires instruction semantics model

Layer 0 (model):         execInstruction matches the Rust VM
                          (ground truth -- currently validated by testing)
```

Current state: Layers 0-2 are built. Layer 3 is the primary new effort. Layer
4 remains future work.

Current trust boundaries for Layer 3:
- The Lean instruction-semantics model (Layer 0)
- The chosen Lean AIR predicates for each subsystem
- Any external claim that those Lean AIR predicates match the Rust AIR

Current theorem target:
- Soundness: `S ⊆ V`
- Completeness: `V ⊆ S`
- Equivalently: the AIR is neither under-constrained nor over-constrained

## 5. Implementation Plan for AIR Constraint Soundness

### 5.1 What Needs Formalizing

The Miden AIR consists of multiple subsystems:

1. **Decoder constraints** -- instruction decoding, control flow
   Source: audit-miden-vm/air/src/constraints/decoder/

2. **Stack constraints** -- stack operations, overflow table
   Source: audit-miden-vm/air/src/constraints/stack/

3. **Range checker** -- u32 range proofs via 16-bit limb decomposition
   Source: audit-miden-vm/air/src/constraints/range/

4. **Chiplets**:
   - Hasher (RPO permutation)
   - Bitwise (u32 bitwise ops)
   - Memory (load/store)
   - Kernel ROM
   Source: audit-miden-vm/air/src/constraints/chiplets/

5. **Chiplet bus** -- multiset equality linking main VM to chiplets
   Source: audit-miden-vm/air/src/constraints/chiplets/bus.rs

### 5.2 Immediate Prerequisites Before the 5-Step Layer-3 Proof

Before running the main Layer-3 proof loop, four setup decisions need to be
fixed:

1. **Freeze the theorem boundary**
   The theorem is relative to the trusted Lean AIR predicates. Rust-AIR
   fidelity is a separate trust-boundary question, not part of this proof.

2. **Separate local and global AIR obligations**
   Local row constraints, boundary constraints, and global bus/running-product
   obligations should not be mixed in one opaque predicate.

3. **Use a proof-oriented representation of global constraints**
   For buses and lookup/permutation arguments, the trusted Lean boundary may use
   a compact normalized witness (for example a running-product segment) rather
   than raw extracted row formulas.

4. **Keep the theorem interface stable**
   Procedure-level soundness/completeness theorems should be stated over one
   trusted Lean AIR predicate and one semantic validity predicate, even if the
   internal proof uses helper witnesses.

### 5.3 Five-Step Layer-3 Proof

For each VM instruction or small routine slice:

1. Define the trusted Lean AIR predicate over the relevant trace fragment.
2. Define the semantic validity predicate for that same fragment.
3. Prove local soundness: AIR implies the intended step semantics.
4. Prove the required global composition lemmas for buses / boundaries / aux checks.
5. Conclude exactness: soundness `S ⊆ V` and completeness `V ⊆ S`.

### 5.4 Approach

Two possible strategies:

**Bottom-up**: Start with the simplest instructions (field add, field mul),
build up to compound operations (u32add, u32mul), then tackle chiplet
interactions. Advantage: early wins, incremental progress. Risk: chiplet bus
interactions are where the real complexity lives, and we defer them.

**Top-down**: Start with the trace validation entry point, formalize the
constraint composition framework, then fill in per-instruction constraints.
Advantage: the overall structure is correct by construction. Risk: long time
before any individual theorem is proved.

**Recommended**: Hybrid. Formalize the trace structure and constraint
composition framework first (top-down skeleton), then fill in individual
instruction constraints bottom-up, starting with the range checker (it
underpins all u32 operations).

### 5.5 Key Challenges

**Challenge 1: Choosing and maintaining the Lean AIR boundary**

For the current Layer 3 effort, the theorem is relative to the Lean AIR
predicate we formalize. If we later want lower trust, we can validate that
predicate against the Rust AIR by extraction or differential testing, but that
fidelity argument is not part of the present theorem goal.

**Challenge 2: Range checker interaction**

Many instructions rely on the range checker chiplet to enforce that values are
in [0, 2^32). The range checker uses a permutation argument (multiset check)
to link the main trace to the range check trace. Formalizing this interaction
is non-trivial -- it's a global property, not a per-row property.

**Challenge 3: Chiplet bus soundness**

The chiplet bus uses a running product column to enforce that every chiplet
request has a matching response. Proving this is sound requires reasoning about
multiset equality over the entire trace, not just individual rows.

**Challenge 4: Field extension**

Some constraints operate over the quadratic extension of the Goldilocks field
(for security). The formalization needs to handle both the base field and the
extension field.

### 5.6 Estimated Scope

Per instruction category:
- Field arithmetic (add, mul, neg, inv): ~1 week (simple single-row constraints)
- Stack operations (dup, swap, movup): ~1 week (index arithmetic)
- u32 operations: ~2 weeks (range checker interaction)
- Memory operations: ~2 weeks (memory chiplet + bus)
- Crypto operations (hperm): ~2 weeks (hasher chiplet)
- Control flow (if, while, call): ~3 weeks (decoder constraints, most complex)
- Chiplet bus framework: ~2 weeks (multiset argument)
- Range checker framework: ~1 week (permutation argument)

Total estimate: 3-4 months for comprehensive coverage.

## 6. Threat Model Summary

| Attack scenario                              | Proof type that catches it          |
|----------------------------------------------|-------------------------------------|
| MASM procedure has wrong operand order       | Functional correctness / spec equiv |
| SHA256 MASM diverges from NIST spec          | Spec equivalence                    |
| Missing u32assert in stdlib procedure        | Input rejection (Thm 3.2)          |
| MASM accepts inputs Rust would reject        | Spec equiv (D_masm \ D_rust gap)   |
| Invalid trace satisfies the AIR             | Constraint soundness ONLY           |
| u32add AIR allows overflow without carry     | Constraint soundness ONLY           |
| Range checker doesn't actually enforce range | Constraint soundness ONLY           |
| Chiplet bus allows request/response mismatch | Constraint soundness ONLY           |
| STARK verifier accepts invalid FRI proof     | End-to-end (Layer 4) ONLY          |

## 7. What "Done" Looks Like

### Minimum viable: per-instruction constraint soundness
For each primitive VM operation, prove that the AIR constraint implies the
correct semantic behavior. Does NOT cover chiplet interactions or the bus.
Already catches constraint bugs on individual instructions.

### Full: trace-level Layer 3 exactness
Prove that the AIR constraints, including chiplet bus, range checker, and
boundary constraints, characterize exactly the valid execution traces. This is
the real Layer 3 theorem: the AIR is neither under-constrained nor
over-constrained.

### Ultimate: end-to-end with STARK verifier
Prove that STARK verification acceptance implies correct execution. Requires
formalizing FRI, the polynomial commitment scheme, and Fiat-Shamir. This is
likely out of scope for a single engagement but would be the gold standard.

## 8. Checklist From Current State

This checklist starts from the repository as it exists today. It is ordered so
that each item removes a concrete trust boundary or replaces an assumption with
an internal theorem.

### 8.1 Freeze and Audit the AIR Boundary

- [ ] Keep the symbolic extraction coverage aligned with Rust top-level AIR
      dispatch (`constraints::enforce_main`, `constraints::enforce_bus`,
      `public_inputs::enforce_main`).
- [ ] Add a machine-checked or script-checked coverage test showing that the
      `symbolic.rs` module list matches the current Rust AIR entrypoints.
- [ ] Make old subsystem names discoverable through aliases or a mapping table
      so that symbolic coverage changes do not look like missing extraction.
- [ ] Decide which Lean predicates are the canonical trusted AIR boundary for
      each proof family:
      - local `Frame` kernels for instruction/helper proofs
      - symbolic row constraints for whole-VM AIR proofs
      - specialized adapters only when a proof genuinely needs them

### 8.2 Close the Layer-3 Local-to-Global Gap

- [ ] Build a reusable symbolic-row -> local-kernel bridge for each major
      opcode family (stack ops, stack arith, crypto helpers, decoder slices).
- [ ] Replace ad hoc bridging lemmas with a standard pattern:
      symbolic satisfaction + decoder facts -> local kernel satisfaction.
- [ ] Separate “honest execution completeness” from “verifier accepts arbitrary
      witness” in theorem statements and documentation for every audited slice.
- [ ] Continue turning procedure-level SHA-256 and stdlib analyses into either
      local soundness theorems or explicit counterexamples.

### 8.3 Close the Source-to-Witness Gap

- [ ] Construct a concrete trace-producing refinement from `execWithEnv` /
      source execution to `VmWitness`, removing the `SourceVmBridge`
      assumption.
- [ ] Extend the refinement beyond visible stack endpoints to include:
      memory, locals, advice/provider state, decoder state, clock/context,
      overflow rows, chiplet rows, bus rows, and public I/O.
- [ ] Prove that the witness-level periodic values used by `VmWitness` match
      the real Miden periodic columns rather than leaving them as free inputs.
- [ ] Prove that public input packing and witness-level final permutation values
      match the Rust layout and verifier expectations.

### 8.4 Close the Global AIR / Verifier Algebra Gap

- [ ] Prove generic running-product and LogUp exactness lemmas strong enough to
      discharge the bus/range/chiplet global obligations uniformly.
- [ ] Connect `VmAirSatisfied` to the executable verifier-side algebra in
      `ReducedAux.lean`.
- [ ] Prove the missing challenge-soundness step that turns encoded
      message-equality statements into literal multiset equality claims.
- [ ] Prove that the final aux values checked by `reduced_aux_values` are the
      ones induced by the actual aux trace, not arbitrary final commitments.

### 8.5 Future Layer-4 / Proof-System Work

- [ ] Formalize the polynomial-commitment / FRI / Fiat-Shamir layer needed to
      turn AIR exactness into STARK proof-system soundness.
- [ ] State and prove the real end-to-end theorem:
      verifier acceptance -> correct source-level execution result.
- [ ] Clarify the exact theorem flavor pursued at Layer 4
      (soundness, knowledge soundness, extraction, or some weaker acceptance
      theorem).

## 9. Full Verification Pipeline

The current design separates the verification story into a sequence of
artifacts and bridges.

### 9.1 Code and Functional Side

1. Rust / mathematical spec:
   typed reference function or pure math statement.
2. MASM code:
   translated into Lean operations and proved against the lifted spec.
3. Source semantics:
   `execInstruction` / `execWithEnv` gives the trusted operational model.
4. Functional theorems:
   Layer 1 and Layer 2 prove that code execution matches the intended
   machine-state spec.

At this point we know what the code is supposed to do, but not yet that the
AIR admits exactly those executions.

### 9.2 AIR Polynomial Side

1. Rust AIR:
   `constraints::enforce_main`, `constraints::enforce_bus`, and
   `public_inputs::enforce_main`.
2. Symbolic extraction:
   `symbolic.rs` runs those Rust entrypoints under `SymbolicAirBuilder`.
3. Lean symbolic constraints:
   emitted into `AIR/Constraints/Symbolic/*`.
4. Local proof kernels:
   smaller `Frame`-based predicates for focused local proofs.
5. Local AIR soundness / counterexamples:
   prove a helper slice is enforced, or show a malicious witness that is
   still accepted.

At this point we know either:
- a local AIR slice implies the intended local semantics, or
- the local AIR slice is under-constrained / over-constrained.

### 9.3 Whole-VM AIR Side

1. `VmWitness` packages typed rows, shared challenges, final permutation
   values, public inputs, and periodic values.
2. `rowView` turns each typed row into a `SymbolicFrame`.
3. Whole-VM predicates state that every row satisfies the symbolic base/bus
   constraints and that the reduced-aux boundary checks hold.
4. Section-level decomposition breaks the whole AIR into decoder, stack,
   chiplet, range, bus, and public-input pieces.

This is the current top of the formal AIR stack.

### 9.4 The Missing Bridges

The two missing bridges are the reason the pipeline is not yet end-to-end.

1. Source execution -> `VmWitness`
   We do not yet have a generic trace extraction theorem from
   `execWithEnv` to a full witness.
2. Symbolic AIR -> local proof kernels
   We do not yet have a uniform theorem that turns symbolic row satisfaction
   plus decode facts into the kernel predicates used by many local proofs.

### 9.5 Verifier Boundary

After whole-VM AIR satisfaction comes the verifier-side algebra:

1. aux-trace running products / LogUp sums produce final aux values,
2. `reduced_aux_values` computes the final acceptance equation,
3. `verifierAccepts` checks the reduced product and reduced sum conditions.

This is already modeled in Lean, but it is not yet connected to a complete
source-to-witness story or to proof-system soundness.

### 9.6 Proof-System Boundary

Only after all of the above do we reach true STARK proof verification:

1. committed trace polynomials,
2. quotient / composition polynomial checks,
3. FRI low-degree testing,
4. Fiat-Shamir transcript soundness,
5. final theorem that a verified proof implies correct execution.

That layer is explicitly future work in this project.

## 10. Decision Log

- 2026-03-26: Decided to pursue full end-to-end execution model, including
  AIR constraint soundness (Layer 3). Layers 0-2 already built.
- 2026-03-27: Narrowed the current theorem goal to Layer 3 exactness only:
  prove `S ⊆ V` and `V ⊆ S` for the trusted Lean AIR predicates, while treating
  Rust-AIR fidelity and STARK proof-system soundness as explicit trust
  boundaries / future work.
- Prior: Functional correctness proofs for u64, u128, word stdlib procedures.
  15 findings logged (F-001 through F-015) from spec equivalence / diff audit.
