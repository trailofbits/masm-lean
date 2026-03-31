# Design: Canonical AIR Semantics

This note describes the AIR redesign that should make the AIR side of
`masm-lean` look structurally like the code side.

Today the AIR folder has two strong ingredients:

- a proof-friendly local checker built around `Frame`,
- and a symbolic extraction of the Rust AIR built by `symbolic.rs`.

What it does **not** yet have is a single canonical Lean AIR semantics layer
that plays the same role for AIR that `Semantics.lean` plays for MASM code.

The goal of this document is to define that missing layer and to break the
implementation into small linear steps that a human can follow one at a time.
The redesign should track the structure Miden itself documents for the
[VM execution trace], [stack], [decoder overview], [range checker],
[chiplets overview], and [lookup buses], rather than inventing a separate
proof-only decomposition.

## 0.1 Spec/Implementation Split Rule

When the extracted Rust AIR and the intended mathematical spec diverge, we must
keep both layers explicitly:

- the **implementation AIR layer** mirrors Rust exactly,
- the **spec layer** keeps the intended documented relation,
- and the mismatch is recorded as a **failed refinement / explicit gap**.

Do **not** weaken the spec layer just to make the bridge go through.

The first concrete example is `U32ADD` / `U32ADD3`: the current Rust AIR allows
the high visible output to be `h_3 \cdot 2^{16} + h_2`, while the intended spec
keeps the documented carry output `h_2` and the documented helper invariant
`h_3 = 0`. This should appear as a gap, not as a quiet redefinition of the
spec.

## 1. Problem Statement

The current AIR story is split:

- `Constraints/Symbolic/*` is the closest Lean artifact to the Rust AIR.
- `Frame.lean` plus hand-written kernels is the easiest layer for local proofs.
- `Soundness/VM.lean` composes symbolic constraints at the whole-VM boundary.

That split is useful, but it leaves a conceptual hole:

- there is no single `AIRSemantics.lean`-style specification,
- the local proof kernels are not uniformly derived from the symbolic AIR,
- and small theorems like `air_add_sound` are often only unpacking lemmas over
  manually chosen local constraints, not theorems about a canonical AIR model.

That gap matters because the published Miden design is already organized as one
connected algebraic machine across [stack AIR constraints],
[decoder constraints], the [range checker], and the [chiplets bus], not as two
disconnected proof trees.

The desired shape is:

1. canonical Lean AIR semantics,
2. extracted Rust AIR,
3. refinement theorem from extracted AIR to canonical AIR semantics,
4. local and global proofs built on top of that canonical layer.

## 2. Design Goal

The target architecture is:

```text
Rust AIR constraint code
  -> symbolic extraction
  -> extracted symbolic AST

canonical Lean AIR builder DSL
  -> canonical AIR expressions and constraints
  -> runnable AIR checker
  -> proof-facing extension denotation via `ExtFelt`
  -> denotation into actual polynomials

bridge theorem
  extracted symbolic AIR = canonical AIR

semantic consequences
  local per-op proofs
  subsystem composition
  whole-VM AIR theorem
```

The key point is that the canonical Lean AIR model should not be an ad hoc
list of helper lemmas. It should be an executable semantics and specification
layer in its own right. It should line up with Miden's own presentation of
row-local equations plus lookup-based glue, especially [lookup buses],
[LogUp constraints], and [multiset checks].

## 3. Core Principles

### 3.1 One Canonical AIR Model

There should be one canonical Lean definition of what it means for a row pair
or a whole witness to satisfy the Miden AIR.

Everything else should refine to that:

- extracted symbolic AIR,
- local proof kernels,
- subsystem decompositions,
- whole-VM satisfaction.

This should mirror the single machine described in [VM components], not fork
into unrelated local and global models.

### 3.2 Builder First, Not Raw Functions First

We should describe constraints with a typed expression language and builder
combinators, not start from opaque functions `AirRow -> Felt`.

This keeps the constraints:

- readable,
- compositional,
- executable,
- and later denotable as actual polynomials.

This is closer to how Miden writes constraints in [field ops], [u32 ops],
[stack AIR constraints], [decoder constraints], and [bitwise constraints].

### 3.3 Executable And Proof-Facing Extension Semantics

The extension-field side should not be modeled with only one representation.

We need both:

- an **executable** extension-field semantics over `QuadFelt`,
- and a **proof-facing** extension-field semantics over `ExtFelt`.

The intended split is:

- `QuadFelt` for concrete witness values, `#eval`, executable AIR checking, and
  extracted-symbolic evaluation,
- `ExtFelt` for algebraic proofs that should benefit from Mathlib's quotient-ring
  interface and, later, field-level reasoning.

Concretely, `QExpr` should eventually have both:

- `evalQuad : AirRow -> QuadFelt`,
- `evalExt  : AirRow -> ExtFelt`,

together with a compatibility theorem of the form:

- `QuadFelt.toExtFelt (q.evalQuad r) = q.evalExt r`.

This keeps executable checking and proof algebra synchronized instead of forcing
the project to choose one at the expense of the other. It also gives
`ExtField.lean` a real downstream role rather than leaving it as a mostly
internal bootstrap artifact.

The main mathematical payoff should come later in the bus/lookup side, where the
docs use readable fraction equations in [LogUp constraints] and then clear
denominators into polynomial AIR constraints.

### 3.4 Actual Polynomials Still Matter

Mathematically, the AIR is a polynomial system.
The canonical Lean representation should therefore have two layers:

- a builder/expression layer for construction and runnable evaluation,
- a denotation layer into multivariate polynomials.

The builder AST is the ergonomic layer.
The polynomial denotation is the mathematical layer.
This matches the style of the [design overview] and [LogUp constraints], where
constraints are written as structured low-degree equations over row variables.

### 3.5 One Small Subsystem At A Time

We should not start with a whole-VM rewrite.
We should first close one tiny slice completely:

- canonical AIR expression,
- runnable checker,
- extracted-vs-canonical bridge,
- semantic theorem.

Only then move to the next slice.
That is also how the Miden docs teach the system: one equation family at a
time, from [ADD] and [U32ADD] to [decoder trace] and [bitwise constraints].

### 3.6 No Big-Bang Rewrite

The current `Frame`, `Constraints/*`, `Constraints/Symbolic/*`, and
`Soundness/*` files should remain in place while the canonical AIR semantics is
being introduced.

The migration should be additive first, then convergent, then subtractive.

## 4. What The Canonical AIR Layer Should Contain

The canonical AIR layer should have these conceptual parts.

### 4.1 Typed AIR State

We need a canonical typed record for one AIR row pair and its shared globals.
This is the Lean counterpart of the two-row view used throughout the
[VM execution trace], with shared data coming from the same machine split as the
[decoder trace], [range execution trace], and [chiplets module trace].

At minimum:

- current main row,
- next main row,
- current aux row,
- next aux row,
- public inputs,
- periodic values,
- verifier challenges,
- final permutation values,
- boundary selectors such as first / last / transition row.

This should be the AIR analogue of `MidenState` on the code side.

### 4.2 Base-Field And Extension-Field Expressions

We need ASTs for expressions over the AIR row:

- base-field expressions for main/base constraints,
- extension-field expressions for bus and running-product constraints.

The ASTs should support:

- constants,
- references to row fields,
- addition,
- subtraction,
- multiplication,
- base-to-extension embedding where needed.

The split between base-field and extension-field expressions should follow the
same distinction Miden uses between ordinary row constraints and lookup/running
product constraints in [lookup buses], [LogUp], and [multiset checks].

For extension expressions, the design should be explicitly dual:

- an executable interpretation into `QuadFelt`,
- a proof-facing interpretation into `ExtFelt`,
- and a proved bridge between the two.

That bridge is what should let later bus proofs move from executable
`QuadFelt` checking to Mathlib-friendly `ExtFelt` algebra without changing the
meaning of the AIR.

### 4.3 Constraint Builder DSL

The DSL should expose a small vocabulary such as:

- `assertZero`,
- `assertEq`,
- `gate`,
- `whenTransition`,
- `allOf`,
- `append`.

Subsystem modules should build constraints out of these combinators rather than
construct lists of anonymous lambdas directly.
The goal is to express the same shapes that appear in the docs for [ADD],
[U32ADD], [stack AIR constraints], [decoder constraints], and
[bitwise constraints].

### 4.4 Runnable Semantics

Expressions and constraints must be executable on concrete rows and witnesses.

We want:

- expression evaluation,
- per-row constraint checking,
- per-subsystem checking,
- whole-VM checking.

This is what makes the AIR semantics behave like a real specification rather
than just a theorem target. It should let us check the same component split the
docs use for [VM components] and the row layouts they give for the
[chiplets module trace].

This executable layer should stay on `QuadFelt`. The proof-facing `ExtFelt`
layer should support proofs *about* the same extension expressions, not replace
the concrete checker.

### 4.5 Polynomial Denotation

Each builder expression should also map to an actual multivariate polynomial.

On the extension side, there should be an intermediate proof-facing layer before
full polynomial denotation:

- `QExpr.evalQuad : AirRow -> QuadFelt`,
- `QExpr.evalExt  : AirRow -> ExtFelt`,
- a compatibility theorem relating them,
- and only then a further denotation into the final polynomial object.

This should support statements of the form:

- builder evaluation equals polynomial evaluation on a row assignment,
- `ExtFelt` proofs can be transported back to the executable `QuadFelt` layer,
- the canonical AIR is literally a polynomial system,
- the extracted symbolic AIR refines to the same polynomial denotation.

This is the step that turns a proof-friendly builder language back into the
mathematical object described in the [design overview] and the lookup algebra
described in [LogUp constraints].

### 4.6 Canonical Subsystem Definitions

Each AIR subsystem should have one canonical module built with the DSL:

- `System`:
  use [VM execution trace] for the row shape, `clk`, and system columns.
- `Range`:
  use [range execution trace] for the trace layout, [range constraints] for
  the local equations, and [range bus] for the lookup side.
- `Decoder`:
  use [decoder trace] for the local row model and [decoder constraints] for the
  gated equations over flags and block metadata.
- `StackGeneral`, `StackOverflow`:
  use [stack AIR constraints] for depth/shift rules and [stack overflow table]
  for the overflow-side semantics.
- `StackOps`:
  use [stack ops], [I/O ops], and [system ops] according to the exact opcode
  family being modeled.
- `StackArith`:
  use [field ops] for field arithmetic and [u32 ops] for range-aware integer
  arithmetic and bitwise-u32 equations.
- `StackCrypto`:
  use [crypto ops] for native cryptographic op constraints and [precompiles]
  for host-deferred semantics.
- `ChipletSelectors`:
  use [chiplet selector constraints] to define exactly when each chiplet's
  internal constraints are active.
- `ChipletBitwise`:
  use [bitwise chiplet] for the limb decomposition model and
  [bitwise constraints] for the gated equations.
- `ChipletHasher`:
  use [hasher chiplet] for selector, state, and multiset/bus constraints.
- `ChipletKernelRom`:
  use [kernel ROM chiplet] for the ROM trace and its bus-coupled constraints.
- `ChipletMemory`:
  use [memory chiplet] for context separation, trace layout, and memory-row
  bus encoding.
- `ChipletAce`:
  use [ACE chiplet] for the circuit-evaluation sections, flags, and wire bus.
- `PublicInputs`:
  use [verifier public inputs] for packing/reduction rules, with [programs]
  giving the program-hash context.
- `Bus`:
  use [lookup buses] for the component-level interface, [LogUp] for the
  logarithmic-derivative construction, and [multiset checks] for virtual-table
  style running products.

### 4.7 Whole-VM AIR Semantics

The whole-VM AIR should be defined as the conjunction of:

- boundary-row facts,
- all base constraints on each row pair,
- all extension/bus constraints,
- any final verifier-algebra checks intentionally included in the AIR boundary.

This should line up with the documented split between the [VM execution trace],
[lookup buses], the [chiplets bus], the [range bus], and the verifier-facing
public-input/final-check material in [verifier public inputs].

## 5. Why Use A Builder AST Instead Of Only Actual Polynomials

The mathematical AIR is polynomial, but storing everything immediately as a
normalized polynomial is the wrong first layer.

Miden's own docs usually describe constraints in structured form, for example
[ADD], [U32ADD], [op batch flags constraints], or [bitwise constraints], not
as expanded monomials. The builder layer should preserve that structure.

The builder AST is better for construction because:

- it matches how the Rust AIR is written,
- it preserves gated forms like `flag * body`,
- it is readable in proofs,
- it is runnable without normalization noise,
- and it is easier to bridge from extracted symbolic syntax.

The polynomial layer should exist underneath, not instead.

So the design is:

- AST for ergonomic construction and evaluation,
- polynomial denotation for mathematical meaning.

## 6. Proposed Module Layout

The new files should live under a new sub-tree and be introduced gradually.
The layout mirrors the documented split by [VM components], with chiplet-heavy
parts matching the [chiplets module trace] and lookup-heavy parts matching the
structure of [lookup buses].

Suggested layout:

```text
MidenLean/AIR/Semantics/
  Core.lean
  Expr.lean         -- includes executable and proof-facing ext expression semantics
  Builder.lean
  Check.lean
  Polynomial.lean
  WholeVM.lean
  Subsystems/
    StackArith.lean
    StackOps.lean
    ...
  Refinement/
    SymbolicToCanonical/
      StackArith.lean
      StackOps.lean
      ...
  Tests/
    Core.lean
    StackArith.lean
    ...
```

The existing files can stay where they are during migration:

- `Frame.lean` remains the legacy local kernel layer,
- `Constraints/Symbolic/*` remains the extracted Rust-facing layer,
- `Soundness/VM.lean` remains the current whole-VM symbolic scaffold.

## 7. Relation To Existing Files

The intended long-term role of the current AIR files should be:

- [Frame.lean](/Users/marcilunga/Documents/ToB/audits/miden/masm-lean/MidenLean/AIR/Frame.lean):
  legacy local proof kernel layer, eventually derivable from the canonical AIR
  semantics or replaced by canonical local projections.
- [Constraints/StackArith.lean](/Users/marcilunga/Documents/ToB/audits/miden/masm-lean/MidenLean/AIR/Constraints/StackArith.lean)
  and similar files:
  hand-written local kernels to be either retired or justified as projections
  from the canonical semantics.
- [Constraints/Symbolic/*](/Users/marcilunga/Documents/ToB/audits/miden/masm-lean/MidenLean/AIR/Constraints/Symbolic):
  extracted Rust AIR source of truth to be bridged into the canonical semantics.
- [Soundness/VM.lean](/Users/marcilunga/Documents/ToB/audits/miden/masm-lean/MidenLean/AIR/Soundness/VM.lean):
  current whole-VM symbolic boundary, eventually restated in terms of the
  canonical AIR semantics.
- [ReducedAux.lean](/Users/marcilunga/Documents/ToB/audits/miden/masm-lean/MidenLean/AIR/ReducedAux.lean):
  verifier-side algebra that may remain outside the core AIR semantics or may
  become a sibling `VerifierSemantics` layer.
- [ExtField.lean](/Users/marcilunga/Documents/ToB/audits/miden/masm-lean/MidenLean/AIR/ExtField.lean):
  should stop being described as a fully active proof layer today and instead
  become the explicit proof-facing extension denotation used by `QExpr.evalExt`,
  compatibility lemmas, and later lookup/bus proofs.

These roles should stay consistent with the published equations for
[stack AIR constraints], [decoder constraints], [chiplets overview], and the
verifier-facing public-input packing in [verifier public inputs].

## 8. Linear Implementation Plan

This section is intentionally sequential.
Each step should be completed, reviewed, and stabilized before starting the
next one. Each milestone should be tied to the corresponding published Miden
equations, not just to the current Lean file layout.

Global warning for every step:

- Do not accept **convention-only semantics**. If the intended meaning of a
  definition lives only in a name or comment, and not in the type,
  constructors, evaluator, or checker, the step is not actually closed.
- In particular, avoid placeholder APIs of the form “semantic-looking name =
  identity function” unless the surrounding type already encodes the intended
  meaning in a way that cannot be forgotten.
- Each step should therefore add a real semantic object, not just a nicer
  spelling of an older one.

### Step 1. Core AIR State

Create:

- `AIR/Semantics/Core.lean`

Add:

- `AirGlobals`
- `AirRow`
- typed selectors for current/next/base/aux/public/periodic/challenge/finals

Use [VM execution trace] and [chiplets module trace] as the source of truth for
row shape and shared columns.

Acceptance criteria:

- the file compiles,
- the row model is concrete and executable,
- no constraints are defined yet.

What not to do yet:

- no subsystem logic,
- no symbolic bridge,
- no whole-VM theorem.

Warning:

- Do not silently drop row families just because they are currently unused or
  width-zero in Rust. If a family exists at the symbolic AIR boundary, the
  canonical row model should keep an explicit slot for it.

### Step 2. Expression AST

Create:

- `AIR/Semantics/Expr.lean`

Add:

- `FExpr` for base-field expressions,
- `QExpr` for extension-field expressions,
- smart constructors for common row references.

Acceptance criteria:

- expressions can reference every needed part of `AirRow`,
- expression examples reduce by computation.

What not to do yet:

- no satisfaction relation,
- no polynomial denotation.

Warning:

- Do not let the AST omit a live variable family and expect later steps to
  “remember” it informally. Every part of `AirRow` that is semantically visible
  at the AIR boundary should be representable in the syntax, even if its
  current runtime width is zero.

### Step 3. Runnable Evaluation

Extend:

- `AIR/Semantics/Expr.lean`

Add:

- `FExpr.eval`
- executable `QExpr.eval` on `QuadFelt`

Acceptance criteria:

- `#eval` examples work,
- simple normalization lemmas exist,
- this is now a runnable AIR expression semantics.

Warning:

- Evaluation must be a real recursive semantics for the AST, not an implicit
  appeal to old helper functions or extracted formulas. If the layer cannot be
  executed on concrete rows, then it is still only notation.
- Keep the executable extension semantics on `QuadFelt`. Do not silently switch
  the runtime checker over to `ExtFelt`; the proof-facing extension denotation
  will be added later as an additional layer, not as a replacement.

### Step 4. Builder DSL

Create:

- `AIR/Semantics/Builder.lean`

Add combinators:

- `assertZero`
- `assertEq`
- `gate`
- `whenTransition`
- `append`
- `allOf`

These combinators should be expressive enough to encode the documented forms of
[ADD], [U32ADD], [op batch flags constraints], [range constraints], and
[LogUp constraints].

Acceptance criteria:

- a small subsystem constraint can be written entirely with the DSL,
- no raw anonymous-lambda lists are needed for new code.

Warning:

- Do not represent constraints as bare expressions plus a naming convention.
  The fact that a constraint is a *zero-assertion* must be explicit in the
  representation, otherwise a definition like `assertZero := id` can silently
  erase the semantic boundary.
- For extension constraints, keep the gating discipline aligned with Rust and
  the docs: gate them by base-field selectors lifted into the extension field,
  not by arbitrary extension-valued selectors.

### Step 5. Constraint Satisfaction

Create:

- `AIR/Semantics/Check.lean`

Add:

- base and extension constraint types,
- `satisfiesBase`,
- `satisfiesExt`,
- executable `checkBase`,
- executable `checkExt`.

Acceptance criteria:

- one row can be checked against one list of builder constraints,
- there are small executable tests.

Warning:

- The satisfaction relation should state actual semantic equality to zero, not
  a restated naming convention. The `Prop` form and the executable `Bool` form
  should both reflect the same zero-checking meaning.

### Step 6. First Tiny Canonical Subsystem: `StackArith.add`

Create:

- `AIR/Semantics/Subsystems/StackArith.lean`

Start with exactly one constraint:

- `add`, i.e. the documented [ADD] equation,

in canonical builder form.

Acceptance criteria:

- canonical `add` constraint is executable,
- the module imports only the new semantics files.

What not to do yet:

- do not add the entire stack arithmetic family,
- do not touch `u32*` yet.

Warning:

- Do not define the first subsystem by directly writing the post-simplified
  equation and calling it done. The subsystem object should be built with the
  canonical DSL so later refinement and composition have something real to
  target.

### Step 7. First Semantic Consequence

Create:

- `AIR/Semantics/Proofs/StackArith.lean`
  or a similarly named proof file under `AIR/Semantics/`.

Prove:

- if the canonical `add` constraint is active and satisfied, then
  `s0' = s0 + s1`.

Acceptance criteria:

- theorem is stated over the canonical builder semantics,
- not over legacy `Frame` kernels.

Warning:

- Do not “prove” the semantic consequence by assuming the already-unpacked
  equality as a hypothesis. The theorem should consume canonical constraint
  satisfaction and derive the intended equation from that.
- At this step it is acceptable for the leaf theorem to assume temporary
  *activation hypotheses* such as `r.isTransition = 1` and
  `StackArith.isAdd.eval r = 1`, but those assumptions are not allowed to
  survive as the final public theorem interface.
- The assumptions to eliminate later are:
  - transition activity, e.g. `r.isTransition = 1`
  - operation activity, e.g. `StackArith.isAdd.eval r = 1`
  - any equivalent “active row” predicate that merely packages those two facts
    without deriving them
- These are temporary only. The decoder bridge must later derive op activity,
  and the whole-row / whole-witness layer must later derive transition activity.

### Step 8. First Extracted-to-Canonical Bridge

Create:

- `AIR/Semantics/Refinement/SymbolicToCanonical/StackArith.lean`

Prove for `add`:

- the extracted symbolic `add` row formula evaluates exactly like the canonical
  builder `add` formula on every matching row.

Acceptance criteria:

- one real extracted Rust AIR constraint is bridged to the canonical spec,
- no global whole-VM assumptions are needed for this single-op proof.

Warning:

- The bridge must compare the extracted symbolic constraint with the canonical
  constraint semantics, not just compare two simplified consequences that
  already forgot how the constraint was built.
- The bridge at this step may still target the temporary active-op theorem from
  Step 7, but it must not redefine the final public interface around those
  temporary assumptions.

### Step 9. Close `StackArith` Completely

This step should no longer be treated as a flat opcode checklist.
The work should now proceed **schema-first**, so later operations are mostly
instantiations of reusable canonical patterns instead of fresh manual proofs.

Concrete Step 9 substeps:

1. **Stabilize reusable canonical proof schemas.**
   Close and reuse the generic semantic consequence lemmas for:
   - transition-gated equality constraints,
   - transition-gated zero constraints,
   - integrity-gated equality constraints,
   - integrity-gated zero constraints.

2. **Stabilize reusable symbolic-to-canonical bridge schemas.**
   Close and reuse the common bridge pattern:
   - unfold one extracted symbolic alias,
   - unfold one canonical builder constraint,
   - normalize projection/named columns,
   - finish with only small explicit algebra normalization.

3. **Stabilize shared `StackArith` helper algebra.**
   Introduce and prove once the helper layer that several ops share, rather than
   re-deriving it per operation. In particular, the `u32*` portion should use a
   shared limb package (`h0..h4`, `u32_v_lo`, `u32_v_hi`, `u32_v48`, `u32_v64`,
   validity helpers, grouped selectors, grouped output constraints) that mirrors
   the Rust structure.

4. **Close the remaining field fragment by instantiation, not by bespoke proof
   scripts.**
   The intended order for the field fragment remains:
   - `neg`
   - `mul`
   - `inv`
   - `incr`
   - `not`
   - `and`
   - `or`
   - `eq`
   - `eqz`
   - `expacc`
   - `ext2mul`

5. **Close the first grouped `u32` block.**
   Start with the smallest coherent Rust-backed slice:
   - shared `u32` limb/helper constraints,
   - `u32split`,
   - `u32assert2`.

6. **Close the shared two-output `u32` arithmetic block.**
   On top of the shared helper layer, close:
   - `u32add`,
   - `u32add3`.

7. **Close the remaining `u32` arithmetic block.**
   Then finish:
   - `u32sub`,
   - `u32mul`,
   - `u32madd`.

8. **Run a final `StackArith` closure review.**
   Before moving to Step 10, verify that all remaining `StackArith` work is now
   expressed through the reusable schemas above rather than through ad hoc
   operation-specific proof scripts.

The intended references here are [field ops] for the field fragment and
[u32 ops] for the integer fragment.

Acceptance criteria:

- every `StackArith` canonical constraint exists,
- every extracted symbolic `StackArith` constraint has a bridge theorem,
- local semantic theorems come from the canonical layer rather than legacy
  kernels,
- shared grouped Rust constraints are modeled explicitly rather than silently
  flattened into fake per-op stories,
- most new per-op theorems are instantiations of reusable schemas rather than
  fresh bespoke proof scripts.

Warning:

- Do not let later operations bypass the pattern established for `add`. Every
  operation should still pass through the same stages: canonical constraint,
  runnable check, extracted bridge, and semantic consequence.
- Do not use larger tactics as a substitute for better theorem factoring. New
  automation in this step should stay small, evidence-based, and layered on top
  of reusable schema lemmas.
- Do not erase grouped Rust constraints just to recover a per-op story. When the
  Rust AIR shares a constraint across several `u32` ops, the canonical layer
  should expose that grouping explicitly and then derive per-op consequences
  from it.
- By the end of this step, leaf theorems may still use temporary activation
  hypotheses, but the file should clearly mark them as intermediate lemmas.
  They are not yet the final subsystem-facing theorem surface.

### Step 10. Add `ExtFelt` Denotation And Polynomial Denotation

Create:

- `AIR/Semantics/Polynomial.lean`

Add:

- `QExpr.evalExt : AirRow -> ExtFelt`
- compatibility theorem `QuadFelt.toExtFelt (q.evalQuad r) = q.evalExt r`
- `FExpr.toPoly`
- `QExpr` polynomial denotation or a staged equivalent
- evaluation-denotation compatibility lemmas

At this point, `ExtField.lean` should become a real dependency of the new AIR
semantics rather than a mostly self-contained bootstrap file. The immediate
goal is not to replace `QuadFelt`, but to make `ExtFelt` the default proof
denotation for extension expressions.

If needed for lookup-heavy proofs, this is also the right stage to prove the
irreducibility facts required to strengthen `ExtFelt` from a quotient-ring
surface into a field-level proof tool.

Acceptance criteria:

- extension-field expressions have both executable and proof-facing semantics,
- `ExtFelt` proofs can be pulled back to executable `QuadFelt` equalities,
- canonical AIR now has a true polynomial semantics,
- the builder layer is proven to denote honest polynomial constraints.

Warning:

- Do not add `toPoly` as a bookkeeping translation without an evaluation
  compatibility theorem. A polynomial denotation that is not proved faithful to
  the runnable semantics is just another parallel syntax tree.
- Do not treat `ExtFelt` as a cosmetic alias for `QuadFelt`. The point of the
  new layer is to exploit Mathlib on the proof side while preserving executable
  checking on the concrete side.

### Step 11. Add More Subsystems One By One

Recommended order:

1. `StackOps` ([stack ops], [I/O ops], [system ops])
2. `StackGeneral` ([stack AIR constraints])
3. `Decoder` ([decoder overview], [decoder constraints])
4. `Range` ([range checker], [range constraints], [range bus])
5. `StackOverflow` ([stack overflow table], [stack AIR constraints])
6. `StackCrypto` ([crypto ops], [precompiles])
7. chiplets ([chiplets overview], [bitwise chiplet], [hasher chiplet],
   [memory chiplet], [ACE chiplet], [kernel ROM chiplet])
8. public inputs ([verifier public inputs], [programs])
9. bus ([lookup buses], [LogUp], [multiset checks])

For each subsystem, repeat the same pattern:

- canonical builder constraints,
- runnable checks,
- extracted symbolic bridge,
- local semantic consequences.

For lookup- and bus-heavy subsystems, the default proof style should now be:

- execute and test constraints over `QuadFelt`,
- state algebraic proof obligations over `ExtFelt`,
- transport the result back via the `QuadFelt.toExtFelt` compatibility lemmas.

Warning:

- Do not bulk-import old extracted or legacy constraint lists and call that a
  canonical subsystem. Each subsystem should be rebuilt in the new semantics,
  then related back to extraction explicitly.
- This is also the step where operation-activity assumptions should start to
  disappear from public theorem statements:
  - when the `Decoder` subsystem is added, prove that the relevant decoder facts
    imply selector facts such as `StackArith.isAdd.eval r = 1`
  - after that, public subsystem theorems should depend on decoder facts, not
    on raw selector-equals-`1` hypotheses
- In other words:
  - Step 7-9 may use `isAdd.eval r = 1` internally
  - Step 11 must introduce the bridge that derives it

### Step 12. Whole-VM Canonical AIR

Create:

- `AIR/Semantics/WholeVM.lean`

Add:

- canonical `VmAirSatisfied`,
- decomposition by subsystem,
- executable whole-VM checking for a witness.

This should combine the same families that Miden documents separately:
[stack AIR constraints], [decoder constraints], [range bus], [chiplets bus],
and [verifier public inputs].

Acceptance criteria:

- whole-VM AIR is defined once in terms of canonical subsystem constraints,
- the old `Soundness/VM.lean` story can be compared against it directly.

Warning:

- Do not define whole-VM satisfaction by merely renaming the old symbolic
  aggregate. Whole-VM AIR should compose the canonical subsystem objects, with
  the symbolic whole-VM layer treated as a refinement target.
- This is the step where transition-activity assumptions should disappear from
  the public theorem surface:
  - move from raw standalone `AirRow` statements to indexed rows or witness-row
    views where “not the last row” is represented structurally
  - derive `isTransition = 1` from the row position / witness context instead
    of assuming it as a free hypothesis
- After this step, public theorems should not expose assumptions like
  `r.isTransition = 1`. That fact should come from the whole-VM row model.

### Step 13. Migrate Existing Proofs

Once enough subsystems are in place:

- port local soundness proofs to the canonical semantics,
- retire tautological local-kernel-only lemmas where possible,
- keep legacy kernels only as temporary projections or compatibility layers.

Acceptance criteria:

- new AIR proofs cite canonical semantics first,
- old kernels are no longer the primary specification.

Warning:

- Do not preserve vacuous or tautological legacy lemmas as the main theorem
  surface. Compatibility lemmas may remain, but canonical semantics should be
  the entrypoint used by new proofs.

### Step 14. Revisit `ReducedAux`

Decide whether:

- `ReducedAux` is part of the AIR semantics boundary,
- or a sibling verifier-semantics layer.

Acceptance criteria:

- the repo states this boundary clearly and uses consistent theorem language.

Warning:

- Do not blur AIR semantics and verifier algebra in names or theorem
  statements. If `ReducedAux` remains separate, the documentation and API
  should say so explicitly rather than implying it was already part of the core
  AIR semantics all along.

## 9. Review Rules For Each Step

Each step should be reviewed with the same questions.
The benchmark is always the documented equations and decompositions in Miden,
for example [ADD], [U32ADD], [decoder constraints], [bitwise constraints], and
[LogUp constraints].

### 9.0 Temporary Assumptions Must Be Discharged

Some intermediate lemmas will need temporary activation hypotheses while a
subsystem is being bootstrapped. Typical examples are:

- `r.isTransition = 1`
- `StackArith.isAdd.eval r = 1`
- `StackArith.isNeg.eval r = 1`
- `StackArith.isMul.eval r = 1`

These assumptions are acceptable only as temporary leaf-lemma hypotheses.

Required discharge schedule:

- Step 11 must remove raw op-selector assumptions from public theorem
  statements by deriving them from decoder facts.
- Step 12 must remove raw transition assumptions from public theorem
  statements by deriving them from row position / whole-witness context.

Failure condition:

- A step is not fully closed if its final public theorem interface still
  exposes selector-equals-`1` or transition-equals-`1` assumptions that should
  have been discharged by the later bridge steps.

### 9.1 Is There A New Canonical Definition?

If a step only adds helper lemmas and no new canonical semantic object, it is
probably too shallow.

### 9.2 Is It Executable?

Every semantic layer should admit small `#eval`-style sanity tests.

### 9.3 Is It Clearly Separate From Rust Extraction?

The canonical semantics should not secretly just be a reformatting of the
extracted symbolic files.
It should be a Lean specification that the extraction refines to.

### 9.4 Is The Theorem Actually About The New Semantics?

Avoid replacing one tautology with another.
Theorems should be stated over the canonical AIR semantics, not only over an
already simplified consequence of it.

### 9.5 Did We Avoid Pulling In The Whole VM Too Early?

If a step needs the entire VM to prove a tiny arithmetic fact, the layering is
probably wrong.

## 10. Immediate Next Step

The next concrete implementation target should be:

- `AIR/Semantics/Core.lean`

with:

- `AirGlobals`,
- `AirRow`,
- typed row accessors,
- and nothing else.

That is the smallest step that creates a real new semantic foundation without
dragging in proofs or whole-VM composition too early. It is also the smallest
step still grounded directly in the documented [VM execution trace] and
[chiplets module trace].

## 11. QC Issues

- `QC-001` Documentation drift in the verifier-side VM docs:
  [audit-miden-vm/crates/lib/core/docs/sys/vm/mod.md](../../../audit-miden-vm/crates/lib/core/docs/sys/vm/mod.md)
  still states that the main trace is 73 columns wide, while the current Rust
  AIR and symbolic extractor use raw `TRACE_WIDTH = 71` and handle alignment
  padding separately via `PADDED_TRACE_WIDTH`. See
  [audit-miden-vm/air/src/trace/mod.rs](../../../audit-miden-vm/air/src/trace/mod.rs)
  and [masm-to-lean/src/symbolic.rs](../../../masm-to-lean/src/symbolic.rs).
  This is a QC/documentation issue, not a bug in Step 1 of the canonical AIR
  semantics work.

[design overview]: ../../../audit-miden-vm/docs/src/design/index.md
[VM components]: ../../../audit-miden-vm/docs/src/design/index.md#vm-components
[VM execution trace]: ../../../audit-miden-vm/docs/src/design/index.md#vm-execution-trace
[lookup buses]: ../../../audit-miden-vm/docs/src/design/lookups/index.md#communication-buses-in-miden-vm
[LogUp]: ../../../audit-miden-vm/docs/src/design/lookups/logup.md
[LogUp constraints]: ../../../audit-miden-vm/docs/src/design/lookups/logup.md#constraints
[multiset checks]: ../../../audit-miden-vm/docs/src/design/lookups/multiset.md
[stack]: ../../../audit-miden-vm/docs/src/design/stack/index.md
[stack AIR constraints]: ../../../audit-miden-vm/docs/src/design/stack/index.md#air-constraints
[stack overflow table]: ../../../audit-miden-vm/docs/src/design/stack/index.md#overflow-table
[field ops]: ../../../audit-miden-vm/docs/src/design/stack/field_ops.md
[ADD]: ../../../audit-miden-vm/docs/src/design/stack/field_ops.md#add
[u32 ops]: ../../../audit-miden-vm/docs/src/design/stack/u32_ops.md
[U32ADD]: ../../../audit-miden-vm/docs/src/design/stack/u32_ops.md#u32add
[stack ops]: ../../../audit-miden-vm/docs/src/design/stack/stack_ops.md
[I/O ops]: ../../../audit-miden-vm/docs/src/design/stack/io_ops.md
[system ops]: ../../../audit-miden-vm/docs/src/design/stack/system_ops.md
[crypto ops]: ../../../audit-miden-vm/docs/src/design/stack/crypto_ops.md
[precompiles]: ../../../audit-miden-vm/docs/src/design/stack/precompiles.md
[decoder overview]: ../../../audit-miden-vm/docs/src/design/decoder/index.md
[decoder trace]: ../../../audit-miden-vm/docs/src/design/decoder/index.md#decoder-trace
[decoder constraints]: ../../../audit-miden-vm/docs/src/design/decoder/constraints.md
[op batch flags constraints]: ../../../audit-miden-vm/docs/src/design/decoder/constraints.md#op-batch-flags-constraints
[chiplets overview]: ../../../audit-miden-vm/docs/src/design/chiplets/index.md
[chiplets module trace]: ../../../audit-miden-vm/docs/src/design/chiplets/index.md#chiplets-module-trace
[chiplet selector constraints]: ../../../audit-miden-vm/docs/src/design/chiplets/index.md#chiplet-selector-constraints
[chiplets bus]: ../../../audit-miden-vm/docs/src/design/chiplets/index.md#chiplets-bus
[bitwise chiplet]: ../../../audit-miden-vm/docs/src/design/chiplets/bitwise.md
[bitwise constraints]: ../../../audit-miden-vm/docs/src/design/chiplets/bitwise.md#constraints
[hasher chiplet]: ../../../audit-miden-vm/docs/src/design/chiplets/hasher.md
[kernel ROM chiplet]: ../../../audit-miden-vm/docs/src/design/chiplets/kernel_rom.md
[memory chiplet]: ../../../audit-miden-vm/docs/src/design/chiplets/memory.md
[ACE chiplet]: ../../../audit-miden-vm/docs/src/design/chiplets/ace.md
[range checker]: ../../../audit-miden-vm/docs/src/design/range.md
[range execution trace]: ../../../audit-miden-vm/docs/src/design/range.md#execution-trace
[range constraints]: ../../../audit-miden-vm/docs/src/design/range.md#execution-trace-constraints
[range bus]: ../../../audit-miden-vm/docs/src/design/range.md#communication-bus
[programs]: ../../../audit-miden-vm/docs/src/design/programs.md
[verifier public inputs]: ../../../audit-miden-vm/crates/lib/core/docs/sys/vm/public_inputs.md
