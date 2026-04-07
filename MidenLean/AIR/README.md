# AIR Constraint Verification

This folder formalizes and stress-tests the Miden VM AIR in Lean 4.
It currently has three distinct AIR views:

- a small runnable local model for row-level proofs,
- a canonical AIR semantics layer under `Semantics/`,
- and a symbolic extraction of the Rust AIR used as the closest implementation-facing source of truth.

The code is useful only if you keep those roles separate.
This README explains that split and states the current proof boundary clearly.

For the canonical AIR-semantics design history and remaining work, see
[DESIGN-AIR-semantics.md](./DESIGN-AIR-semantics.md).

## Why It Matters

The AIR work answers different questions at different layers.

- What does one local transition constraint say?
- Does a small accepted AIR slice force the right math?
- Does the full symbolic AIR row satisfy the extracted Rust constraints?
- Where does the current formalization stop short of a full proof-system theorem?

[!IMPORTANT]
Most theorems here are **not** STARK proof-system soundness theorems.
Most are either:
- local AIR soundness or counterexamples for one instruction or one procedure slice, or
- whole-VM AIR facts at the current symbolic AIR boundary.

## Install And Use

You need Lean 4 from `lean-toolchain`.
You also need Rust if you want to rebuild extractors or test vectors.

[!NOTE]
The first `lake build` may fetch Mathlib.
The symbolic extractor build compiles local Rust crates.

Build the library:

```bash
lake build MidenLean
```

Check one local AIR proof:

```bash
lake env lean MidenLean/AIR/Proofs/StackArith.lean
```

Check the whole-VM symbolic scaffold:

```bash
lake env lean MidenLean/AIR/Soundness/VM.lean
```

Regenerate local differential test vectors:

```bash
cd air-test-vectors
cargo run > test_vectors.json
```

Re-extract the symbolic Rust AIR:

```bash
cargo build --release -p masm-to-lean --features symbolic
./target/release/symbolic-extract MidenLean/AIR/Constraints/Symbolic/
```

## Common Commands

Check the hand-written local arithmetic kernels on real traces:

```bash
lake env lean MidenLean/AIR/Tests/StackArithDiff.lean
```

Check the local op kernels on real traces:

```bash
lake env lean MidenLean/AIR/Tests/OpsDiff.lean
```

Check one SHA-256 local AIR result:

```bash
lake env lean MidenLean/AIR/Proofs/Sha256ChSoundness.lean
```

Check the reduced auxiliary verifier algebra:

```bash
lake env lean MidenLean/AIR/ReducedAux.lean
```

## Current Architecture

### 1. Runnable local AIR semantics

This is the proof-friendly, executable layer used for most local instruction and
procedure proofs.

- [Frame.lean](./Frame.lean) defines `Frame`, `Constraint := Frame → Felt`, `ConstraintSet`, and `Frame.check`.
- [Constraints/StackArith.lean](./Constraints/StackArith.lean) gives hand-written local kernels such as `add`, `mul`, and `u32add`.
- [Constraints/Ops.lean](./Constraints/Ops.lean) gives the local stack-op kernels such as `pad`, `dup`, `swap`, `movup`, and `cswap`.
- [TraceBuilder.lean](./TraceBuilder.lean) builds local witnesses for completeness-style arguments.
- [Constraints/BitwiseChiplet.lean](./Constraints/BitwiseChiplet.lean) provides a separate runnable mini-model for the bitwise chiplet, with `BitwiseFrame.check`.

This layer is the closest thing in this folder to a runnable AIR semantics.
If you want to execute constraints with `#eval`, this is usually the layer you use.

### 2. Executable extension-field and final verifier algebra

Some AIR-adjacent algebra lives outside the `Frame` checker.

- [ExtField.lean](./ExtField.lean) defines executable `QuadFelt` arithmetic for `GF(p²)`.
- [ReducedAux.lean](./ReducedAux.lean) models the final reduced auxiliary check with `reducedAuxValues` and `verifierAccepts`.

`ReducedAux` is part of the verifier boundary, but it is not a row-local
polynomial constraint module.

### 3. Canonical AIR semantics

This is now the canonical Lean AIR specification layer.

- [Semantics/Core.lean](./Semantics/Core.lean) defines the typed row model with `AirGlobals`, `AirRow`, row phases, and boundary selectors.
- [Semantics/Expr.lean](./Semantics/Expr.lean), [Semantics/Builder.lean](./Semantics/Builder.lean), [Semantics/Check.lean](./Semantics/Check.lean), [Semantics/Polynomial.lean](./Semantics/Polynomial.lean), and [Semantics/Tactics.lean](./Semantics/Tactics.lean) define the canonical expression language, builder DSL, executable checking, polynomial denotation, and proof support.
- [Semantics/Subsystems/System.lean](./Semantics/Subsystems/System.lean), [Semantics/Subsystems/Range.lean](./Semantics/Subsystems/Range.lean), [Semantics/Subsystems/Decoder.lean](./Semantics/Subsystems/Decoder.lean), [Semantics/Subsystems/StackGeneral.lean](./Semantics/Subsystems/StackGeneral.lean), [Semantics/Subsystems/StackOverflow.lean](./Semantics/Subsystems/StackOverflow.lean), [Semantics/Subsystems/StackOps.lean](./Semantics/Subsystems/StackOps.lean), [Semantics/Subsystems/StackArith.lean](./Semantics/Subsystems/StackArith.lean), [Semantics/Subsystems/StackCrypto.lean](./Semantics/Subsystems/StackCrypto.lean), [Semantics/Subsystems/ChipletSelectors.lean](./Semantics/Subsystems/ChipletSelectors.lean), [Semantics/Subsystems/ChipletBitwise.lean](./Semantics/Subsystems/ChipletBitwise.lean), [Semantics/Subsystems/ChipletHasher.lean](./Semantics/Subsystems/ChipletHasher.lean), [Semantics/Subsystems/ChipletKernelRom.lean](./Semantics/Subsystems/ChipletKernelRom.lean), [Semantics/Subsystems/ChipletMemory.lean](./Semantics/Subsystems/ChipletMemory.lean), [Semantics/Subsystems/ChipletAce.lean](./Semantics/Subsystems/ChipletAce.lean), and [Semantics/Subsystems/PublicInputs.lean](./Semantics/Subsystems/PublicInputs.lean) are the 15 current canonical subsystem files.
- [Semantics/Refinement/SymbolicToCanonical/System.lean](./Semantics/Refinement/SymbolicToCanonical/System.lean), [Semantics/Refinement/SymbolicToCanonical/Range.lean](./Semantics/Refinement/SymbolicToCanonical/Range.lean), [Semantics/Refinement/SymbolicToCanonical/Decoder.lean](./Semantics/Refinement/SymbolicToCanonical/Decoder.lean), [Semantics/Refinement/SymbolicToCanonical/StackGeneral.lean](./Semantics/Refinement/SymbolicToCanonical/StackGeneral.lean), [Semantics/Refinement/SymbolicToCanonical/StackOverflow.lean](./Semantics/Refinement/SymbolicToCanonical/StackOverflow.lean), [Semantics/Refinement/SymbolicToCanonical/StackOps.lean](./Semantics/Refinement/SymbolicToCanonical/StackOps.lean), [Semantics/Refinement/SymbolicToCanonical/StackArith.lean](./Semantics/Refinement/SymbolicToCanonical/StackArith.lean), [Semantics/Refinement/SymbolicToCanonical/StackCrypto.lean](./Semantics/Refinement/SymbolicToCanonical/StackCrypto.lean), [Semantics/Refinement/SymbolicToCanonical/ChipletSelectors.lean](./Semantics/Refinement/SymbolicToCanonical/ChipletSelectors.lean), [Semantics/Refinement/SymbolicToCanonical/ChipletBitwise.lean](./Semantics/Refinement/SymbolicToCanonical/ChipletBitwise.lean), [Semantics/Refinement/SymbolicToCanonical/ChipletHasher.lean](./Semantics/Refinement/SymbolicToCanonical/ChipletHasher.lean), [Semantics/Refinement/SymbolicToCanonical/ChipletKernelRom.lean](./Semantics/Refinement/SymbolicToCanonical/ChipletKernelRom.lean), [Semantics/Refinement/SymbolicToCanonical/ChipletMemory.lean](./Semantics/Refinement/SymbolicToCanonical/ChipletMemory.lean), [Semantics/Refinement/SymbolicToCanonical/ChipletAce.lean](./Semantics/Refinement/SymbolicToCanonical/ChipletAce.lean), and [Semantics/Refinement/SymbolicToCanonical/PublicInputs.lean](./Semantics/Refinement/SymbolicToCanonical/PublicInputs.lean) are the 15 current subsystem-level bridge files.
- [Semantics/Refinement/SymbolicToCanonical/StackGeneralCore.lean](./Semantics/Refinement/SymbolicToCanonical/StackGeneralCore.lean) is an extra shared helper bridge used by the `StackGeneral` refinement.
- [Semantics/Spec/StackArith.lean](./Semantics/Spec/StackArith.lean), [Semantics/Proofs/StackArith.lean](./Semantics/Proofs/StackArith.lean), and [Semantics/Gaps/StackArith.lean](./Semantics/Gaps/StackArith.lean) show the current canonical spec/proof/gap pattern on one concrete slice.

This layer is no longer planned; it is the canonical AIR specification
currently in the tree. It is still incomplete: some subsystem refinements
remain open, and there is no canonical whole-VM composition file yet.

### 4. Rust-facing symbolic AIR

This is the current source-of-truth view of the Rust AIR.

- [SymbolicFrame.lean](./SymbolicFrame.lean) defines the raw symbolic row model.
- [Constraints/Symbolic/](./Constraints/Symbolic) contains the extracted symbolic Rust AIR.
- [masm-to-lean/src/symbolic.rs](../../masm-to-lean/src/symbolic.rs) builds those files by running the actual `miden-air` `enforce_main()` code under `SymbolicAirBuilder`.

The symbolic constraints still contain selector facts and flag products such as
`is_transition * flag_product * body = 0`.
That is expected.
They are closer to Rust than the local kernels, but harder to use directly in
small proofs.

### 5. Whole-VM symbolic composition

This layer packages the symbolic AIR into a full witness and row-by-row
satisfaction story.

- [TraceFrame.lean](./TraceFrame.lean) models full typed row pairs.
- [Soundness/VM.lean](./Soundness/VM.lean) defines `VmWitness`, `rowView`, `VmAirSatisfied`, and the generic Layer-3 scaffold.
- [Soundness/VMHelpers.lean](./Soundness/VMHelpers.lean) and [Soundness/VMSections.lean](./Soundness/VMSections.lean) decompose the aggregate symbolic AIR by subsystem.
- [Soundness/VMSource.lean](./Soundness/VMSource.lean) states the missing source-to-witness refinement explicitly as `SourceVmBridge`.

This is the strongest whole-VM AIR story currently formalized in Lean.
It stops at the current AIR boundary.

### 6. Semantic side and local bridges

The AIR folder does not contain the source semantics itself.
That lives in [../Semantics.lean](../Semantics.lean) and the procedure proofs under [../Proofs](../Proofs).

- [Bridge.lean](./Bridge.lean) bridges selected local `Frame` constraints to `execInstruction`-style semantics.
- [Soundness/Eqz.lean](./Soundness/Eqz.lean) shows one end-to-end local composition for `u64::eqz`, including a custom global overflow-bus bridge.

`Bridge.lean` is a local bridge.
It is **not** the missing symbolic whole-VM bridge.

## How Current AIR Proofs Relate To Rust

There are three main trust levels in the current tree.

| Layer | Relation to Rust | Typical use |
|-------|------------------|-------------|
| `Constraints/Symbolic/*` | Strongest link. Built by executing actual `miden-air` constraint code. | Whole-VM AIR reasoning and subsystem decomposition. |
| `Semantics/*` | Canonical Lean spec layer. Refined against the extracted symbolic AIR one subsystem at a time. | Canonical subsystem specs, refinement theorems, and semantic consequences. |
| `Constraints/*` hand-written kernels | Manual proof-side kernels. Easier to prove over, but not formally derived from symbolic AIR. | Local soundness and counterexample proofs. |

[!WARNING]
Do not treat every AIR file as equally close to Rust.
If the question is “what does the Rust AIR really enforce?”, prefer the
symbolic files.
If the question is “can I prove this local transition law quickly?”, the local
`Frame` kernels are usually the right tool.

## What “Soundness” Means Here

The word `soundness` is overloaded.
This folder currently uses it in narrower ways.

- **Local AIR soundness**: a local accepted constraint slice forces the intended next-row relation.
- **Local AIR completeness**: an honest execution can build a local witness satisfying that slice.
- **Whole-VM AIR exactness at the current Lean boundary**: symbolic row and bus satisfaction match the current `VmWitness` validity notion.

This folder does **not** yet provide:

- a full STARK proof-system soundness theorem,
- a full knowledge-soundness theorem,
- a generic source-program execution to `VmWitness` refinement,
- or a generic symbolic-row-to-local-kernel bridge for each opcode.

## Current Gaps

[!IMPORTANT]
Two missing bridges explain most of the remaining architecture tension in this folder.

1. **Symbolic AIR -> canonical/local proof kernels**

The canonical `Semantics/*` layer now exists, but the missing generic theorem is
still the one you usually want for per-op proofs:

- symbolic row satisfies extracted symbolic constraints,
- decoder facts say which op is active,
- therefore the projected canonical subsystem constraints, and then any local
  `Frame`-level projection used by `Proofs/*`, are satisfied.

That bridge is not yet built uniformly.
Without it, the canonical proof tree, the local proof tree, and the whole-VM
symbolic proof tree are only partially connected.

2. **Source execution -> whole `VmWitness`**

[Soundness/VMSource.lean](./Soundness/VMSource.lean) says this explicitly.
The repo does not yet have a generic construction that turns source execution
into a full `VmWitness` with decoder, memory, chiplet, clock, and bus facts.

There is also one smaller status item:

- The AIR library no longer has only one known `sorry`. At this snapshot there
  are 64 executable `sorry`s under `MidenLean/AIR`: 40 in
  `Semantics/Refinement/SymbolicToCanonical/ChipletHasher.lean`, 15 in
  `Semantics/Refinement/SymbolicToCanonical/Decoder.lean`, 5 in
  `Semantics/Refinement/SymbolicToCanonical/StackOps.lean`, 3 in
  `Semantics/Refinement/SymbolicToCanonical/StackOverflow.lean`, and 1 legacy
  `sorry` in [BitwiseChiplet.lean](./BitwiseChiplet.lean).

## Extraction Tooling

### Preferred: symbolic extraction

[masm-to-lean/src/symbolic.rs](../../masm-to-lean/src/symbolic.rs) is the preferred extractor.
It runs the actual Rust AIR code and emits `Constraints/Symbolic/*`.

Use this path when you want the closest Lean view of the real Rust AIR.

### Differential test vectors

[air-test-vectors/](../../air-test-vectors) runs the real VM, captures local frames, and emits JSON test vectors.
The Lean tests then use `Frame.check` to confirm that local constraint files
accept those real traces.

This is a useful fidelity check.
It is not a formal equivalence proof.

## Selected Results

The AIR work already contains both positive results and negative results.

- Local soundness proofs exist for many arithmetic, stack, bitwise, word-order, and SHA-256 helper slices.
- Whole-VM symbolic AIR decomposition exists in `Soundness/VM*.lean`.
- Machine-checked counterexamples exist for the lowered `u32rotr.b` / `u32shr.b` family and several SHA-256 helpers that compose them.

These counterexamples matter because they show a real AIR gap can survive
differential testing against honest traces.

## Repo Map

- [Frame.lean](./Frame.lean): local executable AIR model.
- [TraceFrame.lean](./TraceFrame.lean): full typed row pair.
- [SymbolicFrame.lean](./SymbolicFrame.lean): raw symbolic row view.
- [Semantics/](./Semantics): canonical AIR semantics core, subsystem definitions, symbolic-to-canonical refinements, and the current spec/proof/gap files.
- [Constraints/](./Constraints): local kernels and symbolic extraction.
- [Proofs/](./Proofs): local AIR soundness and counterexample proofs.
- [Soundness/](./Soundness): whole-VM symbolic composition and source-boundary statements.
- [ReducedAux.lean](./ReducedAux.lean): final verifier algebra on aux columns.
- [TraceBuilder.lean](./TraceBuilder.lean): local witness construction.

## Developer Notes

- Prefer the symbolic extractor when you need a Rust-facing AIR fact.
- Prefer the local `Frame` kernels when you need a small runnable checker or a short proof.
- If you add a new local proof kernel, document whether it is hand-written, legacy-generated, or bridged from symbolic extraction.
- If you claim a result is “whole-VM” or “source-level,” say which bridge assumptions are still in play.
