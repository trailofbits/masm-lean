# AIR Constraint Verification

This folder formalizes and stress-tests the Miden VM AIR in Lean 4.
It has two main AIR views:

- a small runnable local model for row-level proofs, and
- a symbolic extraction of the Rust AIR used as the current source of truth.

The code is useful only if you keep those two roles separate.
This README explains that split and states the current proof boundary clearly.

For the planned canonical AIR-semantics redesign, see
[DESIGN-AIR-semantics.md](/Users/marcilunga/Documents/ToB/audits/miden/masm-lean/MidenLean/AIR/DESIGN-AIR-semantics.md).

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

- [Frame.lean](/Users/marcilunga/Documents/ToB/audits/miden/masm-lean/MidenLean/AIR/Frame.lean) defines `Frame`, `Constraint := Frame → Felt`, `ConstraintSet`, and `Frame.check`.
- [Constraints/StackArith.lean](/Users/marcilunga/Documents/ToB/audits/miden/masm-lean/MidenLean/AIR/Constraints/StackArith.lean) gives hand-written local kernels such as `add`, `mul`, and `u32add`.
- [Constraints/Ops.lean](/Users/marcilunga/Documents/ToB/audits/miden/masm-lean/MidenLean/AIR/Constraints/Ops.lean) gives the local stack-op kernels such as `pad`, `dup`, `swap`, `movup`, and `cswap`.
- [TraceBuilder.lean](/Users/marcilunga/Documents/ToB/audits/miden/masm-lean/MidenLean/AIR/TraceBuilder.lean) builds local witnesses for completeness-style arguments.
- [Constraints/BitwiseChiplet.lean](/Users/marcilunga/Documents/ToB/audits/miden/masm-lean/MidenLean/AIR/Constraints/BitwiseChiplet.lean) provides a separate runnable mini-model for the bitwise chiplet, with `BitwiseFrame.check`.

This layer is the closest thing in this folder to a runnable AIR semantics.
If you want to execute constraints with `#eval`, this is usually the layer you use.

### 2. Executable extension-field and final verifier algebra

Some AIR-adjacent algebra lives outside the `Frame` checker.

- [ExtField.lean](/Users/marcilunga/Documents/ToB/audits/miden/masm-lean/MidenLean/AIR/ExtField.lean) defines executable `QuadFelt` arithmetic for `GF(p²)`.
- [ReducedAux.lean](/Users/marcilunga/Documents/ToB/audits/miden/masm-lean/MidenLean/AIR/ReducedAux.lean) models the final reduced auxiliary check with `reducedAuxValues` and `verifierAccepts`.

`ReducedAux` is part of the verifier boundary, but it is not a row-local
polynomial constraint module.

### 3. Rust-facing symbolic AIR

This is the current source-of-truth view of the Rust AIR.

- [SymbolicFrame.lean](/Users/marcilunga/Documents/ToB/audits/miden/masm-lean/MidenLean/AIR/SymbolicFrame.lean) defines the raw symbolic row model.
- [Constraints/Symbolic/](/Users/marcilunga/Documents/ToB/audits/miden/masm-lean/MidenLean/AIR/Constraints/Symbolic) contains the extracted symbolic Rust AIR.
- [masm-to-lean/src/symbolic.rs](/Users/marcilunga/Documents/ToB/audits/miden/masm-lean/masm-to-lean/src/symbolic.rs) builds those files by running the actual `miden-air` `enforce_main()` code under `SymbolicAirBuilder`.

The symbolic constraints still contain selector facts and flag products such as
`is_transition * flag_product * body = 0`.
That is expected.
They are closer to Rust than the local kernels, but harder to use directly in
small proofs.

### 4. Whole-VM symbolic composition

This layer packages the symbolic AIR into a full witness and row-by-row
satisfaction story.

- [TraceFrame.lean](/Users/marcilunga/Documents/ToB/audits/miden/masm-lean/MidenLean/AIR/TraceFrame.lean) models full typed row pairs.
- [Soundness/VM.lean](/Users/marcilunga/Documents/ToB/audits/miden/masm-lean/MidenLean/AIR/Soundness/VM.lean) defines `VmWitness`, `rowView`, `VmAirSatisfied`, and the generic Layer-3 scaffold.
- [Soundness/VMHelpers.lean](/Users/marcilunga/Documents/ToB/audits/miden/masm-lean/MidenLean/AIR/Soundness/VMHelpers.lean) and [Soundness/VMSections.lean](/Users/marcilunga/Documents/ToB/audits/miden/masm-lean/MidenLean/AIR/Soundness/VMSections.lean) decompose the aggregate symbolic AIR by subsystem.
- [Soundness/VMSource.lean](/Users/marcilunga/Documents/ToB/audits/miden/masm-lean/MidenLean/AIR/Soundness/VMSource.lean) states the missing source-to-witness refinement explicitly as `SourceVmBridge`.

This is the strongest whole-VM AIR story currently formalized in Lean.
It stops at the current AIR boundary.

### 5. Semantic side and local bridges

The AIR folder does not contain the source semantics itself.
That lives in [Semantics.lean](/Users/marcilunga/Documents/ToB/audits/miden/masm-lean/MidenLean/Semantics.lean) and the procedure proofs under [../Proofs](/Users/marcilunga/Documents/ToB/audits/miden/masm-lean/MidenLean/Proofs).

- [Bridge.lean](/Users/marcilunga/Documents/ToB/audits/miden/masm-lean/MidenLean/AIR/Bridge.lean) bridges selected local `Frame` constraints to `execInstruction`-style semantics.
- [Soundness/Eqz.lean](/Users/marcilunga/Documents/ToB/audits/miden/masm-lean/MidenLean/AIR/Soundness/Eqz.lean) shows one end-to-end local composition for `u64::eqz`, including a custom global overflow-bus bridge.

`Bridge.lean` is a local bridge.
It is **not** the missing symbolic whole-VM bridge.

## How Current AIR Proofs Relate To Rust

There are two main trust levels in the current tree.

| Layer | Relation to Rust | Typical use |
|-------|------------------|-------------|
| `Constraints/Symbolic/*` | Strongest link. Built by executing actual `miden-air` constraint code. | Whole-VM AIR reasoning and subsystem decomposition. |
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
Two missing bridges explain most of the architecture tension in this folder.

1. **Symbolic AIR -> local proof kernels**

The missing generic theorem is the one you usually want for per-op proofs:

- symbolic row satisfies extracted symbolic constraints,
- decoder facts say which op is active,
- therefore the projected local `Frame` satisfies the proof kernel used by `Proofs/*`.

That bridge is not yet built uniformly.
Without it, the local proof tree and the whole-VM symbolic proof tree are only
partially connected.

2. **Source execution -> whole `VmWitness`**

[Soundness/VMSource.lean](/Users/marcilunga/Documents/ToB/audits/miden/masm-lean/MidenLean/AIR/Soundness/VMSource.lean) says this explicitly.
The repo does not yet have a generic construction that turns source execution
into a full `VmWitness` with decoder, memory, chiplet, clock, and bus facts.

There is also one smaller status item:

- The AIR library still contains one known `sorry` in the bitwise chiplet recurrence bound.

## Extraction Tooling

### Preferred: symbolic extraction

[masm-to-lean/src/symbolic.rs](/Users/marcilunga/Documents/ToB/audits/miden/masm-lean/masm-to-lean/src/symbolic.rs) is the preferred extractor.
It runs the actual Rust AIR code and emits `Constraints/Symbolic/*`.

Use this path when you want the closest Lean view of the real Rust AIR.

### Differential test vectors

[air-test-vectors/](/Users/marcilunga/Documents/ToB/audits/miden/masm-lean/air-test-vectors) runs the real VM, captures local frames, and emits JSON test vectors.
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

- [Frame.lean](/Users/marcilunga/Documents/ToB/audits/miden/masm-lean/MidenLean/AIR/Frame.lean): local executable AIR model.
- [TraceFrame.lean](/Users/marcilunga/Documents/ToB/audits/miden/masm-lean/MidenLean/AIR/TraceFrame.lean): full typed row pair.
- [SymbolicFrame.lean](/Users/marcilunga/Documents/ToB/audits/miden/masm-lean/MidenLean/AIR/SymbolicFrame.lean): raw symbolic row view.
- [Constraints/](/Users/marcilunga/Documents/ToB/audits/miden/masm-lean/MidenLean/AIR/Constraints): local kernels and symbolic extraction.
- [Proofs/](/Users/marcilunga/Documents/ToB/audits/miden/masm-lean/MidenLean/AIR/Proofs): local AIR soundness and counterexample proofs.
- [Soundness/](/Users/marcilunga/Documents/ToB/audits/miden/masm-lean/MidenLean/AIR/Soundness): whole-VM symbolic composition and source-boundary statements.
- [ReducedAux.lean](/Users/marcilunga/Documents/ToB/audits/miden/masm-lean/MidenLean/AIR/ReducedAux.lean): final verifier algebra on aux columns.
- [TraceBuilder.lean](/Users/marcilunga/Documents/ToB/audits/miden/masm-lean/MidenLean/AIR/TraceBuilder.lean): local witness construction.

## Developer Notes

- Prefer the symbolic extractor when you need a Rust-facing AIR fact.
- Prefer the local `Frame` kernels when you need a small runnable checker or a short proof.
- If you add a new local proof kernel, document whether it is hand-written, legacy-generated, or bridged from symbolic extraction.
- If you claim a result is “whole-VM” or “source-level,” say which bridge assumptions are still in play.
