# CLAUDE.md

Formal verification of Miden Assembly (MASM) core library procedures in Lean 4. See [ARCHITECTURE.md](ARCHITECTURE.md) for design decisions and repository layout.

## Build

```bash
lake build            # full build (includes Mathlib — slow first time)
lake build MidenLean  # just the Lean library and proofs
```

Lean 4 v4.28.0 via elan. A clean build with zero `sorry` means all theorems are machine-checked.

## Key conventions

- **Lean 4 / Mathlib naming**: lowerCamelCase for defs and theorems, UpperCamelCase for types and namespaces.
- **Dispatch architecture** (`Semantics.lean`): `execInstruction` dispatches each instruction to a dedicated handler (`execDrop`, `execDup`, `execSwap`, `execMovup`, etc.). `execWithEnv` executes `List Op` with a `ProcEnv` for procedure calls.
- **Step lemmas** (`StepLemmas.lean`): parametric where possible (`stepDup`, `stepSwap`), with explicit range hypotheses for `movup`/`movdn`. Proved by `unfold execInstruction execFoo; rfl` or `simp`.
- **Proof pattern**: destructure state, unfold procedure, rewrite to monadic `do`-form, step through with exact `rw [stepFoo]`, structural tactics (`miden_swap`, `miden_dup`, `miden_movup`, `miden_movdn`), and `miden_bind`. Use `miden_step` mainly for short residual steps, not as the default for long proofs. See `MidenLean/Proofs/U64/Min.lean`, `MidenLean/Proofs/U64/Max.lean`, and `MidenLean/Proofs/U64/Shr.lean`.
- **Correctness theorems**: named `<procedure>_correct` in snake_case matching the MASM name (e.g., `u64_wrapping_sub_correct`).
- **Generated code** (`MidenLean/Generated/`): produced by the Rust translator. Do not edit by hand.
- **Generated proof scaffolding** (`MidenLean/Proofs/Generated/`): produced by `masm-to-lean`. Do not edit by hand; copy the relevant scaffold into the manual proof file and complete it there.

## Proof Workflow

The expected workflow for a new or updated proof is:

1. Regenerate the translated Lean code and proof scaffolding from the MASM source under `path-to/miden-vm/crates/lib/core/asm`.

```bash
timeout 180s cargo run --manifest-path masm-to-lean/Cargo.toml -- \
  path/to/miden-vm/crates/lib/core/asm/math/u64.masm \
  -o MidenLean/Generated \
  --namespace Miden.Core \
  --generate-proofs \
  --proofs-output MidenLean/Proofs/Generated
```

2. Find the generated scaffold for the procedure you want to prove.

- Translated procedure definitions live in `MidenLean/Generated/<Module>.lean`.
- Generated proof scaffolds are split per procedure:
  - `MidenLean/Proofs/Generated/<Module>/Common.lean`
  - `MidenLean/Proofs/Generated/<Module>/<Proc>.lean`
- The top-level `MidenLean/Proofs/Generated/<Module>.lean` file is only a lightweight index.

3. Copy the generated scaffold into the manual proof file under `MidenLean/Proofs/...`.

- Example: copy `MidenLean/Proofs/Generated/U64/Shr.lean` into `MidenLean/Proofs/U64/Shr.lean` and then edit the manual file.
- Keep the generated file untouched so it can be regenerated freely.

4. Complete the proof in the manual file.

- For short straight-line procedures, keep the scaffold mostly flat and explicit.
- For longer procedures with expensive ops like `pow2`, `u32DivMod`, `u32OverflowSub`, `div`, or `cswap`, split the proof into semantic chunks.
- Prefer exact step rewrites and structural tactics over repeated `miden_step`.
- Add helper lemmas only for real side conditions such as `isU32`, nonzero divisors, boolean normalization, or small arithmetic identities.
- Remove helper lemmas that are no longer used.

5. Validate with targeted Lean checks before broader builds.

```bash
timeout 180s lake env lean MidenLean/Proofs/U64/Shr.lean
timeout 180s lake build MidenLean.Proofs.U64.Shr
```

Use the smallest relevant target first. Only run broader builds when the local proof checks.

## Scaffolding Expectations

- Generated scaffolds are a starting point, not a finished proof.
- `FlatAuto` and `FlatExplicit` scaffolds should contain useful setup and step structure for simpler procedures.
- `Chunked` scaffolds are intentionally more skeletal. They should guide chunk boundaries and composition, but the final manual proof usually needs named intermediate values and local helper lemmas.
- When looking for examples:
  - use `Min` and `Max` as the reference shape for short proofs
  - use `Shr` as the reference shape for chunked straight-line proofs

## Development Workflow

- Do not commit without explicit permission.
- Do not use git worktrees or branches unless asked.
- Always run Lean checks and `lake build` with strict timeouts. Default to 3-5 minutes. Otherwise you risk getting stuck or causing the entire system to run out of memory.
- Prefer targeted proof checks such as `timeout 180s lake build MidenLean.Proofs.U64.Shr` over whole-project builds while iterating.
- When writing new proofs, follow the existing pattern in the closest existing proof file.
