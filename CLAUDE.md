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
- **MANDATORY memory cap**: every `lake build` invocation must be wrapped in a systemd-run memory cap. Never run `lake build` without this wrapper -- it will OOM the machine (62GB RAM, Lean+Mathlib workers eat it all). Never remove, bypass, or "investigate" by disabling this constraint.
  ```bash
  # Full project build
  timeout 300s systemd-run --user --scope -p MemoryMax=10G -- lake build -j 2 MidenLean
  # Targeted module build
  timeout 180s systemd-run --user --scope -p MemoryMax=10G -- lake build -j 2 MidenLean.Proofs.U64.Shr
  # Single file check
  timeout 180s systemd-run --user --scope -p MemoryMax=6G -- lake env lean MidenLean/Proofs/U64/Shr.lean
  ```
  If a build gets killed by the memory cap, that means the build is too memory-hungry -- reduce parallelism (`-j 1`) or build a smaller target. Do NOT raise or remove the cap.
- Prefer targeted proof checks over whole-project builds while iterating.
- When writing new proofs, follow the existing pattern in the closest existing proof file.

## Lean Proof Principles

General Lean 4 proof guidance that applies to any contributor.

### Goal inspection

Always use `lean_goal` (MCP) or `lake env lean <file>` with error
output to read the actual proof state before writing tactics. The
elaborator rewrites types in ways not visible in source -- never guess
the goal from reading the .lean file.

### No-sorry invariant

Never leave `sorry` in committed code. If a goal cannot be proved,
move the blocking condition into the type signature as an explicit
hypothesis parameter. Sorrys hide proof gaps; explicit hypotheses
expose them. Check before every commit:
```bash
grep -rn 'sorry' --include='*.lean' | grep -v '/\.lake/' \
  | grep -v 'Proofs/Generated/' | grep -v '\-\-.*sorry'
```

### Lint discipline

Treat all warnings as errors. When `simp only [...]` triggers "unused
argument" warnings, remove the flagged arguments rather than
suppressing the linter. Run the full build and check for warnings
after any proof change.

### Step lemma architecture

Each instruction/opcode has a dedicated step lemma in
`StepLemmas.lean` that rewrites `execInstruction <state> <instr>` to
`some <result>`. The `miden_step` tactic in `Tactics.lean` dispatches
across all step lemmas automatically.

- Never unfold `execInstruction` directly in a proof. It is a large
  match that produces huge, slow goals. Always go through step lemmas
  or equation lemmas (e.g., `execInstruction_u32OverflowSub`).
- When a step lemma requires hypotheses not in context (e.g.,
  `isU32`), prove them as `have` before the `rw`. Common helpers:
  `u32_mod_isU32`, `felt_ofNat_isU32_of_lt`, `by native_decide` for
  constants.
- The pattern is always: `rw [stepFoo ...]; miden_bind`.

### Proof setup macros

- `miden_setup Proc.name` -- for theorems using `exec` (no
  sub-procedure calls). Destructures state, substs hypotheses,
  unfolds the procedure, normalizes binds.
- `miden_setup_env Proc.name` -- same but for `execWithEnv`
  (procedures that call sub-procedures via ProcEnv).
- `miden_call Proc.name` -- unfolds a sub-procedure call inside an
  existing proof.

These macros assume the state is named `s` and the stack hypothesis
is named `hs`.

### Chunked proofs for long programs

For procedures with 20+ instructions, decompose the program into
chunks (segments of `List Op`), prove each chunk separately with
concrete stack types, then compose with an append lemma:
```lean
theorem exec_append (fuel : Nat) (s : MidenState)
    (xs ys : List Op) :
    exec fuel s (xs ++ ys) = (do
      let s' <- exec fuel s xs
      exec fuel s' ys)
```
See `Shr.lean` for the reference implementation of this pattern.

### Macro hygiene

If a tactic macro needs to reference variables from the caller's
scope (like `s` or `hs`), use `set_option hygiene false in` before
the `syntax`/`macro_rules` definitions. Without this, Lean's hygienic
scoping renames the variables and the macro silently fails.

### Generated scaffolding isolation

Files under `Proofs/Generated/` must never be imported into the
build. They contain `sorry` placeholders by design and exist only as
starting-point templates. Only the manually completed proofs under
`Proofs/U64/` and `Proofs/Word/` are imported via `MidenLean.lean`.
