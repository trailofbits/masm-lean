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
- **Step lemmas** (`StepLemmas.lean`): parametric where possible (`stepDup`, `stepSwap`), concrete for `movup`/`movdn`. These are cached reductions of `stepInstruction`, not new semantics.
- **Proof pattern**: destructure state, unfold procedure, rewrite to monadic `do`-form, step through with `rw [stepFoo]; dsimp only [bind, ...]`, close with `simp`/`rfl`. See any file in `MidenLean/Proofs/` for examples.
- **Correctness theorems**: named `<procedure>_correct` in snake_case matching the MASM name (e.g., `u64_wrapping_sub_correct`).
- **Generated code** (`MidenLean/Generated/`): produced by the Rust translator. Do not edit by hand.

## Workflow

- Do not commit without explicit permission.
- Do not use git worktrees or branches unless asked.
- Use `lake build` with a 10-minute timeout for verification — Mathlib-heavy files can be slow.
- When writing new proofs, follow the existing pattern in the closest existing proof file.
