# Architecture

This document describes the high-level design of the MASM-to-Lean formal verification project. For build instructions and the list of proven theorems, see [README.md](README.md).

## Overview

The project has two components:

1. **Lean library** (`MidenLean/`) — An executable semantics of the Miden VM in Lean 4, and correctness proofs for core library procedures.
2. **Rust translator** (`masm-to-lean/`) — Parses `.masm` source files and emits a Lean `List Op` definition for each procedure.

## Repository Layout

```
├── MidenLean.lean                  Root import file
├── MidenLean/
│   ├── Felt.lean                   Goldilocks field implementation
│   ├── Instruction.lean            Inductive type with ~130 MASM instructions
│   ├── Op.lean                     Control flow and procedure call operations
│   ├── Concrete/
│   │   ├── State.lean              Miden VM state definition (Concrete.State)
│   │   └── Exec.lean               Executable semantics for MASM instructions and procedures
│   ├── Symbolic/                   Symbolic executor, soundness lemmas, and reflection tactics
│   ├── Generated/                  Auto-generated MASM procedure definitions (do not edit)
│   └── Proofs/
│       ├── Helpers.lean            Reusable helper lemmas for state projections and boolean normalization
│       ├── SimpAttrs.lean          `@[simp]` attributes for helper lemmas
│       ├── StepLemmas.lean         Reusable single-instruction lemmas
│       ├── Tactics.lean            Reusable proof tactics
│       ├── Generated/              Auto-generated proof scaffolding (do not edit)
│       └── ...                     Per-module manual proofs for individual procedures
├── masm-to-lean/                   Rust translator from MASM to Lean
└── README.md                       Quick-start and proof inventory
```

## Design Decisions

MASM programs are represented as `List Op` values rather than Lean functions, with a separate interpreter defining their semantics (in `Concrete/Exec.lean`). This is the same approach used by StarkWare's Cairo formal proofs, the Verified-zkEVM Clean project, and LNSym for ARMv8. The key advantage is that the translator cannot introduce unsoundness. Even if the translator emits a wrong definition, the Lean type-checker will reject any proof that relies on incorrect behavior.

### VM State

Defined in `Concrete/State.lean` as a structure with four fields:

| Field    | Type         | Semantics                           |
| -------- | ------------ | ----------------------------------- |
| `stack`  | `List Felt`  | Operand stack (head = top)          |
| `memory` | `Nat → Felt` | Random-access memory, 0-initialized |
| `frames` | `List LocalFrame` | Local-frame stack for procedure locals |
| `advice` | `List Felt`  | Nondeterministic advice stack       |

Memory is modeled as a total function `Nat → Felt` rather than a finite map. This is standard in machine code formalizations (LNSym, eth-isabelle, Cairo). Writes produce a new function via pointwise update; `simp` reduces reads-after-writes trivially. Out-of-bounds addresses (≥ 2^32) cause the semantics to return `none`.

Each MASM instruction is implemented by a dedicated handler function (e.g., `execDrop`, `execDup`, `execSwap`, `execMovup`). The top-level `execInstruction` is a thin dispatch that pattern-matches on the `Instruction` and delegates to the appropriate handler. This avoids duplicating instruction logic between the semantics and the step lemmas.

The VM executor (defined by `execInstruction` and `execProcedure`) returns `Option Concrete.State`. Failure conditions (failed assertions, division by zero, stack underflow, out-of-bounds memory) produce `none`. A correctness theorem of the form `execProcedure emptyEnv fuel s ops = some s'` proves both that the procedure terminates within the fuel budget and that the result state matches the specification. `execProcedure` takes a `fuel` parameter that bounds recursion depth. This ensures structural termination without complex well-founded arguments.

`ProcEnv` (`String → Option Procedure`) maps procedure names to procedures. `emptyEnv` is the trivial environment (no inter-procedure calls). For manual proofs, per-module proof files typically define concrete environments such as `u64ProcEnv` or `u128ProcEnv` for call-bearing procedures.

## Proof Architecture

The project now has two complementary proof styles:

1. **Manual step-by-step execution proofs** over `execProcedure`, using step lemmas and chunk decomposition.
2. **Symbolic-execution-based reflection proofs**, where a symbolic executor computes the effect of a straight-line block and a soundness theorem transports that symbolic result back to the concrete semantics.

Both styles prove the same semantic object: an equation in the executable semantics. The symbolic path exists to scale proof generation across larger parts of the core library.

### Theorem Layout

The target theorem layout for each verified procedure is:

- **`*_exec`**: a low-level, fuel-parameterized execution theorem over `execProcedure` (with `emptyEnv` for procedures that make no calls). This theorem states the concrete before/after stack shape, and mentions memory or frame-relevant state only when the procedure externally changes them.
- **`*_correct`**: a high-level semantic corollary derived from `*_exec`, stated in terms of the intended mathematical operation on the corresponding Lean model type (`U64`, `U128`, words, etc.).

Historically many files use a `*_raw` name for the low-level theorem. Those theorems play the same role as `*_exec` and are being migrated incrementally toward the new naming/layout.

The `_exec` layer is also the intended theorem-backed call-summary interface for proof automation: when a caller reaches a singleton `.exec "foo"` leaf, automation should prefer `foo_exec` over recomputing a large symbolic summary from the callee body.

### Manual Proof Method

A typical manual correctness proof follows this structure:

1. **Destructure** the state: `obtain ⟨stk, mem, frames, adv⟩ := s`
2. **Unfold** the procedure and execution machinery: `unfold emptyEnv ProcName execProcedure`
3. **Rewrite to monadic form**: `change (do let s' ← execInstruction ...; ...)`
4. **Step through** instruction by instruction: `rw [stepFoo]; miden_bind` or use `miden_step`
5. **Close** with `simp` or `rfl`

For procedures with branching (`ifElse`), step 4 includes a `by_cases` to case-split on the condition. For procedures with loops (`repeat`), `unfold execProcedure.doRepeat` unrolls each iteration. Step lemmas in `StepLemmas.lean` pre-compute the effect of a single `execInstruction` call by unfolding the dispatch and the handler (e.g., `unfold execInstruction execDup; simp`). The lemmas are parametric where possible: `stepDup` handles any `dup n`, `stepSwap` handles any `swap n`, and `stepMovup`/`stepMovdn` handle any valid index with an explicit range hypothesis.

### Tactics (`Tactics.lean`)

Tactic macros automate the step-through pattern:

- **`miden_bind`** — normalizes monadic bind and list operations after a step lemma rewrite
- **`miden_dup`**, **`miden_swap`**, **`miden_movup`**, **`miden_movdn`** — apply the corresponding step lemma with automatic argument resolution
- **`miden_step`** — tries each step lemma in sequence, covering all hypothesis-free instructions
- **`miden_steps`** — repeats `miden_step` until no more instructions remain

These are useful for straightforward linear instruction sequences. Proofs involving branching, loops, or hypotheses (e.g., `isU32` preconditions for bitwise operations) still require manual intervention.

### Symbolic Execution and Reflection

The symbolic proof stack lives under `MidenLean/Symbolic/`:

- `Expr.lean` defines symbolic expressions, boolean/connective combinators, and evaluation.
- `State.lean` and `Exec.lean` define symbolic states, preconditions, and symbolic execution for instructions and straight-line op lists.
- `Soundness.lean` proves that symbolic execution is sound with respect to `execProcedure`.
- `Reflect.lean` packages this into tactic-facing reflection theorems for fully concrete initial states.
- `Tactic.lean` implements `miden_reflect` and `miden_vcg`.

The reflection workflow is:

1. Recognize a concrete `execProcedure` goal.
2. Extract the relevant stack prefix and concrete state projections.
3. Run symbolic execution on the procedure body.
4. Use the soundness theorem to turn the symbolic result into a concrete execution equation.
5. Normalize the reflected result back to the user-facing stack equation.

`miden_reflect` is the leaf closer for straight-line bodies. It supports:

- plain instruction-only blocks
- call-bearing straight-line blocks via `ReflectEnv`
- theorem-shaped goals over a concrete `s : Concrete.State`

`miden_vcg` is the control-flow decomposer. It currently supports:

- `ifElse`
- concrete-count `repeat`

and delegates straight-line leaves back to `miden_reflect`. `whileTrue` is intentionally still out of scope for automatic proofs.

### Call Summaries

There are two call-summary mechanisms:

1. **Symbolic fallback**: `ReflectEnv.ofConcrete` builds a proof-carrying symbolic environment from a reducible concrete `ProcEnv`, and `procSpec` recursively summarizes callees symbolically.
2. **Theorem-backed overrides**: for singleton `.exec` leaves, `miden_reflect` can bridge to a direct callee theorem named by convention as `<module>_<proc>_exec` (for example, `u128_wrapping_mul_exec`) and prefer that theorem over symbolic recomputation.

The theorem-backed path is intended for expensive helpers such as multiplication kernels, where a previously proved `_exec` theorem is far cheaper and more stable than rebuilding the summary from the whole callee body inside every caller proof.

### Helper Lemmas (`Helpers.lean`)

`@[simp]`-tagged lemmas for:

- `Concrete.State.withStack` projections (stack, memory, locals, advice)
- local-frame and read-after-write simplification
- `Felt.isBool` on `if p then 1 else 0` expressions
- boolean-flag normalization (`Felt.ite_prop_eq_one_iff` and friends, scoped to
  the `miden_reflect_norm` set)

These ensure that `simp` can close goals involving state projections and boolean field arithmetic.

## Naming Conventions

Following Lean 4 / Mathlib style:

| Category          | Convention     | Examples                                          |
| ----------------- | -------------- | ------------------------------------------------- |
| Types, structures | UpperCamelCase | `Concrete.State`, `Instruction`, `Op`             |
| Definitions       | lowerCamelCase | `execInstruction`, `execProcedure`, `zeroMemory`  |
| Theorems          | lowerCamelCase | `stepDup`, `stepSwap`, `u64_eq_correct`           |
| Namespaces        | UpperCamelCase | `MidenLean`, `MidenLean.StepLemmas`               |
| Generated procs   | dot-separated  | `Miden.Core.Math.U64.eq`, `Miden.Core.Word.testz` |

Procedure-level theorem names use `snake_case` matching the MASM procedure name:

- low-level execution theorems: `u64_wrapping_sub_exec`
- high-level semantic theorems: `u64_wrapping_sub_correct`

Legacy low-level theorems with `_raw` suffix remain in some files during the transition to the `_exec` layout.

## References

- [Miden VM](https://github.com/0xMiden/miden-vm) — the virtual machine and MASM assembler
- [Miden core library](https://github.com/0xMiden/miden-vm/tree/main/miden-stdlib/asm) — MASM source for the standard library
- [StarkWare Cairo formal proofs](https://github.com/starkware-libs/formal-proofs) — Lean 4, shallow embedding of Cairo
- [ProvenZK](https://github.com/reilabs/proven-zk) — Lean 4 ZK circuit verification
- [Verified-zkEVM Clean](https://github.com/Verified-zkEVM/clean/) — Lean 4, AIR constraint verification
- [LNSym](https://github.com/leanprover/LNSym) — ARMv8 formalization in Lean 4
- [Mathlib ZMod](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/ZMod/Basic.html) — finite field library used for `Felt`
