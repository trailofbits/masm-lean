# Architecture

This document describes the high-level design of the MASM-to-Lean formal verification project. For build instructions and the list of proven theorems, see [README.md](README.md). For the phased implementation roadmap, see [PLAN.md](PLAN.md).

## Overview

The project has two components:

1. **Lean library** (`MidenLean/`) — An executable semantics of the Miden VM in Lean 4, and correctness proofs for core library procedures.
2. **Rust translator** (`masm-to-lean/`) — Parses `.masm` source files and emits a Lean `List Op` definition for each procedure.

## Repository Layout

```
├── MidenLean.lean                  Root import file
├── MidenLean/
│   ├── Felt.lean                   Goldilocks field (ZMod (2^64 - 2^32 + 1))
│   ├── State.lean                  VM state: stack, memory, locals, advice
│   ├── Instruction.lean            Inductive type for ~130 MASM instructions
│   ├── Op.lean                     Control flow: ifElse, repeat, whileTrue
│   ├── Semantics.lean              stepInstruction, execOps, exec
│   ├── Generated/
│   │   ├── Word.lean               11 word procedures as List Op
│   │   └── U64.lean                36 u64 procedures as List Op
│   └── Proofs/
│       ├── Helpers.lean            MidenState simp lemmas and Felt boolean lemmas
│       ├── StepLemmas.lean         Reusable single-instruction lemmas
│       ├── Tactics.lean            miden_step / miden_steps tactic macros
│       ├── Word.lean               word::eqz proof
│       ├── WordTestz.lean          word::testz proof
│       ├── U64.lean                u64::eqz, overflowing_add, wrapping_add proofs
│       ├── U64Eq.lean              u64::eq proof
│       ├── U64Sub.lean             u64::wrapping_sub proof
│       ├── U64And.lean             u64::and proof
│       └── U64Clz.lean             u64::clz proof
├── masm-to-lean/                   Rust translator
│   └── src/
│       ├── main.rs                 CLI entry point
│       ├── translate.rs            AST → Lean code generation
│       ├── instruction.rs          Instruction → Lean constructor mapping
│       └── module.rs               Module/procedure → namespace/def
└── README.md                       Quick-start and proof inventory
```

## Design Decisions

MASM programs are represented as `List Op` values rather than Lean functions, with a separate interpreter defining their semantics (in `Semantics.lean`). This is the same approach used by StarkWare's Cairo formal proofs, the Verified-zkEVM Clean project, and LNSym for ARMv8. The key advantage is that the translator cannot introduce unsoundness. Even if the translator emits a wrong definition, the Lean type-checker will reject any proof that relies on incorrect behavior.

### VM State

Defined in `State.lean` as a structure with four fields:

| Field    | Type         | Semantics                           |
| -------- | ------------ | ----------------------------------- |
| `stack`  | `List Felt`  | Operand stack (head = top)          |
| `memory` | `Nat → Felt` | Random-access memory, 0-initialized |
| `locals` | `Nat → Felt` | Procedure-local memory slots        |
| `advice` | `List Felt`  | Nondeterministic advice stack       |

Memory is modeled as a total function `Nat → Felt` rather than a finite map. This is standard in machine code formalizations (LNSym, eth-isabelle, Cairo). Writes produce a new function via pointwise update; `simp` reduces reads-after-writes trivially. Out-of-bounds addresses (≥ 2^32) cause the semantics to return `none`.

The VM executor (defined by `stepInstruction` and `execOps`) return `Option MidenState`. Failure conditions (failed assertions, division by zero, stack underflow, out-of-bounds memory) produce `none`. A correctness theorem of the form `exec fuel s ops = some s'` proves both that the procedure terminates within the fuel budget and that the result state matches the specification. `execOps` takes a `fuel` parameter that bounds recursion depth. This ensures structural termination without complex well-founded arguments.

`ProcEnv` (`String → Option (List Op)`) maps procedure names to their bodies. `exec` uses an empty environment (no inter-procedure calls); `execWithProcs` resolves `exec` instructions via the environment. Currently all proven procedures are self-contained (no `exec` instructions), so the empty environment suffices.

## Proof Architecture

A typical correctness proof follows this structure:

1. **Destructure** the state: `obtain ⟨stk, mem, locs, adv⟩ := s`
2. **Unfold** the procedure and execution machinery: `unfold exec ProcName execOps`
3. **Rewrite to monadic form**: `change (do let s' ← stepInstruction ...; ...)`
4. **Step through** instruction by instruction: `rw [stepFoo]; dsimp only [bind, ...]`
5. **Close** with `simp` or `rfl`

For procedures with branching (`ifElse`), step 4 includes a `by_cases` to case-split on the condition. For procedures with loops (`repeat`), `unfold execOps.doRepeat` unrolls each iteration. We implement a number of step lemmas to pre-compute the effect of a single `stepInstruction` call on a stack of the appropriate shape. For example, `stepDup` handles any `dup n` instruction regardless of the number of operands on the stack, and `stepSwap` handles any `swap n` instruction regardless of the stack shape.

### Tactics (`Tactics.lean`)

Three tactic macros automate the step-through pattern:

- **`miden_bind`** — `dsimp only [bind, Bind.bind, Option.bind, List.set]`
- **`miden_step`** — tries each step lemma in sequence (with parametric arguments for `stepDup` and `stepSwap`)
- **`miden_steps`** — repeats `miden_step` until no more instructions remain

These are useful for straightforward linear instruction sequences. Proofs involving branching, loops, or hypotheses (e.g., `isU32` preconditions for bitwise operations) still require manual intervention.

### Helper Lemmas (`Helpers.lean`)

`@[simp]`-tagged lemmas for:

- `MidenState.withStack` projections (stack, memory, locals, advice)
- `Felt.isBool` on `if p then 1 else 0` expressions
- `Felt.ite_mul_ite` for boolean AND reduction

These ensure that `simp` can close goals involving state projections and boolean field arithmetic.

## Naming Conventions

Following Lean 4 / Mathlib style:

| Category          | Convention     | Examples                                          |
| ----------------- | -------------- | ------------------------------------------------- |
| Types, structures | UpperCamelCase | `MidenState`, `Instruction`, `Op`                 |
| Definitions       | lowerCamelCase | `stepInstruction`, `execOps`, `zeroMemory`        |
| Theorems          | lowerCamelCase | `stepDup`, `stepSwap`, `u64_eq_correct`           |
| Namespaces        | UpperCamelCase | `MidenLean`, `MidenLean.StepLemmas`               |
| Generated procs   | dot-separated  | `Miden.Core.Math.U64.eq`, `Miden.Core.Word.testz` |

Procedure-level correctness theorems use `snake_case` with a `_correct` suffix to match the MASM procedure name (e.g., `u64_wrapping_sub_correct` for `u64::wrapping_sub`).

## References

- [Miden VM](https://github.com/0xMiden/miden-vm) — the virtual machine and MASM assembler
- [Miden core library](https://github.com/0xMiden/miden-vm/tree/main/miden-stdlib/asm) — MASM source for the standard library
- [StarkWare Cairo formal proofs](https://github.com/starkware-libs/formal-proofs) — Lean 4, shallow embedding of Cairo
- [ProvenZK](https://github.com/reilabs/proven-zk) — Lean 4 ZK circuit verification
- [Verified-zkEVM Clean](https://github.com/Verified-zkEVM/clean/) — Lean 4, AIR constraint verification
- [LNSym](https://github.com/leanprover/LNSym) — ARMv8 formalization in Lean 4
- [Mathlib ZMod](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/ZMod/Basic.html) — finite field library used for `Felt`
