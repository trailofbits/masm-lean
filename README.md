# MASM-to-Lean

Formal verification of the [Miden Assembly](https://github.com/0xMiden/miden-vm) (MASM) core library in Lean 4. MASM programs from the Miden core library are translated into Lean using a shallow embedding, and their correctness is proved against an executable semantics of the Miden VM.

## Components

- **`MidenLean/`** — Lean 4 model of the Miden VM.
- **`MidenLean/Generated/`** — MASM procedures translated to `List Op` definitions.
- **`MidenLean/Proofs/`** — Correctness proofs for individual procedures.
- **`masm-to-lean/`** — Rust tool that parses `.masm` files and emits Lean definitions.

## Correctness Proofs

| Theorem                       | Procedure              | Property                                                         |
| ----------------------------- | ---------------------- | ---------------------------------------------------------------- |
| `u64_and_correct`             | `u64::and`             | Produces limb-wise bitwise AND of two u64 values                 |
| `u64_clz_correct`             | `u64::clz`             | Counts leading zeros of a u64 value                              |
| `u64_eq_correct`              | `u64::eq`              | Returns 1 iff two u64 values are equal                           |
| `u64_eqz_correct`             | `u64::eqz`             | Returns 1 iff both u32 limbs are zero                            |
| `u64_overflowing_add_correct` | `u64::overflowing_add` | Produces `[overflow, c_lo, c_hi]` matching `(a + b)` with carry  |
| `u64_wrapping_add_correct`    | `u64::wrapping_add`    | Produces `[c_lo, c_hi]` equal to `(a + b) mod 2^64`             |
| `u64_wrapping_sub_correct`    | `u64::wrapping_sub`    | Produces `[c_lo, c_hi]` equal to `(a - b) mod 2^64`             |
| `word_eqz_correct`            | `word::eqz`            | Returns 1 iff all four word elements are zero                    |
| `word_testz_correct`           | `word::testz`          | Returns 1 iff all four word elements are zero (non-destructive)  |

## Verifying

Requires [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) (v4.28.0) and [elan](https://github.com/leanprover/elan).

```bash
# Verify all proofs (builds entire project including the Mathlib dependency)
lake build

# Verify a single proof file
lake build MidenLean.Proofs.Word
lake build MidenLean.Proofs.WordTestz
lake build MidenLean.Proofs.U64
lake build MidenLean.Proofs.U64And
lake build MidenLean.Proofs.U64Clz
lake build MidenLean.Proofs.U64Eq
lake build MidenLean.Proofs.U64Sub
```

(A successful build with no `sorry` warnings confirms all theorems are machine-checked.)
