# MASM-to-Lean

Formal verification of the [Miden Assembly](https://github.com/0xMiden/miden-vm) (MASM) core library in Lean 4. MASM programs from the Miden core library are translated into Lean using a shallow embedding, and their correctness is proved against an executable semantics of the Miden VM.

## Components

- **`MidenLean/`** — Lean 4 model of the Miden VM.
- **`MidenLean/Generated/`** — MASM procedures translated to `List Op` definitions.
- **`MidenLean/Proofs/`** — Correctness proofs for individual procedures.
- **`masm-to-lean/`** — Rust tool that parses `.masm` files and emits Lean definitions.

## Correctness Proofs

21 of 31 `u64` procedures proved (68%), plus 2 `word` procedures.

### Arithmetic

| Theorem | Procedure | Property |
| --- | --- | --- |
| `u64_overflowing_add_correct` | `u64::overflowing_add` | Produces `[overflow, c_lo, c_hi]` matching `(a + b)` with carry |
| `u64_wrapping_add_correct` | `u64::wrapping_add` | Produces `[c_lo, c_hi]` equal to `(a + b) mod 2^64` |
| `u64_widening_add_correct` | `u64::widening_add` | Produces `[c_lo, c_hi, carry]` for full 65-bit sum |
| `u64_wrapping_sub_correct` | `u64::wrapping_sub` | Produces `[c_lo, c_hi]` equal to `(a - b) mod 2^64` |
| `u64_overflowing_sub_correct` | `u64::overflowing_sub` | Produces `[underflow, c_lo, c_hi]` matching `(a - b)` with borrow |
| `u64_wrapping_mul_correct` | `u64::wrapping_mul` | Produces `[c_lo, c_hi]` equal to low 64 bits of `a * b` |

### Comparison

| Theorem | Procedure | Property |
| --- | --- | --- |
| `u64_eq_correct` | `u64::eq` | Returns 1 iff two u64 values are equal |
| `u64_neq_correct` | `u64::neq` | Returns 1 iff two u64 values are not equal |
| `u64_eqz_correct` | `u64::eqz` | Returns 1 iff both u32 limbs are zero |
| `u64_lt_correct` | `u64::lt` | Returns 1 iff `a < b` as unsigned 64-bit integers |
| `u64_gt_correct` | `u64::gt` | Returns 1 iff `a > b` as unsigned 64-bit integers |
| `u64_lte_correct` | `u64::lte` | Returns 1 iff `a ≤ b` as unsigned 64-bit integers |
| `u64_gte_correct` | `u64::gte` | Returns 1 iff `a ≥ b` as unsigned 64-bit integers |

### Bitwise

| Theorem | Procedure | Property |
| --- | --- | --- |
| `u64_and_correct` | `u64::and` | Produces limb-wise bitwise AND of two u64 values |
| `u64_or_correct` | `u64::or` | Produces limb-wise bitwise OR of two u64 values |
| `u64_xor_correct` | `u64::xor` | Produces limb-wise bitwise XOR of two u64 values |

### Bit counting

| Theorem | Procedure | Property |
| --- | --- | --- |
| `u64_clz_correct` | `u64::clz` | Counts leading zeros of a u64 value |
| `u64_ctz_correct` | `u64::ctz` | Counts trailing zeros of a u64 value |
| `u64_clo_correct` | `u64::clo` | Counts leading ones of a u64 value |
| `u64_cto_correct` | `u64::cto` | Counts trailing ones of a u64 value |

### Validation

| Theorem | Procedure | Property |
| --- | --- | --- |
| `u64_u32assert4_correct` | `u64::u32assert4` | Validates that four stack elements are u32 values |

### Word

| Theorem | Procedure | Property |
| --- | --- | --- |
| `word_eqz_correct` | `word::eqz` | Returns 1 iff all four word elements are zero |
| `word_testz_correct` | `word::testz` | Returns 1 iff all four word elements are zero (non-destructive) |

## Verifying

Requires [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) (v4.28.0) and [elan](https://github.com/leanprover/elan).

```bash
# Verify all proofs (builds entire project including the Mathlib dependency)
lake build

# Verify a single proof file
lake build MidenLean.Proofs.U64WrappingMul
lake build MidenLean.Proofs.U64Gte
lake build MidenLean.Proofs.U64Clz
lake build MidenLean.Proofs.WordTestz
```

(A successful build with no `sorry` warnings confirms all theorems are machine-checked.)
