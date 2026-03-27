# MASM-to-Lean

Formal verification of the [Miden Assembly](https://github.com/0xMiden/miden-vm) (MASM) core library in Lean 4. MASM programs from the Miden core library are translated into Lean using a shallow embedding, and their correctness is proved against an executable semantics of the Miden VM.

## Components

- **`MidenLean/`** — Lean 4 model of the Miden VM.
- **`MidenLean/Generated/`** — MASM procedures translated to `List Op` definitions.
- **`MidenLean/Proofs/`** — Manual correctness proofs for individual procedures.
- **`MidenLean/Proofs/Generated/`** — Auto-generated proof scaffolding, split per procedure.
- **`masm-to-lean/`** — Rust tool that parses `.masm` files and emits Lean definitions and proof scaffolding.

## Correctness Proofs

Manual proof files are organized per procedure:

- **`MidenLean/Proofs/U32/Common.lean`** contains shared proof helpers for the `u32` type.
- **`MidenLean/Proofs/U64/`** contains the `u64` correctness theorems, one file per procedure.
- **`MidenLean/Proofs/U64/Common.lean`** contains shared proof support for the `u64` proof tree.
- **`MidenLean/Proofs/U128/`** contains the `u128` correctness theorems, one file per procedure.
- **`MidenLean/Proofs/U128/Common.lean`** contains shared proof support for the `u128` proof tree.
- **`MidenLean/Proofs/U256/`** contains the `u256` correctness theorems, one file per procedure.
- **`MidenLean/Proofs/U256/Common.lean`** contains shared proof support for the `u256` proof tree.
- **`MidenLean/Proofs/Word/`** contains the `word` correctness theorems, one file per procedure.

The current checked manual proofs cover 83 procedures: 31 in `u64`, 36 in `u128`, 5 in `u256`, 11 in `word`.

### `u64` (31 / 31)

| Procedure | Theorem | Summary | Manual proof file |
| --- | --- | --- | --- |
| `u64::and` | `u64_and_correct` | `u64::and` computes bitwise AND of two u64 values. | `MidenLean/Proofs/U64/And.lean` |
| `u64::clo` | `u64_clo_correct` | `u64::clo` counts leading ones of a u64 value. | `MidenLean/Proofs/U64/Clo.lean` |
| `u64::clz` | `u64_clz_correct` | `u64::clz` counts leading zeros of a u64 value. | `MidenLean/Proofs/U64/Clz.lean` |
| `u64::cto` | `u64_cto_correct` | `u64::cto` counts trailing ones of a u64 value. | `MidenLean/Proofs/U64/Cto.lean` |
| `u64::ctz` | `u64_ctz_correct` | `u64::ctz` counts trailing zeros of a u64 value. | `MidenLean/Proofs/U64/Ctz.lean` |
| `u64::div` | `u64_div_correct` | `u64::div` verifies and returns the quotient of two u64 values. Execution succeeds iff the advice-supplied q and r satisfy q * b + r = a and r < b. | `MidenLean/Proofs/U64/Div.lean` |
| `u64::divmod` | `u64_divmod_correct` | `u64::divmod` verifies the Euclidean division of two u64 values. Execution succeeds iff the advice-supplied quotient q and remainder r satisfy q * b + r = a and r < b. | `MidenLean/Proofs/U64/Divmod.lean` |
| `u64::eq` | `u64_eq_correct` | `u64::eq` tests equality of two u64 values. | `MidenLean/Proofs/U64/Eq.lean` |
| `u64::eqz` | `u64_eqz_correct` | `u64::eqz` tests whether a u64 value is zero. | `MidenLean/Proofs/U64/Eqz.lean` |
| `u64::gt` | `u64_gt_correct` | `u64::gt` pushes 1 iff `a > b` (as u64). | `MidenLean/Proofs/U64/Gt.lean` |
| `u64::gte` | `u64_gte_correct` | `u64::gte` pushes 1 iff `a ≥ b` (as u64). | `MidenLean/Proofs/U64/Gte.lean` |
| `u64::lt` | `u64_lt_correct` | `u64::lt` pushes 1 iff `a < b` (as u64). | `MidenLean/Proofs/U64/Lt.lean` |
| `u64::lte` | `u64_lte_correct` | `u64::lte` pushes 1 iff `a ≤ b` (as u64). | `MidenLean/Proofs/U64/Lte.lean` |
| `u64::max` | `u64_max_correct` | `u64::max` computes the maximum of two u64 values. | `MidenLean/Proofs/U64/Max.lean` |
| `u64::min` | `u64_min_correct` | `u64::min` computes the minimum of two u64 values. | `MidenLean/Proofs/U64/Min.lean` |
| `u64::mod` | `u64_mod_correct` | `u64::mod` verifies and returns the remainder of two u64 values. Execution succeeds iff the advice-supplied q and r satisfy q * b + r = a and r < b. | `MidenLean/Proofs/U64/Mod.lean` |
| `u64::neq` | `u64_neq_correct` | `u64::neq` tests inequality of two u64 values. | `MidenLean/Proofs/U64/Neq.lean` |
| `u64::or` | `u64_or_correct` | `u64::or` computes bitwise OR of two u64 values. | `MidenLean/Proofs/U64/Or.lean` |
| `u64::overflowing_add` | `u64_overflowing_add_correct` | `u64::overflowing_add` computes `a + b` with overflow detection. | `MidenLean/Proofs/U64/OverflowingAdd.lean` |
| `u64::overflowing_sub` | `u64_overflowing_sub_correct` | `u64::overflowing_sub` computes `a - b` with underflow detection. | `MidenLean/Proofs/U64/OverflowingSub.lean` |
| `u64::rotl` | `u64_rotl_correct` | `u64::rotl` left-rotates a u64 value by `shift` bits. | `MidenLean/Proofs/U64/Rotl.lean` |
| `u64::rotr` | `u64_rotr_correct` | `u64::rotr` right-rotates a u64 value by `shift` bits, only when `shift mod 32 ≠ 0`. | `MidenLean/Proofs/U64/Rotr.lean` |
| `u64::shl` | `u64_shl_correct` | `u64::shl` left-shifts a u64 value by `shift` bits. | `MidenLean/Proofs/U64/Shl.lean` |
| `u64::shr` | `u64_shr_correct` | `u64::shr` right-shifts a u64 value by `shift` bits. | `MidenLean/Proofs/U64/Shr.lean` |
| `u64::u32assert4` | `u64_u32assert4_correct` | `u64::u32assert4` succeeds and leaves the stack unchanged iff all four top elements are u32 values. | `MidenLean/Proofs/U64/U32Assert4.lean` |
| `u64::widening_add` | `u64_widening_add_correct` | `u64::widening_add` computes the full 65-bit sum of two u64 values. | `MidenLean/Proofs/U64/WideningAdd.lean` |
| `u64::widening_mul` | `u64_widening_mul_correct` | `u64::widening_mul` computes the full 128-bit product `a * b`. | `MidenLean/Proofs/U64/WideningMul.lean` |
| `u64::wrapping_add` | `u64_wrapping_add_correct` | `u64::wrapping_add` computes `(a + b) mod 2^64`. | `MidenLean/Proofs/U64/WrappingAdd.lean` |
| `u64::wrapping_mul` | `u64_wrapping_mul_correct` | `u64::wrapping_mul` computes the low 64 bits of the product `a * b`. | `MidenLean/Proofs/U64/WrappingMul.lean` |
| `u64::wrapping_sub` | `u64_wrapping_sub_correct` | `u64::wrapping_sub` computes `a - b` as a u64 value. | `MidenLean/Proofs/U64/WrappingSub.lean` |
| `u64::xor` | `u64_xor_correct` | `u64::xor` computes bitwise XOR of two u64 values. | `MidenLean/Proofs/U64/Xor.lean` |

### `u128` (36 / 36)

| Procedure | Theorem | Summary | Manual proof file |
| --- | --- | --- | --- |
| `u128::and` | `u128_and_correct` | `u128::and` computes bitwise AND of two 128-bit values. | `MidenLean/Proofs/U128/And.lean` |
| `u128::clo` | `u128_clo_correct` | `u128::clo` pushes the count of leading ones of a 128-bit value. | `MidenLean/Proofs/U128/Clo.lean` |
| `u128::clz` | `u128_clz_correct` | `u128::clz` pushes the count of leading zeros of a 128-bit value. | `MidenLean/Proofs/U128/Clz.lean` |
| `u128::cto` | `u128_cto_correct` | `u128::cto` pushes the count of trailing ones of a 128-bit value. | `MidenLean/Proofs/U128/Cto.lean` |
| `u128::ctz` | `u128_ctz_correct` | `u128::ctz` pushes the count of trailing zeros of a 128-bit value. | `MidenLean/Proofs/U128/Ctz.lean` |
| `u128::div` | `u128_div_correct` | `u128::div` verifies an advice-supplied quotient and remainder for u128 division, then drops the remainder word and returns the quotient limbs. Execution succeeds iff the advice-supplied q and r satisfy q * b + r = a and r < b. | `MidenLean/Proofs/U128/Div.lean` |
| `u128::divmod` | `u128_divmod_correct` | `u128::divmod` verifies the Euclidean division of two u128 values. Execution succeeds iff the advice-supplied quotient q and remainder r satisfy q * b + r = a and r < b. | `MidenLean/Proofs/U128/Divmod.lean` |
| `u128::eq` | `u128_eq_correct` | `u128::eq` tests equality of two 128-bit values. | `MidenLean/Proofs/U128/Eq.lean` |
| `u128::eqz` | `u128_eqz_correct` | `u128::eqz` tests whether a 128-bit value is zero. | `MidenLean/Proofs/U128/Eqz.lean` |
| `u128::gt` | `u128_gt_correct` | `u128::gt` pushes 1 iff `b < a` (i.e. `a > b`). | `MidenLean/Proofs/U128/Gt.lean` |
| `u128::gte` | `u128_gte_correct` | `u128::gte` pushes 1 iff `b ≤ a` (i.e. `a ≥ b`). | `MidenLean/Proofs/U128/Gte.lean` |
| `u128::lt` | `u128_lt_correct` | `u128::lt` pushes 1 iff `a < b`. | `MidenLean/Proofs/U128/Lt.lean` |
| `u128::lte` | `u128_lte_correct` | `u128::lte` pushes 1 iff `a ≤ b`. | `MidenLean/Proofs/U128/Lte.lean` |
| `u128::max` | `u128_max_correct` | `u128::max` pushes the limbs of `max(a, b)`. | `MidenLean/Proofs/U128/Max.lean` |
| `u128::min` | `u128_min_correct` | `u128::min` pushes the limbs of `min(a, b)`. | `MidenLean/Proofs/U128/Min.lean` |
| `u128::mod` | `u128_mod_correct` | `u128::mod` verifies an advice-supplied quotient and remainder for u128 division, then keeps only the remainder limbs. Execution succeeds iff the advice-supplied q and r satisfy q * b + r = a and r < b. | `MidenLean/Proofs/U128/Mod.lean` |
| `u128::neq` | `u128_neq_correct` | `u128::neq` tests inequality of two 128-bit values. | `MidenLean/Proofs/U128/Neq.lean` |
| `u128::not` | `u128_not_correct` | `u128::not` pushes the limbs of `~~~a` (bitwise complement). | `MidenLean/Proofs/U128/Not.lean` |
| `u128::or` | `u128_or_correct` | `u128::or` computes bitwise OR of two 128-bit values. | `MidenLean/Proofs/U128/Or.lean` |
| `u128::overflowing_add` | `u128_overflowing_add_correct` | `u128::overflowing_add` computes `a + b` with overflow detection. | `MidenLean/Proofs/U128/OverflowingAdd.lean` |
| `u128::overflowing_mul` | `u128_overflowing_mul_correct` | `u128::overflowing_mul` computes the low 128 bits of the product `a * b` and an overflow flag. | `MidenLean/Proofs/U128/OverflowingMul.lean` |
| `u128::overflowing_sub` | `u128_overflowing_sub_correct` | `u128::overflowing_sub` computes `a - b` with underflow detection. | `MidenLean/Proofs/U128/OverflowingSub.lean` |
| `u128::rotl` | `u128_rotl_correct` | `u128::rotl` left-rotates a u128 value by `shift` bits. | `MidenLean/Proofs/U128/Rotl.lean` |
| `u128::rotr` | `u128_rotr_correct` | `u128::rotr` right-rotates a u128 value by `shift` bits. | `MidenLean/Proofs/U128/Rotr.lean` |
| `u128::shl` | `u128_shl_correct` | `u128::shl` left-shifts a u128 value by `shift` bits (mod 2^128). | `MidenLean/Proofs/U128/Shl.lean` |
| `u128::shr` | `u128_shr_correct` | `u128::shr` right-shifts a u128 value by `shift` bits. | `MidenLean/Proofs/U128/Shr.lean` |
| `u128::shr_k0` | `u128_shr_k0_correct` | `u128::shr_k0` right-shifts a u128 value by a nonzero amount smaller than 32 bits. | `MidenLean/Proofs/U128/ShrK0.lean` |
| `u128::shr_k1` | `u128_shr_k1_correct` | `u128::shr_k1` returns the low three limbs of a u128 value shifted right by `32 + shift` bits. | `MidenLean/Proofs/U128/ShrK1.lean` |
| `u128::shr_k2` | `u128_shr_k2_correct` | `u128::shr_k2` returns the low two limbs of a u128 value shifted right by `64 + shift` bits. | `MidenLean/Proofs/U128/ShrK2.lean` |
| `u128::shr_k3` | `u128_shr_k3_correct` | `u128::shr_k3` returns the low limb of a u128 value shifted right by `96 + shift` bits. | `MidenLean/Proofs/U128/ShrK3.lean` |
| `u128::widening_add` | `u128_widening_add_correct` | `u128::widening_add` computes `a + b` with carry-out moved to the end. | `MidenLean/Proofs/U128/WideningAdd.lean` |
| `u128::widening_mul` | `u128_widening_mul_correct` | `u128::widening_mul` computes `(a * b) mod 2^128` and an overflow flag. | `MidenLean/Proofs/U128/WideningMul.lean` |
| `u128::wrapping_add` | `u128_wrapping_add_correct` | `u128::wrapping_add` computes `(a + b) mod 2^128` for two 128-bit values. | `MidenLean/Proofs/U128/WrappingAdd.lean` |
| `u128::wrapping_mul` | `u128_wrapping_mul_correct` | `u128::wrapping_mul` computes `(a * b) mod 2^128` for two 128-bit values. | `MidenLean/Proofs/U128/WrappingMul.lean` |
| `u128::wrapping_sub` | `u128_wrapping_sub_correct` | `u128::wrapping_sub` computes `(a - b) mod 2^128` for two 128-bit values. | `MidenLean/Proofs/U128/WrappingSub.lean` |
| `u128::xor` | `u128_xor_correct` | `u128::xor` computes bitwise XOR of two 128-bit values. | `MidenLean/Proofs/U128/Xor.lean` |

### `u256` (5 / 17)

| Procedure | Theorem | Summary | Manual proof file |
| --- | --- | --- | --- |
| `u256::and` | `u256_and_correct` | `u256::and` computes bitwise AND of two 256-bit values. | `MidenLean/Proofs/U256/And.lean` |
| `u256::eqz` | `u256_eqz_correct` | `u256::eqz` tests whether a u256 value equals zero. | `MidenLean/Proofs/U256/Eqz.lean` |
| `u256::or` | `u256_or_correct` | `u256::or` computes bitwise OR of two 256-bit values. | `MidenLean/Proofs/U256/Or.lean` |
| `u256::u256_le_to_be` | `u256_u256_le_to_be_correct` | `u256::u256_le_to_be` reverses the order of eight stack elements. | `MidenLean/Proofs/U256/U256LeToBe.lean` |
| `u256::xor` | `u256_xor_correct` | `u256::xor` computes bitwise XOR of two 256-bit values. | `MidenLean/Proofs/U256/Xor.lean` |

### `word` (11 / 11)

| Procedure | Theorem | Summary | Manual proof file |
| --- | --- | --- | --- |
| `word::arrange_words_adjacent_le` | `word_arrange_words_adjacent_le_correct` | `word::arrange_words_adjacent_le` interleaves two words for comparison. | `MidenLean/Proofs/Word/Arrange.lean` |
| `word::eq` | `word_eq_correct` | `word::eq` tests equality of two words. | `MidenLean/Proofs/Word/Eq.lean` |
| `word::eqz` | `word_eqz_correct` | `word::eqz` tests whether a word is zero. | `MidenLean/Proofs/Word/Eqz.lean` |
| `word::gt` | `word_gt_correct` | `word::gt` compares two words lexicographically. | `MidenLean/Proofs/Word/Gt.lean` |
| `word::gte` | `word_gte_correct` | `word::gte` checks whether one word is greater than or equal to another. | `MidenLean/Proofs/Word/Gte.lean` |
| `word::lt` | `word_lt_correct` | `word::lt` compares two words lexicographically. | `MidenLean/Proofs/Word/Lt.lean` |
| `word::lte` | `word_lte_correct` | `word::lte` checks whether one word is less than or equal to another. | `MidenLean/Proofs/Word/Lte.lean` |
| `word::reverse` | `word_reverse_correct` | `word::reverse` reverses the first four stack elements. | `MidenLean/Proofs/Word/Reverse.lean` |
| `word::store_word_u32s_le` | `word_store_word_u32s_le_correct` | `word::store_word_u32s_le` writes a word to memory as eight u32 limbs in little-endian order. | `MidenLean/Proofs/Word/StoreWordU32sLe.lean` |
| `word::test_eq` | `word_test_eq_correct` | `word::test_eq` tests equality of two words without consuming inputs. | `MidenLean/Proofs/Word/TestEq.lean` |
| `word::testz` | `word_testz_correct` | `word::testz` tests whether a word is zero without consuming the input. | `MidenLean/Proofs/Word/Testz.lean` |
Generated proof scaffolding is emitted separately under `MidenLean/Proofs/Generated/<Module>/`.

## Verifying

Requires [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) (v4.28.0) and [elan](https://github.com/leanprover/elan).

```bash
# Verify a single manual proof module.
timeout 180s lake build MidenLean.Proofs.U64.WideningMul
timeout 180s lake build MidenLean.Proofs.U64.Divmod
timeout 180s lake build MidenLean.Proofs.U128.Eqz
timeout 180s lake build MidenLean.Proofs.U256.Eqz
timeout 180s lake build MidenLean.Proofs.Word.Reverse

# Check a single Lean file directly.
timeout 180s lake env lean MidenLean/Proofs/U64/Shr.lean

# Sweep all manual correctness proofs component-wise.
mods=(
  MidenLean.Proofs.U64.Common
  MidenLean.Proofs.U128.Common
  MidenLean.Proofs.U256.Common
  $(find MidenLean/Proofs/U64 -maxdepth 1 -name '*.lean' ! -name 'Common.lean' | sort | sed 's#/#.#g; s#.lean$##')
  $(find MidenLean/Proofs/U128 -maxdepth 1 -name '*.lean' ! -name 'Common.lean' | sort | sed 's#/#.#g; s#.lean$##')
  $(find MidenLean/Proofs/U256 -maxdepth 1 -name '*.lean' ! -name 'Common.lean' | sort | sed 's#/#.#g; s#.lean$##')
  $(find MidenLean/Proofs/Word -maxdepth 1 -name '*.lean' | sort | sed 's#/#.#g; s#.lean$##')
)
for mod in $mods; do
  timeout 180s lake build "$mod"
done
```
