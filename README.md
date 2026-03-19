# MASM-to-Lean

Formal verification of the [Miden Assembly](https://github.com/0xMiden/miden-vm) (MASM) core library in Lean 4. MASM programs from the Miden core library are translated into Lean using a shallow embedding, and their correctness is proved against an executable semantics of the Miden VM.

## Components

- **`MidenLean/`** — Lean 4 model of the Miden VM.
- **`MidenLean/Generated/`** — MASM procedures translated to `List Op` definitions.
- **`MidenLean/Proofs/`** — Manual correctness proofs for individual procedures.
- **`MidenLean/Proofs/Generated/`** — Auto-generated proof scaffolding, split per procedure.
- **`masm-to-lean/`** — Rust tool that parses `.masm` files and emits Lean definitions.

## Correctness Proofs

Manual proof files are organized per procedure:

- **`MidenLean/Proofs/U64/`** contains the `u64` correctness theorems, one file per procedure.
- **`MidenLean/Proofs/U64/Common.lean`** contains shared proof support for the `u64` proof tree.
- **`MidenLean/Proofs/Word/`** contains the `word` correctness theorems, one file per procedure.

The current checked manual proofs cover 39 procedures: 28 in `u64`, 11 in `word`.

### `u64`

| Procedure | Theorem | Summary | Manual proof file |
| --- | --- | --- | --- |
| `u64::and` | `u64_and_correct` | u64.and correctly computes bitwise AND of two u64 values. | `MidenLean/Proofs/U64/And.lean` |
| `u64::clo` | `u64_clo_correct` | u64.clo correctly counts leading ones of a u64 value. | `MidenLean/Proofs/U64/Clo.lean` |
| `u64::clz` | `u64_clz_correct` | u64.clz correctly counts leading zeros of a u64 value. | `MidenLean/Proofs/U64/Clz.lean` |
| `u64::cto` | `u64_cto_correct` | u64.cto correctly counts trailing ones of a u64 value. | `MidenLean/Proofs/U64/Cto.lean` |
| `u64::ctz` | `u64_ctz_correct` | u64.ctz correctly counts trailing zeros of a u64 value. | `MidenLean/Proofs/U64/Ctz.lean` |
| `u64::div` | `u64_div_correct` | u64.div computes the quotient of two u64 values by calling divmod and dropping the remainder. | `MidenLean/Proofs/U64/Div.lean` |
| `u64::divmod` | `u64_divmod_correct` | u64.divmod checks the advised quotient and remainder for a 64-bit division. | `MidenLean/Proofs/U64/Divmod.lean` |
| `u64::eq` | `u64_eq_correct` | u64.eq correctly tests equality of two u64 values. | `MidenLean/Proofs/U64/Eq.lean` |
| `u64::gt` | `u64_gt_correct` | u64.gt correctly compares two u64 values. | `MidenLean/Proofs/U64/Gt.lean` |
| `u64::gte` | `u64_gte_correct` | u64.gte correctly compares two u64 values. | `MidenLean/Proofs/U64/Gte.lean` |
| `u64::lt` | `u64_lt_correct` | u64.lt correctly compares two u64 values. | `MidenLean/Proofs/U64/Lt.lean` |
| `u64::lte` | `u64_lte_correct` | u64.lte correctly compares two u64 values. | `MidenLean/Proofs/U64/Lte.lean` |
| `u64::max` | `u64_max_correct` | u64.max correctly computes the maximum of two u64 values. | `MidenLean/Proofs/U64/Max.lean` |
| `u64::min` | `u64_min_correct` | u64.min correctly computes the minimum of two u64 values. | `MidenLean/Proofs/U64/Min.lean` |
| `u64::mod` | `u64_mod_correct` | u64.mod computes the remainder of two u64 values by calling divmod, then rearranging the stack to keep only the remainder. | `MidenLean/Proofs/U64/Mod.lean` |
| `u64::neq` | `u64_neq_correct` | u64.neq correctly tests inequality of two u64 values. | `MidenLean/Proofs/U64/Neq.lean` |
| `u64::or` | `u64_or_correct` | u64.or correctly computes bitwise OR of two u64 values. | `MidenLean/Proofs/U64/Or.lean` |
| `u64::overflowing_sub` | `u64_overflowing_sub_correct` | u64.overflowing_sub correctly computes subtraction of two u64 values with borrow. | `MidenLean/Proofs/U64/OverflowingSub.lean` |
| `u64::rotl` | `u64_rotl_correct` | u64.rotl correctly left-rotates a u64 value. | `MidenLean/Proofs/U64/Rotl.lean` |
| `u64::rotr` | `u64_rotr_correct` | u64.rotr correctly right-rotates a u64 value. | `MidenLean/Proofs/U64/Rotr.lean` |
| `u64::shl` | `u64_shl_correct` | u64.shl correctly left-shifts a u64 value. | `MidenLean/Proofs/U64/Shl.lean` |
| `u64::shr` | `u64_shr_correct` | u64.shr correctly right-shifts a u64 value. | `MidenLean/Proofs/U64/Shr.lean` |
| `u64::u32assert4` | `u64_u32assert4_correct` | u64.u32assert4 validates that four stack elements are u32 values. | `MidenLean/Proofs/U64/U32Assert4.lean` |
| `u64::widening_add` | `u64_widening_add_correct` | u64.widening_add correctly computes widening addition of two u64 values. | `MidenLean/Proofs/U64/WideningAdd.lean` |
| `u64::widening_mul` | `u64_widening_mul_correct` | u64.widening_mul correctly computes the full 128-bit product of two u64 values. | `MidenLean/Proofs/U64/WideningMul.lean` |
| `u64::wrapping_mul` | `u64_wrapping_mul_correct` | u64.wrapping_mul correctly computes the low 64 bits of the product of two u64 values. | `MidenLean/Proofs/U64/WrappingMul.lean` |
| `u64::wrapping_sub` | `u64_wrapping_sub_correct` | u64.wrapping_sub correctly computes wrapping subtraction of two u64 values. | `MidenLean/Proofs/U64/Sub.lean` |
| `u64::xor` | `u64_xor_correct` | u64.xor correctly computes bitwise XOR of two u64 values. | `MidenLean/Proofs/U64/Xor.lean` |

### `word`

| Procedure | Theorem | Summary | Manual proof file |
| --- | --- | --- | --- |
| `word::arrange_words_adjacent_le` | `word_arrange_words_adjacent_le_correct` | word.arrange_words_adjacent_le correctly interleaves two words for comparison. | `MidenLean/Proofs/Word/Arrange.lean` |
| `word::eq` | `word_eq_correct` | word.eq correctly tests equality of two words. | `MidenLean/Proofs/Word/Eq.lean` |
| `word::eqz` | `word_eqz_correct` | word.eqz correctly tests whether a word is zero. | `MidenLean/Proofs/Word/Eqz.lean` |
| `word::gt` | `word_gt_correct` | word.gt correctly compares two words lexicographically. | `MidenLean/Proofs/Word/Gt.lean` |
| `word::gte` | `word_gte_correct` | word.gte correctly checks whether one word is greater than or equal to another. | `MidenLean/Proofs/Word/Gte.lean` |
| `word::lt` | `word_lt_correct` | word.lt correctly compares two words lexicographically. | `MidenLean/Proofs/Word/Lt.lean` |
| `word::lte` | `word_lte_correct` | word.lte correctly checks whether one word is less than or equal to another. | `MidenLean/Proofs/Word/Lte.lean` |
| `word::reverse` | `word_reverse_correct` | word.reverse correctly reverses the first four stack elements. | `MidenLean/Proofs/Word/Reverse.lean` |
| `word::store_word_u32s_le` | `word_store_word_u32s_le_correct` | word.store_word_u32s_le correctly writes a word to memory as eight u32 limbs in little-endian order. | `MidenLean/Proofs/Word/StoreWordU32sLe.lean` |
| `word::test_eq` | `word_test_eq_correct` | word.test_eq correctly tests equality of two words without consuming inputs. | `MidenLean/Proofs/Word/TestEq.lean` |
| `word::testz` | `word_testz_correct` | word.testz correctly tests whether a word is zero without consuming the input. | `MidenLean/Proofs/Word/Testz.lean` |

Generated proof scaffolding is emitted separately under `MidenLean/Proofs/Generated/<Module>/`.
These files are not edited directly; copy the relevant scaffold into the corresponding manual proof file under `MidenLean/Proofs/` and complete the proof there.

## Verifying

Requires [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) (v4.28.0) and [elan](https://github.com/leanprover/elan).

```bash
# Verify a single manual proof module.
timeout 180s lake build MidenLean.Proofs.U64.WideningMul
timeout 180s lake build MidenLean.Proofs.U64.Divmod
timeout 180s lake build MidenLean.Proofs.Word.Reverse

# Check a single Lean file directly.
timeout 180s lake env lean MidenLean/Proofs/U64/Shr.lean

# Sweep all manual correctness proofs componentwise.
mods=(
  MidenLean.Proofs.U64.Common
  $(find MidenLean/Proofs/U64 -maxdepth 1 -name '*.lean' ! -name 'Common.lean' | sort | sed 's#/#.#g; s#.lean$##')
  $(find MidenLean/Proofs/Word -maxdepth 1 -name '*.lean' | sort | sed 's#/#.#g; s#.lean$##')
)
for mod in $mods; do
  timeout 180s lake build "$mod"
done
```

Use strict timeouts when checking proofs. Some larger proof files can otherwise appear to stall during elaboration.
