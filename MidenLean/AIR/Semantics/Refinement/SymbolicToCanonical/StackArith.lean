import MidenLean.AIR.Semantics.Tactics
/-!
# Symbolic-to-Implementation StackArith Refinement

This file carries the symbolic-to-canonical bridge for the current bounded
slice: `ADD`, `NEG`, `MUL`, `INV`, `INCR`, `NOT`, `AND`, `OR`, `EQ`, `EQZ`,
`EXPACC`, `EXT2MUL`, and grouped `u32` constraints for `U32SPLIT`,
`U32ASSERT2`, `U32ADD`, `U32ADD3`, and `U32SUB`. Each theorem shows that the extracted symbolic
constraint and the
builder-based implementation constraint evaluate to the same base-field expression
on matching rows.

Like the subsystem file it targets, this bridge is only for the op-specific
arithmetic bodies. Shared stack-motion constraints are part of `StackGeneral`.
If the intended spec is stronger than the current Rust AIR, that mismatch
should be modeled as a separate spec/implementation gap, not erased here.
-/

namespace MidenLean.AIR.Semantics.Refinement.SymbolicToCanonical

open MidenLean
open MidenLean.AIR
open MidenLean.AIR.Semantics
open MidenLean.AIR.Semantics.Tactics

/-- Step 8 bridge: the extracted symbolic `ADD` entry and the canonical
`StackArith.add` constraint evaluate to the same field element on matching
rows. -/
theorem extracted_add_eval_eq_canonical_add_eval (r : AirRow) :
    MidenLean.AIR.Constraints.Symbolic.StackArith.add (toSymbolicFrame r) =
      Semantics.Subsystems.StackArith.add.eval r := by
  air_bridge_unfold air_simp_symbolic_add, air_simp_canonical_add
  air_bridge_finish

/-- Step 9 first-slice bridge for `NEG`. -/
theorem extracted_neg_eval_eq_canonical_neg_eval (r : AirRow) :
    MidenLean.AIR.Constraints.Symbolic.StackArith.neg (toSymbolicFrame r) =
      Semantics.Subsystems.StackArith.neg.eval r := by
  air_bridge_unfold air_simp_symbolic_neg, air_simp_canonical_neg
  air_bridge_finish

/-- Step 9 first-slice bridge for `MUL`. -/
theorem extracted_mul_eval_eq_canonical_mul_eval (r : AirRow) :
    MidenLean.AIR.Constraints.Symbolic.StackArith.mul (toSymbolicFrame r) =
      Semantics.Subsystems.StackArith.mul.eval r := by
  air_bridge_unfold air_simp_symbolic_mul, air_simp_canonical_mul
  air_bridge_finish

/-- Step 9 second-slice bridge for `INV`. -/
theorem extracted_inv_eval_eq_canonical_inv_eval (r : AirRow) :
    MidenLean.AIR.Constraints.Symbolic.StackArith.inv (toSymbolicFrame r) =
      Semantics.Subsystems.StackArith.inv.eval r := by
  air_bridge_unfold air_simp_symbolic_inv, air_simp_canonical_inv
  air_bridge_finish

/-- Step 9 second-slice bridge for `INCR`. -/
theorem extracted_incr_eval_eq_canonical_incr_eval (r : AirRow) :
    MidenLean.AIR.Constraints.Symbolic.StackArith.incr (toSymbolicFrame r) =
      Semantics.Subsystems.StackArith.incr.eval r := by
  air_bridge_unfold air_simp_symbolic_incr, air_simp_canonical_incr
  air_simp_stackarith_named_cols
  air_norm_sub_sub

/-- Step 9 third-slice bridge for `NOT` binaryity (`base[5]`). -/
theorem extracted_not_binary_eval_eq_canonical_not_binary_eval (r : AirRow) :
    MidenLean.AIR.Constraints.Symbolic.StackArith.notBinary (toSymbolicFrame r) =
      Semantics.Subsystems.StackArith.notBinary.eval r := by
  air_bridge_unfold air_simp_symbolic_not_binary, air_simp_canonical_not_binary
  air_bridge_finish

/-- Step 9 third-slice bridge for `NOT` value relation (`base[6]`). -/
theorem extracted_not_value_eval_eq_canonical_not_value_eval (r : AirRow) :
    MidenLean.AIR.Constraints.Symbolic.StackArith.notValue (toSymbolicFrame r) =
      Semantics.Subsystems.StackArith.notValue.eval r := by
  air_bridge_unfold air_simp_symbolic_not_value, air_simp_canonical_not_value
  air_bridge_finish

/-- Step 9 third-slice bridge for `AND` s0-binaryity (`base[7]`). -/
theorem extracted_and_s0_binary_eval_eq_canonical_and_s0_binary_eval (r : AirRow) :
    MidenLean.AIR.Constraints.Symbolic.StackArith.andS0Binary (toSymbolicFrame r) =
      Semantics.Subsystems.StackArith.andS0Binary.eval r := by
  air_bridge_unfold air_simp_symbolic_and_s0_binary, air_simp_canonical_and_s0_binary
  air_bridge_finish

/-- Step 9 third-slice bridge for `AND` s1-binaryity (`base[8]`). -/
theorem extracted_and_s1_binary_eval_eq_canonical_and_s1_binary_eval (r : AirRow) :
    MidenLean.AIR.Constraints.Symbolic.StackArith.andS1Binary (toSymbolicFrame r) =
      Semantics.Subsystems.StackArith.andS1Binary.eval r := by
  air_bridge_unfold air_simp_symbolic_and_s1_binary, air_simp_canonical_and_s1_binary
  air_bridge_finish

/-- Step 9 third-slice bridge for `AND` value relation (`base[9]`). -/
theorem extracted_and_value_eval_eq_canonical_and_value_eval (r : AirRow) :
    MidenLean.AIR.Constraints.Symbolic.StackArith.andValue (toSymbolicFrame r) =
      Semantics.Subsystems.StackArith.andValue.eval r := by
  air_bridge_unfold air_simp_symbolic_and_value, air_simp_canonical_and_value
  air_bridge_finish

/-- Step 9 third-slice bridge for `OR` s0-binaryity (`base[10]`). -/
theorem extracted_or_s0_binary_eval_eq_canonical_or_s0_binary_eval (r : AirRow) :
    MidenLean.AIR.Constraints.Symbolic.StackArith.orS0Binary (toSymbolicFrame r) =
      Semantics.Subsystems.StackArith.orS0Binary.eval r := by
  air_bridge_unfold air_simp_symbolic_or_s0_binary, air_simp_canonical_or_s0_binary
  air_bridge_finish

/-- Step 9 third-slice bridge for `OR` s1-binaryity (`base[11]`). -/
theorem extracted_or_s1_binary_eval_eq_canonical_or_s1_binary_eval (r : AirRow) :
    MidenLean.AIR.Constraints.Symbolic.StackArith.orS1Binary (toSymbolicFrame r) =
      Semantics.Subsystems.StackArith.orS1Binary.eval r := by
  air_bridge_unfold air_simp_symbolic_or_s1_binary, air_simp_canonical_or_s1_binary
  air_bridge_finish

/-- Step 9 third-slice bridge for `OR` value relation (`base[12]`). -/
theorem extracted_or_value_eval_eq_canonical_or_value_eval (r : AirRow) :
    MidenLean.AIR.Constraints.Symbolic.StackArith.orValue (toSymbolicFrame r) =
      Semantics.Subsystems.StackArith.orValue.eval r := by
  air_bridge_unfold air_simp_symbolic_or_value, air_simp_canonical_or_value
  air_bridge_finish

/-- Step 9 fourth-slice bridge for `EQ` zero-product relation (`base[13]`). -/
theorem extracted_eq_zero_product_eval_eq_canonical_eq_zero_product_eval (r : AirRow) :
    MidenLean.AIR.Constraints.Symbolic.StackArith.eqZeroProduct (toSymbolicFrame r) =
      Semantics.Subsystems.StackArith.eqZeroProduct.eval r := by
  air_bridge_unfold air_simp_symbolic_eq_zero_product, air_simp_canonical_eq_zero_product
  air_bridge_finish

/-- Step 9 fourth-slice bridge for `EQ` value relation (`base[14]`). -/
theorem extracted_eq_value_eval_eq_canonical_eq_value_eval (r : AirRow) :
    MidenLean.AIR.Constraints.Symbolic.StackArith.eqValue (toSymbolicFrame r) =
      Semantics.Subsystems.StackArith.eqValue.eval r := by
  air_bridge_unfold air_simp_symbolic_eq_value, air_simp_canonical_eq_value
  air_simp_stackarith_named_cols
  air_norm_sub_sub

/-- Step 9 fourth-slice bridge for `EQZ` zero-product relation (`base[15]`). -/
theorem extracted_eqz_zero_product_eval_eq_canonical_eqz_zero_product_eval (r : AirRow) :
    MidenLean.AIR.Constraints.Symbolic.StackArith.eqzZeroProduct (toSymbolicFrame r) =
      Semantics.Subsystems.StackArith.eqzZeroProduct.eval r := by
  air_bridge_unfold air_simp_symbolic_eqz_zero_product, air_simp_canonical_eqz_zero_product
  air_bridge_finish

/-- Step 9 fourth-slice bridge for `EQZ` value relation (`base[16]`). -/
theorem extracted_eqz_value_eval_eq_canonical_eqz_value_eval (r : AirRow) :
    MidenLean.AIR.Constraints.Symbolic.StackArith.eqzValue (toSymbolicFrame r) =
      Semantics.Subsystems.StackArith.eqzValue.eval r := by
  air_bridge_unfold air_simp_symbolic_eqz_value, air_simp_canonical_eqz_value
  air_simp_stackarith_named_cols
  air_norm_sub_sub

/-- Step 9 fifth-slice bridge for `EXPACC` exp-square relation (`base[17]`). -/
theorem extracted_expacc_exp_square_eval_eq_canonical_expacc_exp_square_eval (r : AirRow) :
    MidenLean.AIR.Constraints.Symbolic.StackArith.expaccExpSquare (toSymbolicFrame r) =
      Semantics.Subsystems.StackArith.expaccExpSquare.eval r := by
  air_bridge_unfold air_simp_symbolic_expacc_exp_square, air_simp_canonical_expacc_exp_square
  air_simp_stackarith_named_cols
  air_bridge_finish_gated

/-- Step 9 fifth-slice bridge for `EXPACC` helper relation (`base[18]`). -/
theorem extracted_expacc_exp_val_eval_eq_canonical_expacc_exp_val_eval (r : AirRow) :
    MidenLean.AIR.Constraints.Symbolic.StackArith.expaccExpVal (toSymbolicFrame r) =
      Semantics.Subsystems.StackArith.expaccExpVal.eval r := by
  air_bridge_unfold air_simp_symbolic_expacc_exp_val, air_simp_canonical_expacc_exp_val
  air_simp_stackarith_named_cols
  air_bridge_finish_gated

/-- Step 9 fifth-slice bridge for `EXPACC` accumulator update (`base[19]`). -/
theorem extracted_expacc_acc_update_eval_eq_canonical_expacc_acc_update_eval (r : AirRow) :
    MidenLean.AIR.Constraints.Symbolic.StackArith.expaccAccUpdate (toSymbolicFrame r) =
      Semantics.Subsystems.StackArith.expaccAccUpdate.eval r := by
  air_bridge_unfold air_simp_symbolic_expacc_acc_update, air_simp_canonical_expacc_acc_update
  air_simp_stackarith_named_cols
  air_bridge_finish_gated

/-- Step 9 fifth-slice bridge for `EXPACC` exponent-shift relation (`base[20]`). -/
theorem extracted_expacc_exp_shift_eval_eq_canonical_expacc_exp_shift_eval (r : AirRow) :
    MidenLean.AIR.Constraints.Symbolic.StackArith.expaccExpShift (toSymbolicFrame r) =
      Semantics.Subsystems.StackArith.expaccExpShift.eval r := by
  air_bridge_unfold air_simp_symbolic_expacc_exp_shift, air_simp_canonical_expacc_exp_shift
  air_simp_stackarith_named_cols
  air_norm_sub_sub

/-- Step 9 fifth-slice bridge for `EXPACC` bit-binaryity relation (`base[21]`). -/
theorem extracted_expacc_bit_binary_eval_eq_canonical_expacc_bit_binary_eval (r : AirRow) :
    MidenLean.AIR.Constraints.Symbolic.StackArith.expaccBitBinary (toSymbolicFrame r) =
      Semantics.Subsystems.StackArith.expaccBitBinary.eval r := by
  air_bridge_unfold air_simp_symbolic_expacc_bit_binary, air_simp_canonical_expacc_bit_binary
  air_simp_stackarith_named_cols
  air_bridge_finish_gated

/-- Step 9 sixth-slice bridge for `EXT2MUL` `d0` relation (`base[22]`). -/
theorem extracted_ext2mul_d0_eval_eq_canonical_ext2mul_d0_eval (r : AirRow) :
    MidenLean.AIR.Constraints.Symbolic.StackArith.ext2mulD0 (toSymbolicFrame r) =
      Semantics.Subsystems.StackArith.ext2mulD0Unchanged.eval r := by
  air_bridge_unfold air_simp_symbolic_ext2mul_d0, air_simp_canonical_ext2mul_d0
  air_simp_stackarith_named_cols
  air_bridge_finish_gated

/-- Step 9 sixth-slice bridge for `EXT2MUL` `d1` relation (`base[23]`). -/
theorem extracted_ext2mul_d1_eval_eq_canonical_ext2mul_d1_eval (r : AirRow) :
    MidenLean.AIR.Constraints.Symbolic.StackArith.ext2mulD1 (toSymbolicFrame r) =
      Semantics.Subsystems.StackArith.ext2mulD1Unchanged.eval r := by
  air_bridge_unfold air_simp_symbolic_ext2mul_d1, air_simp_canonical_ext2mul_d1
  air_simp_stackarith_named_cols
  air_bridge_finish_gated

/-- Step 9 sixth-slice bridge for `EXT2MUL` `c0` relation (`base[24]`). -/
theorem extracted_ext2mul_c0_eval_eq_canonical_ext2mul_c0_eval (r : AirRow) :
    MidenLean.AIR.Constraints.Symbolic.StackArith.ext2mulC0 (toSymbolicFrame r) =
      Semantics.Subsystems.StackArith.ext2mulC0.eval r := by
  air_bridge_unfold air_simp_symbolic_ext2mul_c0, air_simp_canonical_ext2mul_c0
  air_simp_stackarith_named_cols
  air_bridge_finish_gated

/-- Step 9 sixth-slice bridge for `EXT2MUL` `c1` relation (`base[25]`). -/
theorem extracted_ext2mul_c1_eval_eq_canonical_ext2mul_c1_eval (r : AirRow) :
    MidenLean.AIR.Constraints.Symbolic.StackArith.ext2mulC1 (toSymbolicFrame r) =
      Semantics.Subsystems.StackArith.ext2mulC1.eval r := by
  air_bridge_unfold air_simp_symbolic_ext2mul_c1, air_simp_canonical_ext2mul_c1
  air_simp_stackarith_named_cols
  air_bridge_finish_gated

/-- Step 9 sixth-slice bridge for `U32SUB` difference relation (`base[32]`). -/
theorem extracted_u32sub_diff_eval_eq_canonical_u32_sub_diff_eval (r : AirRow) :
    MidenLean.AIR.Constraints.Symbolic.StackArith.u32SubDiff (toSymbolicFrame r) =
      Semantics.Subsystems.StackArith.u32SubDiff.eval r := by
  air_bridge_unfold air_simp_symbolic_u32_sub_diff, air_simp_canonical_u32_sub_diff
  air_simp_stackarith_named_cols
  air_bridge_ring
  simp

/-- Step 9 sixth-slice bridge for `U32SUB` borrow binaryity (`base[33]`). -/
theorem extracted_u32sub_borrow_binary_eval_eq_canonical_u32_sub_borrow_binary_eval
    (r : AirRow) :
    MidenLean.AIR.Constraints.Symbolic.StackArith.u32SubBorrowBinary (toSymbolicFrame r) =
      Semantics.Subsystems.StackArith.u32SubBorrowBinary.eval r := by
  air_bridge_unfold air_simp_symbolic_u32_sub_borrow_binary,
    air_simp_canonical_u32_sub_borrow_binary
  air_simp_stackarith_named_cols
  air_bridge_finish_gated

/-- Step 9 sixth-slice bridge for `U32SUB` low output relation (`base[34]`). -/
theorem extracted_u32sub_low_eval_eq_canonical_u32_sub_low_eval (r : AirRow) :
    MidenLean.AIR.Constraints.Symbolic.StackArith.u32SubLow (toSymbolicFrame r) =
      Semantics.Subsystems.StackArith.u32SubLow.eval r := by
  air_bridge_unfold air_simp_symbolic_u32_sub_low, air_simp_canonical_u32_sub_low
  air_simp_stackarith_named_cols
  air_bridge_pick_selector_eq

/-- Step 9 seventh-slice bridge for grouped `u32` validity (`base[26]`). -/
theorem extracted_u32_split_mul_madd_validity_eval_eq_canonical_u32_split_mul_madd_validity_eval
    (r : AirRow) :
    MidenLean.AIR.Constraints.Symbolic.StackArith.u32SplitMulMaddValidity (toSymbolicFrame r) =
      Semantics.Subsystems.StackArith.u32SplitMulMaddValidity.eval r := by
  air_bridge_unfold air_simp_symbolic_u32_split_mul_madd_validity,
    air_simp_canonical_u32_split_mul_madd_validity
  air_simp_stackarith_named_cols
  air_bridge_pick_selector_eq

/-- Step 9 seventh-slice bridge for grouped `u32` low-output relation (`base[27]`). -/
theorem extracted_u32_two_outputs_lo_eval_eq_canonical_u32_two_outputs_lo_eval
    (r : AirRow) :
    MidenLean.AIR.Constraints.Symbolic.StackArith.u32TwoOutputsLo (toSymbolicFrame r) =
      Semantics.Subsystems.StackArith.u32TwoOutputsLo.eval r := by
  air_bridge_unfold air_simp_symbolic_u32_two_outputs_lo, air_simp_canonical_u32_two_outputs_lo
  air_simp_stackarith_named_cols
  air_bridge_pick_selector_eq

/-- Step 9 seventh-slice bridge for grouped `u32` high-output relation (`base[28]`). -/
theorem extracted_u32_two_outputs_hi_eval_eq_canonical_u32_two_outputs_hi_eval
    (r : AirRow) :
    MidenLean.AIR.Constraints.Symbolic.StackArith.u32TwoOutputsHi (toSymbolicFrame r) =
      Semantics.Subsystems.StackArith.u32TwoOutputsHi.eval r := by
  air_bridge_unfold air_simp_symbolic_u32_two_outputs_hi, air_simp_canonical_u32_two_outputs_hi
  air_simp_stackarith_named_cols
  air_bridge_pick_selector_eq

/-- Step 9 seventh-slice bridge for `U32SPLIT` input relation (`base[29]`). -/
theorem extracted_u32_split_input_eval_eq_canonical_u32_split_input_eval
    (r : AirRow) :
    MidenLean.AIR.Constraints.Symbolic.StackArith.u32SplitInput (toSymbolicFrame r) =
      Semantics.Subsystems.StackArith.u32SplitInput.eval r := by
  air_bridge_unfold air_simp_symbolic_u32_split_input, air_simp_canonical_u32_split_input
  air_simp_stackarith_named_cols
  air_bridge_pick_selector_eq

/-- Step 9 bounded-slice bridge for `U32ADD` input relation (`base[30]`). -/
theorem extracted_u32_add_input_eval_eq_canonical_u32_add_input_eval
    (r : AirRow) :
    MidenLean.AIR.Constraints.Symbolic.StackArith.u32AddInput (toSymbolicFrame r) =
      Semantics.Subsystems.StackArith.u32AddInput.eval r := by
  air_bridge_unfold air_simp_symbolic_u32_add_input, air_simp_canonical_u32_add_input
  air_simp_stackarith_named_cols
  air_bridge_pick_selector_eq

/-- Step 9 bounded-slice bridge for `U32ADD3` input relation (`base[31]`). -/
theorem extracted_u32_add3_input_eval_eq_canonical_u32_add3_input_eval
    (r : AirRow) :
    MidenLean.AIR.Constraints.Symbolic.StackArith.u32Add3Input (toSymbolicFrame r) =
      Semantics.Subsystems.StackArith.u32Add3Input.eval r := by
  air_bridge_unfold air_simp_symbolic_u32_add3_input, air_simp_canonical_u32_add3_input
  air_simp_stackarith_named_cols
  air_bridge_pick_selector_eq

/-- Step 9 bounded-slice bridge for `U32MUL` relation (`base[35]`). -/
theorem extracted_u32_mul_eval_eq_canonical_u32_mul_eval (r : AirRow) :
    MidenLean.AIR.Constraints.Symbolic.StackArith.u32Mul (toSymbolicFrame r) =
      Semantics.Subsystems.StackArith.u32Mul.eval r := by
  air_bridge_unfold air_simp_symbolic_u32_mul, air_simp_canonical_u32_mul
  air_simp_stackarith_named_cols
  air_bridge_pick_selector_eq

/-- Step 9 bounded-slice bridge for `U32MADD` relation (`base[36]`). -/
theorem extracted_u32_madd_eval_eq_canonical_u32_madd_eval (r : AirRow) :
    MidenLean.AIR.Constraints.Symbolic.StackArith.u32Madd (toSymbolicFrame r) =
      Semantics.Subsystems.StackArith.u32Madd.eval r := by
  air_bridge_unfold air_simp_symbolic_u32_madd, air_simp_canonical_u32_madd
  air_simp_stackarith_named_cols
  air_bridge_pick_selector_eq

/-- Step 9 bounded-slice bridge for `U32DIV` dividend relation (`base[37]`). -/
theorem extracted_u32_div_dividend_eval_eq_canonical_u32_div_dividend_eval (r : AirRow) :
    MidenLean.AIR.Constraints.Symbolic.StackArith.u32DivDividend (toSymbolicFrame r) =
      Semantics.Subsystems.StackArith.u32DivDividend.eval r := by
  air_bridge_unfold air_simp_symbolic_u32_div_dividend,
    air_simp_canonical_u32_div_dividend
  air_simp_stackarith_named_cols
  air_bridge_ring
  simp

/-- Step 9 bounded-slice bridge for `U32DIV` low-output relation (`base[38]`). -/
theorem extracted_u32_div_low_eval_eq_canonical_u32_div_low_eval (r : AirRow) :
    MidenLean.AIR.Constraints.Symbolic.StackArith.u32DivLow (toSymbolicFrame r) =
      Semantics.Subsystems.StackArith.u32DivLow.eval r := by
  air_bridge_unfold air_simp_symbolic_u32_div_low, air_simp_canonical_u32_div_low
  air_simp_stackarith_named_cols
  air_bridge_pick_selector_eq

/-- Step 9 bounded-slice bridge for `U32DIV` high-output relation (`base[39]`). -/
theorem extracted_u32_div_high_eval_eq_canonical_u32_div_high_eval (r : AirRow) :
    MidenLean.AIR.Constraints.Symbolic.StackArith.u32DivHigh (toSymbolicFrame r) =
      Semantics.Subsystems.StackArith.u32DivHigh.eval r := by
  air_bridge_unfold air_simp_symbolic_u32_div_high, air_simp_canonical_u32_div_high
  air_simp_stackarith_named_cols
  air_bridge_pick_selector_eq

/-- Step 9 bounded-slice bridge for `U32ASSERT2` high-output relation (`base[40]`). -/
theorem extracted_u32_assert2_hi_eval_eq_canonical_u32_assert2_hi_eval
    (r : AirRow) :
    MidenLean.AIR.Constraints.Symbolic.StackArith.u32Assert2Hi (toSymbolicFrame r) =
      Semantics.Subsystems.StackArith.u32Assert2Hi.eval r := by
  air_bridge_unfold air_simp_symbolic_u32_assert2_hi, air_simp_canonical_u32_assert2_hi
  air_simp_stackarith_named_cols
  air_bridge_pick_selector_eq

/-- Step 9 bounded-slice bridge for `U32ASSERT2` low-output relation (`base[41]`). -/
theorem extracted_u32_assert2_lo_eval_eq_canonical_u32_assert2_lo_eval
    (r : AirRow) :
    MidenLean.AIR.Constraints.Symbolic.StackArith.u32Assert2Lo (toSymbolicFrame r) =
      Semantics.Subsystems.StackArith.u32Assert2Lo.eval r := by
  air_bridge_unfold air_simp_symbolic_u32_assert2_lo, air_simp_canonical_u32_assert2_lo
  air_simp_stackarith_named_cols
  air_bridge_pick_selector_eq

end MidenLean.AIR.Semantics.Refinement.SymbolicToCanonical
