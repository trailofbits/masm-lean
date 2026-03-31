import MidenLean.Spec.WordAccessors

namespace MidenLean.Proofs.Word

open MidenLean

/--
Processor accessor boundary:
`get_stack_word` / `stack_get_word_safe` expose top-of-stack at `word[0]`.
-/
theorem processor_get_stack_word_safe_top_matches_word0
    (e0 e1 e2 e3 : Felt) (tail : List Felt) :
    processorSafeWordAccessor (stackWord e0 e1 e2 e3 ++ tail) 0 = stackWord e0 e1 e2 e3 :=
  processorSafeWordAccessor_matches_top_word e0 e1 e2 e3 tail

/-- Processor accessor preserves forward order at non-zero offsets. -/
theorem processor_get_stack_word_safe_offset_matches_word0
    (pre : List Felt) (e0 e1 e2 e3 : Felt) (tail : List Felt) :
    processorSafeWordAccessor (pre ++ stackWord e0 e1 e2 e3 ++ tail) pre.length =
      stackWord e0 e1 e2 e3 :=
  processorSafeWordAccessor_matches_offset_word pre e0 e1 e2 e3 tail

/-- Processor accessor zero-pads when reading beyond the available stack tail. -/
theorem processor_get_stack_word_safe_zero_padding (e0 : Felt) :
    processorSafeWordAccessor [e0] 0 = stackWord e0 0 0 0 :=
  processorSafeWordAccessor_zero_pads_past_stack e0

/--
`StackOutputs::get_word` boundary:
returns exact words when in range and enough elements are available.
-/
theorem stack_outputs_get_word_exact_at_valid_offset
    (pre : List Felt) (e0 e1 e2 e3 : Felt) (tail : List Felt) (hpre : pre.length ≤ 12) :
    stackOutputsWordAccessor (pre ++ stackWord e0 e1 e2 e3 ++ tail) pre.length =
      some (stackWord e0 e1 e2 e3) :=
  stackOutputsWordAccessor_some_at_valid_offset pre e0 e1 e2 e3 tail hpre

/-- `StackOutputs::get_word` returns none once `idx` exceeds 12. -/
theorem stack_outputs_get_word_none_past_boundary
    (stk : List Felt) (idx : Nat) (hidx : 12 < idx) :
    stackOutputsWordAccessor stk idx = none :=
  stackOutputsWordAccessor_none_past_boundary stk idx hidx

/-- `StackOutputs::get_word` does not partially zero-pad short reads. -/
theorem stack_outputs_get_word_no_partial_padding (e0 : Felt) :
    stackOutputsWordAccessor [e0] 0 = none :=
  stackOutputsWordAccessor_no_partial_padding e0

/--
Concrete separation lemma: processor-safe accessor and stack-outputs accessor have
different behavior on short stacks.
-/
theorem accessor_boundaries_diverge_on_short_stack (e0 : Felt) :
    processorSafeWordAccessor [e0] 0 = stackWord e0 0 0 0
      ∧ stackOutputsWordAccessor [e0] 0 = none := by
  exact ⟨processorSafeWordAccessor_zero_pads_past_stack e0,
    stackOutputsWordAccessor_no_partial_padding e0⟩

/-- Explicit forward-order witness for `StackOutputs::get_word`. -/
theorem stack_outputs_get_word_forward_order_example :
    stackOutputsWordAccessor
      [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
      0 = some (stackWord 1 2 3 4) :=
  stackOutputsWordAccessor_forward_order_example

end MidenLean.Proofs.Word
