import MidenLean.Spec.WordOrder

namespace MidenLean

/--
Model of `processor.get_stack_word(start_idx)` / `stack_get_word_safe(start_idx)`.
Orientation is top-of-stack at `word[0]`, and missing elements are zero-padded.
-/
def processorSafeWordAccessor (stk : List Felt) (startIdx : Nat) : List Felt :=
  stackWord
    (stk.getD startIdx 0)
    (stk.getD (startIdx + 1) 0)
    (stk.getD (startIdx + 2) 0)
    (stk.getD (startIdx + 3) 0)

/-- Exact four-element read with no implicit padding. -/
def readWordExact? (stk : List Felt) (idx : Nat) : Option (List Felt) := do
  match stk.drop idx with
  | e0 :: e1 :: e2 :: e3 :: _ => pure (stackWord e0 e1 e2 e3)
  | _ => none

/--
Model of `StackOutputs::get_word(idx)`.
It is bounded (`idx <= 12`) and does not partially zero-pad short words.
-/
def stackOutputsWordAccessor (stk : List Felt) (idx : Nat) : Option (List Felt) :=
  if idx ≤ 12 then readWordExact? stk idx else none

theorem processorSafeWordAccessor_matches_top_word
    (e0 e1 e2 e3 : Felt) (tail : List Felt) :
    processorSafeWordAccessor (stackWord e0 e1 e2 e3 ++ tail) 0 = stackWord e0 e1 e2 e3 := by
  simp [processorSafeWordAccessor, stackWord]

theorem processorSafeWordAccessor_matches_offset_word
    (pre : List Felt) (e0 e1 e2 e3 : Felt) (tail : List Felt) :
    processorSafeWordAccessor (pre ++ stackWord e0 e1 e2 e3 ++ tail) pre.length =
      stackWord e0 e1 e2 e3 := by
  simp [processorSafeWordAccessor, stackWord]

theorem processorSafeWordAccessor_zero_pads_past_stack (e0 : Felt) :
    processorSafeWordAccessor [e0] 0 = stackWord e0 0 0 0 := by
  simp [processorSafeWordAccessor, stackWord]

theorem stackOutputsWordAccessor_some_at_valid_offset
    (pre : List Felt) (e0 e1 e2 e3 : Felt) (tail : List Felt) (hpre : pre.length ≤ 12) :
    stackOutputsWordAccessor (pre ++ stackWord e0 e1 e2 e3 ++ tail) pre.length =
      some (stackWord e0 e1 e2 e3) := by
  simp [stackOutputsWordAccessor, readWordExact?, stackWord, hpre]

theorem stackOutputsWordAccessor_none_past_boundary
    (stk : List Felt) (idx : Nat) (hidx : 12 < idx) :
    stackOutputsWordAccessor stk idx = none := by
  simp [stackOutputsWordAccessor, Nat.not_le.mpr hidx]

theorem stackOutputsWordAccessor_no_partial_padding (e0 : Felt) :
    stackOutputsWordAccessor [e0] 0 = none := by
  simp [stackOutputsWordAccessor, readWordExact?]

/-- Explicit orientation witness: concrete sample is returned in forward stack order. -/
theorem stackOutputsWordAccessor_forward_order_example :
    stackOutputsWordAccessor
      [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
      0 = some (stackWord 1 2 3 4) := by
  native_decide

end MidenLean
