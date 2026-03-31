import MidenLean.Spec.DebugStackObserver

namespace MidenLean.Proofs.Observer

open MidenLean

/-- Observer projection preserves concrete top-prefix order. -/
theorem debug_stack_prefix_exact
    (a b c d : Felt) (tail : List Felt) :
    debugStackSlots (a :: b :: c :: d :: tail) 4 =
      [some a, some b, some c, some d] :=
  debugStackSlots_prefix4 a b c d tail

/-- Observer projection appends `EMPTY` slots when requested range exceeds stack size. -/
theorem debug_stack_adds_empty_slots
    (a b : Felt) :
    debugStackSlots [a, b] 4 = [some a, some b, none, none] :=
  debugStackSlots_pad_empty a b

/-- `debug.stack.0` is modeled as "show all current stack items". -/
theorem debug_stack_zero_is_all
    (stack : List Felt) :
    debugStackSlots stack 0 = stack.map some :=
  debugStackSlots_zero_means_all stack

/-- If the input stack already has a `reversew`-style rewrite, debug observer shows it as-is. -/
theorem debug_stack_reflects_reversew_rewrite :
    debugStackSlots [4, 3, 2, 1, 5, 6, 7, 8] 8 =
      [some (4 : Felt), some 3, some 2, some 1, some 5, some 6, some 7, some 8] :=
  debugStackSlots_reflects_reversew_style

/-- If the input stack already has a `reversedw`-style rewrite, debug observer shows it as-is. -/
theorem debug_stack_reflects_reversedw_rewrite :
    debugStackSlots [8, 7, 6, 5, 1, 2, 3, 4] 8 =
      [some (8 : Felt), some 7, some 6, some 5, some 1, some 2, some 3, some 4] :=
  debugStackSlots_reflects_reversedw_style

/-- Partial interval metadata: reports remaining items only for strict prefixes. -/
theorem debug_stack_remaining_partial_example
    (a b c d : Felt) :
    debugStackRemaining [a, b, c, d] 3 = some 1 :=
  debugStackRemaining_partial a b c d

end MidenLean.Proofs.Observer
