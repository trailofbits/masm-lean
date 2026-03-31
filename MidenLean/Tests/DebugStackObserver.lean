import MidenLean.Spec.DebugStackObserver
import MidenLean.Proofs.Observer.DebugStackObserver

namespace MidenLean.Tests

open MidenLean
open MidenLean.Proofs.Observer

private def someF (n : Nat) : Option Felt := some (n : Felt)

-- Initial stack interval ordering (top-of-stack index 0).
#eval do
  let got := debugStackSlots [1, 2, 3, 4] 4
  unless got == [someF 1, someF 2, someF 3, someF 4] do
    panic! "debugStackSlots initial ordering failed"

-- `debug.stack.0` means "all available items".
#eval do
  let got := debugStackSlots [1, 2, 3, 4] 0
  unless got == [someF 1, someF 2, someF 3, someF 4] do
    panic! "debugStackSlots n=0 all-items semantics failed"

-- Extra EMPTY slots when requesting past available items.
#eval do
  let got := debugStackSlots [1, 2, 3, 4] 6
  unless got == [someF 1, someF 2, someF 3, someF 4, none, none] do
    panic! "debugStackSlots EMPTY padding failed"

-- Remaining-count behavior for partial vs full views.
#eval do
  let remainingPartial := debugStackRemaining [1, 2, 3, 4] 3
  let full := debugStackRemaining [1, 2, 3, 4] 0
  unless remainingPartial == some 1 do
    panic! "debugStackRemaining partial view failed"
  unless full == none do
    panic! "debugStackRemaining full view failed"

-- Post-`reversew` style projection from Rust debug tests.
#eval do
  let got := debugStackSlots [4, 3, 2, 1, 5, 6, 7, 8] 8
  unless got == [someF 4, someF 3, someF 2, someF 1, someF 5, someF 6, someF 7, someF 8] do
    panic! "debugStackSlots reversew-style reflection failed"

-- Post-`reversedw` style projection from Rust debug tests.
#eval do
  let got := debugStackSlots [8, 7, 6, 5, 1, 2, 3, 4] 8
  unless got == [someF 8, someF 7, someF 6, someF 5, someF 1, someF 2, someF 3, someF 4] do
    panic! "debugStackSlots reversedw-style reflection failed"

-- Theorems from the observer proof module are usable directly.
#eval do
  have _ := debug_stack_reflects_reversew_rewrite
  have _ := debug_stack_reflects_reversedw_rewrite
  pure ()

end MidenLean.Tests
