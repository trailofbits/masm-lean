import MidenLean.Spec.WordAccessors
import MidenLean.Proofs.Word.AccessorBoundaries

namespace MidenLean.Tests

open MidenLean

-- Processor accessor orientation at top-of-stack.
#eval do
  let got := processorSafeWordAccessor [1, 2, 3, 4, 5] 0
  unless got == [1, 2, 3, 4] do panic! "processorSafeWordAccessor top-word orientation failed"

-- Processor accessor orientation at non-zero offset.
#eval do
  let got := processorSafeWordAccessor [1, 2, 3, 4, 5] 1
  unless got == [2, 3, 4, 5] do panic! "processorSafeWordAccessor offset orientation failed"

-- Processor accessor zero-padding on partial reads.
#eval do
  let got := processorSafeWordAccessor [16] 0
  unless got == [16, 0, 0, 0] do panic! "processorSafeWordAccessor zero padding failed"

-- StackOutputs accessor returns exact words in range.
#eval do
  let stk := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
  let got0 := stackOutputsWordAccessor stk 0
  let got4 := stackOutputsWordAccessor stk 4
  let got1 := stackOutputsWordAccessor stk 1
  unless got0 == some [1, 2, 3, 4] do panic! "stackOutputsWordAccessor idx=0 failed"
  unless got4 == some [5, 6, 7, 8] do panic! "stackOutputsWordAccessor idx=4 failed"
  unless got1 == some [2, 3, 4, 5] do panic! "stackOutputsWordAccessor idx=1 failed"

-- StackOutputs accessor enforces the hard boundary idx <= 12.
#eval do
  let stk := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
  let got := stackOutputsWordAccessor stk 13
  unless got == none do panic! "stackOutputsWordAccessor idx=13 should be none"

-- StackOutputs accessor does not partially zero-pad short reads.
#eval do
  let got := stackOutputsWordAccessor [16] 0
  unless got == none do panic! "stackOutputsWordAccessor short read should be none"

-- Non-reversal regression check from Rust boundary tests.
#eval do
  let stk := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
  let got := stackOutputsWordAccessor stk 0
  unless !(got == some [4, 3, 2, 1]) do panic! "stackOutputsWordAccessor unexpectedly reversed order"

-- The two accessors intentionally diverge on short stacks.
#eval do
  let p := processorSafeWordAccessor [16] 0
  let o := stackOutputsWordAccessor [16] 0
  unless p == [16, 0, 0, 0] do panic! "processor short-read behavior mismatch"
  unless o == none do panic! "stackOutputs short-read behavior mismatch"

end MidenLean.Tests
