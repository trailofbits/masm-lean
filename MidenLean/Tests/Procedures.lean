/-
  Procedure-level sanity checks: run key u64/u128 procedures with concrete
  inputs and verify output stacks match expected results.

  These tests catch naming inversions, formula errors, and stack ordering bugs.
  `lake build` success implies all tests pass.
-/
import MidenLean.Generated.U64
import MidenLean.Generated.U128
import MidenLean.Semantics
import MidenLean.Proofs.U64.Common

namespace MidenLean.Tests.Procedures

open MidenLean MidenLean.Proofs

private def mkState (stk : List Felt) : MidenState :=
  MidenState.ofStack stk

/-- Check that the top of the result stack matches expected values (prefix check).
    Ignores trailing elements from `rest` after execution. -/
private def checkStackPrefix (result : Option MidenState) (expected : List Felt) : Bool :=
  match result with
  | some s => s.stack.take expected.length == expected
  | none => false

-- ============================================================================
-- u64 comparisons
-- ============================================================================

-- u64_lt: 5 < 7 should give 1 (true)
-- Stack: [b_lo, b_hi, a_lo, a_hi] = [7, 0, 5, 0]
#eval do
  let s := mkState [7, 0, 5, 0]
  let r := exec 20 s Miden.Core.U64.lt
  unless checkStackPrefix r [1] do panic! "u64_lt: 5 < 7 should be true"

-- u64_lt: 7 < 5 should give 0 (false)
#eval do
  let s := mkState [5, 0, 7, 0]
  let r := exec 20 s Miden.Core.U64.lt
  unless checkStackPrefix r [0] do panic! "u64_lt: 7 < 5 should be false"

-- u64_lt: equal values should give 0
#eval do
  let s := mkState [42, 0, 42, 0]
  let r := exec 20 s Miden.Core.U64.lt
  unless checkStackPrefix r [0] do panic! "u64_lt: 42 < 42 should be false"

-- u64_lt: high-limb comparison dominates
-- a = 0 + 1*2^32 = 2^32, b = 2^32-1 + 0*2^32 = 2^32-1
#eval do
  let s := mkState [(2^32 - 1 : Felt), 0, 0, 1]
  let r := exec 20 s Miden.Core.U64.lt
  unless checkStackPrefix r [0] do panic! "u64_lt: 2^32 < 2^32-1 should be false"

-- u64_gt: 7 > 5 should give 1
#eval do
  let s := mkState [5, 0, 7, 0]
  let r := exec 20 s Miden.Core.U64.gt
  unless checkStackPrefix r [1] do panic! "u64_gt: 7 > 5 should be true"

-- u64_lte: 5 <= 5 should give 1 (lte calls gt internally, needs ProcEnv)
#eval do
  let s := mkState [5, 0, 5, 0]
  let r := execWithEnv u64ProcEnv 30 s Miden.Core.U64.lte
  unless checkStackPrefix r [1] do panic! "u64_lte: 5 <= 5 should be true"

-- u64_gte: 3 >= 7 should give 0 (gte calls lt internally, needs ProcEnv)
#eval do
  let s := mkState [7, 0, 3, 0]
  let r := execWithEnv u64ProcEnv 30 s Miden.Core.U64.gte
  unless checkStackPrefix r [0] do panic! "u64_gte: 3 >= 7 should be false"

-- ============================================================================
-- u64 arithmetic
-- ============================================================================

-- u64_overflowing_sub: 10 - 3 = 7 with no borrow (calls overflowing_add internally)
-- Stack: [b_lo, b_hi, a_lo, a_hi]
#eval do
  let s := mkState [3, 0, 10, 0]
  let r := execWithEnv u64ProcEnv 30 s Miden.Core.U64.overflowing_sub
  -- Output: [borrow, diff_lo, diff_hi]
  unless checkStackPrefix r [0, 7, 0] do panic! "u64_overflowing_sub: 10 - 3 should be (0, 7, 0)"

-- u64_overflowing_sub: 3 - 10 underflows
#eval do
  let s := mkState [10, 0, 3, 0]
  let r := execWithEnv u64ProcEnv 30 s Miden.Core.U64.overflowing_sub
  -- diff = 3 - 10 mod 2^64 = 2^64 - 7, lo = 2^32-7, hi = 2^32-1
  unless checkStackPrefix r [1, (2^32 - 7 : Felt), (2^32 - 1 : Felt)]
    do panic! "u64_overflowing_sub: 3 - 10 should underflow"

-- u64_overflowing_add: 5 + 3 = 8 with no overflow
-- Stack: [b_lo, b_hi, a_lo, a_hi]
#eval do
  let s := mkState [3, 0, 5, 0]
  let r := exec 20 s Miden.Core.U64.overflowing_add
  -- Output: [overflow, sum_lo, sum_hi]
  unless checkStackPrefix r [0, 8, 0] do panic! "u64_overflowing_add: 5 + 3 should be (0, 8, 0)"

-- ============================================================================
-- u64 shifts
-- ============================================================================

-- u64_shr: 256 >> 4 = 16
-- 256 as u64: lo=256, hi=0
-- Stack: [shift, lo, hi]
#eval do
  let s := mkState [4, 256, 0]
  let r := exec 50 s Miden.Core.U64.shr
  unless checkStackPrefix r [16, 0] do panic! "u64_shr: 256 >> 4 should be 16"

-- u64_shl: 1 << 4 = 16 (shl calls wrapping_mul internally)
-- Stack: [shift, lo, hi]
#eval do
  let s := mkState [4, 1, 0]
  let r := execWithEnv u64ProcEnv 50 s Miden.Core.U64.shl
  unless checkStackPrefix r [16, 0] do panic! "u64_shl: 1 << 4 should be 16"

end MidenLean.Tests.Procedures
