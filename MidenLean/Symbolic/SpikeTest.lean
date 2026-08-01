import MidenLean.Symbolic.Exec

/-!
# Kernel-Reduction Budget Regression Tests

Each theorem asserts that `execBlock` on a fixed instruction block reduces
to `some _` by `rfl` (kernel evaluation) within a fixed heartbeat budget.
The `maxHeartbeats` caps ARE the assertion: 30-instruction blocks must
reduce within 800K heartbeats, 60-instruction blocks within 1.6M, and
100-instruction blocks within 4M. If a change to the symbolic executor
makes kernel reduction slower, these theorems time out and the build of
`MidenLeanTests` fails.
-/

namespace MidenLean.Symbolic.SpikeTest

-- ============================================================================
-- Test instruction sequences
-- ============================================================================

/-- 30-instruction block using all 5 supported instruction types:
    drop, dup, swap, add, u32WidenAdd. -/
def spikeInsts : List Instruction :=
  [ -- Group 1: (dup 0, add) × 5 = 10 instructions, stack stays at 10
    .dup 0, .add, .dup 0, .add, .dup 0,
    .add, .dup 0, .add, .dup 0, .add,
    -- Group 2: swap+add patterns = 10 instructions, stack shrinks to 7
    .swap 1, .add, .swap 1, .add, .swap 1,
    .add, .dup 0, .add, .dup 0, .add,
    -- Group 3: u32WidenAdd + cleanup = 10 instructions, ends at 5
    .u32WidenAdd, .swap 1, .drop, .dup 0, .add,
    .dup 0, .add, .drop, .dup 0, .add ]

-- ============================================================================
-- Kernel reduction tests
-- ============================================================================

set_option maxHeartbeats 800000 in
/-- Key test: kernel reduction of `execBlock` on a 30-instruction block.
    If `rfl` closes this goal, the symbolic executor evaluates correctly
    via kernel reduction. -/
theorem spike_kernel_30 :
    ∃ r, execBlock spikeInsts (State.ofInputs 10) = some r := by
  exact ⟨_, rfl⟩

/-- 30-instruction sequence using movup, eq, swap, and, u32WidenAdd. -/
def mixedInsts30 : List Instruction :=
  [.movup 2, .eq, .swap 2, .eq, Instruction.and,   -- 5: eq pattern
   .dup 0, .add, .dup 0, .add, .dup 0,              -- 10
   .add, .swap 1, .add, .dup 0, .mul,               -- 15
   .dup 0, .sub, .dup 0, .add, .dup 0,              -- 20
   .mul, .swap 1, .add, .dup 0, .add,               -- 25
   .dup 0, .sub, .dup 0, .add, .drop]               -- 30

set_option maxHeartbeats 800000 in
/-- 30-instruction block with a wider instruction mix (movup, eq, and, mul,
    sub) reduces in <800K heartbeats. -/
theorem mixed_30_reduces :
    ∃ r, execBlock mixedInsts30 (State.ofInputs 8) = some r := by
  exact ⟨_, rfl⟩

-- ============================================================================
-- Stress tests: larger blocks
-- ============================================================================

/-- 60-instruction block: (dup 0, add) × 30. Stack-neutral on each pair. -/
def spikeInsts60 : List Instruction :=
  (List.replicate 30 [Instruction.dup 0, Instruction.add]).flatten

set_option maxHeartbeats 1600000 in
theorem spike_kernel_60 :
    ∃ r, execBlock spikeInsts60 (State.ofInputs 10) = some r := by
  exact ⟨_, rfl⟩

/-- 100-instruction block: (dup 0, add) × 50. -/
def spikeInsts100 : List Instruction :=
  (List.replicate 50 [Instruction.dup 0, Instruction.add]).flatten

set_option maxHeartbeats 4000000 in
theorem spike_kernel_100 :
    ∃ r, execBlock spikeInsts100 (State.ofInputs 10) = some r := by
  exact ⟨_, rfl⟩

end MidenLean.Symbolic.SpikeTest
