import MidenLean.Symbolic.Exec

/-!
# Phase 2 Spike Test: Kernel Reduction Performance

Tests that `execBlock` reduces via kernel evaluation within acceptable
heartbeat and time budgets. Target: <30 seconds, <800K heartbeats for
a 30-instruction block.
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
