import MidenLean.Symbolic.Soundness

/-!
# Phase 5 Validation: Memory, Advice, and Event Instructions

Demonstrates that the symbolic block executor correctly handles memory,
advice, and event instructions via kernel reduction. For each test:

1. `execBlock` reduces via kernel evaluation to a concrete `BlockResult`.
2. The resulting symbolic stack (and where relevant, advice) matches the
   expected output, verified by `rfl`.

These tests validate the Phase 5 extensions to the symbolic executor.
-/

namespace MidenLean.Symbolic.MemoryAdviceTest

open MidenLean

/-- Test frame with 4 locals at base 0. -/
def testFrame : LocalFrame :=
  { base := 0, numLocals := 4, alignedNumLocals := 4 }

-- ============================================================================
-- locStore + locLoad round-trip
-- ============================================================================

set_option maxHeartbeats 1600000 in
/-- locStore followed by locLoad at the same index recovers the stored value. -/
theorem locStore_locLoad_roundtrip :
    ∃ r, execBlock [.locStore 0, .locLoad 0]
      { stack := [.var 0, .var 1], memory := fun _ => .lit 0,
        frames := [testFrame], advice := [] }
      = some r ∧ r.state.stack = [.var 0, .var 1] := by
  exact ⟨_, rfl, rfl⟩

-- ============================================================================
-- advPush 2
-- ============================================================================

set_option maxHeartbeats 800000 in
/-- advPush 2 consumes 2 advice elements and pushes them (reversed) onto the stack. -/
theorem advPush_2_reduces :
    ∃ r, execBlock [.advPush 2]
      { stack := [.var 0, .var 1], memory := fun _ => .lit 0,
        frames := [], advice := [.var 2, .var 3] }
      = some r ∧
      r.state.stack = [.var 3, .var 2, .var 0, .var 1] ∧
      r.state.advice = [] := by
  exact ⟨_, rfl, rfl, rfl⟩

-- ============================================================================
-- locStorewBe + locLoadwBe round-trip (big-endian)
-- ============================================================================

set_option maxHeartbeats 4000000 in
/-- locStorewBe followed by locLoadwBe at the same index is a round-trip. -/
theorem locStorewBe_locLoadwBe_roundtrip :
    ∃ r, execBlock [.locStorewBe 0, .locLoadwBe 0]
      { stack := [.var 0, .var 1, .var 2, .var 3, .var 4],
        memory := fun _ => .lit 0, frames := [testFrame], advice := [] }
      = some r ∧
      r.state.stack = [.var 0, .var 1, .var 2, .var 3, .var 4] := by
  exact ⟨_, rfl, rfl⟩

-- ============================================================================
-- locStorewLe + locLoadwLe round-trip (little-endian)
-- ============================================================================

set_option maxHeartbeats 4000000 in
/-- locStorewLe followed by locLoadwLe at the same index is a round-trip. -/
theorem locStorewLe_locLoadwLe_roundtrip :
    ∃ r, execBlock [.locStorewLe 0, .locLoadwLe 0]
      { stack := [.var 0, .var 1, .var 2, .var 3, .var 4],
        memory := fun _ => .lit 0, frames := [testFrame], advice := [] }
      = some r ∧
      r.state.stack = [.var 0, .var 1, .var 2, .var 3, .var 4] := by
  exact ⟨_, rfl, rfl⟩

-- ============================================================================
-- memStoreImm + memLoadImm round-trip (static-address memory)
-- ============================================================================

set_option maxHeartbeats 1600000 in
/-- memStoreImm followed by memLoadImm at the same address recovers the value. -/
theorem memStoreImm_memLoadImm_roundtrip :
    ∃ r, execBlock [.memStoreImm 100, .memLoadImm 100]
      { stack := [.var 0, .var 1], memory := fun _ => .lit 0,
        frames := [], advice := [] }
      = some r ∧ r.state.stack = [.var 0, .var 1] := by
  exact ⟨_, rfl, rfl⟩

-- ============================================================================
-- locaddr
-- ============================================================================

set_option maxHeartbeats 800000 in
/-- locaddr pushes a local's address onto the stack. -/
theorem locaddr_reduces :
    ∃ r, execBlock [.locaddr 0]
      { stack := [.var 0], memory := fun _ => .lit 0,
        frames := [testFrame], advice := [] }
      = some r := by
  exact ⟨_, rfl⟩

-- ============================================================================
-- emit (no-op)
-- ============================================================================

set_option maxHeartbeats 800000 in
/-- emit succeeds and leaves the stack unchanged. -/
theorem emit_noop :
    ∃ r, execBlock [.emit]
      { stack := [.var 0, .var 1], memory := fun _ => .lit 0,
        frames := [], advice := [] }
      = some r ∧ r.state.stack = [.var 0, .var 1] := by
  exact ⟨_, rfl, rfl⟩

-- ============================================================================
-- emitImm (no-op)
-- ============================================================================

set_option maxHeartbeats 800000 in
/-- emitImm succeeds and leaves the stack unchanged. -/
theorem emitImm_noop :
    ∃ r, execBlock [.emitImm 42]
      { stack := [.var 0, .var 1], memory := fun _ => .lit 0,
        frames := [], advice := [] }
      = some r ∧ r.state.stack = [.var 0, .var 1] := by
  exact ⟨_, rfl, rfl⟩

-- ============================================================================
-- advLoadW
-- ============================================================================

set_option maxHeartbeats 800000 in
/-- advLoadW consumes 4 advice elements, replacing the top 4 stack elements. -/
theorem advLoadW_reduces :
    ∃ r, execBlock [.advLoadW]
      { stack := [.var 0, .var 1, .var 2, .var 3, .var 4],
        memory := fun _ => .lit 0, frames := [],
        advice := [.var 5, .var 6, .var 7, .var 8] }
      = some r ∧
      r.state.stack = [.var 5, .var 6, .var 7, .var 8, .var 4] ∧
      r.state.advice = [] := by
  exact ⟨_, rfl, rfl, rfl⟩

end MidenLean.Symbolic.MemoryAdviceTest
