import MidenLean.AIR.Proofs.StackArith
import MidenLean.AIR.Proofs.U32Semantic
import MidenLean.Semantics
/-!
# Semantic Bridge: AIR Constraints ↔ execInstruction

Connects Layer 1 (MASM instruction semantics) with Layer 3 (AIR constraints).

For each bridged operation, we prove two directions:
- **exec → AIR**: If `execInstruction` produces state s', the transition frame satisfies constraints.
- **AIR → correct output**: If constraints are satisfied, the output matches the instruction spec.

Together these show: the AIR constraints are a faithful encoding of the instruction semantics.
-/

namespace MidenLean.AIR.Bridge

open MidenLean MidenLean.AIR MidenLean.AIR.Constraints

/-- Construct a Frame from a before/after MidenState pair.
    Maps state stacks to Frame columns. Helpers default to 0
    (they are prover-chosen, not part of MidenState). -/
def Frame.ofStates (before after : MidenState) : Frame where
  s  := fun i => (before.stack.getD i 0)
  s' := fun i => (after.stack.getD i 0)
  h  := fun _ => 0

-- ============================================================================
-- ADD bridge
-- ============================================================================

/-- exec → AIR: ADD execution produces a frame satisfying the ADD constraint. -/
theorem add_exec_satisfies_air (a b : Felt) (rest : List Felt)
    (s : MidenState) (hs : s.stack = b :: a :: rest) :
    let s' := s.withStack ((a + b) :: rest)
    (Frame.ofStates s s').satisfies Constraints.add := by
  simp only [Frame.ofStates, Frame.satisfies, Constraints.add,
    MidenState.withStack, List.mem_singleton]
  intro c hc; subst hc; simp [hs]; ring

/-- AIR → correct: ADD constraint satisfaction implies s0' = s0 + s1. -/
theorem air_add_implies_correct (f : Frame) (hsat : f.satisfies Constraints.add) :
    f.s' 0 = f.s 0 + f.s 1 :=
  Proofs.air_add_sound f hsat

-- ============================================================================
-- MUL bridge
-- ============================================================================

/-- exec → AIR: MUL execution produces a frame satisfying the MUL constraint. -/
theorem mul_exec_satisfies_air (a b : Felt) (rest : List Felt)
    (s : MidenState) (hs : s.stack = b :: a :: rest) :
    let s' := s.withStack ((a * b) :: rest)
    (Frame.ofStates s s').satisfies Constraints.mul := by
  simp only [Frame.ofStates, Frame.satisfies, Constraints.mul,
    MidenState.withStack, List.mem_singleton]
  intro c hc; subst hc; simp [hs]; ring

/-- AIR → correct: MUL constraint satisfaction implies s0' = s0 * s1. -/
theorem air_mul_implies_correct (f : Frame) (hsat : f.satisfies Constraints.mul) :
    f.s' 0 = f.s 0 * f.s 1 :=
  Proofs.air_mul_sound f hsat

-- ============================================================================
-- NEG bridge
-- ============================================================================

/-- exec → AIR: NEG execution satisfies the NEG constraint. -/
theorem neg_exec_satisfies_air (a : Felt) (rest : List Felt)
    (s : MidenState) (hs : s.stack = a :: rest) :
    let s' := s.withStack ((-a) :: rest)
    (Frame.ofStates s s').satisfies Constraints.neg := by
  simp only [Frame.ofStates, Frame.satisfies, Constraints.neg,
    MidenState.withStack, List.mem_singleton]
  intro c hc; subst hc; simp [hs]

/-- AIR → correct: NEG constraint implies s0' = -s0. -/
theorem air_neg_implies_correct (f : Frame) (hsat : f.satisfies Constraints.neg) :
    f.s' 0 = -f.s 0 :=
  Proofs.air_neg_sound f hsat

-- ============================================================================
-- U32ADD bridge (exec → AIR direction)
-- ============================================================================

/-- Construct a Frame with explicit helper registers (for u32 ops where
    the prover must supply the limb decomposition). -/
def Frame.ofStatesWithHelpers (before after : MidenState)
    (helpers : Fin 6 → Felt) : Frame where
  s  := fun i => (before.stack.getD i 0)
  s' := fun i => (after.stack.getD i 0)
  h  := helpers

/-- U32ADD: AIR → correct output. If u32add constraints are satisfied and
    helpers are range-checked, then the outputs faithfully represent the sum. -/
theorem air_u32add_implies_decomposition (f : Frame)
    (hsat : f.satisfies Constraints.u32add)
    (hrc : f.RangeChecked) :
    f.s' 0 = f.v_lo ∧ f.s' 1 = f.v_hi ∧ f.s 0 + f.s 1 = f.v48
    ∧ f.v_lo.val < 2^32 ∧ f.v_hi.val < 2^32 :=
  Proofs.U32Semantic.air_u32add_semantic f hsat hrc

end MidenLean.AIR.Bridge
