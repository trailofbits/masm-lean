import MidenLean.Proofs.U64.Common
import MidenLean.Proofs.Tactics
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 4000000 in
/-- `u64::eq` tests equality of two u64 values, limb by limb.
    Input stack:  [b_lo, b_hi, a_lo, a_hi] ++ rest
    Output stack: [result] ++ rest
    where result = 1 iff b_lo == a_lo && b_hi == a_hi, else 0. -/
theorem u64_eq_raw (b_lo b_hi a_lo a_hi : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest) :
    exec 10 s Miden.Core.U64.eq =
    some (s.withStack (
      (if (b_lo == a_lo) && (b_hi == a_hi)
       then (1 : Felt) else 0) :: rest)) := by
  obtain ⟨stk, mem, frames, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.U64.eq execWithEnv
  simp only [List.foldlM]
  change (do
    let s' ← execInstruction ⟨b_lo :: b_hi :: a_lo :: a_hi :: rest, mem, frames, adv⟩ (.movup 2)
    let s' ← execInstruction s' (.eq)
    let s' ← execInstruction s' (.swap 2)
    let s' ← execInstruction s' (.eq)
    let s' ← execInstruction s' Instruction.and
    pure s') = _
  miden_movup
  rw [stepEq]; miden_bind
  miden_swap
  rw [stepEq]; miden_bind
  rw [stepAndIte]; dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]

/-- `u64::eq` tests equality of two u64 values.
    Input stack:  [b.lo, b.hi, a.lo, a.hi] ++ rest
    Output stack: [if a == b then 1 else 0] ++ rest -/
theorem u64_eq_correct (a b : U64) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b.lo.val :: b.hi.val :: a.lo.val :: a.hi.val :: rest) :
    exec 10 s Miden.Core.U64.eq =
    some (s.withStack (
      (if a == b then (1 : Felt) else 0) :: rest)) := by
  have h := u64_eq_raw b.lo.val b.hi.val a.lo.val a.hi.val rest s hs
  rw [U64.beq_comm a b]; exact h

-- ============================================================================
-- Soundness dual: execution success implies valid inputs and correct output
-- ============================================================================

set_option maxHeartbeats 4000000 in
/-- Soundness of `u64::eq`: if execution succeeds, then the stack had four
    elements and the output is the correct equality test.
    This is the converse of `u64_eq_correct`. Together they form a
    biconditional: the procedure succeeds iff the stack has at least four
    elements, and the output is always the u64 equality result.

    Hypothesis audit (Phase 1):
    - `hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest` — enforced:
      `movup 2` requires at least 3 elements, and the sequence of instructions
      needs 4 stack elements total. Execution returns `none` otherwise.
    - No `isU32` hypotheses — the procedure uses only `movup`, `eq`, `swap`,
      and `and`. The `eq` instruction works on arbitrary field elements and
      always produces a boolean (0 or 1), so `and` always succeeds. -/
theorem u64_eq_sound (s s' : MidenState)
    (h : exec 10 s Miden.Core.U64.eq = some s') :
    ∃ b_lo b_hi a_lo a_hi rest,
      s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest
      ∧ s' = s.withStack (
        (if (b_lo == a_lo) && (b_hi == a_hi)
         then (1 : Felt) else 0) :: rest) := by
  obtain ⟨stk, mem, frames, adv⟩ := s
  simp only [MidenState.withStack] at h ⊢
  unfold exec Miden.Core.U64.eq execWithEnv at h
  simp only [List.foldlM] at h
  match hstk : stk with
  | [] => simp [execInstruction, execMovup, removeNth] at h
  | [_] => simp [execInstruction, execMovup, removeNth] at h
  | [_, _] => simp [execInstruction, execMovup, removeNth] at h
  | [_, _, _] =>
    simp [execInstruction, execMovup, removeNth, execEq, execSwap,
      bind, Bind.bind, Option.bind, List.eraseIdx] at h
  | b_lo :: b_hi :: a_lo :: a_hi :: rest =>
    refine ⟨b_lo, b_hi, a_lo, a_hi, rest, rfl, ?_⟩
    have hc :=
      u64_eq_raw b_lo b_hi a_lo a_hi rest
        ⟨b_lo :: b_hi :: a_lo :: a_hi :: rest, mem, frames, adv⟩ rfl
    have : exec 10 ⟨b_lo :: b_hi :: a_lo :: a_hi :: rest, mem, frames, adv⟩
        Miden.Core.U64.eq = some s' := by
      unfold exec Miden.Core.U64.eq execWithEnv
      simp only [List.foldlM]
      exact h
    rw [hc] at this
    exact (Option.some.inj this).symm

end MidenLean.Proofs
