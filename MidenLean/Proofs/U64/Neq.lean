import MidenLean.Proofs.U64.Common
import MidenLean.Proofs.Tactics
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 4000000 in
/-- `u64::neq` tests inequality of two u64 values, limb by limb.
    Input stack:  [b_lo, b_hi, a_lo, a_hi] ++ rest
    Output stack: [result] ++ rest
    where result = 1 iff b_lo != a_lo || b_hi != a_hi, else 0. -/
theorem u64_neq_raw (b_lo b_hi a_lo a_hi : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest) :
    exec 10 s Miden.Core.U64.neq =
    some (s.withStack (
      (if (b_lo != a_lo) || (b_hi != a_hi)
       then (1 : Felt) else 0) :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.U64.neq execWithEnv
  simp only [List.foldlM]
  change (do
    let s' ← execInstruction ⟨b_lo :: b_hi :: a_lo :: a_hi :: rest, mem, locs, adv⟩ (.movup 2)
    let s' ← execInstruction s' (.neq)
    let s' ← execInstruction s' (.swap 2)
    let s' ← execInstruction s' (.neq)
    let s' ← execInstruction s' Instruction.or
    pure s') = _
  miden_movup
  rw [stepNeq]; miden_bind
  miden_swap
  rw [stepNeq]; miden_bind
  rw [stepOrIte]; dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]

/-- `u64::neq` tests inequality of two u64 values.
    Input stack:  [b.lo, b.hi, a.lo, a.hi] ++ rest
    Output stack: [if a != b then 1 else 0] ++ rest -/
theorem u64_neq_correct (a b : U64) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b.lo.val :: b.hi.val :: a.lo.val :: a.hi.val :: rest) :
    exec 10 s Miden.Core.U64.neq =
    some (s.withStack (
      (if a != b then (1 : Felt) else 0) :: rest)) := by
  have h := u64_neq_raw b.lo.val b.hi.val a.lo.val a.hi.val rest s hs
  rw [U64.bne_comm a b, U64.bne_iff]; exact h

end MidenLean.Proofs
