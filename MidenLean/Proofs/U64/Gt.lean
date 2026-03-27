import MidenLean.Proofs.U64.Common
import MidenLean.Proofs.Tactics
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 8000000 in
/-- `u64::gt` compares two u64 values.
    Input stack:  [b_lo, b_hi, a_lo, a_hi] ++ rest
    Output stack: [result] ++ rest
    where result = 1 iff a > b (as u64), else 0.
    The comparison is: b_hi < a_hi, or (b_hi == a_hi and b_lo < a_lo). -/
theorem u64_gt_raw
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest)
    (ha_lo : a_lo.isU32 = true) (ha_hi : a_hi.isU32 = true)
    (hb_lo : b_lo.isU32 = true) (hb_hi : b_hi.isU32 = true) :
    exec 20 s Miden.Core.U64.gt =
    some (s.withStack (
      let borrow_lo := decide (b_lo.val < a_lo.val)
      let borrow_hi := decide (b_hi.val < a_hi.val)
      let hi_eq := Felt.ofNat (u32OverflowingSub b_hi.val a_hi.val).2 == (0 : Felt)
      (if borrow_hi || (hi_eq && borrow_lo) then (1 : Felt) else 0) :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.U64.gt execWithEnv
  simp only [List.foldlM]
  -- gt differs from lt: swap 1 before first sub, no swap before second sub
  change (do
    let s' ← execInstruction ⟨b_lo :: b_hi :: a_lo :: a_hi :: rest, mem, locs, adv⟩ (.movup 3)
    let s' ← execInstruction s' (.movup 3)
    let s' ← execInstruction s' (.movup 2)
    let s' ← execInstruction s' (.swap 1)
    let s' ← execInstruction s' (.u32OverflowSub)
    let s' ← execInstruction s' (.movdn 3)
    let s' ← execInstruction s' (.drop)
    let s' ← execInstruction s' (.u32OverflowSub)
    let s' ← execInstruction s' (.swap 1)
    let s' ← execInstruction s' (.eqImm 0)
    let s' ← execInstruction s' (.movup 2)
    let s' ← execInstruction s' Instruction.and
    let s' ← execInstruction s' Instruction.or
    pure s') = _
  miden_movup; miden_movup; miden_movup
  miden_swap
  rw [stepU32OverflowSub (ha := by assumption) (hb := by assumption)]; miden_bind
  miden_movdn
  rw [stepDrop]; miden_bind
  rw [stepU32OverflowSub (ha := by assumption) (hb := by assumption)]; miden_bind
  miden_swap
  rw [stepEqImm]; miden_bind
  miden_movup
  -- Convert borrow_lo to boolean ite form for stepAndIte
  rw [u32OverflowingSub_borrow_ite b_lo.val a_lo.val]
  rw [stepAndIte]; miden_bind
  -- Convert borrow_hi to boolean ite form for stepOrIte
  rw [u32OverflowingSub_borrow_ite b_hi.val a_hi.val]
  rw [stepOrIte]; dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]

/-- `u64::gt` pushes 1 iff `a > b` (as u64).
    Input stack:  [b_lo, b_hi, a_lo, a_hi] ++ rest
    Output stack: [(if b < a then 1 else 0)] ++ rest -/
theorem u64_gt_correct (a b : U64) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b.lo.val :: b.hi.val :: a.lo.val :: a.hi.val :: rest) :
    exec 20 s Miden.Core.U64.gt =
    some (s.withStack (
      (if decide (b < a) then (1 : Felt) else 0) :: rest)) := by
  rw [u64_gt_raw a.lo.val a.hi.val b.lo.val b.hi.val rest s hs a.lo.isU32 a.hi.isU32 b.lo.isU32 b.hi.isU32]
  simp only [u64_borrow_iff_lt b a]; rfl

end MidenLean.Proofs
