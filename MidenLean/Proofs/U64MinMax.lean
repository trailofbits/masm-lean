import MidenLean.Proofs.U64
import MidenLean.Proofs.Tactics
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 8000000 in
/-- u64.min correctly computes the minimum of two u64 values.
    Input stack:  [b_lo, b_hi, a_lo, a_hi] ++ rest
    Output stack: [min_lo, min_hi] ++ rest
    where min is the minimum of a and b as u64 values. -/
theorem u64_min_correct
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest)
    (ha_lo : a_lo.isU32 = true) (ha_hi : a_hi.isU32 = true)
    (hb_lo : b_lo.isU32 = true) (hb_hi : b_hi.isU32 = true) :
    execWithEnv u64ProcEnv 10 s Miden.Core.Math.U64.min =
    some (s.withStack (
      let lt_lo := decide (a_lo.val < b_lo.val)
      let lt_hi := decide (a_hi.val < b_hi.val)
      let hi_eq := Felt.ofNat (u32OverflowingSub a_hi.val b_hi.val).2 == (0 : Felt)
      let b_gt_a := lt_hi || (hi_eq && lt_lo)
      let min_lo := if b_gt_a then a_lo else b_lo
      let min_hi := if b_gt_a then a_hi else b_hi
      min_lo :: min_hi :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold execWithEnv Miden.Core.Math.U64.min
  simp only [List.foldlM]
  -- movup 3, movup 3
  miden_movup; miden_movup
  -- dupw 0
  rw [stepDupw (0 : Fin 4)
      (a_lo :: a_hi :: b_lo :: b_hi :: rest) mem locs adv
      a_lo a_hi b_lo b_hi rfl rfl rfl rfl]
  -- exec "gt": unfold ProcEnv lookup and gt body
  simp only [bind, Bind.bind, Option.bind, u64ProcEnv]
  unfold Miden.Core.Math.U64.gt execWithEnv at *
  simp only [List.foldlM]
  -- Execute gt procedure: movup 3, movup 3, movup 2
  miden_movup; miden_movup; miden_movup
  -- swap 1
  miden_swap
  -- u32OverflowSub
  rw [stepU32OverflowSub (ha := by assumption) (hb := by assumption)]
  dsimp only [bind, Bind.bind, Option.bind]
  -- movdn 3
  miden_movdn
  -- drop
  rw [stepDrop]; dsimp only [bind, Bind.bind, Option.bind]
  -- u32OverflowSub
  rw [stepU32OverflowSub (ha := by assumption) (hb := by assumption)]
  dsimp only [bind, Bind.bind, Option.bind]
  -- swap 1
  miden_swap
  -- eqImm 0
  rw [stepEqImm]; dsimp only [bind, Bind.bind, Option.bind]
  -- movup 2
  miden_movup
  -- Convert borrows to ite form
  rw [u32OverflowingSub_borrow_ite a_lo.val b_lo.val]
  rw [stepAndIte]; dsimp only [bind, Bind.bind, Option.bind]
  rw [u32OverflowingSub_borrow_ite a_hi.val b_hi.val]
  rw [stepOrIte]; dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
  -- movup 4, movup 3, dup 2, cdrop, movdn 3, cdrop
  miden_movup; miden_movup
  rw [stepDup (h := rfl)]
  dsimp only [bind, Bind.bind, Option.bind]
  rw [stepCdropIte]; dsimp only [bind, Bind.bind, Option.bind]
  miden_movdn
  rw [stepCdropIte]

set_option maxHeartbeats 8000000 in
/-- u64.max correctly computes the maximum of two u64 values.
    Input stack:  [b_lo, b_hi, a_lo, a_hi] ++ rest
    Output stack: [max_lo, max_hi] ++ rest
    where max is the maximum of a and b as u64 values. -/
theorem u64_max_correct
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest)
    (ha_lo : a_lo.isU32 = true) (ha_hi : a_hi.isU32 = true)
    (hb_lo : b_lo.isU32 = true) (hb_hi : b_hi.isU32 = true) :
    execWithEnv u64ProcEnv 10 s Miden.Core.Math.U64.max =
    some (s.withStack (
      let lt_lo := decide (b_lo.val < a_lo.val)
      let lt_hi := decide (b_hi.val < a_hi.val)
      let hi_eq := Felt.ofNat (u32OverflowingSub b_hi.val a_hi.val).2 == (0 : Felt)
      let b_lt_a := lt_hi || (hi_eq && lt_lo)
      let max_lo := if b_lt_a then a_lo else b_lo
      let max_hi := if b_lt_a then a_hi else b_hi
      max_lo :: max_hi :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold execWithEnv Miden.Core.Math.U64.max
  simp only [List.foldlM]
  -- movup 3, movup 3
  miden_movup; miden_movup
  -- dupw 0
  rw [stepDupw (0 : Fin 4)
      (a_lo :: a_hi :: b_lo :: b_hi :: rest) mem locs adv
      a_lo a_hi b_lo b_hi rfl rfl rfl rfl]
  -- exec "lt": unfold ProcEnv lookup and lt body
  simp only [bind, Bind.bind, Option.bind, u64ProcEnv]
  unfold Miden.Core.Math.U64.lt execWithEnv at *
  simp only [List.foldlM]
  -- Execute lt procedure: movup 3, movup 3, movup 2
  miden_movup; miden_movup; miden_movup
  -- u32OverflowSub
  rw [stepU32OverflowSub (ha := by assumption) (hb := by assumption)]
  dsimp only [bind, Bind.bind, Option.bind]
  -- movdn 3
  miden_movdn
  -- drop
  rw [stepDrop]; dsimp only [bind, Bind.bind, Option.bind]
  -- swap 1
  miden_swap
  -- u32OverflowSub
  rw [stepU32OverflowSub (ha := by assumption) (hb := by assumption)]
  dsimp only [bind, Bind.bind, Option.bind]
  -- swap 1
  miden_swap
  -- eqImm 0
  rw [stepEqImm]; dsimp only [bind, Bind.bind, Option.bind]
  -- movup 2
  miden_movup
  -- Convert borrows to ite form
  rw [u32OverflowingSub_borrow_ite b_lo.val a_lo.val]
  rw [stepAndIte]; dsimp only [bind, Bind.bind, Option.bind]
  rw [u32OverflowingSub_borrow_ite b_hi.val a_hi.val]
  rw [stepOrIte]; dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
  -- movup 4, movup 3, dup 2, cdrop, movdn 3, cdrop
  miden_movup; miden_movup
  rw [stepDup (h := rfl)]
  dsimp only [bind, Bind.bind, Option.bind]
  rw [stepCdropIte]; dsimp only [bind, Bind.bind, Option.bind]
  miden_movdn
  rw [stepCdropIte]

end MidenLean.Proofs
