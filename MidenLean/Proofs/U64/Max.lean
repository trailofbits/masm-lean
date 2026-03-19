import MidenLean.Proofs.U64.Common
import MidenLean.Proofs.Tactics
import MidenLean.Proofs.Interp
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

-- Based on generated skeleton: SEMI | Instructions: 10 | Calls: true (lt)
/-- `u64::max` correctly computes the maximum of two u64 values.
    Input stack:  [b_lo, b_hi, a_lo, a_hi] ++ rest
    Output stack: [max_lo, max_hi] ++ rest
    lt is called on [a_lo, a_hi, b_lo, b_hi], computing b < a.
    If b < a, returns a; otherwise returns b. -/
theorem u64_max_correct
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest)
    (ha_lo : a_lo.isU32 = true) (ha_hi : a_hi.isU32 = true)
    (hb_lo : b_lo.isU32 = true) (hb_hi : b_hi.isU32 = true) :
    execWithEnv u64ProcEnv 20 s Miden.Core.U64.max =
    some (s.withStack (
      let borrow_lo := decide (b_lo.val < a_lo.val)
      let borrow_hi := decide (b_hi.val < a_hi.val)
      let hi_eq := Felt.ofNat (u32OverflowingSub b_hi.val a_hi.val).2 == (0 : Felt)
      let is_lt := borrow_hi || (hi_eq && borrow_lo)
      (if is_lt then a_lo else b_lo) ::
      (if is_lt then a_hi else b_hi) :: rest)) := by
  -- Setup: unfold max, resolve ProcEnv, unfold lt body
  obtain ⟨stk, mem, locs, adv, evts⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold Miden.Core.U64.max execWithEnv
  simp only [List.foldlM, u64ProcEnv]
  dsimp only [bind, Bind.bind, Option.bind]
  unfold Miden.Core.U64.lt execWithEnv
  simp only [List.foldlM, bind, Bind.bind, Option.bind, pure, Pure.pure]
  -- Instruction 1: movup 3
  miden_step
  -- Instruction 2: movup 3
  miden_step
  -- Instruction 3: dupw 0
  miden_step
  -- lt body (13 instructions)
  miden_step  -- movup 3
  miden_step  -- movup 3
  miden_step  -- movup 2
  miden_step  -- u32OverflowSub
  miden_step  -- movdn 3
  miden_step  -- drop
  miden_step  -- swap 1
  miden_step  -- u32OverflowSub
  miden_step  -- swap 1
  miden_step  -- eqImm 0
  miden_step  -- movup 2
  -- and: need to rewrite borrow first
  rw [u32OverflowingSub_borrow_ite b_lo.val a_lo.val]
  miden_step  -- and
  rw [u32OverflowingSub_borrow_ite b_hi.val a_hi.val]
  miden_step  -- or
  -- Instruction 5: movup 4
  miden_step
  -- Instruction 6: movup 3
  miden_step
  -- Instruction 7: dup 2
  miden_step
  -- Instruction 8: cdrop
  miden_step
  -- Instruction 9: movdn 3
  miden_step
  -- Instruction 10: cdrop
  rw [stepCdropIte]

/-- Semantic version: u64.max returns the larger of
    two u64 values. The comparison condition equals
    decide (toU64 b < toU64 a). -/
theorem u64_max_semantic
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt)
    (s : MidenState)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest)
    (ha_lo : a_lo.isU32 = true)
    (ha_hi : a_hi.isU32 = true)
    (hb_lo : b_lo.isU32 = true)
    (hb_hi : b_hi.isU32 = true) :
    execWithEnv u64ProcEnv 20 s Miden.Core.U64.max =
    some (s.withStack (
      (if decide (toU64 b_lo b_hi < toU64 a_lo a_hi)
       then a_lo else b_lo) ::
      (if decide (toU64 b_lo b_hi < toU64 a_lo a_hi)
       then a_hi else b_hi) :: rest)) := by
  rw [u64_max_correct a_lo a_hi b_lo b_hi rest s hs
    ha_lo ha_hi hb_lo hb_hi]
  simp only [u64_lt_condition_eq b_lo b_hi a_lo a_hi
    hb_lo hb_hi ha_lo ha_hi]

end MidenLean.Proofs
