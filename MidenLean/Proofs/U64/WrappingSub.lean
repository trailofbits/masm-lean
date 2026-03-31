import MidenLean.Proofs.U64.Common
import MidenLean.Proofs.Tactics

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 8000000 in
/-- `u64::wrapping_sub` computes wrapping subtraction of two u64 values. -/
theorem u64_wrapping_sub_raw
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest)
    (ha_lo : a_lo.isU32 = true) (ha_hi : a_hi.isU32 = true)
    (hb_lo : b_lo.isU32 = true) (hb_hi : b_hi.isU32 = true) :
    exec 20 s Miden.Core.U64.wrapping_sub =
    some (s.withStack (
      let sub_lo := u32OverflowingSub a_lo.val b_lo.val
      let sub_hi := u32OverflowingSub a_hi.val b_hi.val
      let sub_final := u32OverflowingSub sub_hi.2 sub_lo.1
      Felt.ofNat sub_lo.2 :: Felt.ofNat sub_final.2 :: rest)) := by
  obtain ⟨stk, mem, frames, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.U64.wrapping_sub execWithEnv
  simp only [List.foldlM]
  change (do
    let s' ← execInstruction ⟨b_lo :: b_hi :: a_lo :: a_hi :: rest, mem, frames, adv⟩ (.movup 3)
    let s' ← execInstruction s' (.movup 3)
    let s' ← execInstruction s' (.movup 2)
    let s' ← execInstruction s' (.u32OverflowSub)
    let s' ← execInstruction s' (.movup 2)
    let s' ← execInstruction s' (.movup 3)
    let s' ← execInstruction s' (.u32OverflowSub)
    let s' ← execInstruction s' (.drop)
    let s' ← execInstruction s' (.swap 1)
    let s' ← execInstruction s' (.u32OverflowSub)
    let s' ← execInstruction s' (.drop)
    let s' ← execInstruction s' (.swap 1)
    pure s') = _
  miden_movup; miden_movup; miden_movup
  rw [stepU32OverflowSub (ha := by assumption) (hb := by assumption)]; miden_bind
  miden_movup; miden_movup
  rw [stepU32OverflowSub (ha := by assumption) (hb := by assumption)]; miden_bind
  rw [stepDrop]; miden_bind
  miden_swap
  -- The third u32OverflowSub operates on Felt.ofNat values
  have h_val_snd : (Felt.ofNat (u32OverflowingSub a_hi.val b_hi.val).2).val =
      (u32OverflowingSub a_hi.val b_hi.val).2 :=
    felt_ofNat_val_lt _ (u32_overflow_sub_snd_lt _ _ (ZMod.val_lt a_hi) (ZMod.val_lt b_hi))
  have h_val_fst : (Felt.ofNat (u32OverflowingSub a_lo.val b_lo.val).1).val =
      (u32OverflowingSub a_lo.val b_lo.val).1 :=
    felt_ofNat_val_lt _ (u32_overflow_sub_fst_lt _ _)
  have h_isU32_snd : (Felt.ofNat (u32OverflowingSub a_hi.val b_hi.val).2).isU32 = true :=
    u32OverflowingSub_snd_isU32 _ _ (by simp [Felt.isU32, decide_eq_true_eq] at ha_hi; exact ha_hi)
      (by simp [Felt.isU32, decide_eq_true_eq] at hb_hi; exact hb_hi)
  have h_isU32_fst : (Felt.ofNat (u32OverflowingSub a_lo.val b_lo.val).1).isU32 = true :=
    u32OverflowingSub_fst_isU32 _ _
  rw [stepU32OverflowSub (ha := h_isU32_snd) (hb := h_isU32_fst)]; miden_bind
  rw [h_val_snd, h_val_fst]
  rw [stepDrop]; miden_bind
  miden_swap
  dsimp only [pure, Pure.pure]

/-- `u64::wrapping_sub` computes `a - b` as a u64 value.
    Input stack:  [b.lo, b.hi, a.lo, a.hi] ++ rest
    Output stack: [(a - b).lo, (a - b).hi] ++ rest -/
theorem u64_wrapping_sub_correct (a b : U64) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b.lo.val :: b.hi.val :: a.lo.val :: a.hi.val :: rest) :
    exec 20 s Miden.Core.U64.wrapping_sub =
    some (s.withStack ((a - b).lo.val :: (a - b).hi.val :: rest)) := by
  have h := u64_wrapping_sub_raw a.lo.val a.hi.val b.lo.val b.hi.val rest s hs a.lo.isU32 a.hi.isU32 b.lo.isU32 b.hi.isU32
  have ⟨hlo, hhi⟩ := u64_sub_limbs_felt a b
  rw [h]; simp only [hlo, hhi]

-- ============================================================================
-- Soundness dual: execution success implies valid inputs and correct output
-- ============================================================================

-- Phase 1: Hypothesis Audit
-- | Hypothesis                                            | Enforced?                                           |
-- |--------------------------------------------------------|-----------------------------------------------------|
-- | hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest    | Yes — movup 3 requires ≥4 elements, else none       |
-- | ha_lo : a_lo.isU32 = true                              | Yes — 1st u32OverflowSub checks isU32               |
-- | ha_hi : a_hi.isU32 = true                              | Yes — 2nd u32OverflowSub checks isU32               |
-- | hb_lo : b_lo.isU32 = true                              | Yes — 1st u32OverflowSub checks isU32               |
-- | hb_hi : b_hi.isU32 = true                              | Yes — 2nd u32OverflowSub checks isU32               |
-- All hypotheses enforced. Full dual is provable.

set_option maxHeartbeats 32000000 in
/-- Soundness of `u64::wrapping_sub`: if execution succeeds, then all four input
    limbs were u32 and the output is the correct wrapping subtraction. -/
theorem u64_wrapping_sub_sound
    (s s' : MidenState)
    (h : exec 20 s Miden.Core.U64.wrapping_sub = some s') :
    ∃ a_lo a_hi b_lo b_hi rest,
      s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest
      ∧ a_lo.isU32 = true
      ∧ a_hi.isU32 = true
      ∧ b_lo.isU32 = true
      ∧ b_hi.isU32 = true
      ∧ s' = s.withStack (
        let sub_lo := u32OverflowingSub a_lo.val b_lo.val
        let sub_hi := u32OverflowingSub a_hi.val b_hi.val
        let sub_final := u32OverflowingSub sub_hi.2 sub_lo.1
        Felt.ofNat sub_lo.2 :: Felt.ofNat sub_final.2 :: rest) := by
  obtain ⟨stk, mem, frames, adv⟩ := s
  simp only [MidenState.withStack] at h ⊢
  unfold exec Miden.Core.U64.wrapping_sub execWithEnv at h
  simp only [List.foldlM] at h
  match stk with
  | [] | [_] | [_, _] | [_, _, _] =>
    simp [execInstruction, execMovup, removeNth] at h
  | b_lo :: b_hi :: a_lo :: a_hi :: rest =>
    simp (config := { decide := true }) only [execInstruction, execMovup, removeNth,
      MidenState.withStack, bind, Bind.bind, Option.bind, ↓reduceIte,
      List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.eraseIdx_cons_succ, List.eraseIdx_cons_zero] at h
    by_cases ha_lo : a_lo.isU32 = true <;> by_cases hb_lo : b_lo.isU32 = true
    ·
      by_cases ha_hi : a_hi.isU32 = true <;> by_cases hb_hi : b_hi.isU32 = true
      · refine ⟨a_lo, a_hi, b_lo, b_hi, rest, rfl, ha_lo, ha_hi, hb_lo, hb_hi, ?_⟩
        have hc := u64_wrapping_sub_raw a_lo a_hi b_lo b_hi rest
          ⟨b_lo :: b_hi :: a_lo :: a_hi :: rest, mem, frames, adv⟩ rfl ha_lo ha_hi hb_lo hb_hi
        show s' = _
        have : exec 20 ⟨b_lo :: b_hi :: a_lo :: a_hi :: rest, mem, frames, adv⟩
            Miden.Core.U64.wrapping_sub = some s' := by
          unfold exec Miden.Core.U64.wrapping_sub execWithEnv
          simp only [List.foldlM]
          exact h
        rw [hc] at this; exact (Option.some.inj this).symm
      all_goals (exfalso; simp only [execU32OverflowSub, MidenState.withStack] at h; simp_all)
    all_goals (exfalso; simp only [execU32OverflowSub, MidenState.withStack] at h; simp_all)

end MidenLean.Proofs
