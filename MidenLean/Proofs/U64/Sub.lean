import MidenLean.Proofs.Tactics
import MidenLean.Proofs.Interp
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

/-- `u64::wrapping_sub` correctly computes wrapping subtraction of two u64 values. -/
theorem u64_wrapping_sub_correct
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
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.U64.wrapping_sub execWithEnv
  simp only [List.foldlM]
  change (do
    let s' ← execInstruction ⟨b_lo :: b_hi :: a_lo :: a_hi :: rest, mem, locs, adv⟩ (.movup 3)
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

/-- Semantic: wrapping_sub computes the output limbs
    such that their u64 value equals
    (toU64 a + 2^64 - toU64 b) % 2^64. -/
theorem u64_wrapping_sub_semantic
    (a_lo a_hi b_lo b_hi : Felt)
    (ha_lo : a_lo.isU32 = true)
    (ha_hi : a_hi.isU32 = true)
    (hb_lo : b_lo.isU32 = true)
    (hb_hi : b_hi.isU32 = true) :
    let sub_lo := u32OverflowingSub a_lo.val b_lo.val
    let sub_hi := u32OverflowingSub a_hi.val b_hi.val
    let sub_final := u32OverflowingSub sub_hi.2 sub_lo.1
    sub_final.2 * 2 ^ 32 + sub_lo.2 =
    (toU64 a_lo a_hi + 2 ^ 64 - toU64 b_lo b_hi) %
      2 ^ 64 := by
  simp only [toU64, u32OverflowingSub, u32Max,
    Felt.isU32, decide_eq_true_eq] at *
  split <;> split <;> split <;> omega

end MidenLean.Proofs
