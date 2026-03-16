import MidenLean.Proofs.U64
import MidenLean.Proofs.StepLemmas
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas

-- ============================================================================
-- Helper lemmas: u32OverflowingSub outputs are small
-- ============================================================================

theorem u32_overflow_sub_fst_lt (a b : Nat) :
    (u32OverflowingSub a b).1 < GOLDILOCKS_PRIME := by
  unfold u32OverflowingSub
  split
  · simp [GOLDILOCKS_PRIME]
  · simp [GOLDILOCKS_PRIME]

theorem u32_overflow_sub_snd_lt (a b : Nat) (ha : a < GOLDILOCKS_PRIME) (hb : b < GOLDILOCKS_PRIME) :
    (u32OverflowingSub a b).2 < GOLDILOCKS_PRIME := by
  unfold u32OverflowingSub
  split
  · -- a >= b case: result is a - b
    simp; omega
  · -- a < b case: result is u32Max - b + a
    simp [u32Max, GOLDILOCKS_PRIME] at *; omega

-- ============================================================================
-- Main proof: u64_wrapping_sub_correct
-- ============================================================================

set_option maxHeartbeats 8000000 in
theorem u64_wrapping_sub_correct
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest) :
    exec 20 s Miden.Core.Math.U64.wrapping_sub =
    some (s.withStack (
      let sub_lo := u32OverflowingSub a_lo.val b_lo.val
      let sub_hi := u32OverflowingSub a_hi.val b_hi.val
      let sub_final := u32OverflowingSub sub_hi.2 sub_lo.1
      Felt.ofNat sub_lo.2 :: Felt.ofNat sub_final.2 :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.Math.U64.wrapping_sub execOps
  simp only [List.foldlM]
  change (do
    let s' ← stepInstruction ⟨b_lo :: b_hi :: a_lo :: a_hi :: rest, mem, locs, adv⟩ (.movup 3)
    let s' ← stepInstruction s' (.movup 3)
    let s' ← stepInstruction s' (.movup 2)
    let s' ← stepInstruction s' (.u32OverflowSub)
    let s' ← stepInstruction s' (.movup 2)
    let s' ← stepInstruction s' (.movup 3)
    let s' ← stepInstruction s' (.u32OverflowSub)
    let s' ← stepInstruction s' (.drop)
    let s' ← stepInstruction s' (.swap 1)
    let s' ← stepInstruction s' (.u32OverflowSub)
    let s' ← stepInstruction s' (.drop)
    let s' ← stepInstruction s' (.swap 1)
    pure s') = _
  -- Step 1: movup 3 → [a_hi, b_lo, b_hi, a_lo, ...rest]
  rw [stepMovup3]; dsimp only [bind, Bind.bind, Option.bind]
  -- Step 2: movup 3 → [a_lo, a_hi, b_lo, b_hi, ...rest]
  rw [stepMovup3]; dsimp only [bind, Bind.bind, Option.bind]
  -- Step 3: movup 2 → [b_lo, a_lo, a_hi, b_hi, ...rest]
  rw [stepMovup2]; dsimp only [bind, Bind.bind, Option.bind]
  -- Step 4: u32OverflowSub (a_lo - b_lo) → [borrow₁, lo_diff, a_hi, b_hi, ...rest]
  rw [stepU32OverflowSub]; dsimp only [bind, Bind.bind, Option.bind]
  -- Step 5: movup 2 → [a_hi, borrow₁, lo_diff, b_hi, ...rest]
  rw [stepMovup2]; dsimp only [bind, Bind.bind, Option.bind]
  -- Step 6: movup 3 → [b_hi, a_hi, borrow₁, lo_diff, ...rest]
  rw [stepMovup3]; dsimp only [bind, Bind.bind, Option.bind]
  -- Step 7: u32OverflowSub (a_hi - b_hi) → [borrow₂, hi_diff₁, borrow₁, lo_diff, ...rest]
  rw [stepU32OverflowSub]; dsimp only [bind, Bind.bind, Option.bind]
  -- Step 8: drop → [hi_diff₁, borrow₁, lo_diff, ...rest]
  rw [stepDrop]; dsimp only [bind, Bind.bind, Option.bind]
  -- Step 9: swap 1 → [borrow₁, hi_diff₁, lo_diff, ...rest]
  rw [stepSwap (hn := by decide) (htop := rfl) (hnth := rfl)]
  dsimp only [bind, Bind.bind, Option.bind, List.set]
  -- Now the third u32OverflowSub operates on Felt.ofNat values.
  -- We need (Felt.ofNat x).val = x for the intermediate values.
  have h_snd_lt : (u32OverflowingSub a_hi.val b_hi.val).2 < GOLDILOCKS_PRIME :=
    u32_overflow_sub_snd_lt _ _ (ZMod.val_lt a_hi) (ZMod.val_lt b_hi)
  have h_fst_lt : (u32OverflowingSub a_lo.val b_lo.val).1 < GOLDILOCKS_PRIME :=
    u32_overflow_sub_fst_lt _ _
  have h_val_snd : (Felt.ofNat (u32OverflowingSub a_hi.val b_hi.val).2).val =
      (u32OverflowingSub a_hi.val b_hi.val).2 :=
    felt_ofNat_val_lt _ h_snd_lt
  have h_val_fst : (Felt.ofNat (u32OverflowingSub a_lo.val b_lo.val).1).val =
      (u32OverflowingSub a_lo.val b_lo.val).1 :=
    felt_ofNat_val_lt _ h_fst_lt
  -- Step 10: u32OverflowSub (hi_diff₁ - borrow₁)
  rw [stepU32OverflowSub]; dsimp only [bind, Bind.bind, Option.bind]
  rw [h_val_snd, h_val_fst]
  -- Step 11: drop
  rw [stepDrop]; dsimp only [bind, Bind.bind, Option.bind]
  -- Step 12: swap 1
  rw [stepSwap (hn := by decide) (htop := rfl) (hnth := rfl)]
  dsimp only [bind, Bind.bind, Option.bind, List.set, pure, Pure.pure]

end MidenLean.Proofs
