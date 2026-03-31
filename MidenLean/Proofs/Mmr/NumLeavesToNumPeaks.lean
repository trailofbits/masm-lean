import MidenLean.Proofs.Tactics
import MidenLean.Generated.Mmr

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

-- ============================================================================
-- Helper: lo32 and hi32 are u32
-- ============================================================================

private theorem lo32_isU32 (a : Felt) : a.lo32.isU32 = true := by
  simp only [Felt.lo32, Felt.isU32, decide_eq_true_eq]
  rw [felt_ofNat_val_lt _ (u32_mod_lt_prime _)]
  exact Nat.mod_lt _ (by decide)

private theorem hi32_isU32 (a : Felt) : a.hi32.isU32 = true := by
  simp only [Felt.hi32, Felt.isU32, decide_eq_true_eq]
  rw [felt_ofNat_val_lt _ (by
    calc a.val / 2 ^ 32 ≤ a.val := Nat.div_le_self _ _
      _ < GOLDILOCKS_PRIME := felt_val_lt_prime a)]
  exact Nat.div_lt_of_lt_mul (by
    calc a.val < GOLDILOCKS_PRIME := felt_val_lt_prime a
      _ < 2 ^ 32 * 2 ^ 32 := by unfold GOLDILOCKS_PRIME; omega)

-- ============================================================================
-- Correctness: num_leaves_to_num_peaks
-- ============================================================================

set_option maxHeartbeats 16000000 in
/-- The MASM `num_leaves_to_num_peaks` procedure correctly computes the number
    of peaks in an MMR by counting the total number of 1-bits in `num_leaves`.
    Input stack:  [n] ++ rest
    Output stack: [popcount(n.lo32) + popcount(n.hi32)] ++ rest
    where lo32 and hi32 are the low and high 32-bit halves of n. -/
theorem num_leaves_to_num_peaks_correct
    (n : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = n :: rest) :
    exec 10 s Miden.Core.Collections.Mmr.num_leaves_to_num_peaks =
    some (s.withStack (
      (Felt.ofNat (u32PopCount n.lo32.val) +
       Felt.ofNat (u32PopCount n.hi32.val)) :: rest)) := by
  -- Setup
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold Miden.Core.Collections.Mmr.num_leaves_to_num_peaks exec execWithEnv
  simp only [List.foldlM]
  -- Step 1: u32split -> [lo32, hi32 | rest]
  miden_step
  -- Step 2: u32popcnt (on lo32)
  have hlo : n.lo32.isU32 = true := lo32_isU32 n
  miden_step
  -- Step 3: swap -> [hi32, popcnt(lo32) | rest]
  miden_step
  -- Step 4: u32popcnt (on hi32)
  have hhi : n.hi32.isU32 = true := hi32_isU32 n
  miden_step
  -- Step 5: add -> [popcnt(lo32) + popcnt(hi32) | rest]
  miden_step
  dsimp only [pure, Pure.pure]

-- ============================================================================
-- Soundness dual: execution success implies correct output
-- ============================================================================

set_option maxHeartbeats 16000000 in
/-- Soundness of `num_leaves_to_num_peaks`: if execution succeeds, then the input
    was a single felt and the output is its total popcount. Note: u32split accepts
    ANY felt, and lo32/hi32 are always u32, so u32popcnt always succeeds.
    This procedure has NO precondition — it succeeds on all inputs. -/
theorem num_leaves_to_num_peaks_sound
    (s s' : MidenState)
    (h : exec 10 s Miden.Core.Collections.Mmr.num_leaves_to_num_peaks = some s') :
    ∃ n rest,
      s.stack = n :: rest
      ∧ s' = s.withStack (
        (Felt.ofNat (u32PopCount n.lo32.val) +
         Felt.ofNat (u32PopCount n.hi32.val)) :: rest) := by
  unfold exec Miden.Core.Collections.Mmr.num_leaves_to_num_peaks execWithEnv at h
  simp only [List.foldlM] at h
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at h ⊢
  match stk with
  | [] => simp [execInstruction, execU32Split] at h
  | n :: rest =>
    refine ⟨n, rest, rfl, ?_⟩
    have hc := num_leaves_to_num_peaks_correct n rest
      ⟨n :: rest, mem, locs, adv⟩ rfl
    unfold exec Miden.Core.Collections.Mmr.num_leaves_to_num_peaks execWithEnv at hc
    simp only [List.foldlM, MidenState.withStack] at hc
    rw [hc] at h
    exact (Option.some.inj h).symm

end MidenLean.Proofs
