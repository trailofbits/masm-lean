import MidenLean.Proofs.U256.Common
import MidenLean.Proofs.Tactics

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

-- ============================================================================
-- Helper lemmas
-- ============================================================================

private theorem u32OverflowingSub_identity (a b : Nat) (hb : b < 2^32) :
    (u32OverflowingSub a b).2 + b = a + (u32OverflowingSub a b).1 * 2^32 := by
  unfold u32OverflowingSub u32Max; split <;> omega

private theorem u32OverflowingSub_fst_le_one (a b : Nat) :
    (u32OverflowingSub a b).1 ≤ 1 := by
  unfold u32OverflowingSub; split <;> omega

private theorem u32OverflowingSub_snd_lt (a b : Nat) (ha : a < 2^32) (hb : b < 2^32) :
    (u32OverflowingSub a b).2 < 2^32 := by
  unfold u32OverflowingSub u32Max; split <;> omega

private theorem u32OverflowingSub_fst_val (a b : Nat) :
    (Felt.ofNat (u32OverflowingSub a b).1).val = (u32OverflowingSub a b).1 := by
  apply felt_ofNat_val_lt; unfold u32OverflowingSub GOLDILOCKS_PRIME; split <;> omega

/-- Felt.ofNat a + Felt.ofNat b = Felt.ofNat (a + b) when the sum is small. -/
private theorem felt_ofNat_add_eq (a b : Nat) (h : a + b < GOLDILOCKS_PRIME) :
    Felt.ofNat a + Felt.ofNat b = Felt.ofNat (a + b) := by
  have ha : a < GOLDILOCKS_PRIME := by omega
  have hb : b < GOLDILOCKS_PRIME := by omega
  apply ZMod.val_injective
  rw [felt_add_val_no_wrap _ _ (by rw [felt_ofNat_val_lt _ ha, felt_ofNat_val_lt _ hb]; exact h),
      felt_ofNat_val_lt _ ha, felt_ofNat_val_lt _ hb, felt_ofNat_val_lt _ h]

-- ============================================================================
-- Local step lemma for u32OverflowSub
-- ============================================================================

set_option maxHeartbeats 4000000 in
private theorem stepU32OverflowSubLocal (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, frames, adv⟩ .u32OverflowSub =
    some ⟨Felt.ofNat (u32OverflowingSub a.val b.val).1 ::
          Felt.ofNat (u32OverflowingSub a.val b.val).2 ::
          rest, mem, frames, adv⟩ := by
  unfold execInstruction execU32OverflowSub
  simp [ha, hb, Concrete.State.withStack]

-- ============================================================================
-- Chunk definitions
-- ============================================================================

private def swb_chunk1 : List Op := [
  .inst (.swapw 3), .inst (.movup 3), .inst (.movup 7), .inst .u32OverflowSub,
  .inst (.movup 7), .inst .u32WidenAdd, .inst (.movup 5), .inst (.swap 1),
  .inst .u32OverflowSub, .inst (.movup 2), .inst .add
]

private def swb_chunk2 : List Op := [
  .inst (.movup 6), .inst .u32WidenAdd, .inst (.movup 5), .inst (.swap 1),
  .inst .u32OverflowSub, .inst (.movup 2), .inst .add,
  .inst (.movup 5), .inst .u32WidenAdd, .inst (.movup 5), .inst (.swap 1),
  .inst .u32OverflowSub, .inst (.movup 2), .inst .add
]

private def swb_chunk3 : List Op := [
  .inst (.movup 12), .inst .u32WidenAdd, .inst (.movup 9), .inst (.swap 1),
  .inst .u32OverflowSub, .inst (.movup 2), .inst .add,
  .inst (.movup 11), .inst .u32WidenAdd, .inst (.movup 9), .inst (.swap 1),
  .inst .u32OverflowSub, .inst (.movup 2), .inst .add
]

private def swb_chunk4 : List Op := [
  .inst (.movup 10), .inst .u32WidenAdd, .inst (.movup 9), .inst (.swap 1),
  .inst .u32OverflowSub, .inst (.movup 2), .inst .add,
  .inst (.movup 9), .inst .u32WidenAdd, .inst (.movup 9), .inst (.swap 1),
  .inst .u32OverflowSub, .inst (.movup 2), .inst .add
]

private theorem swb_decomp :
    Miden.Core.U256.sub_with_borrow_be.body =
    swb_chunk1 ++ (swb_chunk2 ++ (swb_chunk3 ++ swb_chunk4)) := by
  simp [Miden.Core.U256.sub_with_borrow_be, swb_chunk1, swb_chunk2, swb_chunk3, swb_chunk4]

-- ============================================================================
-- Per-iteration borrow bound helper
-- ============================================================================

/-- After one subtraction iteration with borrow, the output borrow is ≤ 1. -/
private theorem borrow_iter_le_one (a_i b_i borrow_in : Nat)
    (ha : a_i < 2^32) (hb : b_i < 2^32) (hc : borrow_in ≤ 1) :
    (borrow_in + b_i) / 2^32 +
      (u32OverflowingSub a_i ((borrow_in + b_i) % 2^32)).1 ≤ 1 := by
  have hfst := u32OverflowingSub_fst_le_one a_i ((borrow_in + b_i) % 2^32)
  have hhi : (borrow_in + b_i) / 2^32 ≤ 1 := by omega
  by_cases hhi1 : (borrow_in + b_i) / 2^32 = 1
  · have hmod : (borrow_in + b_i) % 2^32 = 0 := by omega
    rw [hmod]; unfold u32OverflowingSub; split <;> omega
  · omega

-- ============================================================================
-- Chunk correctness lemmas
-- ============================================================================

set_option maxHeartbeats 4000000 in
private theorem swb_chunk1_correct
    (env : ProcEnv) (fuel : Nat)
    (b7 b6 b5 b4 b3 b2 b1 b0 a7 a6 a5 a4 a3 a2 a1 a0 : Felt)
    (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true) :
    let borrow₀ := (u32OverflowingSub a0.val b0.val).1
    let d₀ := (u32OverflowingSub a0.val b0.val).2
    let wb₁ := borrow₀ + b1.val
    let lo₁ := wb₁ % 2^32
    let hi₁ := wb₁ / 2^32
    let sub_borrow₁ := (u32OverflowingSub a1.val lo₁).1
    let d₁ := (u32OverflowingSub a1.val lo₁).2
    let borrow₁ := hi₁ + sub_borrow₁
    execProcedure env (fuel + 1)
      ⟨b7 :: b6 :: b5 :: b4 :: b3 :: b2 :: b1 :: b0 ::
       a7 :: a6 :: a5 :: a4 :: a3 :: a2 :: a1 :: a0 :: rest, mem, frames, adv⟩
      swb_chunk1 =
    some ⟨Felt.ofNat borrow₁ ::
          Felt.ofNat d₁ :: Felt.ofNat d₀ ::
          a3 :: a2 :: b3 :: b2 ::
          a7 :: a6 :: a5 :: a4 :: b7 :: b6 :: b5 :: b4 :: rest,
          mem, frames, adv⟩ := by
  have ha0_lt : a0.val < 2^32 := by simpa [Felt.isU32, decide_eq_true_eq] using ha0
  have ha1_lt : a1.val < 2^32 := by simpa [Felt.isU32, decide_eq_true_eq] using ha1
  have hb1_lt : b1.val < 2^32 := by simpa [Felt.isU32, decide_eq_true_eq] using hb1
  have hborrow0_isU32 : (Felt.ofNat (u32OverflowingSub a0.val b0.val).1).isU32 = true :=
    u32OverflowingSub_fst_isU32 _ _
  have hborrow0_val : (Felt.ofNat (u32OverflowingSub a0.val b0.val).1).val =
      (u32OverflowingSub a0.val b0.val).1 := u32OverflowingSub_fst_val _ _
  have hlo1_isU32 : (Felt.ofNat (((u32OverflowingSub a0.val b0.val).1 + b1.val) % 2^32)).isU32 = true :=
    felt_ofNat_isU32_of_lt _ (Nat.mod_lt _ (by positivity))
  have hlo1_val : (Felt.ofNat (((u32OverflowingSub a0.val b0.val).1 + b1.val) % 2^32)).val =
      ((u32OverflowingSub a0.val b0.val).1 + b1.val) % 2^32 :=
    felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)
  unfold swb_chunk1 execProcedure
  simp only [List.foldlM]
  rw [stepSwapw3]; miden_bind
  miden_movup; miden_movup
  rw [stepU32OverflowSubLocal (ha := ha0) (hb := hb0)]; miden_bind
  miden_movup
  rw [stepU32WidenAdd (ha := hborrow0_isU32) (hb := hb1)]; miden_bind
  rw [hborrow0_val]
  miden_movup; miden_swap
  rw [stepU32OverflowSubLocal (ha := ha1) (hb := hlo1_isU32)]; miden_bind
  rw [hlo1_val]
  miden_movup
  rw [stepAdd]; miden_bind
  simp only [pure, Pure.pure]
  congr 1; congr 1; congr 1
  rw [add_comm]
  apply felt_ofNat_add_eq
  unfold GOLDILOCKS_PRIME
  have := u32OverflowingSub_fst_le_one a0.val b0.val
  have := u32OverflowingSub_fst_le_one a1.val (((u32OverflowingSub a0.val b0.val).1 + b1.val) % 2^32)
  omega

set_option maxHeartbeats 4000000 in
private theorem swb_chunk2_correct
    (env : ProcEnv) (fuel : Nat)
    (borrow_in prev1 prev0 x3 x2 y3 y2 z0 z1 z2 z3 w0 w1 w2 w3 : Felt)
    (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (hbin : borrow_in.isU32 = true) (hbin_le : borrow_in.val ≤ 1)
    (hx2 : x2.isU32 = true) (hy2 : y2.isU32 = true)
    (hx3 : x3.isU32 = true) (hy3 : y3.isU32 = true) :
    let wb₂ := borrow_in.val + y2.val
    let lo₂ := wb₂ % 2^32
    let borrow₂ := wb₂ / 2^32 + (u32OverflowingSub x2.val lo₂).1
    let d₂ := (u32OverflowingSub x2.val lo₂).2
    let wb₃ := borrow₂ + y3.val
    let lo₃ := wb₃ % 2^32
    let borrow₃ := wb₃ / 2^32 + (u32OverflowingSub x3.val lo₃).1
    let d₃ := (u32OverflowingSub x3.val lo₃).2
    execProcedure env (fuel + 1)
      ⟨borrow_in :: prev1 :: prev0 :: x3 :: x2 :: y3 :: y2 :: z0 :: z1 :: z2 :: z3 ::
       w0 :: w1 :: w2 :: w3 :: rest, mem, frames, adv⟩
      swb_chunk2 =
    some ⟨Felt.ofNat borrow₃ ::
          Felt.ofNat d₃ :: Felt.ofNat d₂ :: prev1 :: prev0 ::
          z0 :: z1 :: z2 :: z3 :: w0 :: w1 :: w2 :: w3 :: rest,
          mem, frames, adv⟩ := by
  have hx2_lt : x2.val < 2^32 := by simpa [Felt.isU32, decide_eq_true_eq] using hx2
  have hy2_lt : y2.val < 2^32 := by simpa [Felt.isU32, decide_eq_true_eq] using hy2
  have hx3_lt : x3.val < 2^32 := by simpa [Felt.isU32, decide_eq_true_eq] using hx3
  have hy3_lt : y3.val < 2^32 := by simpa [Felt.isU32, decide_eq_true_eq] using hy3
  -- lo₂ isU32
  have hlo2_isU32 : (Felt.ofNat ((borrow_in.val + y2.val) % 2^32)).isU32 = true :=
    felt_ofNat_isU32_of_lt _ (Nat.mod_lt _ (by positivity))
  have hlo2_val : (Felt.ofNat ((borrow_in.val + y2.val) % 2^32)).val =
      (borrow_in.val + y2.val) % 2^32 :=
    felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)
  -- borrow₂ facts
  set borrow₂ := (borrow_in.val + y2.val) / 2^32 +
      (u32OverflowingSub x2.val ((borrow_in.val + y2.val) % 2^32)).1
  have hborrow2_le : borrow₂ ≤ 1 := borrow_iter_le_one _ _ _ hx2_lt hy2_lt hbin_le
  have hborrow2_isU32 : (Felt.ofNat borrow₂).isU32 = true :=
    felt_ofNat_isU32_of_lt _ (by omega)
  have hborrow2_val : (Felt.ofNat borrow₂).val = borrow₂ :=
    felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)
  have hborrow2_add :
      Felt.ofNat (u32OverflowingSub x2.val ((borrow_in.val + y2.val) % 2^32)).1 +
      Felt.ofNat ((borrow_in.val + y2.val) / 2^32) =
      Felt.ofNat borrow₂ := by
    rw [add_comm]; apply felt_ofNat_add_eq; unfold GOLDILOCKS_PRIME; omega
  -- lo₃ isU32
  have hlo3_isU32 : (Felt.ofNat ((borrow₂ + y3.val) % 2^32)).isU32 = true :=
    felt_ofNat_isU32_of_lt _ (Nat.mod_lt _ (by positivity))
  have hlo3_val : (Felt.ofNat ((borrow₂ + y3.val) % 2^32)).val =
      (borrow₂ + y3.val) % 2^32 :=
    felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)
  unfold swb_chunk2 execProcedure
  simp only [List.foldlM]
  -- Limb 2
  miden_movup
  rw [stepU32WidenAdd (ha := hbin) (hb := hy2)]; miden_bind
  miden_movup; miden_swap
  rw [stepU32OverflowSubLocal (ha := hx2) (hb := hlo2_isU32)]; miden_bind
  rw [hlo2_val]
  miden_movup
  rw [stepAdd]; miden_bind
  -- Limb 3
  rw [show Felt.ofNat (u32OverflowingSub x2.val ((borrow_in.val + y2.val) % 2 ^ 32)).1 +
      Felt.ofNat ((borrow_in.val + y2.val) / 2 ^ 32) =
      Felt.ofNat borrow₂ from hborrow2_add]
  miden_movup
  rw [stepU32WidenAdd (ha := hborrow2_isU32) (hb := hy3)]; miden_bind
  rw [hborrow2_val]
  miden_movup; miden_swap
  rw [stepU32OverflowSubLocal (ha := hx3) (hb := hlo3_isU32)]; miden_bind
  rw [hlo3_val]
  miden_movup
  rw [stepAdd]; miden_bind
  simp only [pure, Pure.pure]
  congr 1; congr 1; congr 1
  rw [add_comm]
  apply felt_ofNat_add_eq; unfold GOLDILOCKS_PRIME
  have := borrow_iter_le_one x3.val y3.val borrow₂ hx3_lt hy3_lt hborrow2_le
  omega

set_option maxHeartbeats 4000000 in
private theorem swb_chunk3_correct
    (env : ProcEnv) (fuel : Nat)
    (borrow_in prev3 prev2 prev1 prev0 z0 z1 z2 z3 w0 w1 w2 w3 : Felt)
    (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (hbin : borrow_in.isU32 = true) (hbin_le : borrow_in.val ≤ 1)
    (hz3 : z3.isU32 = true) (hw3 : w3.isU32 = true)
    (hz2 : z2.isU32 = true) (hw2 : w2.isU32 = true) :
    let wb₄ := borrow_in.val + w3.val
    let lo₄ := wb₄ % 2^32
    let borrow₄ := wb₄ / 2^32 + (u32OverflowingSub z3.val lo₄).1
    let d₄ := (u32OverflowingSub z3.val lo₄).2
    let wb₅ := borrow₄ + w2.val
    let lo₅ := wb₅ % 2^32
    let borrow₅ := wb₅ / 2^32 + (u32OverflowingSub z2.val lo₅).1
    let d₅ := (u32OverflowingSub z2.val lo₅).2
    execProcedure env (fuel + 1)
      ⟨borrow_in :: prev3 :: prev2 :: prev1 :: prev0 ::
       z0 :: z1 :: z2 :: z3 :: w0 :: w1 :: w2 :: w3 :: rest, mem, frames, adv⟩
      swb_chunk3 =
    some ⟨Felt.ofNat borrow₅ ::
          Felt.ofNat d₅ :: Felt.ofNat d₄ ::
          prev3 :: prev2 :: prev1 :: prev0 ::
          z0 :: z1 :: w0 :: w1 :: rest,
          mem, frames, adv⟩ := by
  have hz3_lt : z3.val < 2^32 := by simpa [Felt.isU32, decide_eq_true_eq] using hz3
  have hw3_lt : w3.val < 2^32 := by simpa [Felt.isU32, decide_eq_true_eq] using hw3
  have hz2_lt : z2.val < 2^32 := by simpa [Felt.isU32, decide_eq_true_eq] using hz2
  have hw2_lt : w2.val < 2^32 := by simpa [Felt.isU32, decide_eq_true_eq] using hw2
  have hlo4_isU32 : (Felt.ofNat ((borrow_in.val + w3.val) % 2^32)).isU32 = true :=
    felt_ofNat_isU32_of_lt _ (Nat.mod_lt _ (by positivity))
  have hlo4_val : (Felt.ofNat ((borrow_in.val + w3.val) % 2^32)).val =
      (borrow_in.val + w3.val) % 2^32 :=
    felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)
  set borrow₄ := (borrow_in.val + w3.val) / 2^32 +
      (u32OverflowingSub z3.val ((borrow_in.val + w3.val) % 2^32)).1
  have hborrow4_le : borrow₄ ≤ 1 := borrow_iter_le_one _ _ _ hz3_lt hw3_lt hbin_le
  have hborrow4_isU32 : (Felt.ofNat borrow₄).isU32 = true :=
    felt_ofNat_isU32_of_lt _ (by omega)
  have hborrow4_val : (Felt.ofNat borrow₄).val = borrow₄ :=
    felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)
  have hborrow4_add :
      Felt.ofNat (u32OverflowingSub z3.val ((borrow_in.val + w3.val) % 2^32)).1 +
      Felt.ofNat ((borrow_in.val + w3.val) / 2^32) =
      Felt.ofNat borrow₄ := by
    rw [add_comm]; apply felt_ofNat_add_eq; unfold GOLDILOCKS_PRIME; omega
  have hlo5_isU32 : (Felt.ofNat ((borrow₄ + w2.val) % 2^32)).isU32 = true :=
    felt_ofNat_isU32_of_lt _ (Nat.mod_lt _ (by positivity))
  have hlo5_val : (Felt.ofNat ((borrow₄ + w2.val) % 2^32)).val =
      (borrow₄ + w2.val) % 2^32 :=
    felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)
  unfold swb_chunk3 execProcedure
  simp only [List.foldlM]
  miden_movup
  rw [stepU32WidenAdd (ha := hbin) (hb := hw3)]; miden_bind
  miden_movup; miden_swap
  rw [stepU32OverflowSubLocal (ha := hz3) (hb := hlo4_isU32)]; miden_bind
  rw [hlo4_val]
  miden_movup
  rw [stepAdd]; miden_bind
  rw [show Felt.ofNat (u32OverflowingSub z3.val ((borrow_in.val + w3.val) % 2 ^ 32)).1 +
      Felt.ofNat ((borrow_in.val + w3.val) / 2 ^ 32) =
      Felt.ofNat borrow₄ from hborrow4_add]
  miden_movup
  rw [stepU32WidenAdd (ha := hborrow4_isU32) (hb := hw2)]; miden_bind
  rw [hborrow4_val]
  miden_movup; miden_swap
  rw [stepU32OverflowSubLocal (ha := hz2) (hb := hlo5_isU32)]; miden_bind
  rw [hlo5_val]
  miden_movup
  rw [stepAdd]; miden_bind
  simp only [pure, Pure.pure]
  congr 1; congr 1; congr 1
  rw [add_comm]
  apply felt_ofNat_add_eq; unfold GOLDILOCKS_PRIME
  have := borrow_iter_le_one z2.val w2.val borrow₄ hz2_lt hw2_lt hborrow4_le
  omega

set_option maxHeartbeats 4000000 in
private theorem swb_chunk4_correct
    (env : ProcEnv) (fuel : Nat)
    (borrow_in prev5 prev4 prev3 prev2 prev1 prev0 z0 z1 w0 w1 : Felt)
    (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (hbin : borrow_in.isU32 = true) (hbin_le : borrow_in.val ≤ 1)
    (hz1 : z1.isU32 = true) (hw1 : w1.isU32 = true)
    (hz0 : z0.isU32 = true) (hw0 : w0.isU32 = true) :
    let wb₆ := borrow_in.val + w1.val
    let lo₆ := wb₆ % 2^32
    let borrow₆ := wb₆ / 2^32 + (u32OverflowingSub z1.val lo₆).1
    let d₆ := (u32OverflowingSub z1.val lo₆).2
    let wb₇ := borrow₆ + w0.val
    let lo₇ := wb₇ % 2^32
    let borrow₇ := wb₇ / 2^32 + (u32OverflowingSub z0.val lo₇).1
    let d₇ := (u32OverflowingSub z0.val lo₇).2
    execProcedure env (fuel + 1)
      ⟨borrow_in :: prev5 :: prev4 :: prev3 :: prev2 :: prev1 :: prev0 ::
       z0 :: z1 :: w0 :: w1 :: rest, mem, frames, adv⟩
      swb_chunk4 =
    some ⟨Felt.ofNat borrow₇ ::
          Felt.ofNat d₇ :: Felt.ofNat d₆ ::
          prev5 :: prev4 :: prev3 :: prev2 :: prev1 :: prev0 :: rest,
          mem, frames, adv⟩ := by
  have hz1_lt : z1.val < 2^32 := by simpa [Felt.isU32, decide_eq_true_eq] using hz1
  have hw1_lt : w1.val < 2^32 := by simpa [Felt.isU32, decide_eq_true_eq] using hw1
  have hz0_lt : z0.val < 2^32 := by simpa [Felt.isU32, decide_eq_true_eq] using hz0
  have hw0_lt : w0.val < 2^32 := by simpa [Felt.isU32, decide_eq_true_eq] using hw0
  have hlo6_isU32 : (Felt.ofNat ((borrow_in.val + w1.val) % 2^32)).isU32 = true :=
    felt_ofNat_isU32_of_lt _ (Nat.mod_lt _ (by positivity))
  have hlo6_val : (Felt.ofNat ((borrow_in.val + w1.val) % 2^32)).val =
      (borrow_in.val + w1.val) % 2^32 :=
    felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)
  set borrow₆ := (borrow_in.val + w1.val) / 2^32 +
      (u32OverflowingSub z1.val ((borrow_in.val + w1.val) % 2^32)).1
  have hborrow6_le : borrow₆ ≤ 1 := borrow_iter_le_one _ _ _ hz1_lt hw1_lt hbin_le
  have hborrow6_isU32 : (Felt.ofNat borrow₆).isU32 = true :=
    felt_ofNat_isU32_of_lt _ (by omega)
  have hborrow6_val : (Felt.ofNat borrow₆).val = borrow₆ :=
    felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)
  have hborrow6_add :
      Felt.ofNat (u32OverflowingSub z1.val ((borrow_in.val + w1.val) % 2^32)).1 +
      Felt.ofNat ((borrow_in.val + w1.val) / 2^32) =
      Felt.ofNat borrow₆ := by
    rw [add_comm]; apply felt_ofNat_add_eq; unfold GOLDILOCKS_PRIME; omega
  have hlo7_isU32 : (Felt.ofNat ((borrow₆ + w0.val) % 2^32)).isU32 = true :=
    felt_ofNat_isU32_of_lt _ (Nat.mod_lt _ (by positivity))
  have hlo7_val : (Felt.ofNat ((borrow₆ + w0.val) % 2^32)).val =
      (borrow₆ + w0.val) % 2^32 :=
    felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)
  unfold swb_chunk4 execProcedure
  simp only [List.foldlM]
  miden_movup
  rw [stepU32WidenAdd (ha := hbin) (hb := hw1)]; miden_bind
  miden_movup; miden_swap
  rw [stepU32OverflowSubLocal (ha := hz1) (hb := hlo6_isU32)]; miden_bind
  rw [hlo6_val]
  miden_movup
  rw [stepAdd]; miden_bind
  rw [show Felt.ofNat (u32OverflowingSub z1.val ((borrow_in.val + w1.val) % 2 ^ 32)).1 +
      Felt.ofNat ((borrow_in.val + w1.val) / 2 ^ 32) =
      Felt.ofNat borrow₆ from hborrow6_add]
  miden_movup
  rw [stepU32WidenAdd (ha := hborrow6_isU32) (hb := hw0)]; miden_bind
  rw [hborrow6_val]
  miden_movup; miden_swap
  rw [stepU32OverflowSubLocal (ha := hz0) (hb := hlo7_isU32)]; miden_bind
  rw [hlo7_val]
  miden_movup
  rw [stepAdd]; miden_bind
  simp only [pure, Pure.pure]
  congr 1; congr 1; congr 1
  rw [add_comm]
  apply felt_ofNat_add_eq; unfold GOLDILOCKS_PRIME
  have := borrow_iter_le_one z0.val w0.val borrow₆ hz0_lt hw0_lt hborrow6_le
  omega

-- ============================================================================
-- Borrow chain bridging lemma
-- ============================================================================

private theorem borrow_chain_eq_sub
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Nat)
    (d0 d1 d2 d3 d4 d5 d6 d7 : Nat)
    (c0 c1 c2 c3 c4 c5 c6 c7 : Nat)
    (h0 : d0 + b0 = a0 + c0 * 2^32)
    (h1 : d1 + b1 + c0 = a1 + c1 * 2^32)
    (h2 : d2 + b2 + c1 = a2 + c2 * 2^32)
    (h3 : d3 + b3 + c2 = a3 + c3 * 2^32)
    (h4 : d4 + b4 + c3 = a4 + c4 * 2^32)
    (h5 : d5 + b5 + c4 = a5 + c5 * 2^32)
    (h6 : d6 + b6 + c5 = a6 + c6 * 2^32)
    (h7 : d7 + b7 + c6 = a7 + c7 * 2^32) :
    (d7 * 2^224 + d6 * 2^192 + d5 * 2^160 + d4 * 2^128 +
     d3 * 2^96 + d2 * 2^64 + d1 * 2^32 + d0) +
    (b7 * 2^224 + b6 * 2^192 + b5 * 2^160 + b4 * 2^128 +
     b3 * 2^96 + b2 * 2^64 + b1 * 2^32 + b0) =
    (a7 * 2^224 + a6 * 2^192 + a5 * 2^160 + a4 * 2^128 +
     a3 * 2^96 + a2 * 2^64 + a1 * 2^32 + a0) +
    c7 * 2^256 := by omega

/-- Convert borrow chain identity to digit_extraction input form. -/
private theorem chain_to_extraction (a b : U256)
    (d₀ d₁ d₂ d₃ d₄ d₅ d₆ d₇ borrow₇ : Nat)
    (hchain : (d₇ * 2^224 + d₆ * 2^192 + d₅ * 2^160 + d₄ * 2^128 +
              d₃ * 2^96 + d₂ * 2^64 + d₁ * 2^32 + d₀) +
             (b.a7.val.val * 2^224 + b.a6.val.val * 2^192 + b.a5.val.val * 2^160 +
              b.a4.val.val * 2^128 + b.a3.val.val * 2^96 + b.a2.val.val * 2^64 +
              b.a1.val.val * 2^32 + b.a0.val.val) =
             (a.a7.val.val * 2^224 + a.a6.val.val * 2^192 + a.a5.val.val * 2^160 +
              a.a4.val.val * 2^128 + a.a3.val.val * 2^96 + a.a2.val.val * 2^64 +
              a.a1.val.val * 2^32 + a.a0.val.val) +
             borrow₇ * 2^256)
    (hc_le : borrow₇ ≤ 1) :
    (1 - borrow₇) * 2^256 +
    (d₇ * 2^224 + d₆ * 2^192 + d₅ * 2^160 + d₄ * 2^128 +
     d₃ * 2^96 + d₂ * 2^64 + d₁ * 2^32 + d₀) =
    a.toNat + 2^256 - b.toNat := by
  simp only [U256.toNat]
  have := a.toNat_lt; have := b.toNat_lt
  simp only [U256.toNat] at this
  omega

/-- Digit extraction: given carry * 2^256 + digits = total with each digit < 2^32,
    each digit equals the corresponding extraction from total. -/
private theorem digit_extraction
    (carry d7 d6 d5 d4 d3 d2 d1 d0 total : Nat)
    (h0 : d0 < 2^32) (h1 : d1 < 2^32) (h2 : d2 < 2^32) (h3 : d3 < 2^32)
    (h4 : d4 < 2^32) (h5 : d5 < 2^32) (h6 : d6 < 2^32) (h7 : d7 < 2^32)
    (hchain : carry * 2^256 +
              (d7 * 2^224 + d6 * 2^192 + d5 * 2^160 + d4 * 2^128 +
               d3 * 2^96 + d2 * 2^64 + d1 * 2^32 + d0) = total) :
    carry = total / 2^256 ∧
    d7 = (total / 2^224) % 2^32 ∧
    d6 = (total / 2^192) % 2^32 ∧
    d5 = (total / 2^160) % 2^32 ∧
    d4 = (total / 2^128) % 2^32 ∧
    d3 = (total / 2^96) % 2^32 ∧
    d2 = (total / 2^64) % 2^32 ∧
    d1 = (total / 2^32) % 2^32 ∧
    d0 = total % 2^32 := by
  constructor; · omega
  constructor; · omega
  constructor; · omega
  constructor; · omega
  constructor; · omega
  constructor; · omega
  constructor; · omega
  constructor; · omega
  omega

-- ============================================================================
-- Per-limb identity helper
-- ============================================================================

private theorem sub_limb_identity (a b borrow_in : Nat) :
    (u32OverflowingSub a ((borrow_in + b) % 2^32)).2 + b + borrow_in =
    a + ((borrow_in + b) / 2^32 + (u32OverflowingSub a ((borrow_in + b) % 2^32)).1) * 2^32 := by
  have hlo_lt : (borrow_in + b) % 2^32 < 2^32 := Nat.mod_lt _ (by positivity)
  have := u32OverflowingSub_identity a ((borrow_in + b) % 2^32) hlo_lt
  omega

-- ============================================================================
-- Raw theorem: chunked composition (digit-extraction form)
-- ============================================================================

set_option maxHeartbeats 8000000 in
/-- `u256::sub_with_borrow_be` raw digit-extraction form.
    Input stack:  [b.a7, ..., b.a0, a.a7, ..., a.a0] ++ rest
    Output stack: [1-s/2^256, (s/2^224)%2^32, ..., s%2^32] ++ rest
    where s = a.toNat + 2^256 - b.toNat. -/
private theorem u256_sub_with_borrow_be_raw
    (a b : U256) (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) :
    execProcedure u256ProcEnv (fuel + 1)
      ⟨b.a7.val :: b.a6.val :: b.a5.val :: b.a4.val ::
       b.a3.val :: b.a2.val :: b.a1.val :: b.a0.val ::
       a.a7.val :: a.a6.val :: a.a5.val :: a.a4.val ::
       a.a3.val :: a.a2.val :: a.a1.val :: a.a0.val :: rest, mem, frames, adv⟩
      Miden.Core.U256.sub_with_borrow_be =
    some ⟨Felt.ofNat (1 - (a.toNat + 2^256 - b.toNat) / 2^256) ::
          Felt.ofNat (((a.toNat + 2^256 - b.toNat) / 2^224) % 2^32) ::
          Felt.ofNat (((a.toNat + 2^256 - b.toNat) / 2^192) % 2^32) ::
          Felt.ofNat (((a.toNat + 2^256 - b.toNat) / 2^160) % 2^32) ::
          Felt.ofNat (((a.toNat + 2^256 - b.toNat) / 2^128) % 2^32) ::
          Felt.ofNat (((a.toNat + 2^256 - b.toNat) / 2^96) % 2^32)  ::
          Felt.ofNat (((a.toNat + 2^256 - b.toNat) / 2^64) % 2^32)  ::
          Felt.ofNat (((a.toNat + 2^256 - b.toNat) / 2^32) % 2^32)  ::
          Felt.ofNat ((a.toNat + 2^256 - b.toNat) % 2^32) :: rest,
          mem, frames, adv⟩ := by
  -- Decompose procedure into chunks
  rw [execProcedure_body_eq _ _ _ _ _ swb_decomp rfl, execProcedure_append]
  -- Define borrow₀
  set borrow₀ := (u32OverflowingSub a.a0.val.val b.a0.val.val).1
  have hborrow0_le : borrow₀ ≤ 1 := u32OverflowingSub_fst_le_one _ _
  -- Chunk 1
  rw [swb_chunk1_correct (ha0 := a.a0_isU32) (ha1 := a.a1_isU32)
      (hb0 := b.a0_isU32) (hb1 := b.a1_isU32)]
  simp only [bind, Bind.bind, Option.bind]
  -- Define borrow₁
  set borrow₁ := (borrow₀ + b.a1.val.val) / 2^32 +
    (u32OverflowingSub a.a1.val.val ((borrow₀ + b.a1.val.val) % 2^32)).1
  have hborrow1_le : borrow₁ ≤ 1 :=
    borrow_iter_le_one _ _ _ a.a1.val_lt b.a1.val_lt hborrow0_le
  have hborrow1_isU32 : (Felt.ofNat borrow₁).isU32 = true :=
    felt_ofNat_isU32_of_lt _ (by omega)
  have hborrow1_val : (Felt.ofNat borrow₁).val = borrow₁ :=
    felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)
  -- Chunk 2
  rw [execProcedure_append]
  rw [swb_chunk2_correct (hbin := hborrow1_isU32) (hbin_le := by rw [hborrow1_val]; exact hborrow1_le)
      (hx2 := a.a2_isU32) (hy2 := b.a2_isU32)
      (hx3 := a.a3_isU32) (hy3 := b.a3_isU32)]
  simp only [bind, Bind.bind, Option.bind]
  conv_lhs => rw [hborrow1_val]
  set borrow₂ := (borrow₁ + b.a2.val.val) / 2^32 +
    (u32OverflowingSub a.a2.val.val ((borrow₁ + b.a2.val.val) % 2^32)).1
  have hborrow2_le : borrow₂ ≤ 1 :=
    borrow_iter_le_one _ _ _ a.a2.val_lt b.a2.val_lt hborrow1_le
  set borrow₃ := (borrow₂ + b.a3.val.val) / 2^32 +
    (u32OverflowingSub a.a3.val.val ((borrow₂ + b.a3.val.val) % 2^32)).1
  have hborrow3_le : borrow₃ ≤ 1 :=
    borrow_iter_le_one _ _ _ a.a3.val_lt b.a3.val_lt hborrow2_le
  have hborrow3_isU32 : (Felt.ofNat borrow₃).isU32 = true :=
    felt_ofNat_isU32_of_lt _ (by omega)
  have hborrow3_val : (Felt.ofNat borrow₃).val = borrow₃ :=
    felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)
  -- Chunk 3
  rw [execProcedure_append]
  rw [swb_chunk3_correct (hbin := hborrow3_isU32) (hbin_le := by rw [hborrow3_val]; exact hborrow3_le)
      (hz3 := a.a4_isU32) (hw3 := b.a4_isU32)
      (hz2 := a.a5_isU32) (hw2 := b.a5_isU32)]
  simp only [bind, Bind.bind, Option.bind]
  conv_lhs => rw [hborrow3_val]
  set borrow₄ := (borrow₃ + b.a4.val.val) / 2^32 +
    (u32OverflowingSub a.a4.val.val ((borrow₃ + b.a4.val.val) % 2^32)).1
  have hborrow4_le : borrow₄ ≤ 1 :=
    borrow_iter_le_one _ _ _ a.a4.val_lt b.a4.val_lt hborrow3_le
  set borrow₅ := (borrow₄ + b.a5.val.val) / 2^32 +
    (u32OverflowingSub a.a5.val.val ((borrow₄ + b.a5.val.val) % 2^32)).1
  have hborrow5_le : borrow₅ ≤ 1 :=
    borrow_iter_le_one _ _ _ a.a5.val_lt b.a5.val_lt hborrow4_le
  have hborrow5_isU32 : (Felt.ofNat borrow₅).isU32 = true :=
    felt_ofNat_isU32_of_lt _ (by omega)
  have hborrow5_val : (Felt.ofNat borrow₅).val = borrow₅ :=
    felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)
  -- Chunk 4
  rw [swb_chunk4_correct (hbin := hborrow5_isU32) (hbin_le := by rw [hborrow5_val]; exact hborrow5_le)
      (hz1 := a.a6_isU32) (hw1 := b.a6_isU32)
      (hz0 := a.a7_isU32) (hw0 := b.a7_isU32)]
  conv_lhs => rw [hborrow5_val]
  -- Define remaining borrows and digit values
  set borrow₆ := (borrow₅ + b.a6.val.val) / 2^32 +
    (u32OverflowingSub a.a6.val.val ((borrow₅ + b.a6.val.val) % 2^32)).1
  set borrow₇ := (borrow₆ + b.a7.val.val) / 2^32 +
    (u32OverflowingSub a.a7.val.val ((borrow₆ + b.a7.val.val) % 2^32)).1
  set d₀ := (u32OverflowingSub a.a0.val.val b.a0.val.val).2
  set d₁ := (u32OverflowingSub a.a1.val.val ((borrow₀ + b.a1.val.val) % 2^32)).2
  set d₂ := (u32OverflowingSub a.a2.val.val ((borrow₁ + b.a2.val.val) % 2^32)).2
  set d₃ := (u32OverflowingSub a.a3.val.val ((borrow₂ + b.a3.val.val) % 2^32)).2
  set d₄ := (u32OverflowingSub a.a4.val.val ((borrow₃ + b.a4.val.val) % 2^32)).2
  set d₅ := (u32OverflowingSub a.a5.val.val ((borrow₄ + b.a5.val.val) % 2^32)).2
  set d₆ := (u32OverflowingSub a.a6.val.val ((borrow₅ + b.a6.val.val) % 2^32)).2
  set d₇ := (u32OverflowingSub a.a7.val.val ((borrow₆ + b.a7.val.val) % 2^32)).2
  -- Per-limb identities
  have hlimb0 := u32OverflowingSub_identity a.a0.val.val b.a0.val.val b.a0.val_lt
  have hlimb1 := sub_limb_identity a.a1.val.val b.a1.val.val borrow₀
  have hlimb2 := sub_limb_identity a.a2.val.val b.a2.val.val borrow₁
  have hlimb3 := sub_limb_identity a.a3.val.val b.a3.val.val borrow₂
  have hlimb4 := sub_limb_identity a.a4.val.val b.a4.val.val borrow₃
  have hlimb5 := sub_limb_identity a.a5.val.val b.a5.val.val borrow₄
  have hlimb6 := sub_limb_identity a.a6.val.val b.a6.val.val borrow₅
  have hlimb7 := sub_limb_identity a.a7.val.val b.a7.val.val borrow₆
  -- Borrow chain identity: result + b.toNat = a.toNat + borrow₇ * 2^256
  have hchain := borrow_chain_eq_sub
    a.a0.val.val a.a1.val.val a.a2.val.val a.a3.val.val
    a.a4.val.val a.a5.val.val a.a6.val.val a.a7.val.val
    b.a0.val.val b.a1.val.val b.a2.val.val b.a3.val.val
    b.a4.val.val b.a5.val.val b.a6.val.val b.a7.val.val
    d₀ d₁ d₂ d₃ d₄ d₅ d₆ d₇
    borrow₀ borrow₁ borrow₂ borrow₃ borrow₄ borrow₅ borrow₆ borrow₇
    hlimb0 hlimb1 hlimb2 hlimb3 hlimb4 hlimb5 hlimb6 hlimb7
  -- Convert chain to extraction form using helper
  have hborrow7_le : borrow₇ ≤ 1 :=
    borrow_iter_le_one _ _ _ a.a7.val_lt b.a7.val_lt
      (borrow_iter_le_one _ _ _ a.a6.val_lt b.a6.val_lt hborrow5_le)
  have hconv := chain_to_extraction a b d₀ d₁ d₂ d₃ d₄ d₅ d₆ d₇ borrow₇ hchain hborrow7_le
  -- Digit extraction
  have hdigits := digit_extraction (1 - borrow₇)
    d₇ d₆ d₅ d₄ d₃ d₂ d₁ d₀
    (a.toNat + 2^256 - b.toNat)
    (u32OverflowingSub_snd_lt _ _ a.a0.val_lt b.a0.val_lt)
    (u32OverflowingSub_snd_lt _ _ a.a1.val_lt (Nat.mod_lt _ (by norm_num)))
    (u32OverflowingSub_snd_lt _ _ a.a2.val_lt (Nat.mod_lt _ (by norm_num)))
    (u32OverflowingSub_snd_lt _ _ a.a3.val_lt (Nat.mod_lt _ (by norm_num)))
    (u32OverflowingSub_snd_lt _ _ a.a4.val_lt (Nat.mod_lt _ (by norm_num)))
    (u32OverflowingSub_snd_lt _ _ a.a5.val_lt (Nat.mod_lt _ (by norm_num)))
    (u32OverflowingSub_snd_lt _ _ a.a6.val_lt (Nat.mod_lt _ (by norm_num)))
    (u32OverflowingSub_snd_lt _ _ a.a7.val_lt (Nat.mod_lt _ (by norm_num)))
    hconv
  obtain ⟨hdc, hd7, hd6, hd5, hd4, hd3, hd2, hd1, hd0⟩ := hdigits
  have hborrow7_eq : borrow₇ = 1 - (a.toNat + 2^256 - b.toNat) / 2^256 := by omega
  simp only [hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hborrow7_eq]

-- ============================================================================
-- Main theorem: high-level correctness
-- ============================================================================

/-- `u256::sub_with_borrow_be` subtracts two big-endian 256-bit values with borrow propagation.
    Input stack:  [b.a7, ..., b.a0, a.a7, ..., a.a0] ++ rest
    Output stack: [borrow, (a-b).a7, ..., (a-b).a0] ++ rest
    where borrow = 1 if a < b (underflow occurred), 0 otherwise. -/
theorem u256_sub_with_borrow_be_correct
    (a b : U256) (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) :
    execProcedure u256ProcEnv (fuel + 1)
      ⟨b.a7.val :: b.a6.val :: b.a5.val :: b.a4.val ::
       b.a3.val :: b.a2.val :: b.a1.val :: b.a0.val ::
       a.a7.val :: a.a6.val :: a.a5.val :: a.a4.val ::
       a.a3.val :: a.a2.val :: a.a1.val :: a.a0.val :: rest, mem, frames, adv⟩
      Miden.Core.U256.sub_with_borrow_be =
    some ⟨Felt.ofNat (if a.toNat < b.toNat then 1 else 0) ::
          (a - b).a7.val :: (a - b).a6.val :: (a - b).a5.val :: (a - b).a4.val ::
          (a - b).a3.val :: (a - b).a2.val :: (a - b).a1.val :: (a - b).a0.val :: rest,
          mem, frames, adv⟩ := by
  rw [u256_sub_with_borrow_be_raw a b rest mem frames adv fuel]
  have hborrow : 1 - (a.toNat + 2^256 - b.toNat) / 2^256 =
      if a.toNat < b.toNat then 1 else 0 := by
    have := a.toNat_lt; have := b.toNat_lt
    by_cases h : a.toNat < b.toNat <;> simp [h] <;> omega
  rw [hborrow]
  simp only [HSub.hSub, Sub.sub, U256.ofNat_a0, U256.ofNat_a1, U256.ofNat_a2,
             U256.ofNat_a3, U256.ofNat_a4, U256.ofNat_a5, U256.ofNat_a6, U256.ofNat_a7]

end MidenLean.Proofs
