import MidenLean.Proofs.U256.Common
import MidenLean.Proofs.Tactics

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

-- ============================================================================
-- Helper step lemmas for subtraction
-- ============================================================================

set_option maxHeartbeats 4000000 in
private theorem stepU32OverflowSub' (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, frames, adv⟩ .u32OverflowSub =
    some ⟨Felt.ofNat (u32OverflowingSub a.val b.val).1 ::
          Felt.ofNat (u32OverflowingSub a.val b.val).2 ::
          rest, mem, frames, adv⟩ := by
  unfold execInstruction execU32OverflowSub
  simp [ha, hb, MidenState.withStack]

set_option maxHeartbeats 4000000 in
private theorem stepU32WidenAdd' (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, frames, adv⟩ .u32WidenAdd =
    some ⟨Felt.ofNat ((a.val + b.val) % 2^32) ::
          Felt.ofNat ((a.val + b.val) / 2^32) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execU32WidenAdd u32WideAdd u32Max
  simp [ha, hb, MidenState.withStack]

private theorem stepSwapw3' (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 : Felt) (rest : List Felt) :
    execInstruction ⟨a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
        c0 :: c1 :: c2 :: c3 :: d0 :: d1 :: d2 :: d3 :: rest, mem, frames, adv⟩ (.swapw 3) =
      some ⟨d0 :: d1 :: d2 :: d3 :: b0 :: b1 :: b2 :: b3 ::
        c0 :: c1 :: c2 :: c3 :: a0 :: a1 :: a2 :: a3 :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execSwapw; simp [MidenState.withStack]

-- ============================================================================
-- Chunk definitions
-- ============================================================================

/-- Chunk 1: swapw3, movup3, movup7, u32OverflowSub — first subtraction (a0 - b0). -/
private def swb_chunk1 : List Op := [
  .inst (.swapw 3), .inst (.movup 3), .inst (.movup 7), .inst .u32OverflowSub
]

/-- Chunk 2: borrow propagation + subtraction for limb 1. -/
private def swb_chunk2 : List Op := [
  .inst (.movup 7), .inst .u32WidenAdd, .inst (.movup 5), .inst (.swap 1),
  .inst .u32OverflowSub, .inst (.movup 2), .inst .add
]

/-- Chunk 3: borrow propagation + subtraction for limb 2. -/
private def swb_chunk3 : List Op := [
  .inst (.movup 6), .inst .u32WidenAdd, .inst (.movup 5), .inst (.swap 1),
  .inst .u32OverflowSub, .inst (.movup 2), .inst .add
]

/-- Chunk 4: borrow propagation + subtraction for limb 3. -/
private def swb_chunk4 : List Op := [
  .inst (.movup 5), .inst .u32WidenAdd, .inst (.movup 5), .inst (.swap 1),
  .inst .u32OverflowSub, .inst (.movup 2), .inst .add
]

/-- Chunk 5: borrow propagation + subtraction for limb 4 (transition). -/
private def swb_chunk5 : List Op := [
  .inst (.movup 12), .inst .u32WidenAdd, .inst (.movup 9), .inst (.swap 1),
  .inst .u32OverflowSub, .inst (.movup 2), .inst .add
]

/-- Chunk 6: borrow propagation + subtraction for limb 5. -/
private def swb_chunk6 : List Op := [
  .inst (.movup 11), .inst .u32WidenAdd, .inst (.movup 9), .inst (.swap 1),
  .inst .u32OverflowSub, .inst (.movup 2), .inst .add
]

/-- Chunk 7: borrow propagation + subtraction for limb 6. -/
private def swb_chunk7 : List Op := [
  .inst (.movup 10), .inst .u32WidenAdd, .inst (.movup 9), .inst (.swap 1),
  .inst .u32OverflowSub, .inst (.movup 2), .inst .add
]

/-- Chunk 8: borrow propagation + subtraction for limb 7 (final). -/
private def swb_chunk8 : List Op := [
  .inst (.movup 9), .inst .u32WidenAdd, .inst (.movup 9), .inst (.swap 1),
  .inst .u32OverflowSub, .inst (.movup 2), .inst .add
]

/-- The procedure body decomposes into the eight chunks. -/
private theorem swb_decomp :
    Miden.Core.U256.sub_with_borrow_be.body =
    swb_chunk1 ++ (swb_chunk2 ++ (swb_chunk3 ++ (swb_chunk4 ++
    (swb_chunk5 ++ (swb_chunk6 ++ (swb_chunk7 ++ swb_chunk8)))))) := by
  simp [Miden.Core.U256.sub_with_borrow_be, swb_chunk1, swb_chunk2, swb_chunk3, swb_chunk4,
        swb_chunk5, swb_chunk6, swb_chunk7, swb_chunk8]

-- ============================================================================
-- Key helper: Felt.ofNat val recovery for mod values
-- ============================================================================

private theorem felt_ofNat_mod_val (a b : Nat) (ha : a < GOLDILOCKS_PRIME) (hb : b < GOLDILOCKS_PRIME) :
    (Felt.ofNat ((a + b) % 2^32)).val = (a + b) % 2^32 :=
  felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME at *; omega)

-- ============================================================================
-- Chunk correctness lemmas
-- ============================================================================

set_option maxHeartbeats 4000000 in
private theorem swb_chunk1_correct
    (env : ProcEnv) (fuel : Nat)
    (b7 b6 b5 b4 b3 b2 b1 b0 a7 a6 a5 a4 a3 a2 a1 a0 : Felt)
    (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (ha0 : a0.isU32 = true) (hb0 : b0.isU32 = true) :
    execWithEnv env (fuel + 1)
      ⟨b7 :: b6 :: b5 :: b4 :: b3 :: b2 :: b1 :: b0 ::
       a7 :: a6 :: a5 :: a4 :: a3 :: a2 :: a1 :: a0 :: rest, mem, frames, adv⟩
      swb_chunk1 =
    some ⟨Felt.ofNat (u32OverflowingSub a0.val b0.val).1 ::
          Felt.ofNat (u32OverflowingSub a0.val b0.val).2 ::
          a3 :: a2 :: a1 :: b3 :: b2 :: b1 ::
          a7 :: a6 :: a5 :: a4 :: b7 :: b6 :: b5 :: b4 :: rest,
          mem, frames, adv⟩ := by
  unfold swb_chunk1 execWithEnv
  simp only [List.foldlM]
  rw [stepSwapw3']; miden_bind
  miden_movup; miden_movup
  rw [stepU32OverflowSub' (ha := ha0) (hb := hb0)]; miden_bind
  simp only [pure, Pure.pure]

set_option maxHeartbeats 8000000 in
private theorem swb_chunk2_correct
    (env : ProcEnv) (fuel : Nat)
    (bor0 d0 a3 a2 a1 b3 b2 b1 a7 a6 a5 a4 b7 b6 b5 b4 : Felt)
    (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (hbor0 : bor0.isU32 = true) (hb1 : b1.isU32 = true) (ha1 : a1.isU32 = true)
    (hba1_lo : (Felt.ofNat ((bor0.val + b1.val) % 2^32)).isU32 = true) :
    let ba1_lo := (bor0.val + b1.val) % 2^32
    let ba1_hi := (bor0.val + b1.val) / 2^32
    let sub1 := u32OverflowingSub a1.val ba1_lo
    execWithEnv env (fuel + 1)
      ⟨bor0 :: d0 :: a3 :: a2 :: a1 :: b3 :: b2 :: b1 ::
       a7 :: a6 :: a5 :: a4 :: b7 :: b6 :: b5 :: b4 :: rest, mem, frames, adv⟩
      swb_chunk2 =
    some ⟨(Felt.ofNat sub1.1 + Felt.ofNat ba1_hi) ::
          Felt.ofNat sub1.2 :: d0 :: a3 :: a2 :: b3 :: b2 ::
          a7 :: a6 :: a5 :: a4 :: b7 :: b6 :: b5 :: b4 :: rest,
          mem, frames, adv⟩ := by
  have hbor0_val : bor0.val < GOLDILOCKS_PRIME := felt_val_lt_prime bor0
  have hb1_val : b1.val < GOLDILOCKS_PRIME := felt_val_lt_prime b1
  have hmod_val : (Felt.ofNat ((bor0.val + b1.val) % 2^32)).val = (bor0.val + b1.val) % 2^32 :=
    felt_ofNat_mod_val _ _ hbor0_val hb1_val
  unfold swb_chunk2 execWithEnv
  simp only [List.foldlM]
  miden_movup
  rw [stepU32WidenAdd' (ha := hbor0) (hb := hb1)]; miden_bind
  miden_movup; miden_swap
  rw [stepU32OverflowSub' (ha := ha1) (hb := hba1_lo)]; miden_bind
  rw [hmod_val]
  miden_movup
  rw [stepAdd]; miden_bind
  simp only [pure, Pure.pure]

set_option maxHeartbeats 8000000 in
private theorem swb_chunk3_correct
    (env : ProcEnv) (fuel : Nat)
    (bor_in d1 d0 a3 a2 b3 b2 a7 a6 a5 a4 b7 b6 b5 b4 : Felt)
    (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (hbor_in : bor_in.isU32 = true) (hb2 : b2.isU32 = true) (ha2 : a2.isU32 = true)
    (hba2_lo : (Felt.ofNat ((bor_in.val + b2.val) % 2^32)).isU32 = true) :
    let ba2_lo := (bor_in.val + b2.val) % 2^32
    let ba2_hi := (bor_in.val + b2.val) / 2^32
    let sub2 := u32OverflowingSub a2.val ba2_lo
    execWithEnv env (fuel + 1)
      ⟨bor_in :: d1 :: d0 :: a3 :: a2 :: b3 :: b2 ::
       a7 :: a6 :: a5 :: a4 :: b7 :: b6 :: b5 :: b4 :: rest, mem, frames, adv⟩
      swb_chunk3 =
    some ⟨(Felt.ofNat sub2.1 + Felt.ofNat ba2_hi) ::
          Felt.ofNat sub2.2 :: d1 :: d0 :: a3 :: b3 ::
          a7 :: a6 :: a5 :: a4 :: b7 :: b6 :: b5 :: b4 :: rest,
          mem, frames, adv⟩ := by
  have hbor_val : bor_in.val < GOLDILOCKS_PRIME := felt_val_lt_prime bor_in
  have hb2_val : b2.val < GOLDILOCKS_PRIME := felt_val_lt_prime b2
  have hmod_val : (Felt.ofNat ((bor_in.val + b2.val) % 2^32)).val = (bor_in.val + b2.val) % 2^32 :=
    felt_ofNat_mod_val _ _ hbor_val hb2_val
  unfold swb_chunk3 execWithEnv
  simp only [List.foldlM]
  miden_movup
  rw [stepU32WidenAdd' (ha := hbor_in) (hb := hb2)]; miden_bind
  miden_movup; miden_swap
  rw [stepU32OverflowSub' (ha := ha2) (hb := hba2_lo)]; miden_bind
  rw [hmod_val]
  miden_movup
  rw [stepAdd]; miden_bind
  simp only [pure, Pure.pure]

set_option maxHeartbeats 8000000 in
private theorem swb_chunk4_correct
    (env : ProcEnv) (fuel : Nat)
    (bor_in d2 d1 d0 a3 b3 a7 a6 a5 a4 b7 b6 b5 b4 : Felt)
    (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (hbor_in : bor_in.isU32 = true) (hb3 : b3.isU32 = true) (ha3 : a3.isU32 = true)
    (hba3_lo : (Felt.ofNat ((bor_in.val + b3.val) % 2^32)).isU32 = true) :
    let ba3_lo := (bor_in.val + b3.val) % 2^32
    let ba3_hi := (bor_in.val + b3.val) / 2^32
    let sub3 := u32OverflowingSub a3.val ba3_lo
    execWithEnv env (fuel + 1)
      ⟨bor_in :: d2 :: d1 :: d0 :: a3 :: b3 ::
       a7 :: a6 :: a5 :: a4 :: b7 :: b6 :: b5 :: b4 :: rest, mem, frames, adv⟩
      swb_chunk4 =
    some ⟨(Felt.ofNat sub3.1 + Felt.ofNat ba3_hi) ::
          Felt.ofNat sub3.2 :: d2 :: d1 :: d0 ::
          a7 :: a6 :: a5 :: a4 :: b7 :: b6 :: b5 :: b4 :: rest,
          mem, frames, adv⟩ := by
  have hbor_val : bor_in.val < GOLDILOCKS_PRIME := felt_val_lt_prime bor_in
  have hb3_val : b3.val < GOLDILOCKS_PRIME := felt_val_lt_prime b3
  have hmod_val : (Felt.ofNat ((bor_in.val + b3.val) % 2^32)).val = (bor_in.val + b3.val) % 2^32 :=
    felt_ofNat_mod_val _ _ hbor_val hb3_val
  unfold swb_chunk4 execWithEnv
  simp only [List.foldlM]
  miden_movup
  rw [stepU32WidenAdd' (ha := hbor_in) (hb := hb3)]; miden_bind
  miden_movup; miden_swap
  rw [stepU32OverflowSub' (ha := ha3) (hb := hba3_lo)]; miden_bind
  rw [hmod_val]
  miden_movup
  rw [stepAdd]; miden_bind
  simp only [pure, Pure.pure]

set_option maxHeartbeats 8000000 in
private theorem swb_chunk5_correct
    (env : ProcEnv) (fuel : Nat)
    (bor_in d3 d2 d1 d0 a7 a6 a5 a4 b7 b6 b5 b4 : Felt)
    (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (hbor_in : bor_in.isU32 = true) (hb4 : b4.isU32 = true) (ha4 : a4.isU32 = true)
    (hba4_lo : (Felt.ofNat ((bor_in.val + b4.val) % 2^32)).isU32 = true) :
    let ba4_lo := (bor_in.val + b4.val) % 2^32
    let ba4_hi := (bor_in.val + b4.val) / 2^32
    let sub4 := u32OverflowingSub a4.val ba4_lo
    execWithEnv env (fuel + 1)
      ⟨bor_in :: d3 :: d2 :: d1 :: d0 ::
       a7 :: a6 :: a5 :: a4 :: b7 :: b6 :: b5 :: b4 :: rest, mem, frames, adv⟩
      swb_chunk5 =
    some ⟨(Felt.ofNat sub4.1 + Felt.ofNat ba4_hi) ::
          Felt.ofNat sub4.2 :: d3 :: d2 :: d1 :: d0 ::
          a7 :: a6 :: a5 :: b7 :: b6 :: b5 :: rest,
          mem, frames, adv⟩ := by
  have hbor_val : bor_in.val < GOLDILOCKS_PRIME := felt_val_lt_prime bor_in
  have hb4_val : b4.val < GOLDILOCKS_PRIME := felt_val_lt_prime b4
  have hmod_val : (Felt.ofNat ((bor_in.val + b4.val) % 2^32)).val = (bor_in.val + b4.val) % 2^32 :=
    felt_ofNat_mod_val _ _ hbor_val hb4_val
  unfold swb_chunk5 execWithEnv
  simp only [List.foldlM]
  miden_movup
  rw [stepU32WidenAdd' (ha := hbor_in) (hb := hb4)]; miden_bind
  miden_movup; miden_swap
  rw [stepU32OverflowSub' (ha := ha4) (hb := hba4_lo)]; miden_bind
  rw [hmod_val]
  miden_movup
  rw [stepAdd]; miden_bind
  simp only [pure, Pure.pure]

set_option maxHeartbeats 8000000 in
private theorem swb_chunk6_correct
    (env : ProcEnv) (fuel : Nat)
    (bor_in d4 d3 d2 d1 d0 a7 a6 a5 b7 b6 b5 : Felt)
    (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (hbor_in : bor_in.isU32 = true) (hb5 : b5.isU32 = true) (ha5 : a5.isU32 = true)
    (hba5_lo : (Felt.ofNat ((bor_in.val + b5.val) % 2^32)).isU32 = true) :
    let ba5_lo := (bor_in.val + b5.val) % 2^32
    let ba5_hi := (bor_in.val + b5.val) / 2^32
    let sub5 := u32OverflowingSub a5.val ba5_lo
    execWithEnv env (fuel + 1)
      ⟨bor_in :: d4 :: d3 :: d2 :: d1 :: d0 ::
       a7 :: a6 :: a5 :: b7 :: b6 :: b5 :: rest, mem, frames, adv⟩
      swb_chunk6 =
    some ⟨(Felt.ofNat sub5.1 + Felt.ofNat ba5_hi) ::
          Felt.ofNat sub5.2 :: d4 :: d3 :: d2 :: d1 :: d0 ::
          a7 :: a6 :: b7 :: b6 :: rest,
          mem, frames, adv⟩ := by
  have hbor_val : bor_in.val < GOLDILOCKS_PRIME := felt_val_lt_prime bor_in
  have hb5_val : b5.val < GOLDILOCKS_PRIME := felt_val_lt_prime b5
  have hmod_val : (Felt.ofNat ((bor_in.val + b5.val) % 2^32)).val = (bor_in.val + b5.val) % 2^32 :=
    felt_ofNat_mod_val _ _ hbor_val hb5_val
  unfold swb_chunk6 execWithEnv
  simp only [List.foldlM]
  miden_movup
  rw [stepU32WidenAdd' (ha := hbor_in) (hb := hb5)]; miden_bind
  miden_movup; miden_swap
  rw [stepU32OverflowSub' (ha := ha5) (hb := hba5_lo)]; miden_bind
  rw [hmod_val]
  miden_movup
  rw [stepAdd]; miden_bind
  simp only [pure, Pure.pure]

set_option maxHeartbeats 8000000 in
private theorem swb_chunk7_correct
    (env : ProcEnv) (fuel : Nat)
    (bor_in d5 d4 d3 d2 d1 d0 a7 a6 b7 b6 : Felt)
    (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (hbor_in : bor_in.isU32 = true) (hb6 : b6.isU32 = true) (ha6 : a6.isU32 = true)
    (hba6_lo : (Felt.ofNat ((bor_in.val + b6.val) % 2^32)).isU32 = true) :
    let ba6_lo := (bor_in.val + b6.val) % 2^32
    let ba6_hi := (bor_in.val + b6.val) / 2^32
    let sub6 := u32OverflowingSub a6.val ba6_lo
    execWithEnv env (fuel + 1)
      ⟨bor_in :: d5 :: d4 :: d3 :: d2 :: d1 :: d0 ::
       a7 :: a6 :: b7 :: b6 :: rest, mem, frames, adv⟩
      swb_chunk7 =
    some ⟨(Felt.ofNat sub6.1 + Felt.ofNat ba6_hi) ::
          Felt.ofNat sub6.2 :: d5 :: d4 :: d3 :: d2 :: d1 :: d0 ::
          a7 :: b7 :: rest,
          mem, frames, adv⟩ := by
  have hbor_val : bor_in.val < GOLDILOCKS_PRIME := felt_val_lt_prime bor_in
  have hb6_val : b6.val < GOLDILOCKS_PRIME := felt_val_lt_prime b6
  have hmod_val : (Felt.ofNat ((bor_in.val + b6.val) % 2^32)).val = (bor_in.val + b6.val) % 2^32 :=
    felt_ofNat_mod_val _ _ hbor_val hb6_val
  unfold swb_chunk7 execWithEnv
  simp only [List.foldlM]
  miden_movup
  rw [stepU32WidenAdd' (ha := hbor_in) (hb := hb6)]; miden_bind
  miden_movup; miden_swap
  rw [stepU32OverflowSub' (ha := ha6) (hb := hba6_lo)]; miden_bind
  rw [hmod_val]
  miden_movup
  rw [stepAdd]; miden_bind
  simp only [pure, Pure.pure]

set_option maxHeartbeats 8000000 in
private theorem swb_chunk8_correct
    (env : ProcEnv) (fuel : Nat)
    (bor_in d6 d5 d4 d3 d2 d1 d0 a7 b7 : Felt)
    (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (hbor_in : bor_in.isU32 = true) (hb7 : b7.isU32 = true) (ha7 : a7.isU32 = true)
    (hba7_lo : (Felt.ofNat ((bor_in.val + b7.val) % 2^32)).isU32 = true) :
    let ba7_lo := (bor_in.val + b7.val) % 2^32
    let ba7_hi := (bor_in.val + b7.val) / 2^32
    let sub7 := u32OverflowingSub a7.val ba7_lo
    execWithEnv env (fuel + 1)
      ⟨bor_in :: d6 :: d5 :: d4 :: d3 :: d2 :: d1 :: d0 ::
       a7 :: b7 :: rest, mem, frames, adv⟩
      swb_chunk8 =
    some ⟨(Felt.ofNat sub7.1 + Felt.ofNat ba7_hi) ::
          Felt.ofNat sub7.2 :: d6 :: d5 :: d4 :: d3 :: d2 :: d1 :: d0 :: rest,
          mem, frames, adv⟩ := by
  have hbor_val : bor_in.val < GOLDILOCKS_PRIME := felt_val_lt_prime bor_in
  have hb7_val : b7.val < GOLDILOCKS_PRIME := felt_val_lt_prime b7
  have hmod_val : (Felt.ofNat ((bor_in.val + b7.val) % 2^32)).val = (bor_in.val + b7.val) % 2^32 :=
    felt_ofNat_mod_val _ _ hbor_val hb7_val
  unfold swb_chunk8 execWithEnv
  simp only [List.foldlM]
  miden_movup
  rw [stepU32WidenAdd' (ha := hbor_in) (hb := hb7)]; miden_bind
  miden_movup; miden_swap
  rw [stepU32OverflowSub' (ha := ha7) (hb := hba7_lo)]; miden_bind
  rw [hmod_val]
  miden_movup
  rw [stepAdd]; miden_bind
  simp only [pure, Pure.pure]

-- ============================================================================
-- Borrow bound lemma: combined borrow is always 0 or 1
-- ============================================================================

/-- For a single limb subtraction step, the combined borrow (sub_borrow + carry)
    is at most 1. This is because when carry = 1 (b + borrow >= 2^32),
    then lo = 0, so sub_borrow = 0. -/
private theorem combined_borrow_le_one (ak bk borrow : Nat)
    (hak : ak < 2^32) (hbk : bk < 2^32) (hbor : borrow ≤ 1) :
    (u32OverflowingSub ak ((borrow + bk) % 2^32)).1 + (borrow + bk) / 2^32 ≤ 1 := by
  unfold u32OverflowingSub u32Max
  split <;> omega

/-- The initial borrow from u32OverflowingSub is 0 or 1. -/
private theorem initial_borrow_le_one (a b : Nat) :
    (u32OverflowingSub a b).1 ≤ 1 := by
  unfold u32OverflowingSub; split <;> omega

-- ============================================================================
-- Borrow chain bridging lemma
-- ============================================================================

/-- Key identity for each limb: a_k + borrow_k * 2^32 = diff_k + b_k + borrow_{k-1}
    when borrow is computed via u32WidenAdd + u32OverflowSub + add. -/
private theorem limb_identity (ak bk borrow_in : Nat)
    (hak : ak < 2^32) (hbk : bk < 2^32) (hbor : borrow_in ≤ 1) :
    let ba_lo := (borrow_in + bk) % 2^32
    let ba_hi := (borrow_in + bk) / 2^32
    let sub := u32OverflowingSub ak ba_lo
    let borrow_out := sub.1 + ba_hi
    ak + borrow_out * 2^32 = sub.2 + bk + borrow_in := by
  simp only []
  unfold u32OverflowingSub u32Max
  split <;> omega

/-- Key identity for limb 0 (no incoming borrow):
    a0 + borrow0 * 2^32 = diff0 + b0 -/
private theorem limb0_identity (a0 b0 : Nat)
    (ha0 : a0 < 2^32) (hb0 : b0 < 2^32) :
    a0 + (u32OverflowingSub a0 b0).1 * 2^32 = (u32OverflowingSub a0 b0).2 + b0 := by
  unfold u32OverflowingSub u32Max; split <;> omega

set_option maxHeartbeats 16000000 in
/-- The borrow chain computes the limb decomposition of a + borrow_final * 2^256 = D + B,
    where D = sum of diff limbs and B = sum of b limbs.
    This means D = A - B + borrow_final * 2^256, giving us a - b mod 2^256. -/
private theorem borrow_chain_identity
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Nat)
    (ha0 : a0 < 2^32) (ha1 : a1 < 2^32) (ha2 : a2 < 2^32) (ha3 : a3 < 2^32)
    (ha4 : a4 < 2^32) (ha5 : a5 < 2^32) (ha6 : a6 < 2^32) (ha7 : a7 < 2^32)
    (hb0 : b0 < 2^32) (hb1 : b1 < 2^32) (hb2 : b2 < 2^32) (hb3 : b3 < 2^32)
    (hb4 : b4 < 2^32) (hb5 : b5 < 2^32) (hb6 : b6 < 2^32) (hb7 : b7 < 2^32) :
    let sub0 := u32OverflowingSub a0 b0
    let bor0 := sub0.1
    let sub1 := u32OverflowingSub a1 ((bor0 + b1) % 2^32)
    let bor1 := sub1.1 + (bor0 + b1) / 2^32
    let sub2 := u32OverflowingSub a2 ((bor1 + b2) % 2^32)
    let bor2 := sub2.1 + (bor1 + b2) / 2^32
    let sub3 := u32OverflowingSub a3 ((bor2 + b3) % 2^32)
    let bor3 := sub3.1 + (bor2 + b3) / 2^32
    let sub4 := u32OverflowingSub a4 ((bor3 + b4) % 2^32)
    let bor4 := sub4.1 + (bor3 + b4) / 2^32
    let sub5 := u32OverflowingSub a5 ((bor4 + b5) % 2^32)
    let bor5 := sub5.1 + (bor4 + b5) / 2^32
    let sub6 := u32OverflowingSub a6 ((bor5 + b6) % 2^32)
    let bor6 := sub6.1 + (bor5 + b6) / 2^32
    let sub7 := u32OverflowingSub a7 ((bor6 + b7) % 2^32)
    let bor7 := sub7.1 + (bor6 + b7) / 2^32
    -- The chain identity:
    (a7 * 2^224 + a6 * 2^192 + a5 * 2^160 + a4 * 2^128 +
     a3 * 2^96 + a2 * 2^64 + a1 * 2^32 + a0) + bor7 * 2^256 =
    (sub7.2 * 2^224 + sub6.2 * 2^192 + sub5.2 * 2^160 + sub4.2 * 2^128 +
     sub3.2 * 2^96 + sub2.2 * 2^64 + sub1.2 * 2^32 + sub0.2) +
    (b7 * 2^224 + b6 * 2^192 + b5 * 2^160 + b4 * 2^128 +
     b3 * 2^96 + b2 * 2^64 + b1 * 2^32 + b0) := by
  simp only []
  -- Name intermediate borrow chain values
  set d0 := (u32OverflowingSub a0 b0).2
  set c0 := (u32OverflowingSub a0 b0).1
  set d1 := (u32OverflowingSub a1 ((c0 + b1) % 2^32)).2
  set sb1 := (u32OverflowingSub a1 ((c0 + b1) % 2^32)).1
  set c1 := sb1 + (c0 + b1) / 2^32
  set d2 := (u32OverflowingSub a2 ((c1 + b2) % 2^32)).2
  set sb2 := (u32OverflowingSub a2 ((c1 + b2) % 2^32)).1
  set c2 := sb2 + (c1 + b2) / 2^32
  set d3 := (u32OverflowingSub a3 ((c2 + b3) % 2^32)).2
  set sb3 := (u32OverflowingSub a3 ((c2 + b3) % 2^32)).1
  set c3 := sb3 + (c2 + b3) / 2^32
  set d4 := (u32OverflowingSub a4 ((c3 + b4) % 2^32)).2
  set sb4 := (u32OverflowingSub a4 ((c3 + b4) % 2^32)).1
  set c4 := sb4 + (c3 + b4) / 2^32
  set d5 := (u32OverflowingSub a5 ((c4 + b5) % 2^32)).2
  set sb5 := (u32OverflowingSub a5 ((c4 + b5) % 2^32)).1
  set c5 := sb5 + (c4 + b5) / 2^32
  set d6 := (u32OverflowingSub a6 ((c5 + b6) % 2^32)).2
  set sb6 := (u32OverflowingSub a6 ((c5 + b6) % 2^32)).1
  set c6 := sb6 + (c5 + b6) / 2^32
  set d7 := (u32OverflowingSub a7 ((c6 + b7) % 2^32)).2
  set sb7 := (u32OverflowingSub a7 ((c6 + b7) % 2^32)).1
  set c7 := sb7 + (c6 + b7) / 2^32
  -- Per-limb identities: a_k + bor_k * 2^32 = d_k + b_k + bor_{k-1}
  have h0 : a0 + c0 * 2^32 = d0 + b0 := limb0_identity a0 b0 ha0 hb0
  have hc0_le := initial_borrow_le_one a0 b0
  have h1 : a1 + c1 * 2^32 = d1 + b1 + c0 := limb_identity a1 b1 c0 ha1 hb1 hc0_le
  have hc1_le := combined_borrow_le_one a1 b1 c0 ha1 hb1 hc0_le
  have h2 : a2 + c2 * 2^32 = d2 + b2 + c1 := limb_identity a2 b2 c1 ha2 hb2 hc1_le
  have hc2_le := combined_borrow_le_one a2 b2 c1 ha2 hb2 hc1_le
  have h3 : a3 + c3 * 2^32 = d3 + b3 + c2 := limb_identity a3 b3 c2 ha3 hb3 hc2_le
  have hc3_le := combined_borrow_le_one a3 b3 c2 ha3 hb3 hc2_le
  have h4 : a4 + c4 * 2^32 = d4 + b4 + c3 := limb_identity a4 b4 c3 ha4 hb4 hc3_le
  have hc4_le := combined_borrow_le_one a4 b4 c3 ha4 hb4 hc3_le
  have h5 : a5 + c5 * 2^32 = d5 + b5 + c4 := limb_identity a5 b5 c4 ha5 hb5 hc4_le
  have hc5_le := combined_borrow_le_one a5 b5 c4 ha5 hb5 hc4_le
  have h6 : a6 + c6 * 2^32 = d6 + b6 + c5 := limb_identity a6 b6 c5 ha6 hb6 hc5_le
  have hc6_le := combined_borrow_le_one a6 b6 c5 ha6 hb6 hc5_le
  have h7 : a7 + c7 * 2^32 = d7 + b7 + c6 := limb_identity a7 b7 c6 ha7 hb7 hc6_le
  -- Use per-limb identities: multiply by 2^(32k) and sum telescopes.
  omega

-- ============================================================================
-- Felt arithmetic bridging: combined borrow Felt values
-- ============================================================================

/-- When the combined borrow b is 0 or 1, Felt.ofNat b1 + Felt.ofNat b2 where b1 + b2 = b
    produces a Felt whose val equals b. Key: when b1 + b2 ≤ 1, the field add doesn't wrap. -/
private theorem felt_add_borrow_val (b1 b2 : Nat)
    (h : b1 + b2 ≤ 1) :
    (Felt.ofNat b1 + Felt.ofNat b2).val = b1 + b2 := by
  have h1 : b1 < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; omega
  have h2 : b2 < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; omega
  rw [felt_add_val_no_wrap]
  · rw [felt_ofNat_val_lt _ h1, felt_ofNat_val_lt _ h2]
  · rw [felt_ofNat_val_lt _ h1, felt_ofNat_val_lt _ h2]
    unfold GOLDILOCKS_PRIME; omega

/-- Combined borrow as Felt is equal to Felt.ofNat of the sum. -/
private theorem felt_add_borrow_eq (b1 b2 : Nat)
    (h : b1 + b2 ≤ 1) :
    Felt.ofNat b1 + Felt.ofNat b2 = Felt.ofNat (b1 + b2) := by
  apply felt_eq_ofNat_of_val_eq
  · exact felt_add_borrow_val b1 b2 h
  · unfold GOLDILOCKS_PRIME; omega

/-- Combined borrow Felt is isU32. -/
private theorem felt_add_borrow_isU32 (b1 b2 : Nat)
    (h : b1 + b2 ≤ 1) :
    (Felt.ofNat b1 + Felt.ofNat b2).isU32 = true := by
  simp only [Felt.isU32, decide_eq_true_eq]
  rw [felt_add_borrow_val b1 b2 h]; omega

-- ============================================================================
-- Main theorem (with corrected borrow convention)
-- ============================================================================

-- ============================================================================
-- Digit extraction for subtraction
-- ============================================================================

/-- Given borrow * 2^256 + D = A, each digit of D equals the corresponding
    digit extraction from A (or equivalently from A + 2^256 - B when
    we know borrow * 2^256 + D = A + 2^256 - B but via the chain identity). -/
private theorem digit_extraction_sub
    (borrow d7 d6 d5 d4 d3 d2 d1 d0 A B : Nat)
    (hd0 : d0 < 2^32) (hd1 : d1 < 2^32) (hd2 : d2 < 2^32) (hd3 : d3 < 2^32)
    (hd4 : d4 < 2^32) (hd5 : d5 < 2^32) (hd6 : d6 < 2^32) (hd7 : d7 < 2^32)
    (hA : A < 2^256) (hB : B < 2^256)
    (hchain : A + borrow * 2^256 =
              (d7 * 2^224 + d6 * 2^192 + d5 * 2^160 + d4 * 2^128 +
               d3 * 2^96 + d2 * 2^64 + d1 * 2^32 + d0) + B) :
    let S := A + 2^256 - B  -- always ≥ 0 since both < 2^256
    borrow = 1 - S / 2^256 ∧
    d7 = (S / 2^224) % 2^32 ∧
    d6 = (S / 2^192) % 2^32 ∧
    d5 = (S / 2^160) % 2^32 ∧
    d4 = (S / 2^128) % 2^32 ∧
    d3 = (S / 2^96) % 2^32 ∧
    d2 = (S / 2^64) % 2^32 ∧
    d1 = (S / 2^32) % 2^32 ∧
    d0 = S % 2^32 := by
  simp only []
  -- From chain: D + B = A + borrow * 2^256
  -- => D = A - B + borrow * 2^256
  -- And A + 2^256 - B = D + (1 - borrow) * 2^256
  -- Since D < 2^256: (A + 2^256 - B) / 2^256 = 1 - borrow, (A + 2^256 - B) % 2^256 = D
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
-- Main theorem (with corrected borrow convention)
-- ============================================================================

set_option maxHeartbeats 32000000 in
/-- `u256::sub_with_borrow_be` subtracts two big-endian 256-bit values with borrow propagation.
    Input stack:  [b.a7, ..., b.a0, a.a7, ..., a.a0] ++ rest  (big-endian limbs)
    Output stack: [borrow, (a-b).a7, ..., (a-b).a0] ++ rest
    where borrow = 1 - (a.toNat + 2^256 - b.toNat) / 2^256  (0 if a >= b, 1 if a < b). -/
theorem u256_sub_with_borrow_be_correct
    (a b : U256) (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) :
    execWithEnv u256ProcEnv (fuel + 1)
      ⟨b.a7.val :: b.a6.val :: b.a5.val :: b.a4.val ::
       b.a3.val :: b.a2.val :: b.a1.val :: b.a0.val ::
       a.a7.val :: a.a6.val :: a.a5.val :: a.a4.val ::
       a.a3.val :: a.a2.val :: a.a1.val :: a.a0.val :: rest, mem, frames, adv⟩
      Miden.Core.U256.sub_with_borrow_be =
    some ⟨Felt.ofNat (1 - (a.toNat + 2^256 - b.toNat) / 2^256) ::
          (a - b).a7.val :: (a - b).a6.val :: (a - b).a5.val :: (a - b).a4.val ::
          (a - b).a3.val :: (a - b).a2.val :: (a - b).a1.val :: (a - b).a0.val :: rest,
          mem, frames, adv⟩ := by
  -- Decompose procedure into chunks
  rw [execWithEnv_body_eq _ _ _ _ _ swb_decomp rfl, execWithEnv_append]
  -- Chunk 1: first subtraction (a0 - b0)
  rw [swb_chunk1_correct (ha0 := a.a0_isU32) (hb0 := b.a0_isU32)]
  simp only [bind, Bind.bind, Option.bind]
  -- Abbreviate borrow chain values after chunk 1
  set sub0 := u32OverflowingSub a.a0.val.val b.a0.val.val
  -- Chunk 2: limb 1
  rw [execWithEnv_append]
  have hbor0_isU32 : (Felt.ofNat sub0.1).isU32 = true := u32OverflowingSub_fst_isU32 _ _
  have hba1_lo_isU32 : (Felt.ofNat (((Felt.ofNat sub0.1).val + b.a1.val.val) % 2^32)).isU32 = true :=
    u32_mod_isU32 _
  rw [swb_chunk2_correct (hbor0 := hbor0_isU32) (hb1 := b.a1_isU32) (ha1 := a.a1_isU32)
      (hba1_lo := hba1_lo_isU32)]
  simp only [bind, Bind.bind, Option.bind]
  -- Recover bor0 value
  have hbor0_val : (Felt.ofNat sub0.1).val = sub0.1 :=
    felt_ofNat_val_lt _ (u32_overflow_sub_fst_lt _ _)
  conv_lhs => rw [hbor0_val]
  set sub1 := u32OverflowingSub a.a1.val.val ((sub0.1 + b.a1.val.val) % 2^32)
  set bor1 := sub1.1 + (sub0.1 + b.a1.val.val) / 2^32
  -- Convert combined borrow to Felt.ofNat
  have hbor1_le : bor1 ≤ 1 := combined_borrow_le_one _ _ _ a.a1.val_lt b.a1.val_lt
    (initial_borrow_le_one _ _)
  rw [felt_add_borrow_eq sub1.1 ((sub0.1 + b.a1.val.val) / 2^32) hbor1_le]
  -- Chunk 3: limb 2
  rw [execWithEnv_append]
  have hbor1_isU32 : (Felt.ofNat bor1).isU32 = true :=
    felt_ofNat_isU32_of_lt _ (by omega)
  have hbor1_val : (Felt.ofNat bor1).val = bor1 :=
    felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)
  have hba2_lo_isU32 : (Felt.ofNat ((bor1 + b.a2.val.val) % 2^32)).isU32 = true :=
    u32_mod_isU32 _
  rw [swb_chunk3_correct (hbor_in := hbor1_isU32) (hb2 := b.a2_isU32) (ha2 := a.a2_isU32)
      (hba2_lo := by rw [show (Felt.ofNat bor1).val = bor1 from hbor1_val]; exact hba2_lo_isU32)]
  simp only [bind, Bind.bind, Option.bind]
  conv_lhs => rw [hbor1_val]
  set sub2 := u32OverflowingSub a.a2.val.val ((bor1 + b.a2.val.val) % 2^32)
  set bor2 := sub2.1 + (bor1 + b.a2.val.val) / 2^32
  have hbor2_le : bor2 ≤ 1 := combined_borrow_le_one _ _ _ a.a2.val_lt b.a2.val_lt hbor1_le
  rw [felt_add_borrow_eq sub2.1 ((bor1 + b.a2.val.val) / 2^32) hbor2_le]
  -- Chunk 4: limb 3
  rw [execWithEnv_append]
  have hbor2_isU32 : (Felt.ofNat bor2).isU32 = true :=
    felt_ofNat_isU32_of_lt _ (by omega)
  have hbor2_val : (Felt.ofNat bor2).val = bor2 :=
    felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)
  have hba3_lo_isU32 : (Felt.ofNat ((bor2 + b.a3.val.val) % 2^32)).isU32 = true :=
    u32_mod_isU32 _
  rw [swb_chunk4_correct (hbor_in := hbor2_isU32) (hb3 := b.a3_isU32) (ha3 := a.a3_isU32)
      (hba3_lo := by rw [show (Felt.ofNat bor2).val = bor2 from hbor2_val]; exact hba3_lo_isU32)]
  simp only [bind, Bind.bind, Option.bind]
  conv_lhs => rw [hbor2_val]
  set sub3 := u32OverflowingSub a.a3.val.val ((bor2 + b.a3.val.val) % 2^32)
  set bor3 := sub3.1 + (bor2 + b.a3.val.val) / 2^32
  have hbor3_le : bor3 ≤ 1 := combined_borrow_le_one _ _ _ a.a3.val_lt b.a3.val_lt hbor2_le
  rw [felt_add_borrow_eq sub3.1 ((bor2 + b.a3.val.val) / 2^32) hbor3_le]
  -- Chunk 5: limb 4 (transition)
  rw [execWithEnv_append]
  have hbor3_isU32 : (Felt.ofNat bor3).isU32 = true :=
    felt_ofNat_isU32_of_lt _ (by omega)
  have hbor3_val : (Felt.ofNat bor3).val = bor3 :=
    felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)
  have hba4_lo_isU32 : (Felt.ofNat ((bor3 + b.a4.val.val) % 2^32)).isU32 = true :=
    u32_mod_isU32 _
  rw [swb_chunk5_correct (hbor_in := hbor3_isU32) (hb4 := b.a4_isU32) (ha4 := a.a4_isU32)
      (hba4_lo := by rw [show (Felt.ofNat bor3).val = bor3 from hbor3_val]; exact hba4_lo_isU32)]
  simp only [bind, Bind.bind, Option.bind]
  conv_lhs => rw [hbor3_val]
  set sub4 := u32OverflowingSub a.a4.val.val ((bor3 + b.a4.val.val) % 2^32)
  set bor4 := sub4.1 + (bor3 + b.a4.val.val) / 2^32
  have hbor4_le : bor4 ≤ 1 := combined_borrow_le_one _ _ _ a.a4.val_lt b.a4.val_lt hbor3_le
  rw [felt_add_borrow_eq sub4.1 ((bor3 + b.a4.val.val) / 2^32) hbor4_le]
  -- Chunk 6: limb 5
  rw [execWithEnv_append]
  have hbor4_isU32 : (Felt.ofNat bor4).isU32 = true :=
    felt_ofNat_isU32_of_lt _ (by omega)
  have hbor4_val : (Felt.ofNat bor4).val = bor4 :=
    felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)
  have hba5_lo_isU32 : (Felt.ofNat ((bor4 + b.a5.val.val) % 2^32)).isU32 = true :=
    u32_mod_isU32 _
  rw [swb_chunk6_correct (hbor_in := hbor4_isU32) (hb5 := b.a5_isU32) (ha5 := a.a5_isU32)
      (hba5_lo := by rw [show (Felt.ofNat bor4).val = bor4 from hbor4_val]; exact hba5_lo_isU32)]
  simp only [bind, Bind.bind, Option.bind]
  conv_lhs => rw [hbor4_val]
  set sub5 := u32OverflowingSub a.a5.val.val ((bor4 + b.a5.val.val) % 2^32)
  set bor5 := sub5.1 + (bor4 + b.a5.val.val) / 2^32
  have hbor5_le : bor5 ≤ 1 := combined_borrow_le_one _ _ _ a.a5.val_lt b.a5.val_lt hbor4_le
  rw [felt_add_borrow_eq sub5.1 ((bor4 + b.a5.val.val) / 2^32) hbor5_le]
  -- Chunk 7: limb 6
  rw [execWithEnv_append]
  have hbor5_isU32 : (Felt.ofNat bor5).isU32 = true :=
    felt_ofNat_isU32_of_lt _ (by omega)
  have hbor5_val : (Felt.ofNat bor5).val = bor5 :=
    felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)
  have hba6_lo_isU32 : (Felt.ofNat ((bor5 + b.a6.val.val) % 2^32)).isU32 = true :=
    u32_mod_isU32 _
  rw [swb_chunk7_correct (hbor_in := hbor5_isU32) (hb6 := b.a6_isU32) (ha6 := a.a6_isU32)
      (hba6_lo := by rw [show (Felt.ofNat bor5).val = bor5 from hbor5_val]; exact hba6_lo_isU32)]
  simp only [bind, Bind.bind, Option.bind]
  conv_lhs => rw [hbor5_val]
  set sub6 := u32OverflowingSub a.a6.val.val ((bor5 + b.a6.val.val) % 2^32)
  set bor6 := sub6.1 + (bor5 + b.a6.val.val) / 2^32
  have hbor6_le : bor6 ≤ 1 := combined_borrow_le_one _ _ _ a.a6.val_lt b.a6.val_lt hbor5_le
  rw [felt_add_borrow_eq sub6.1 ((bor5 + b.a6.val.val) / 2^32) hbor6_le]
  -- Chunk 8: limb 7 (final)
  have hbor6_isU32 : (Felt.ofNat bor6).isU32 = true :=
    felt_ofNat_isU32_of_lt _ (by omega)
  have hbor6_val : (Felt.ofNat bor6).val = bor6 :=
    felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)
  have hba7_lo_isU32 : (Felt.ofNat ((bor6 + b.a7.val.val) % 2^32)).isU32 = true :=
    u32_mod_isU32 _
  rw [swb_chunk8_correct (hbor_in := hbor6_isU32) (hb7 := b.a7_isU32) (ha7 := a.a7_isU32)
      (hba7_lo := by rw [show (Felt.ofNat bor6).val = bor6 from hbor6_val]; exact hba7_lo_isU32)]
  conv_lhs => rw [hbor6_val]
  set sub7 := u32OverflowingSub a.a7.val.val ((bor6 + b.a7.val.val) % 2^32)
  set bor7 := sub7.1 + (bor6 + b.a7.val.val) / 2^32
  have hbor7_le : bor7 ≤ 1 := combined_borrow_le_one _ _ _ a.a7.val_lt b.a7.val_lt hbor6_le
  rw [felt_add_borrow_eq sub7.1 ((bor6 + b.a7.val.val) / 2^32) hbor7_le]
  -- Now we have the raw carry-chain result on the LHS.
  -- Apply the chain identity + digit extraction to relate the borrow chain to the spec.
  have hchain := borrow_chain_identity
    a.a0.val.val a.a1.val.val a.a2.val.val a.a3.val.val
    a.a4.val.val a.a5.val.val a.a6.val.val a.a7.val.val
    b.a0.val.val b.a1.val.val b.a2.val.val b.a3.val.val
    b.a4.val.val b.a5.val.val b.a6.val.val b.a7.val.val
    a.a0.val_lt a.a1.val_lt a.a2.val_lt a.a3.val_lt
    a.a4.val_lt a.a5.val_lt a.a6.val_lt a.a7.val_lt
    b.a0.val_lt b.a1.val_lt b.a2.val_lt b.a3.val_lt
    b.a4.val_lt b.a5.val_lt b.a6.val_lt b.a7.val_lt
  -- Unfold let bindings in hchain
  simp only [] at hchain
  -- Diff bounds: u32OverflowingSub x y produces .2 < 2^32 when x, y < 2^32
  have u32sub_snd_lt : ∀ x y, x < 2^32 → y < 2^32 → (u32OverflowingSub x y).2 < 2^32 := by
    intro x y hx hy; unfold u32OverflowingSub u32Max; split <;> omega
  -- sub0 through sub7 all have inputs < 2^32 (from U32 bounds and mod 2^32)
  have hd0_lt : sub0.2 < 2^32 := u32sub_snd_lt _ _ a.a0.val_lt b.a0.val_lt
  have hmod_lt : ∀ n, n % 2^32 < 2^32 := fun n => Nat.mod_lt _ (by positivity)
  have hd1_lt : sub1.2 < 2^32 := u32sub_snd_lt _ _ a.a1.val_lt (hmod_lt _)
  have hd2_lt : sub2.2 < 2^32 := u32sub_snd_lt _ _ a.a2.val_lt (hmod_lt _)
  have hd3_lt : sub3.2 < 2^32 := u32sub_snd_lt _ _ a.a3.val_lt (hmod_lt _)
  have hd4_lt : sub4.2 < 2^32 := u32sub_snd_lt _ _ a.a4.val_lt (hmod_lt _)
  have hd5_lt : sub5.2 < 2^32 := u32sub_snd_lt _ _ a.a5.val_lt (hmod_lt _)
  have hd6_lt : sub6.2 < 2^32 := u32sub_snd_lt _ _ a.a6.val_lt (hmod_lt _)
  have hd7_lt : sub7.2 < 2^32 := u32sub_snd_lt _ _ a.a7.val_lt (hmod_lt _)
  -- Derive the digit equalities from hchain
  have ha_lt := a.toNat_lt
  have hb_lt := b.toNat_lt
  -- Compute: from hchain (A + bor7 * 2^256 = D + B),
  -- derive bor7 = 1 - (A + 2^256 - B) / 2^256 and d_k = ((A + 2^256 - B) / 2^(32k)) % 2^32
  -- Apply digit_extraction_sub to get all the digit equalities at once
  -- First, convert hchain to use a.toNat and b.toNat
  have hchain' : a.toNat + bor7 * 2^256 =
      (sub7.2 * 2^224 + sub6.2 * 2^192 + sub5.2 * 2^160 + sub4.2 * 2^128 +
       sub3.2 * 2^96 + sub2.2 * 2^64 + sub1.2 * 2^32 + sub0.2) + b.toNat := by
    unfold U256.toNat; exact hchain
  obtain ⟨hdc, hd7', hd6', hd5', hd4', hd3', hd2', hd1', hd0'⟩ :=
    digit_extraction_sub bor7 sub7.2 sub6.2 sub5.2 sub4.2 sub3.2 sub2.2 sub1.2 sub0.2
      a.toNat b.toNat
      hd0_lt hd1_lt hd2_lt hd3_lt hd4_lt hd5_lt hd6_lt hd7_lt
      a.toNat_lt b.toNat_lt hchain'
  -- Now LHS = some ⟨Felt.ofNat bor7 :: Felt.ofNat sub7.2 :: ... :: Felt.ofNat sub0.2 :: rest, ...⟩
  -- RHS = some ⟨Felt.ofNat (1 - S/2^256) :: (a-b).a7.val :: ... :: (a-b).a0.val :: rest, ...⟩
  -- Rewrite LHS digit values using hdc, hd_k'
  rw [show (Felt.ofNat bor7 : Felt) = Felt.ofNat (1 - (a.toNat + 2^256 - b.toNat) / 2^256)
      from congrArg Felt.ofNat hdc,
    show (Felt.ofNat sub7.2 : Felt) = Felt.ofNat ((a.toNat + 2^256 - b.toNat) / 2^224 % 2^32)
      from congrArg Felt.ofNat hd7',
    show (Felt.ofNat sub6.2 : Felt) = Felt.ofNat ((a.toNat + 2^256 - b.toNat) / 2^192 % 2^32)
      from congrArg Felt.ofNat hd6',
    show (Felt.ofNat sub5.2 : Felt) = Felt.ofNat ((a.toNat + 2^256 - b.toNat) / 2^160 % 2^32)
      from congrArg Felt.ofNat hd5',
    show (Felt.ofNat sub4.2 : Felt) = Felt.ofNat ((a.toNat + 2^256 - b.toNat) / 2^128 % 2^32)
      from congrArg Felt.ofNat hd4',
    show (Felt.ofNat sub3.2 : Felt) = Felt.ofNat ((a.toNat + 2^256 - b.toNat) / 2^96 % 2^32)
      from congrArg Felt.ofNat hd3',
    show (Felt.ofNat sub2.2 : Felt) = Felt.ofNat ((a.toNat + 2^256 - b.toNat) / 2^64 % 2^32)
      from congrArg Felt.ofNat hd2',
    show (Felt.ofNat sub1.2 : Felt) = Felt.ofNat ((a.toNat + 2^256 - b.toNat) / 2^32 % 2^32)
      from congrArg Felt.ofNat hd1',
    show (Felt.ofNat sub0.2 : Felt) = Felt.ofNat ((a.toNat + 2^256 - b.toNat) % 2^32)
      from congrArg Felt.ofNat hd0']
  -- Now both sides should have the same Felt.ofNat values on LHS.
  -- RHS has (a-b).a_k.val which unfolds to Felt.ofNat of the same digit extractions.
  simp only [show (a - b) = U256.ofNat (a.toNat + 2^256 - b.toNat) from rfl,
             U256.ofNat_a0, U256.ofNat_a1, U256.ofNat_a2, U256.ofNat_a3,
             U256.ofNat_a4, U256.ofNat_a5, U256.ofNat_a6, U256.ofNat_a7]

end MidenLean.Proofs
