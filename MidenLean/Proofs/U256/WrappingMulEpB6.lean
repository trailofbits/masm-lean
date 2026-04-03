import MidenLean.Proofs.U256.WrappingMulDefs

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

-- ============================================================================
-- Epilogue b₆: chunk decomposition
-- ============================================================================

-- Chunk 1: memory load + isolate b₆ + mulstep 1 + swap/movdn
private def ep_b6_chunk1 : List Op := [
  .inst (.padw), .inst (.locLoadwBe 12), .inst (.padw), .inst (.locLoadwBe 0),
  .inst (.swap 1), .inst (.movdn 3), .inst (.push 0), .inst (.dropw),
  .inst (.movup 6), .inst (.dup 1), .inst (.movup 6), .inst (.push 0),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.movdn 6)]

-- Chunk 2: prep + mulstep 2 + cleanup
private def ep_b6_chunk2 : List Op := [
  .inst (.swap 1), .inst (.movup 4), .inst (.movup 5), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.drop),
  .inst (.movdn 2), .inst (.drop), .inst (.drop)]

private theorem ep_b6_decomp :
    (wm_ep_b6 : List Op) = ep_b6_chunk1 ++ ep_b6_chunk2 := by
  unfold wm_ep_b6 ep_b6_chunk1 ep_b6_chunk2; rfl

-- ============================================================================
-- Chunk 1 correctness: memory load + first mulstep
-- ============================================================================

set_option maxHeartbeats 16000000 in
private theorem ep_b6_chunk1_correct (a b : U256) (rest : List Felt)
    (mem : Nat → Felt) (frame : LocalFrame) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) (hnl : frame.numLocals ≥ 24)
    (L₇ L₆ L₅ L₄ : Felt)
    (hL₆ : L₆.isU32 = true)
    (h12_3 : mem (frame.localAddr 12 + 3) = a.a3.val)
    (h12_2 : mem (frame.localAddr 12 + 2) = a.a2.val)
    (h12_1 : mem (frame.localAddr 12 + 1) = a.a1.val)
    (h12_0 : mem (frame.localAddr 12) = a.a0.val)
    (h0_3 : mem (frame.localAddr 0 + 3) = b.a7.val)
    (h0_2 : mem (frame.localAddr 0 + 2) = b.a6.val)
    (h0_1 : mem (frame.localAddr 0 + 1) = b.a5.val)
    (h0_0 : mem (frame.localAddr 0) = b.a4.val) :
    execWithEnv u256ProcEnv (fuel + 3)
      ⟨L₇ :: L₆ :: L₅ :: L₄ :: rest, mem, frame :: frames, adv⟩
      (Procedure.ofOps ep_b6_chunk1) =
    some ⟨mulstepCarry 0 a.a0.val b.a6.val L₆ ::
          b.a6.val :: a.a3.val :: a.a2.val :: a.a1.val :: L₇ ::
          mulstepLo 0 a.a0.val b.a6.val L₆ :: L₅ :: L₄ :: rest,
          mem, frame :: frames, adv⟩ := by
  unfold ep_b6_chunk1 execWithEnv Procedure.ofOps
  simp only [List.foldlM, u256ProcEnv]
  dsimp only [bind, Bind.bind, Option.bind]
  -- padw + locLoadwBe 12
  rw [stepPadw]; dsimp only [bind, Bind.bind, Option.bind]
  rw [stepLocLoadwBe (halign := wm_align_12) (hbound := wm_bound_12 hnl)]
  rw [h12_3, h12_2, h12_1, h12_0]; dsimp only [bind, Bind.bind, Option.bind]
  -- padw + locLoadwBe 0
  rw [stepPadw]; dsimp only [bind, Bind.bind, Option.bind]
  rw [stepLocLoadwBe (halign := wm_align_0) (hbound := wm_bound_0 hnl)]
  rw [h0_3, h0_2, h0_1, h0_0]; dsimp only [bind, Bind.bind, Option.bind]
  -- swap 1, movdn 3, push 0, dropw
  miden_swap; miden_movdn; miden_step
  rw [stepDropw]; dsimp only [bind, Bind.bind, Option.bind]
  -- movup 6, dup 1, movup 6, push 0
  miden_movup; miden_dup; miden_movup; miden_step
  -- mulstep(0, a₀, b₆, L₆)
  have h0u : (0 : Felt).isU32 = true := by simp [Felt.isU32]
  have hms := mulstep_execWithEnv u256ProcEnv (fuel + 1)
    (0 : Felt) a.a0.val b.a6.val L₆
    (b.a6.val :: a.a3.val :: a.a2.val :: a.a1.val :: L₇ :: L₅ :: L₄ :: rest)
    ⟨(0 : Felt) :: a.a0.val :: b.a6.val :: L₆ ::
     b.a6.val :: a.a3.val :: a.a2.val :: a.a1.val :: L₇ :: L₅ :: L₄ :: rest,
     mem, frame :: frames, adv⟩
    rfl h0u (U256.a0_isU32 a) (U256.a6_isU32 b) hL₆
  simp only [MidenState.withStack] at hms
  rw [hms]; clear hms; dsimp only [bind, Bind.bind, Option.bind]
  -- swap 1, movdn 6
  miden_swap; miden_movdn
  simp only [pure, Pure.pure]

-- ============================================================================
-- Chunk 2 correctness: mulstep 2 + cleanup (abstract variables)
-- ============================================================================

set_option maxHeartbeats 8000000 in
private theorem ep_b6_chunk2_correct
    (carry b₆ a₃ a₂ a₁ L₇ lo₁ L₅ L₄ : Felt) (rest : List Felt)
    (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (hcarry : carry.isU32 = true) (ha₁ : a₁.isU32 = true)
    (hb₆ : b₆.isU32 = true) (hL₇ : L₇.isU32 = true)
    (fuel : Nat) :
    execWithEnv u256ProcEnv (fuel + 2)
      ⟨carry :: b₆ :: a₃ :: a₂ :: a₁ :: L₇ :: lo₁ :: L₅ :: L₄ :: rest,
       mem, frames, adv⟩
      (Procedure.ofOps ep_b6_chunk2) =
    some ⟨mulstepLo carry a₁ b₆ L₇ :: lo₁ :: L₅ :: L₄ :: rest,
          mem, frames, adv⟩ := by
  unfold ep_b6_chunk2 execWithEnv Procedure.ofOps
  simp only [List.foldlM, u256ProcEnv]
  dsimp only [bind, Bind.bind, Option.bind]
  miden_swap; miden_movup; miden_movup; miden_swap
  -- mulstep(carry, a₁, b₆, L₇)
  have hms := mulstep_execWithEnv u256ProcEnv fuel
    carry a₁ b₆ L₇
    (a₃ :: a₂ :: lo₁ :: L₅ :: L₄ :: rest)
    ⟨carry :: a₁ :: b₆ :: L₇ ::
     a₃ :: a₂ :: lo₁ :: L₅ :: L₄ :: rest,
     mem, frames, adv⟩
    rfl hcarry ha₁ hb₆ hL₇
  simp only [MidenState.withStack] at hms
  rw [hms]; clear hms; dsimp only [bind, Bind.bind, Option.bind]
  -- drop, movdn 2, drop, drop
  rw [stepDrop]; dsimp only [bind, Bind.bind, Option.bind]
  miden_movdn
  rw [stepDrop]; dsimp only [bind, Bind.bind, Option.bind]
  rw [stepDrop]; simp only [pure, Pure.pure]

-- ============================================================================
-- Main theorem: compose the 2 chunks
-- ============================================================================

set_option maxHeartbeats 8000000 in
/-- Epilogue b₆: 2 individual mulsteps for b₆ × a[0..1].
    Input stack: [L₇, L₆, L₅, L₄] ++ rest
    Output stack: [l₇', l₆', L₅, L₄] ++ rest -/
theorem wm_ep_b6_correct (a b : U256) (rest : List Felt)
    (mem : Nat → Felt) (frame : LocalFrame) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) (hnl : frame.numLocals ≥ 24)
    (L₇ L₆ L₅ L₄ : Felt) (hL₆ : L₆.isU32 = true) (hL₇ : L₇.isU32 = true)
    (h12_3 : mem (frame.localAddr 12 + 3) = a.a3.val)
    (h12_2 : mem (frame.localAddr 12 + 2) = a.a2.val)
    (h12_1 : mem (frame.localAddr 12 + 1) = a.a1.val)
    (h12_0 : mem (frame.localAddr 12) = a.a0.val)
    (h0_3 : mem (frame.localAddr 0 + 3) = b.a7.val)
    (h0_2 : mem (frame.localAddr 0 + 2) = b.a6.val)
    (h0_1 : mem (frame.localAddr 0 + 1) = b.a5.val)
    (h0_0 : mem (frame.localAddr 0) = b.a4.val) :
    let c₁ := mulstepCarry 0 a.a0.val b.a6.val L₆
    execWithEnv u256ProcEnv (fuel + 3)
      ⟨L₇ :: L₆ :: L₅ :: L₄ :: rest, mem, frame :: frames, adv⟩
      (Procedure.ofOps wm_ep_b6) =
    some ⟨mulstepLo c₁ a.a1.val b.a6.val L₇ ::
          mulstepLo 0 a.a0.val b.a6.val L₆ :: L₅ :: L₄ :: rest,
          mem, frame :: frames, adv⟩ := by
  -- Decompose into 2 chunks
  rw [show (wm_ep_b6 : List Op) = ep_b6_chunk1 ++ ep_b6_chunk2 from ep_b6_decomp]
  rw [execWithEnv_append]
  -- Chunk 1: memory load + first mulstep
  rw [ep_b6_chunk1_correct a b rest mem frame frames adv fuel hnl
      L₇ L₆ L₅ L₄ hL₆ h12_3 h12_2 h12_1 h12_0 h0_3 h0_2 h0_1 h0_0]
  simp only [bind, Bind.bind, Option.bind]
  -- Chunk 2: second mulstep + cleanup
  have hc₁u : (mulstepCarry 0 a.a0.val b.a6.val L₆).isU32 = true :=
    mulstep_carry_isU32 0 a.a0.val b.a6.val L₆
      (by simp [Felt.isU32]) (U256.a0_isU32 a) (U256.a6_isU32 b) hL₆
  rw [ep_b6_chunk2_correct
      (mulstepCarry 0 a.a0.val b.a6.val L₆) b.a6.val a.a3.val a.a2.val a.a1.val
      L₇ (mulstepLo 0 a.a0.val b.a6.val L₆) L₅ L₄ rest
      mem (frame :: frames) adv
      hc₁u (U256.a1_isU32 a) (U256.a6_isU32 b) hL₇ (fuel + 1)]

end MidenLean.Proofs
