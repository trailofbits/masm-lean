import MidenLean.Proofs.U256.WrappingMulDefs

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

-- ============================================================================
-- Epilogue b₅: chunk decomposition (following the mulstep4 pattern)
-- ============================================================================

-- Chunk 1: memory load + isolate b₅ + mulstep 1 + swap/movdn
private def ep_b5_chunk1 : List Op := [
  .inst (.padw), .inst (.locLoadwBe 12), .inst (.padw), .inst (.locLoadwBe 0),
  .inst (.movup 2), .inst (.movdn 3), .inst (.push 0), .inst (.dropw),
  .inst (.movup 7), .inst (.dup 1), .inst (.movup 6), .inst (.push 0),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.movdn 7)]

-- Chunk 2: prep + mulstep 2 + swap/movdn
private def ep_b5_chunk2 : List Op := [
  .inst (.movup 4), .inst (.dup 2), .inst (.movup 7), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.movdn 5)]

-- Chunk 3: prep + mulstep 3 + cleanup
private def ep_b5_chunk3 : List Op := [
  .inst (.swap 1), .inst (.movup 3), .inst (.movup 4), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.drop), .inst (.swap 1), .inst (.drop)]

private theorem ep_b5_decomp :
    (wm_ep_b5 : List Op) = ep_b5_chunk1 ++ (ep_b5_chunk2 ++ ep_b5_chunk3) := by
  unfold wm_ep_b5 ep_b5_chunk1 ep_b5_chunk2 ep_b5_chunk3; rfl

-- ============================================================================
-- Chunk 1 correctness: memory load + first mulstep
-- ============================================================================

set_option maxHeartbeats 16000000 in
private theorem ep_b5_chunk1_correct (a b : U256) (rest : List Felt)
    (mem : Nat → Felt) (frame : LocalFrame) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) (hnl : frame.numLocals ≥ 24)
    (L₇ L₆ L₅ L₄ : Felt)
    (hL₅ : L₅.isU32 = true)
    (h12_3 : mem (frame.localAddr 12 + 3) = a.a3.val)
    (h12_2 : mem (frame.localAddr 12 + 2) = a.a2.val)
    (h12_1 : mem (frame.localAddr 12 + 1) = a.a1.val)
    (h12_0 : mem (frame.localAddr 12) = a.a0.val)
    (h0_3 : mem (frame.localAddr 0 + 3) = b.a7.val)
    (h0_2 : mem (frame.localAddr 0 + 2) = b.a6.val)
    (h0_1 : mem (frame.localAddr 0 + 1) = b.a5.val)
    (h0_0 : mem (frame.localAddr 0) = b.a4.val) :
    execProcedure u256ProcEnv (fuel + 3)
      ⟨L₇ :: L₆ :: L₅ :: L₄ :: rest, mem, frame :: frames, adv⟩
      (Procedure.ofOps ep_b5_chunk1) =
    some ⟨mulstepCarry 0 a.a0.val b.a5.val L₅ ::
          b.a5.val :: a.a3.val :: a.a2.val :: a.a1.val :: L₇ :: L₆ ::
          mulstepLo 0 a.a0.val b.a5.val L₅ :: L₄ :: rest,
          mem, frame :: frames, adv⟩ := by
  unfold ep_b5_chunk1 execProcedure Procedure.ofOps
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
  -- movup 2, movdn 3, push 0, dropw
  miden_movup; miden_movdn; miden_step
  rw [stepDropw]; dsimp only [bind, Bind.bind, Option.bind]
  -- movup 7, dup 1, movup 6, push 0
  miden_movup; miden_dup; miden_movup; miden_step
  -- mulstep(0, a₀, b₅, L₅)
  have h0u : (0 : Felt).isU32 = true := by simp [Felt.isU32]
  have hms := mulstep_execWithEnv u256ProcEnv (fuel + 1)
    (0 : Felt) a.a0.val b.a5.val L₅
    (b.a5.val :: a.a3.val :: a.a2.val :: a.a1.val :: L₇ :: L₆ :: L₄ :: rest)
    ⟨(0 : Felt) :: a.a0.val :: b.a5.val :: L₅ ::
     b.a5.val :: a.a3.val :: a.a2.val :: a.a1.val :: L₇ :: L₆ :: L₄ :: rest,
     mem, frame :: frames, adv⟩
    rfl h0u (U256.a0_isU32 a) (U256.a5_isU32 b) hL₅
  simp only [Concrete.State.withStack] at hms
  rw [hms]; clear hms; dsimp only [bind, Bind.bind, Option.bind]
  -- swap 1, movdn 7
  miden_swap; miden_movdn
  simp only [pure, Pure.pure]

-- ============================================================================
-- Chunk 2 correctness: mulstep 2 (abstract variables, no memory)
-- ============================================================================

set_option maxHeartbeats 8000000 in
private theorem ep_b5_chunk2_correct
    (carry b₅ a₃ a₂ a₁ L₇ L₆ lo₁ L₄ : Felt) (rest : List Felt)
    (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (hcarry : carry.isU32 = true) (hb₅ : b₅.isU32 = true)
    (ha₁ : a₁.isU32 = true) (hL₆ : L₆.isU32 = true)
    (fuel : Nat) :
    execProcedure u256ProcEnv (fuel + 2)
      ⟨carry :: b₅ :: a₃ :: a₂ :: a₁ :: L₇ :: L₆ :: lo₁ :: L₄ :: rest,
       mem, frames, adv⟩
      (Procedure.ofOps ep_b5_chunk2) =
    some ⟨mulstepCarry carry b₅ a₁ L₆ ::
          b₅ :: a₃ :: a₂ :: L₇ ::
          mulstepLo carry b₅ a₁ L₆ :: lo₁ :: L₄ :: rest,
          mem, frames, adv⟩ := by
  unfold ep_b5_chunk2 execProcedure Procedure.ofOps
  simp only [List.foldlM, u256ProcEnv]
  dsimp only [bind, Bind.bind, Option.bind]
  miden_movup; miden_dup; miden_movup; miden_swap
  have hms := mulstep_execWithEnv u256ProcEnv fuel
    carry b₅ a₁ L₆
    (b₅ :: a₃ :: a₂ :: L₇ :: lo₁ :: L₄ :: rest)
    ⟨carry :: b₅ :: a₁ :: L₆ ::
     b₅ :: a₃ :: a₂ :: L₇ :: lo₁ :: L₄ :: rest,
     mem, frames, adv⟩
    rfl hcarry hb₅ ha₁ hL₆
  simp only [Concrete.State.withStack] at hms
  rw [hms]; clear hms; dsimp only [bind, Bind.bind, Option.bind]
  miden_swap; miden_movdn
  simp only [pure, Pure.pure]

-- ============================================================================
-- Chunk 3 correctness: mulstep 3 + cleanup (abstract variables, no memory)
-- ============================================================================

set_option maxHeartbeats 8000000 in
private theorem ep_b5_chunk3_correct
    (carry b₅ a₃ a₂ L₇ lo₂ lo₁ L₄ : Felt) (rest : List Felt)
    (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (hcarry : carry.isU32 = true) (ha₂ : a₂.isU32 = true)
    (hb₅ : b₅.isU32 = true) (hL₇ : L₇.isU32 = true)
    (fuel : Nat) :
    execProcedure u256ProcEnv (fuel + 2)
      ⟨carry :: b₅ :: a₃ :: a₂ :: L₇ :: lo₂ :: lo₁ :: L₄ :: rest,
       mem, frames, adv⟩
      (Procedure.ofOps ep_b5_chunk3) =
    some ⟨mulstepLo carry a₂ b₅ L₇ :: lo₂ :: lo₁ :: L₄ :: rest,
          mem, frames, adv⟩ := by
  unfold ep_b5_chunk3 execProcedure Procedure.ofOps
  simp only [List.foldlM, u256ProcEnv]
  dsimp only [bind, Bind.bind, Option.bind]
  miden_swap; miden_movup; miden_movup; miden_swap
  have hms := mulstep_execWithEnv u256ProcEnv fuel
    carry a₂ b₅ L₇
    (a₃ :: lo₂ :: lo₁ :: L₄ :: rest)
    ⟨carry :: a₂ :: b₅ :: L₇ ::
     a₃ :: lo₂ :: lo₁ :: L₄ :: rest,
     mem, frames, adv⟩
    rfl hcarry ha₂ hb₅ hL₇
  simp only [Concrete.State.withStack] at hms
  rw [hms]; clear hms; dsimp only [bind, Bind.bind, Option.bind]
  rw [stepDrop]; dsimp only [bind, Bind.bind, Option.bind]
  miden_swap
  rw [stepDrop]; simp only [pure, Pure.pure]

-- ============================================================================
-- Main theorem: compose the 3 chunks
-- ============================================================================

set_option maxHeartbeats 8000000 in
/-- Epilogue b₅: 3 individual mulsteps for b₅ × a[0..2].
    Input stack: [L₇, L₆, L₅, L₄] ++ rest
    Output stack: [l₇', l₆', l₅', L₄] ++ rest -/
theorem wm_ep_b5_correct (a b : U256) (rest : List Felt)
    (mem : Nat → Felt) (frame : LocalFrame) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) (hnl : frame.numLocals ≥ 24)
    (L₇ L₆ L₅ L₄ : Felt)
    (hL₅ : L₅.isU32 = true) (hL₆ : L₆.isU32 = true) (hL₇ : L₇.isU32 = true)
    (h12_3 : mem (frame.localAddr 12 + 3) = a.a3.val)
    (h12_2 : mem (frame.localAddr 12 + 2) = a.a2.val)
    (h12_1 : mem (frame.localAddr 12 + 1) = a.a1.val)
    (h12_0 : mem (frame.localAddr 12) = a.a0.val)
    (h0_3 : mem (frame.localAddr 0 + 3) = b.a7.val)
    (h0_2 : mem (frame.localAddr 0 + 2) = b.a6.val)
    (h0_1 : mem (frame.localAddr 0 + 1) = b.a5.val)
    (h0_0 : mem (frame.localAddr 0) = b.a4.val) :
    let c₁ := mulstepCarry 0 a.a0.val b.a5.val L₅
    let c₂ := mulstepCarry c₁ b.a5.val a.a1.val L₆
    execProcedure u256ProcEnv (fuel + 3)
      ⟨L₇ :: L₆ :: L₅ :: L₄ :: rest, mem, frame :: frames, adv⟩
      (Procedure.ofOps wm_ep_b5) =
    some ⟨mulstepLo c₂ a.a2.val b.a5.val L₇ ::
          mulstepLo c₁ b.a5.val a.a1.val L₆ ::
          mulstepLo 0 a.a0.val b.a5.val L₅ :: L₄ :: rest,
          mem, frame :: frames, adv⟩ := by
  -- Decompose into 3 chunks
  rw [show (wm_ep_b5 : List Op) = ep_b5_chunk1 ++ (ep_b5_chunk2 ++ ep_b5_chunk3)
      from ep_b5_decomp]
  rw [execProcedure_append]
  -- Chunk 1: memory load + first mulstep
  rw [ep_b5_chunk1_correct a b rest mem frame frames adv fuel hnl
      L₇ L₆ L₅ L₄ hL₅ h12_3 h12_2 h12_1 h12_0 h0_3 h0_2 h0_1 h0_0]
  simp only [bind, Bind.bind, Option.bind]
  -- Chunk 2 + 3
  rw [execProcedure_append]
  have hc₁u : (mulstepCarry 0 a.a0.val b.a5.val L₅).isU32 = true :=
    mulstep_carry_isU32 0 a.a0.val b.a5.val L₅
      (by simp [Felt.isU32]) (U256.a0_isU32 a) (U256.a5_isU32 b) hL₅
  rw [ep_b5_chunk2_correct
      (mulstepCarry 0 a.a0.val b.a5.val L₅) b.a5.val a.a3.val a.a2.val a.a1.val
      L₇ L₆ (mulstepLo 0 a.a0.val b.a5.val L₅) L₄ rest
      mem (frame :: frames) adv
      hc₁u (U256.a5_isU32 b) (U256.a1_isU32 a) hL₆ (fuel + 1)]
  simp only [bind, Bind.bind, Option.bind]
  -- Chunk 3
  have hc₂u : (mulstepCarry (mulstepCarry 0 a.a0.val b.a5.val L₅)
      b.a5.val a.a1.val L₆).isU32 = true :=
    mulstep_carry_isU32 _ b.a5.val a.a1.val L₆
      hc₁u (U256.a5_isU32 b) (U256.a1_isU32 a) hL₆
  rw [ep_b5_chunk3_correct
      (mulstepCarry (mulstepCarry 0 a.a0.val b.a5.val L₅) b.a5.val a.a1.val L₆)
      b.a5.val a.a3.val a.a2.val L₇
      (mulstepLo (mulstepCarry 0 a.a0.val b.a5.val L₅) b.a5.val a.a1.val L₆)
      (mulstepLo 0 a.a0.val b.a5.val L₅) L₄ rest
      mem (frame :: frames) adv
      hc₂u (U256.a2_isU32 a) (U256.a5_isU32 b) hL₇ (fuel + 1)]

end MidenLean.Proofs
