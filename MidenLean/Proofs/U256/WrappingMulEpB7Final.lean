import MidenLean.Proofs.U256.WrappingMulDefs

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

-- ============================================================================
-- Epilogue: b₇ × a₀ correctness
-- ============================================================================

set_option maxHeartbeats 32000000 in
/-- Epilogue b₇: 1 mulstep for b₇ × a₀.
    Input stack: [L₇, L₆, L₅, L₄] ++ rest
    Output stack: [mulstepLo(0, a₀, b₇, L₇), L₆, L₅, L₄] ++ rest -/
theorem wm_ep_b7_correct (a b : U256) (rest : List Felt)
    (mem : Nat → Felt) (frame : LocalFrame) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) (hnl : frame.numLocals ≥ 24)
    (L₇ L₆ L₅ L₄ : Felt) (hL₇ : L₇.isU32 = true)
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
      (Procedure.ofOps wm_ep_b7) =
    some ⟨mulstepLo 0 a.a0.val b.a7.val L₇ :: L₆ :: L₅ :: L₄ :: rest,
          mem, frame :: frames, adv⟩ := by
  unfold wm_ep_b7 execWithEnv Procedure.ofOps
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
  -- movdn 3 (b₇ goes to position 3)
  miden_movdn
  -- push 0
  miden_step
  -- dropw (removes [0, b₆, b₅, b₄])
  rw [stepDropw]; dsimp only [bind, Bind.bind, Option.bind]
  -- Stack: [b₇, a₃, a₂, a₁, a₀, L₇, L₆, L₅, L₄] ++ rest
  -- movup 4 (bring a₀)
  miden_movup
  -- movup 5 (bring L₇)
  miden_movup
  -- movdn 2
  miden_movdn
  -- push 0
  miden_step
  -- Stack: [0, a₀, b₇, L₇, a₃, a₂, a₁, L₆, L₅, L₄] ++ rest
  -- === Mulstep: mulstep(0, a₀, b₇, L₇) ===
  have h0u : (0 : Felt).isU32 = true := by simp [Felt.isU32]
  have hms := mulstep_execWithEnv u256ProcEnv (fuel + 1)
    (0 : Felt) a.a0.val b.a7.val L₇
    (a.a3.val :: a.a2.val :: a.a1.val :: L₆ :: L₅ :: L₄ :: rest)
    ⟨(0 : Felt) :: a.a0.val :: b.a7.val :: L₇ ::
     a.a3.val :: a.a2.val :: a.a1.val :: L₆ :: L₅ :: L₄ :: rest,
     mem, frame :: frames, adv⟩
    rfl h0u (U256.a0_isU32 a) (U256.a7_isU32 b) hL₇
  simp only [MidenState.withStack] at hms
  rw [hms]; clear hms; dsimp only [bind, Bind.bind, Option.bind]
  -- drop (remove carry)
  rw [stepDrop]; dsimp only [bind, Bind.bind, Option.bind]
  -- movdn 3
  miden_movdn
  -- drop (remove a₃)
  rw [stepDrop]; dsimp only [bind, Bind.bind, Option.bind]
  -- drop (remove a₂)
  rw [stepDrop]; dsimp only [bind, Bind.bind, Option.bind]
  -- drop (remove a₁)
  rw [stepDrop]; simp only [pure, Pure.pure]

-- ============================================================================
-- Final phase: load la(16), le_to_be, swapdw cleanup
-- ============================================================================

set_option maxHeartbeats 8000000 in
/-- Final phase: load accumulated low 4 limbs from la(16), convert to LE via le_to_be,
    then use swapdw/dropw cleanup to remove the 16 dummy elements below the result.
    Input stack:  [L₇, L₆, L₅, L₄, d0..d15] ++ rest
    Output stack: [R₀, R₁, R₂, R₃, L₄, L₅, L₆, L₇] ++ rest -/
theorem wm_final_correct
    (rest : List Felt)
    (mem : Nat → Felt) (frame : LocalFrame) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) (hnl : frame.numLocals ≥ 24)
    (L₇ L₆ L₅ L₄ : Felt)
    (R₀ R₁ R₂ R₃ : Felt)
    (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 : Felt)
    (h16_3 : mem (frame.localAddr 16 + 3) = R₃)
    (h16_2 : mem (frame.localAddr 16 + 2) = R₂)
    (h16_1 : mem (frame.localAddr 16 + 1) = R₁)
    (h16_0 : mem (frame.localAddr 16) = R₀) :
    execWithEnv u256ProcEnv (fuel + 3)
      ⟨L₇ :: L₆ :: L₅ :: L₄ :: d0 :: d1 :: d2 :: d3 ::
       d4 :: d5 :: d6 :: d7 :: d8 :: d9 :: d10 :: d11 ::
       d12 :: d13 :: d14 :: d15 :: rest, mem, frame :: frames, adv⟩
      (Procedure.ofOps wm_final) =
    some ⟨R₀ :: R₁ :: R₂ :: R₃ :: L₄ :: L₅ :: L₆ :: L₇ :: rest,
          mem, frame :: frames, adv⟩ := by
  unfold wm_final execWithEnv Procedure.ofOps
  simp only [List.foldlM, u256ProcEnv]
  dsimp only [bind, Bind.bind, Option.bind]
  -- padw
  rw [stepPadw]; dsimp only [bind, Bind.bind, Option.bind]
  -- locLoadwBe 16
  rw [stepLocLoadwBe (halign := wm_align_16) (hbound := wm_bound_16 hnl)]
  rw [h16_3, h16_2, h16_1, h16_0]; dsimp only [bind, Bind.bind, Option.bind]
  -- swapw 1: swap [R₃, R₂, R₁, R₀] with [L₇, L₆, L₅, L₄]
  rw [stepSwapw1]; dsimp only [bind, Bind.bind, Option.bind]
  -- exec u256_le_to_be: reverse top 8
  -- Stack before: [L₇, L₆, L₅, L₄, R₃, R₂, R₁, R₀, d0..d15, rest]
  -- Stack after:  [R₀, R₁, R₂, R₃, L₄, L₅, L₆, L₇, d0..d15, rest]
  rw [le_to_be_env]; dsimp only [bind, Bind.bind, Option.bind]
  -- swapdw (first): swap [R₀..L₇] with [d0..d7]
  rw [stepSwapdw]; dsimp only [bind, Bind.bind, Option.bind]
  -- dropw: removes [d0, d1, d2, d3]
  rw [stepDropw]; dsimp only [bind, Bind.bind, Option.bind]
  -- dropw: removes [d4, d5, d6, d7]
  rw [stepDropw]; dsimp only [bind, Bind.bind, Option.bind]
  -- swapdw (second): swap [R₀..L₇] with [d8..d15]
  rw [stepSwapdw]; dsimp only [bind, Bind.bind, Option.bind]
  -- dropw: removes [d8, d9, d10, d11]
  rw [stepDropw]; dsimp only [bind, Bind.bind, Option.bind]
  -- dropw: removes [d12, d13, d14, d15]
  rw [stepDropw]; simp only [pure, Pure.pure]

end MidenLean.Proofs
