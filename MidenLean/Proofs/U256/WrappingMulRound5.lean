import MidenLean.Proofs.U256.WrappingMulDefs

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

-- ============================================================================
-- Round 5 correctness
-- ============================================================================

set_option maxHeartbeats 32000000 in
/-- Round 5: b₄ × a[0..3] using mulstep4 with stack accumulators.
    Input stack: [l₅, lo4, lo3, lo2] ++ rest
    Output stack: [lo4', lo3', lo2', lo1'] ++ rest -/
theorem wm_round5_correct (a b : U256) (rest : List Felt)
    (mem : Nat → Felt) (frame : LocalFrame) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) (hnl : frame.numLocals ≥ 24)
    (l₅ lo4 lo3 lo2 : Felt)
    (hl₅ : l₅.isU32 = true) (hlo4 : lo4.isU32 = true)
    (hlo3 : lo3.isU32 = true) (hlo2 : lo2.isU32 = true)
    (h12_3 : mem (frame.localAddr 12 + 3) = a.a3.val)
    (h12_2 : mem (frame.localAddr 12 + 2) = a.a2.val)
    (h12_1 : mem (frame.localAddr 12 + 1) = a.a1.val)
    (h12_0 : mem (frame.localAddr 12) = a.a0.val)
    (h8_3 : mem (frame.localAddr 8 + 3) = a.a7.val)
    (h8_2 : mem (frame.localAddr 8 + 2) = a.a6.val)
    (h8_1 : mem (frame.localAddr 8 + 1) = a.a5.val)
    (h8_0 : mem (frame.localAddr 8) = a.a4.val)
    (h0_3 : mem (frame.localAddr 0 + 3) = b.a7.val)
    (h0_2 : mem (frame.localAddr 0 + 2) = b.a6.val)
    (h0_1 : mem (frame.localAddr 0 + 1) = b.a5.val)
    (h0_0 : mem (frame.localAddr 0) = b.a4.val) :
    let carry1 := mulstepCarry 0 a.a0.val b.a4.val lo2
    let carry2 := mulstepCarry carry1 a.a1.val b.a4.val lo3
    let carry3 := mulstepCarry carry2 a.a2.val b.a4.val lo4
    execWithEnv u256ProcEnv (fuel + 3)
      ⟨l₅ :: lo4 :: lo3 :: lo2 :: rest, mem, frame :: frames, adv⟩
      (Procedure.ofOps wm_round5) =
    some ⟨mulstepLo carry3 a.a3.val b.a4.val l₅ ::
          mulstepLo carry2 a.a2.val b.a4.val lo4 ::
          mulstepLo carry1 a.a1.val b.a4.val lo3 ::
          mulstepLo 0 a.a0.val b.a4.val lo2 :: rest,
          mem, frame :: frames, adv⟩ := by
  unfold wm_round5 execWithEnv Procedure.ofOps
  simp only [List.foldlM, u256ProcEnv]
  dsimp only [bind, Bind.bind, Option.bind]
  -- padw
  rw [stepPadw]; dsimp only [bind, Bind.bind, Option.bind]
  -- locLoadwBe 12
  rw [stepLocLoadwBe (halign := wm_align_12) (hbound := wm_bound_12 hnl)]
  rw [h12_3, h12_2, h12_1, h12_0]; dsimp only [bind, Bind.bind, Option.bind]
  -- padw
  rw [stepPadw]; dsimp only [bind, Bind.bind, Option.bind]
  -- locLoadwBe 8
  rw [stepLocLoadwBe (halign := wm_align_8) (hbound := wm_bound_8 hnl)]
  rw [h8_3, h8_2, h8_1, h8_0]; dsimp only [bind, Bind.bind, Option.bind]
  -- padw
  rw [stepPadw]; dsimp only [bind, Bind.bind, Option.bind]
  -- locLoadwBe 0
  rw [stepLocLoadwBe (halign := wm_align_0) (hbound := wm_bound_0 hnl)]
  rw [h0_3, h0_2, h0_1, h0_0]; dsimp only [bind, Bind.bind, Option.bind]
  -- push 0
  miden_step
  -- dropw
  rw [stepDropw]; dsimp only [bind, Bind.bind, Option.bind]
  -- exec "mulstep4"
  have hmul4 := u256_mulstep4_correct
    b.a4.val a.a7.val a.a6.val a.a5.val a.a4.val
    a.a3.val a.a2.val a.a1.val a.a0.val
    l₅ lo4 lo3 lo2 rest
    ⟨b.a4.val :: a.a7.val :: a.a6.val :: a.a5.val :: a.a4.val ::
     a.a3.val :: a.a2.val :: a.a1.val :: a.a0.val :: l₅ :: lo4 :: lo3 :: lo2 :: rest,
     mem, frame :: frames, adv⟩
    rfl (U256.a4_isU32 b) (U256.a3_isU32 a) (U256.a2_isU32 a) (U256.a1_isU32 a) (U256.a0_isU32 a)
    hl₅ hlo4 hlo3 hlo2 fuel
  simp only [MidenState.withStack] at hmul4
  rw [hmul4]; clear hmul4; dsimp only [bind, Bind.bind, Option.bind]
  -- dropw (removes carry4, b₄, a₇, a₆)
  rw [stepDropw]; dsimp only [bind, Bind.bind, Option.bind]
  -- drop (removes a₅)
  rw [stepDrop]; dsimp only [bind, Bind.bind, Option.bind]
  -- drop (removes a₄)
  rw [stepDrop]; simp only [pure, Pure.pure]

end MidenLean.Proofs
