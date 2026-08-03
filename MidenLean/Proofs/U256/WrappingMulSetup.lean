import MidenLean.Proofs.U256.WrappingMulDefs

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

-- ============================================================================
-- Setup chunk correctness
-- ============================================================================

set_option maxHeartbeats 8000000 in
/-- The setup phase converts LE→BE, stores operands to locals 0-15,
    and initializes accumulators at locals 16-23 to zero.
    Output stack: [a7, a6, a5, a4, a3, a2, a1, a0, b0] ++ rest -/
theorem wm_setup_spec (a b : U256) (rest : List Felt) (mem : Nat → Felt)
    (frame : LocalFrame) (frames : List LocalFrame) (adv : List Felt) (fuel : Nat)
    (hnl : frame.numLocals ≥ 24) :
    let la := frame.localAddr
    execProcedure u256ProcEnv (fuel + 3)
      ⟨b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val ::
       b.a4.val :: b.a5.val :: b.a6.val :: b.a7.val ::
       a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val ::
       a.a4.val :: a.a5.val :: a.a6.val :: a.a7.val :: rest,
       mem, frame :: frames, adv⟩
      wm_setup =
    some ⟨a.a7.val :: a.a6.val :: a.a5.val :: a.a4.val ::
          a.a3.val :: a.a2.val :: a.a1.val :: a.a0.val :: b.a0.val :: rest,
          fun i =>
            if i = la 20 + 3 then 0 else if i = la 20 + 2 then 0
            else if i = la 20 + 1 then 0 else if i = la 20 then 0
            else if i = la 16 + 3 then 0 else if i = la 16 + 2 then 0
            else if i = la 16 + 1 then 0 else if i = la 16 then 0
            else if i = la 12 + 3 then a.a3.val else if i = la 12 + 2 then a.a2.val
            else if i = la 12 + 1 then a.a1.val else if i = la 12 then a.a0.val
            else if i = la 8 + 3 then a.a7.val else if i = la 8 + 2 then a.a6.val
            else if i = la 8 + 1 then a.a5.val else if i = la 8 then a.a4.val
            else if i = la 4 + 3 then b.a3.val else if i = la 4 + 2 then b.a2.val
            else if i = la 4 + 1 then b.a1.val else if i = la 4 then b.a0.val
            else if i = la 0 + 3 then b.a7.val else if i = la 0 + 2 then b.a6.val
            else if i = la 0 + 1 then b.a5.val else if i = la 0 then b.a4.val
            else mem i,
          frame :: frames, adv⟩ := by
  unfold wm_setup execProcedure Procedure.ofOps
  simp only [List.foldlM, u256ProcEnv]
  -- Step 1: execProcedure emptyEnv "u256_le_to_be_pair"
  dsimp only [bind, Bind.bind, Option.bind]
  rw [u256_u256_le_to_be_pair_exec]
  dsimp only [bind, Bind.bind, Option.bind]
  -- Step 2: locStorewBe 0
  rw [stepLocStorewBe (halign := wm_align_0) (hbound := wm_bound_0 hnl)]
  dsimp only [bind, Bind.bind, Option.bind]
  -- Step 3: dropw
  rw [stepDropw]
  dsimp only [bind, Bind.bind, Option.bind]
  -- Step 4: locStorewBe 4
  rw [stepLocStorewBe (halign := wm_align_4) (hbound := wm_bound_4 hnl)]
  dsimp only [bind, Bind.bind, Option.bind]
  -- Step 5: push 0
  miden_step
  -- Step 6: dropw
  rw [stepDropw]
  dsimp only [bind, Bind.bind, Option.bind]
  -- Step 7: movdn 8
  miden_movdn
  -- Step 8: locStorewBe 8
  rw [stepLocStorewBe (halign := wm_align_8) (hbound := wm_bound_8 hnl)]
  dsimp only [bind, Bind.bind, Option.bind]
  -- Step 9: swapw 1
  rw [stepSwapw1]
  dsimp only [bind, Bind.bind, Option.bind]
  -- Step 10: locStorewBe 12
  rw [stepLocStorewBe (halign := wm_align_12) (hbound := wm_bound_12 hnl)]
  dsimp only [bind, Bind.bind, Option.bind]
  -- Step 11: padw
  rw [stepPadw]
  dsimp only [bind, Bind.bind, Option.bind]
  -- Step 12: locStorewBe 16
  rw [stepLocStorewBe (halign := wm_align_16) (hbound := wm_bound_16 hnl)]
  dsimp only [bind, Bind.bind, Option.bind]
  -- Step 13: locStorewBe 20
  rw [stepLocStorewBe (halign := wm_align_20) (hbound := wm_bound_20 hnl)]
  dsimp only [bind, Bind.bind, Option.bind]
  -- Step 14: dropw
  rw [stepDropw]
  dsimp only [bind, Bind.bind, Option.bind]
  -- Step 15: swapw 1
  rw [stepSwapw1]
  simp only [pure, Pure.pure]

end MidenLean.Proofs
