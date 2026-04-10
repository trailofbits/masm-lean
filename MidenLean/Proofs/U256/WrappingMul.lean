import MidenLean.Proofs.U256.WrappingMulDefs
import MidenLean.Proofs.U256.WrappingMulSetup
import MidenLean.Proofs.U256.WrappingMulRound1
import MidenLean.Proofs.U256.WrappingMulRound2
import MidenLean.Proofs.U256.WrappingMulRound3
import MidenLean.Proofs.U256.WrappingMulRound4
import MidenLean.Proofs.U256.WrappingMulRound5
import MidenLean.Proofs.U256.WrappingMulEpB5
import MidenLean.Proofs.U256.WrappingMulEpB6
import MidenLean.Proofs.U256.WrappingMulEpB7Final

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

-- ============================================================================
-- Main theorem
-- ============================================================================

set_option maxHeartbeats 32000000 in
/-- `u256::wrapping_mul` computes `(a * b) mod 2^256` for two 256-bit values.
    Input stack:  [b.a0, ..., b.a7, a.a0, ..., a.a7, d0, ..., d15] ++ rest  (LE limbs)
    Output stack: [(a*b).a0, ..., (a*b).a7] ++ rest
    The 16 elements d0..d15 below the inputs are consumed by the swapdw cleanup. -/
theorem u256_wrapping_mul_correct
    (a b : U256) (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 : Felt)
    (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) :
    ∃ mem', execWithEnv u256ProcEnv (fuel + 3)
      ⟨b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val ::
       b.a4.val :: b.a5.val :: b.a6.val :: b.a7.val ::
       a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val ::
       a.a4.val :: a.a5.val :: a.a6.val :: a.a7.val ::
       d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: d6 :: d7 ::  -- Because of an issue in the procedure epilogue.
       d8 :: d9 :: d10 :: d11 :: d12 :: d13 :: d14 :: d15 :: rest, mem, frames, adv⟩
      Miden.Core.U256.wrapping_mul =
    some ⟨(a * b).a0.val :: (a * b).a1.val :: (a * b).a2.val :: (a * b).a3.val ::
          (a * b).a4.val :: (a * b).a5.val :: (a * b).a6.val :: (a * b).a7.val :: rest,
          mem', frames, adv⟩ := by
  -- Step 1: Handle frame allocation (numLocals = 24 = 23 + 1)
  rw [execWithEnv_body_eq_withLocals u256ProcEnv (fuel + 3) _ _ _ 23 rfl rfl]
  dsimp only
  -- Step 2: Reduce to proving body execution under the allocated frame
  set frame : LocalFrame :=
    { base := nextFrameBase frames, numLocals := 23 + 1,
      alignedNumLocals := alignLocals (23 + 1) } with hframe_def
  -- Abbreviate the 16 dummy elements appended to rest
  set drest : List Felt := d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: d6 :: d7 ::
    d8 :: d9 :: d10 :: d11 :: d12 :: d13 :: d14 :: d15 :: rest with hdrest
  suffices h : ∃ mem', execWithEnv u256ProcEnv (fuel + 3)
      ⟨b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val ::
       b.a4.val :: b.a5.val :: b.a6.val :: b.a7.val ::
       a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val ::
       a.a4.val :: a.a5.val :: a.a6.val :: a.a7.val :: drest,
       mem, frame :: frames, adv⟩
      (Procedure.ofOps Miden.Core.U256.wrapping_mul.body) =
      some ⟨(a * b).a0.val :: (a * b).a1.val :: (a * b).a2.val :: (a * b).a3.val ::
            (a * b).a4.val :: (a * b).a5.val :: (a * b).a6.val :: (a * b).a7.val :: rest,
            mem', frame :: frames, adv⟩ by
    obtain ⟨mem', hmem'⟩ := h
    exact ⟨mem', by rw [hmem']⟩
  -- Step 3: Decompose body into setup ++ rest
  rw [show Miden.Core.U256.wrapping_mul.body = wm_setup ++ wm_rest from wm_body_decomp]
  rw [execWithEnv_append]
  -- Step 4: Apply setup correctness
  rw [wm_setup_correct a b drest mem frame frames adv fuel (by simp only [frame]; omega)]
  simp only [bind, Bind.bind, Option.bind]
  -- Step 5: Decompose wm_rest into round 1 + remaining
  rw [show (wm_rest : List Op) = wm_round1 ++ wm_rest_after_r1 from wm_rest_eq_r1_append]
  rw [execWithEnv_append]
  -- Step 6: Apply Round 1 correctness
  rw [wm_round1_correct a b drest _ frame frames adv fuel
      (by simp only [frame]; omega)
      (by mem_simp) (by mem_simp) (by mem_simp) (by mem_simp)
      (by mem_simp) (by mem_simp) (by mem_simp) (by mem_simp)]
  simp only [bind, Bind.bind, Option.bind]
  -- Step 7: Decompose rest_after_r1 into round 2 + rest_after_r2
  rw [show (wm_rest_after_r1 : List Op) = wm_round2 ++ wm_rest_after_r2 from wm_rest_after_r1_eq_r2_append]
  rw [execWithEnv_append]
  -- Step 8: Apply Round 2 correctness (b₁ × a[0..6])
  -- Abbreviate Round 1 carry chain in the goal
  set c₁₀ := mulstepCarry 0 a.a0.val b.a0.val 0
  set c₂₀ := mulstepCarry c₁₀ a.a1.val b.a0.val 0
  set c₃₀ := mulstepCarry c₂₀ a.a2.val b.a0.val 0
  set c₄₀ := mulstepCarry c₃₀ a.a3.val b.a0.val 0
  set c₅₀ := mulstepCarry c₄₀ a.a4.val b.a0.val 0
  set c₆₀ := mulstepCarry c₅₀ a.a5.val b.a0.val 0
  set c₇₀ := mulstepCarry c₆₀ a.a6.val b.a0.val 0
  rw [wm_round2_correct a b drest _ frame frames adv fuel
      (by simp only [frame]; omega)
      (mulstepLo 0 a.a0.val b.a0.val 0)
      (mulstepLo c₁₀ a.a1.val b.a0.val 0)
      (mulstepLo c₂₀ a.a2.val b.a0.val 0)
      (mulstepLo c₃₀ a.a3.val b.a0.val 0)
      (mulstepLo c₄₀ a.a4.val b.a0.val 0)
      (mulstepLo c₅₀ a.a5.val b.a0.val 0)
      (mulstepLo c₆₀ a.a6.val b.a0.val 0)
      (mulstepLo c₇₀ a.a7.val b.a0.val 0)
      (mulstepLo_isU32 _ _ _ _) (mulstepLo_isU32 _ _ _ _) (mulstepLo_isU32 _ _ _ _)
      (mulstepLo_isU32 _ _ _ _) (mulstepLo_isU32 _ _ _ _) (mulstepLo_isU32 _ _ _ _) (mulstepLo_isU32 _ _ _ _)
      (by mem_simp) (by mem_simp) (by mem_simp) (by mem_simp)
      (by mem_simp) (by mem_simp) (by mem_simp) (by mem_simp)
      (by mem_simp) (by mem_simp) (by mem_simp) (by mem_simp)
      (by mem_simp) (by mem_simp) (by mem_simp) (by mem_simp)
      (by mem_simp) (by mem_simp) (by mem_simp) (by mem_simp)]
  simp only [bind, Bind.bind, Option.bind]
  -- Step 9: Decompose rest_after_r2 into round 3 + rest_after_r3
  rw [show (wm_rest_after_r2 : List Op) = wm_round3 ++ wm_rest_after_r3 from wm_rest_after_r2_eq_r3_append]
  rw [execWithEnv_append]
  -- Step 10: Apply Round 3 correctness (b₂ × a[0..5])
  -- Abbreviate Round 2 carry chain
  set c₁₁ := mulstepCarry 0 a.a0.val b.a1.val (mulstepLo c₁₀ a.a1.val b.a0.val 0)
  set c₂₁ := mulstepCarry c₁₁ a.a1.val b.a1.val (mulstepLo c₂₀ a.a2.val b.a0.val 0)
  set c₃₁ := mulstepCarry c₂₁ a.a2.val b.a1.val (mulstepLo c₃₀ a.a3.val b.a0.val 0)
  set c₄₁ := mulstepCarry c₃₁ a.a3.val b.a1.val (mulstepLo c₄₀ a.a4.val b.a0.val 0)
  set c₅₁ := mulstepCarry c₄₁ a.a4.val b.a1.val (mulstepLo c₅₀ a.a5.val b.a0.val 0)
  rw [wm_round3_correct a b drest _ frame frames adv fuel
      (by simp only [frame]; omega)
      (mulstepLo 0 a.a0.val b.a0.val 0)
      (mulstepLo 0 a.a0.val b.a1.val (mulstepLo c₁₀ a.a1.val b.a0.val 0))
      (mulstepLo c₁₁ a.a1.val b.a1.val (mulstepLo c₂₀ a.a2.val b.a0.val 0))
      (mulstepLo c₂₁ a.a2.val b.a1.val (mulstepLo c₃₀ a.a3.val b.a0.val 0))
      (mulstepLo c₃₁ a.a3.val b.a1.val (mulstepLo c₄₀ a.a4.val b.a0.val 0))
      (mulstepLo c₄₁ a.a4.val b.a1.val (mulstepLo c₅₀ a.a5.val b.a0.val 0))
      (mulstepLo c₅₁ a.a5.val b.a1.val (mulstepLo c₆₀ a.a6.val b.a0.val 0))
      (mulstepLo (mulstepCarry c₅₁ a.a5.val b.a1.val (mulstepLo c₆₀ a.a6.val b.a0.val 0))
        a.a6.val b.a1.val (mulstepLo c₇₀ a.a7.val b.a0.val 0))
      (mulstepLo_isU32 _ _ _ _) (mulstepLo_isU32 _ _ _ _)
      (mulstepLo_isU32 _ _ _ _) (mulstepLo_isU32 _ _ _ _)
      (mulstepLo_isU32 _ _ _ _) (mulstepLo_isU32 _ _ _ _)
      (by mem_simp) (by mem_simp) (by mem_simp) (by mem_simp)
      (by mem_simp) (by mem_simp) (by mem_simp) (by mem_simp)
      (by mem_simp) (by mem_simp) (by mem_simp) (by mem_simp)
      (by mem_simp) (by mem_simp) (by mem_simp) (by mem_simp)
      (by mem_simp) (by mem_simp) (by mem_simp) (by mem_simp)]
  simp only [bind, Bind.bind, Option.bind]
  -- Step 11: Decompose rest_after_r3 into round 4 + rest_after_r4
  rw [show (wm_rest_after_r3 : List Op) = wm_round4 ++ wm_rest_after_r4 from wm_rest_after_r3_eq_r4_append]
  rw [execWithEnv_append]
  -- Step 12: Apply Round 4 correctness (b₃ × a[0..4])
  -- Abbreviate Round 3 carry chain
  set c₁₂ := mulstepCarry 0 a.a0.val b.a2.val
    (mulstepLo c₁₁ a.a1.val b.a1.val (mulstepLo c₂₀ a.a2.val b.a0.val 0))
  set c₂₂ := mulstepCarry c₁₂ a.a1.val b.a2.val
    (mulstepLo c₂₁ a.a2.val b.a1.val (mulstepLo c₃₀ a.a3.val b.a0.val 0))
  set c₃₂ := mulstepCarry c₂₂ a.a2.val b.a2.val
    (mulstepLo c₃₁ a.a3.val b.a1.val (mulstepLo c₄₀ a.a4.val b.a0.val 0))
  set c₄₂ := mulstepCarry c₃₂ a.a3.val b.a2.val
    (mulstepLo c₄₁ a.a4.val b.a1.val (mulstepLo c₅₀ a.a5.val b.a0.val 0))
  rw [wm_round4_correct a b drest _ frame frames adv fuel
      (by simp only [frame]; omega)
      (mulstepLo 0 a.a0.val b.a0.val 0)
      (mulstepLo 0 a.a0.val b.a1.val (mulstepLo c₁₀ a.a1.val b.a0.val 0))
      (mulstepLo 0 a.a0.val b.a2.val
        (mulstepLo c₁₁ a.a1.val b.a1.val (mulstepLo c₂₀ a.a2.val b.a0.val 0)))
      (mulstepLo c₁₂ a.a1.val b.a2.val
        (mulstepLo c₂₁ a.a2.val b.a1.val (mulstepLo c₃₀ a.a3.val b.a0.val 0)))
      (mulstepLo c₂₂ a.a2.val b.a2.val
        (mulstepLo c₃₁ a.a3.val b.a1.val (mulstepLo c₄₀ a.a4.val b.a0.val 0)))
      (mulstepLo c₃₂ a.a3.val b.a2.val
        (mulstepLo c₄₁ a.a4.val b.a1.val (mulstepLo c₅₀ a.a5.val b.a0.val 0)))
      (mulstepLo c₄₂ a.a4.val b.a2.val
        (mulstepLo c₅₁ a.a5.val b.a1.val (mulstepLo c₆₀ a.a6.val b.a0.val 0)))
      (mulstepLo (mulstepCarry c₄₂ a.a4.val b.a2.val
          (mulstepLo c₅₁ a.a5.val b.a1.val (mulstepLo c₆₀ a.a6.val b.a0.val 0)))
        a.a5.val b.a2.val
        (mulstepLo (mulstepCarry c₅₁ a.a5.val b.a1.val (mulstepLo c₆₀ a.a6.val b.a0.val 0))
          a.a6.val b.a1.val (mulstepLo c₇₀ a.a7.val b.a0.val 0)))
      (mulstepLo_isU32 _ _ _ _)
      (mulstepLo_isU32 _ _ _ _) (mulstepLo_isU32 _ _ _ _)
      (mulstepLo_isU32 _ _ _ _) (mulstepLo_isU32 _ _ _ _)
      (by mem_simp) (by mem_simp) (by mem_simp) (by mem_simp)
      (by mem_simp) (by mem_simp) (by mem_simp) (by mem_simp)
      (by mem_simp) (by mem_simp) (by mem_simp) (by mem_simp)
      (by mem_simp) (by mem_simp) (by mem_simp) (by mem_simp)
      (by mem_simp) (by mem_simp) (by mem_simp) (by mem_simp)]
  simp only [bind, Bind.bind, Option.bind]
  -- Step 13: Decompose rest_after_r4 into round 5 + epilogue_and_final
  rw [show (wm_rest_after_r4 : List Op) = wm_round5 ++ wm_epilogue_and_final from wm_rest_after_r4_eq_r5_append]
  rw [execWithEnv_append]
  -- Step 14: Apply Round 5 correctness (b₄ × a[0..3])
  -- Abbreviate Round 4 carry chain
  set c₁₃ := mulstepCarry 0 a.a0.val b.a3.val
    (mulstepLo c₁₂ a.a1.val b.a2.val
      (mulstepLo c₂₁ a.a2.val b.a1.val (mulstepLo c₃₀ a.a3.val b.a0.val 0)))
  set c₂₃ := mulstepCarry c₁₃ a.a1.val b.a3.val
    (mulstepLo c₂₂ a.a2.val b.a2.val
      (mulstepLo c₃₁ a.a3.val b.a1.val (mulstepLo c₄₀ a.a4.val b.a0.val 0)))
  set c₃₃ := mulstepCarry c₂₃ a.a2.val b.a3.val
    (mulstepLo c₃₂ a.a3.val b.a2.val
      (mulstepLo c₄₁ a.a4.val b.a1.val (mulstepLo c₅₀ a.a5.val b.a0.val 0)))
  rw [wm_round5_correct a b drest _ frame frames adv fuel
      (by simp only [frame]; omega)
      _ _ _ _
      (mulstepLo_isU32 _ _ _ _) (mulstepLo_isU32 _ _ _ _)
      (mulstepLo_isU32 _ _ _ _) (mulstepLo_isU32 _ _ _ _)
      (by mem_simp) (by mem_simp) (by mem_simp) (by mem_simp)
      (by mem_simp) (by mem_simp) (by mem_simp) (by mem_simp)
      (by mem_simp) (by mem_simp) (by mem_simp) (by mem_simp)]
  simp only [bind, Bind.bind, Option.bind]
  -- Step 15: Decompose epilogue_and_final into ep_b5 + rest
  rw [show (wm_epilogue_and_final : List Op) = wm_ep_b5 ++ wm_ep_b6_b7_final from wm_epilogue_split_b5]
  rw [execWithEnv_append]
  -- Step 16: Apply epilogue b₅ correctness
  rw [wm_ep_b5_correct a b drest _ frame frames adv fuel
      (by simp only [frame]; omega) _ _ _ _
      (mulstepLo_isU32 _ _ _ _) (mulstepLo_isU32 _ _ _ _) (mulstepLo_isU32 _ _ _ _)
      (by mem_simp) (by mem_simp) (by mem_simp) (by mem_simp)
      (by mem_simp) (by mem_simp) (by mem_simp) (by mem_simp)]
  simp only [bind, Bind.bind, Option.bind]
  -- Normalize ep_b5 argument order: b₅,a₁ → a₁,b₅ to match bridge lemma
  rw [mulstepCarry_comm _ b.a5.val a.a1.val, mulstepLo_comm _ b.a5.val a.a1.val]
  -- Step 17: Decompose remaining into ep_b6 + ep_b7_final
  rw [show (wm_ep_b6_b7_final : List Op) = wm_ep_b6 ++ wm_ep_b7_final from wm_ep_b6_b7_final_split]
  rw [execWithEnv_append]
  -- Step 18: Apply epilogue b₆ correctness
  rw [wm_ep_b6_correct a b drest _ frame frames adv fuel
      (by simp only [frame]; omega) _ _ _ _
      (mulstepLo_isU32 _ _ _ _) (mulstepLo_isU32 _ _ _ _)
      (by mem_simp) (by mem_simp) (by mem_simp) (by mem_simp)
      (by mem_simp) (by mem_simp) (by mem_simp) (by mem_simp)]
  simp only [bind, Bind.bind, Option.bind]
  -- Step 19: Decompose remaining into ep_b7 + final
  rw [show (wm_ep_b7_final : List Op) = wm_ep_b7 ++ wm_final from wm_ep_b7_final_split]
  rw [execWithEnv_append]
  -- Step 20: Apply epilogue b₇ correctness
  rw [wm_ep_b7_correct a b drest _ frame frames adv fuel
      (by simp only [frame]; omega) _ _ _ _
      (mulstepLo_isU32 _ _ _ _)
      (by mem_simp) (by mem_simp) (by mem_simp) (by mem_simp)
      (by mem_simp) (by mem_simp) (by mem_simp) (by mem_simp)]
  simp only [bind, Bind.bind, Option.bind]
  -- Step 21: Apply final phase correctness (unfold drest for explicit dummy elements)
  rw [show (drest : List Felt) = d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: d6 :: d7 ::
    d8 :: d9 :: d10 :: d11 :: d12 :: d13 :: d14 :: d15 :: rest from hdrest]
  rw [wm_final_correct rest _ frame frames adv fuel
      (by simp only [frame]; omega) _ _ _ _
      (mulstepLo 0 a.a0.val b.a0.val 0)
      (mulstepLo 0 a.a0.val b.a1.val (mulstepLo c₁₀ a.a1.val b.a0.val 0))
      (mulstepLo 0 a.a0.val b.a2.val
        (mulstepLo c₁₁ a.a1.val b.a1.val (mulstepLo c₂₀ a.a2.val b.a0.val 0)))
      (mulstepLo 0 a.a0.val b.a3.val
        (mulstepLo c₁₂ a.a1.val b.a2.val
          (mulstepLo c₂₁ a.a2.val b.a1.val (mulstepLo c₃₀ a.a3.val b.a0.val 0))))
      d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
      (by mem_simp) (by mem_simp) (by mem_simp) (by mem_simp)]
  -- Semantic bridge: mulstep chain = (a * b) mod 2^256
  have hlimbs := wrapping_mul_limbs_correct a b
  exact ⟨_, by
    congr 1
    congr 1
    exact List.cons_eq_cons.mpr ⟨hlimbs.1, List.cons_eq_cons.mpr ⟨hlimbs.2.1,
      List.cons_eq_cons.mpr ⟨hlimbs.2.2.1, List.cons_eq_cons.mpr ⟨hlimbs.2.2.2.1,
      List.cons_eq_cons.mpr ⟨hlimbs.2.2.2.2.1, List.cons_eq_cons.mpr ⟨hlimbs.2.2.2.2.2.1,
      List.cons_eq_cons.mpr ⟨hlimbs.2.2.2.2.2.2.1, List.cons_eq_cons.mpr
        ⟨hlimbs.2.2.2.2.2.2.2, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩

end MidenLean.Proofs
