import MidenLean.Proofs.U256.WrappingMulDefs

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

-- ============================================================================
-- Round 4 Part A: pre-load + mulstep4 + store la(16)
-- ============================================================================

set_option maxHeartbeats 64000000 in
/-- Round 4 Part A: load accumulators [q₂, q₁, q₀, p₃] and operands, run mulstep4 for b₃ × a[0..3],
    store updated partial products to la(16).
    Input stack: rest
    Output stack: [lo4, lo3, lo2, a₇, a₆, a₅, a₄, carry4, b₃] ++ rest -/
theorem wm_r4a_spec (a b : U256) (rest : List Felt)
    (mem : Nat → Felt) (frame : LocalFrame) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) (hnl : frame.numLocals ≥ 24)
    (p₀ p₁ p₂ p₃ q₀ q₁ q₂ q₃ : Felt)
    (hp₃ : p₃.isU32 = true)
    (hq₀ : q₀.isU32 = true) (hq₁ : q₁.isU32 = true) (hq₂ : q₂.isU32 = true)
    (h16_3 : mem (frame.localAddr 16 + 3) = p₃)
    (h16_2 : mem (frame.localAddr 16 + 2) = p₂)
    (h16_1 : mem (frame.localAddr 16 + 1) = p₁)
    (h16_0 : mem (frame.localAddr 16) = p₀)
    (h20_3 : mem (frame.localAddr 20 + 3) = q₃)
    (h20_2 : mem (frame.localAddr 20 + 2) = q₂)
    (h20_1 : mem (frame.localAddr 20 + 1) = q₁)
    (h20_0 : mem (frame.localAddr 20) = q₀)
    (h12_3 : mem (frame.localAddr 12 + 3) = a.a3.val)
    (h12_2 : mem (frame.localAddr 12 + 2) = a.a2.val)
    (h12_1 : mem (frame.localAddr 12 + 1) = a.a1.val)
    (h12_0 : mem (frame.localAddr 12) = a.a0.val)
    (h8_3 : mem (frame.localAddr 8 + 3) = a.a7.val)
    (h8_2 : mem (frame.localAddr 8 + 2) = a.a6.val)
    (h8_1 : mem (frame.localAddr 8 + 1) = a.a5.val)
    (h8_0 : mem (frame.localAddr 8) = a.a4.val)
    (h4_3 : mem (frame.localAddr 4 + 3) = b.a3.val)
    (h4_2 : mem (frame.localAddr 4 + 2) = b.a2.val)
    (h4_1 : mem (frame.localAddr 4 + 1) = b.a1.val)
    (h4_0 : mem (frame.localAddr 4) = b.a0.val) :
    let la := frame.localAddr
    let carry1 := mulstepCarry 0 a.a0.val b.a3.val p₃
    let lo1 := mulstepLo 0 a.a0.val b.a3.val p₃
    let carry2 := mulstepCarry carry1 a.a1.val b.a3.val q₀
    let carry3 := mulstepCarry carry2 a.a2.val b.a3.val q₁
    let lo3 := mulstepLo carry2 a.a2.val b.a3.val q₁
    let carry4 := mulstepCarry carry3 a.a3.val b.a3.val q₂
    let lo4 := mulstepLo carry3 a.a3.val b.a3.val q₂
    execProcedure u256ProcEnv (fuel + 3)
      ⟨rest, mem, frame :: frames, adv⟩
      (Procedure.ofOps wm_r4a) =
    some ⟨lo4 :: lo3 :: mulstepLo carry1 a.a1.val b.a3.val q₀ ::
          a.a7.val :: a.a6.val :: a.a5.val :: a.a4.val :: carry4 :: b.a3.val :: rest,
          fun i =>
            if i = la 16 + 3 then lo1
            else if i = la 16 + 2 then p₂
            else if i = la 16 + 1 then p₁
            else if i = la 16 then p₀
            else mem i,
          frame :: frames, adv⟩ := by
  -- Split into pre (loads) + post (mulstep4 + store)
  rw [show (wm_r4a : List Op) = wm_r4a_pre ++ wm_r4a_post from rfl]
  rw [execProcedure_append]
  -- Part A pre: load accumulators, operands, extract b₃
  show (do
    let s ← execProcedure u256ProcEnv (fuel + 3)
      ⟨rest, mem, frame :: frames, adv⟩ (Procedure.ofOps wm_r4a_pre)
    execProcedure u256ProcEnv (fuel + 3) s (Procedure.ofOps wm_r4a_post)) = _
  conv_lhs => rw [show execProcedure u256ProcEnv (fuel + 3)
      ⟨rest, mem, frame :: frames, adv⟩ (Procedure.ofOps wm_r4a_pre) =
    some ⟨b.a3.val :: a.a7.val :: a.a6.val :: a.a5.val :: a.a4.val ::
          a.a3.val :: a.a2.val :: a.a1.val :: a.a0.val :: q₂ :: q₁ :: q₀ :: p₃ :: rest,
          mem, frame :: frames, adv⟩ from by
    unfold wm_r4a_pre execProcedure Procedure.ofOps
    simp only [List.foldlM]
    dsimp only [bind, Bind.bind, Option.bind]
    rw [stepPadw]; dsimp only [bind, Bind.bind, Option.bind]
    rw [stepLocLoadwBe (halign := wm_align_16) (hbound := wm_bound_16 hnl)]
    rw [h16_3, h16_2, h16_1, h16_0]; dsimp only [bind, Bind.bind, Option.bind]
    rw [stepPadw]; dsimp only [bind, Bind.bind, Option.bind]
    rw [stepLocLoadwBe (halign := wm_align_20) (hbound := wm_bound_20 hnl)]
    rw [h20_3, h20_2, h20_1, h20_0]; dsimp only [bind, Bind.bind, Option.bind]
    miden_movup; miden_movup; miden_movup
    rw [stepDropw]; dsimp only [bind, Bind.bind, Option.bind]
    rw [stepPadw]; dsimp only [bind, Bind.bind, Option.bind]
    rw [stepLocLoadwBe (halign := wm_align_12) (hbound := wm_bound_12 hnl)]
    rw [h12_3, h12_2, h12_1, h12_0]; dsimp only [bind, Bind.bind, Option.bind]
    rw [stepPadw]; dsimp only [bind, Bind.bind, Option.bind]
    rw [stepLocLoadwBe (halign := wm_align_8) (hbound := wm_bound_8 hnl)]
    rw [h8_3, h8_2, h8_1, h8_0]; dsimp only [bind, Bind.bind, Option.bind]
    rw [stepPadw]; dsimp only [bind, Bind.bind, Option.bind]
    rw [stepLocLoadwBe (halign := wm_align_4) (hbound := wm_bound_4 hnl)]
    rw [h4_3, h4_2, h4_1, h4_0]; dsimp only [bind, Bind.bind, Option.bind]
    miden_movdn; miden_step
    rw [stepDropw]; simp only [pure, Pure.pure]]
  dsimp only [bind, Bind.bind, Option.bind]
  -- Part A post: mulstep4 + post-shuffle + store la(16)
  unfold wm_r4a_post execProcedure Procedure.ofOps
  simp only [List.foldlM, u256ProcEnv]
  dsimp only [bind, Bind.bind, Option.bind]
  -- execProcedure emptyEnv "mulstep4"
  have hmul4 := u256_mulstep4_correct
    b.a3.val a.a7.val a.a6.val a.a5.val a.a4.val
    a.a3.val a.a2.val a.a1.val a.a0.val
    q₂ q₁ q₀ p₃ rest
    ⟨b.a3.val :: a.a7.val :: a.a6.val :: a.a5.val :: a.a4.val ::
     a.a3.val :: a.a2.val :: a.a1.val :: a.a0.val :: q₂ :: q₁ :: q₀ :: p₃ :: rest,
     mem, frame :: frames, adv⟩
    rfl (U256.a3_isU32 b) (U256.a3_isU32 a) (U256.a2_isU32 a) (U256.a1_isU32 a) (U256.a0_isU32 a)
    hq₂ hq₁ hq₀ hp₃ fuel
  simp only [Concrete.State.withStack] at hmul4
  rw [hmul4]; clear hmul4; dsimp only [bind, Bind.bind, Option.bind]
  -- movdn 9, movdn 9
  miden_movdn; miden_movdn
  -- swapw 1
  rw [stepSwapw1]; dsimp only [bind, Bind.bind, Option.bind]
  -- movup 3
  miden_movup
  -- padw
  rw [stepPadw]; dsimp only [bind, Bind.bind, Option.bind]
  -- locLoadwBe 16 (re-load original values)
  rw [stepLocLoadwBe (halign := wm_align_16) (hbound := wm_bound_16 hnl)]
  rw [h16_3, h16_2, h16_1, h16_0]; dsimp only [bind, Bind.bind, Option.bind]
  -- drop (remove p₃)
  rw [stepDrop]; dsimp only [bind, Bind.bind, Option.bind]
  -- movup 3
  miden_movup
  -- locStorewBe 16
  rw [stepLocStorewBe (halign := wm_align_16) (hbound := wm_bound_16 hnl)]
  dsimp only [bind, Bind.bind, Option.bind]
  -- dropw
  rw [stepDropw]; simp only [pure, Pure.pure]

-- ============================================================================
-- Round 4 Part B: 1 individual mulstep for b₃ × a₄
-- ============================================================================

set_option maxHeartbeats 32000000 in
/-- Round 4 Part B: load la(20), extract q₃, run 1 mulstep, cleanup.
    Input stack: [lo4, lo3, lo2, a₇, a₆, a₅, a₄, carry4, b₃] ++ rest
    Output stack: [l₅, lo4, lo3, lo2] ++ rest -/
private theorem wm_r4b_correct (a b : U256) (rest : List Felt)
    (mem : Nat → Felt) (frame : LocalFrame) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) (hnl : frame.numLocals ≥ 24)
    (lo4 lo3 lo2 carry4 : Felt) (hcarry4 : carry4.isU32 = true)
    (q₀ q₁ q₂ q₃ : Felt) (hq₃ : q₃.isU32 = true)
    (h20_3 : mem (frame.localAddr 20 + 3) = q₃)
    (h20_2 : mem (frame.localAddr 20 + 2) = q₂)
    (h20_1 : mem (frame.localAddr 20 + 1) = q₁)
    (h20_0 : mem (frame.localAddr 20) = q₀) :
    let l₅ := mulstepLo carry4 a.a4.val b.a3.val q₃
    execProcedure u256ProcEnv (fuel + 3)
      ⟨lo4 :: lo3 :: lo2 :: a.a7.val :: a.a6.val :: a.a5.val :: a.a4.val ::
       carry4 :: b.a3.val :: rest,
       mem, frame :: frames, adv⟩
      (Procedure.ofOps wm_r4b) =
    some ⟨l₅ :: lo4 :: lo3 :: lo2 :: rest,
          mem, frame :: frames, adv⟩ := by
  unfold wm_r4b execProcedure Procedure.ofOps
  simp only [List.foldlM, u256ProcEnv]
  dsimp only [bind, Bind.bind, Option.bind]
  -- padw
  rw [stepPadw]; dsimp only [bind, Bind.bind, Option.bind]
  -- locLoadwBe 20
  rw [stepLocLoadwBe (halign := wm_align_20) (hbound := wm_bound_20 hnl)]
  rw [h20_3, h20_2, h20_1, h20_0]; dsimp only [bind, Bind.bind, Option.bind]
  -- movdn 3 (q₃ to position 3)
  miden_movdn
  -- push 0
  miden_step
  -- dropw (removes 0, q₂, q₁, q₀ → keeps q₃)
  rw [stepDropw]; dsimp only [bind, Bind.bind, Option.bind]
  -- swapw 1
  rw [stepSwapw1]; dsimp only [bind, Bind.bind, Option.bind]
  -- movup 9, movup 9
  miden_movup; miden_movup
  -- swap 1
  miden_swap
  -- movup 5
  miden_movup
  -- movup 6
  miden_movup
  -- swap 3
  miden_swap
  -- execProcedure emptyEnv "mulstep"
  have hms := mulstep_execWithEnv u256ProcEnv (fuel + 1)
    carry4 a.a4.val b.a3.val q₃
    (a.a7.val :: a.a6.val :: a.a5.val :: lo4 :: lo3 :: lo2 :: rest)
    ⟨carry4 :: a.a4.val :: b.a3.val :: q₃ ::
     a.a7.val :: a.a6.val :: a.a5.val :: lo4 :: lo3 :: lo2 :: rest,
     mem, frame :: frames, adv⟩
    rfl hcarry4 (U256.a4_isU32 a) (U256.a3_isU32 b) hq₃
  simp only [Concrete.State.withStack] at hms
  rw [hms]; clear hms; dsimp only [bind, Bind.bind, Option.bind]
  -- drop (remove carry)
  rw [stepDrop]; dsimp only [bind, Bind.bind, Option.bind]
  -- movdn 3
  miden_movdn
  -- push 0
  miden_step
  -- dropw (removes 0, a₇, a₆, a₅)
  rw [stepDropw]; simp only [pure, Pure.pure]

-- ============================================================================
-- Round 4 correctness
-- ============================================================================

set_option maxHeartbeats 16000000 in
/-- Round 4: b₃ × a[0..4] with accumulators from Round 3.
    Input stack: rest
    Output stack: [l₅, lo4, lo3, lo2] ++ rest
    Memory: la(16) position 3 updated. -/
theorem wm_round4_correct (a b : U256) (rest : List Felt)
    (mem : Nat → Felt) (frame : LocalFrame) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) (hnl : frame.numLocals ≥ 24)
    (p₀ p₁ p₂ p₃ q₀ q₁ q₂ q₃ : Felt)
    (hp₃ : p₃.isU32 = true)
    (hq₀ : q₀.isU32 = true) (hq₁ : q₁.isU32 = true)
    (hq₂ : q₂.isU32 = true) (hq₃ : q₃.isU32 = true)
    (h16_3 : mem (frame.localAddr 16 + 3) = p₃)
    (h16_2 : mem (frame.localAddr 16 + 2) = p₂)
    (h16_1 : mem (frame.localAddr 16 + 1) = p₁)
    (h16_0 : mem (frame.localAddr 16) = p₀)
    (h20_3 : mem (frame.localAddr 20 + 3) = q₃)
    (h20_2 : mem (frame.localAddr 20 + 2) = q₂)
    (h20_1 : mem (frame.localAddr 20 + 1) = q₁)
    (h20_0 : mem (frame.localAddr 20) = q₀)
    (h12_3 : mem (frame.localAddr 12 + 3) = a.a3.val)
    (h12_2 : mem (frame.localAddr 12 + 2) = a.a2.val)
    (h12_1 : mem (frame.localAddr 12 + 1) = a.a1.val)
    (h12_0 : mem (frame.localAddr 12) = a.a0.val)
    (h8_3 : mem (frame.localAddr 8 + 3) = a.a7.val)
    (h8_2 : mem (frame.localAddr 8 + 2) = a.a6.val)
    (h8_1 : mem (frame.localAddr 8 + 1) = a.a5.val)
    (h8_0 : mem (frame.localAddr 8) = a.a4.val)
    (h4_3 : mem (frame.localAddr 4 + 3) = b.a3.val)
    (h4_2 : mem (frame.localAddr 4 + 2) = b.a2.val)
    (h4_1 : mem (frame.localAddr 4 + 1) = b.a1.val)
    (h4_0 : mem (frame.localAddr 4) = b.a0.val) :
    let la := frame.localAddr
    let carry1 := mulstepCarry 0 a.a0.val b.a3.val p₃
    let carry2 := mulstepCarry carry1 a.a1.val b.a3.val q₀
    let carry3 := mulstepCarry carry2 a.a2.val b.a3.val q₁
    let carry4 := mulstepCarry carry3 a.a3.val b.a3.val q₂
    execProcedure u256ProcEnv (fuel + 3)
      ⟨rest, mem, frame :: frames, adv⟩
      (Procedure.ofOps wm_round4) =
    some ⟨mulstepLo carry4 a.a4.val b.a3.val q₃ ::
          mulstepLo carry3 a.a3.val b.a3.val q₂ ::
          mulstepLo carry2 a.a2.val b.a3.val q₁ ::
          mulstepLo carry1 a.a1.val b.a3.val q₀ :: rest,
          fun i =>
            if i = la 16 + 3 then mulstepLo 0 a.a0.val b.a3.val p₃
            else if i = la 16 + 2 then p₂
            else if i = la 16 + 1 then p₁
            else if i = la 16 then p₀
            else mem i,
          frame :: frames, adv⟩ := by
  rw [show (wm_round4 : List Op) = wm_r4a ++ wm_r4b from wm_round4_eq_r4a_r4b]
  rw [execProcedure_append]
  -- Apply Part A
  rw [wm_r4a_spec a b rest mem frame frames adv fuel hnl
      p₀ p₁ p₂ p₃ q₀ q₁ q₂ q₃ hp₃ hq₀ hq₁ hq₂
      h16_3 h16_2 h16_1 h16_0 h20_3 h20_2 h20_1 h20_0
      h12_3 h12_2 h12_1 h12_0 h8_3 h8_2 h8_1 h8_0
      h4_3 h4_2 h4_1 h4_0]
  simp only [bind, Bind.bind, Option.bind]
  -- Apply Part B (la(20) reads pass through la(16) updates)
  have hcarry4u : (mulstepCarry
    (mulstepCarry (mulstepCarry (mulstepCarry 0 a.a0.val b.a3.val p₃)
      a.a1.val b.a3.val q₀) a.a2.val b.a3.val q₁) a.a3.val b.a3.val q₂).isU32 = true := by
    apply mulstep_carry_isU32
    · apply mulstep_carry_isU32
      · apply mulstep_carry_isU32
        · apply mulstep_carry_isU32
          · simp [Felt.isU32]
          · exact U256.a0_isU32 a
          · exact U256.a3_isU32 b
          · exact hp₃
        · exact U256.a1_isU32 a
        · exact U256.a3_isU32 b
        · exact hq₀
      · exact U256.a2_isU32 a
      · exact U256.a3_isU32 b
      · exact hq₁
    · exact U256.a3_isU32 a
    · exact U256.a3_isU32 b
    · exact hq₂
  rw [wm_r4b_correct a b rest _ frame frames adv fuel hnl _ _ _ _ hcarry4u
      q₀ q₁ q₂ q₃ hq₃
      (by mem_simp; exact h20_3) (by mem_simp; exact h20_2) (by mem_simp; exact h20_1) (by mem_simp; exact h20_0)]

end MidenLean.Proofs
