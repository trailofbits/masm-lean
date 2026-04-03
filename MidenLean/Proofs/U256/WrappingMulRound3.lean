import MidenLean.Proofs.U256.WrappingMulDefs

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

-- ============================================================================
-- Round 3 Part A: pre-load + mulstep4 + store la(16)
-- ============================================================================

set_option maxHeartbeats 64000000 in
/-- Round 3 Part A: load accumulators [q₁, q₀, p₃, p₂] and operands, run mulstep4 for b₂ × a[0..3],
    store updated partial products to la(16).
    Input stack: rest
    Output stack: [lo4, lo3, a₇, a₆, a₅, a₄, carry4, b₂] ++ rest -/
theorem wm_r3a_correct (a b : U256) (rest : List Felt)
    (mem : Nat → Felt) (frame : LocalFrame) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) (hnl : frame.numLocals ≥ 24)
    (p₀ p₁ p₂ p₃ q₀ q₁ q₂ q₃ : Felt)
    (hp₂ : p₂.isU32 = true) (hp₃ : p₃.isU32 = true)
    (hq₀ : q₀.isU32 = true) (hq₁ : q₁.isU32 = true)
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
    let carry1 := mulstepCarry 0 a.a0.val b.a2.val p₂
    let lo1 := mulstepLo 0 a.a0.val b.a2.val p₂
    let carry2 := mulstepCarry carry1 a.a1.val b.a2.val p₃
    let lo2 := mulstepLo carry1 a.a1.val b.a2.val p₃
    let carry3 := mulstepCarry carry2 a.a2.val b.a2.val q₀
    let lo3 := mulstepLo carry2 a.a2.val b.a2.val q₀
    let carry4 := mulstepCarry carry3 a.a3.val b.a2.val q₁
    let lo4 := mulstepLo carry3 a.a3.val b.a2.val q₁
    execWithEnv u256ProcEnv (fuel + 3)
      ⟨rest, mem, frame :: frames, adv⟩
      (Procedure.ofOps wm_r3a) =
    some ⟨lo4 :: lo3 :: a.a7.val :: a.a6.val :: a.a5.val :: a.a4.val :: carry4 :: b.a2.val :: rest,
          fun i =>
            if i = la 16 + 3 then lo2
            else if i = la 16 + 2 then lo1
            else if i = la 16 + 1 then p₁
            else if i = la 16 then p₀
            else mem i,
          frame :: frames, adv⟩ := by
  -- Split into pre (loads) + post (mulstep4 + store)
  rw [show (wm_r3a : List Op) = wm_r3a_pre ++ wm_r3a_post from rfl]
  rw [execWithEnv_append]
  -- Part A pre: load accumulators, operands, extract b₂
  show (do
    let s ← execWithEnv u256ProcEnv (fuel + 3)
      ⟨rest, mem, frame :: frames, adv⟩ (Procedure.ofOps wm_r3a_pre)
    execWithEnv u256ProcEnv (fuel + 3) s (Procedure.ofOps wm_r3a_post)) = _
  conv_lhs => rw [show execWithEnv u256ProcEnv (fuel + 3)
      ⟨rest, mem, frame :: frames, adv⟩ (Procedure.ofOps wm_r3a_pre) =
    some ⟨b.a2.val :: a.a7.val :: a.a6.val :: a.a5.val :: a.a4.val ::
          a.a3.val :: a.a2.val :: a.a1.val :: a.a0.val :: q₁ :: q₀ :: p₃ :: p₂ :: rest,
          mem, frame :: frames, adv⟩ from by
    unfold wm_r3a_pre execWithEnv Procedure.ofOps
    simp only [List.foldlM]
    dsimp only [bind, Bind.bind, Option.bind]
    rw [stepPadw]; dsimp only [bind, Bind.bind, Option.bind]
    rw [stepLocLoadwBe (halign := wm_align_16) (hbound := wm_bound_16 hnl)]
    rw [h16_3, h16_2, h16_1, h16_0]; dsimp only [bind, Bind.bind, Option.bind]
    rw [stepPadw]; dsimp only [bind, Bind.bind, Option.bind]
    rw [stepLocLoadwBe (halign := wm_align_20) (hbound := wm_bound_20 hnl)]
    rw [h20_3, h20_2, h20_1, h20_0]; dsimp only [bind, Bind.bind, Option.bind]
    miden_movup; miden_movup
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
    miden_swap; miden_movdn; miden_step
    rw [stepDropw]; simp only [pure, Pure.pure]]
  dsimp only [bind, Bind.bind, Option.bind]
  -- Part A post: mulstep4 + post-shuffle + store la(16)
  unfold wm_r3a_post execWithEnv Procedure.ofOps
  simp only [List.foldlM, u256ProcEnv]
  dsimp only [bind, Bind.bind, Option.bind]
  -- exec "mulstep4"
  have hmul4 := u256_mulstep4_correct
    b.a2.val a.a7.val a.a6.val a.a5.val a.a4.val
    a.a3.val a.a2.val a.a1.val a.a0.val
    q₁ q₀ p₃ p₂ rest
    ⟨b.a2.val :: a.a7.val :: a.a6.val :: a.a5.val :: a.a4.val ::
     a.a3.val :: a.a2.val :: a.a1.val :: a.a0.val :: q₁ :: q₀ :: p₃ :: p₂ :: rest,
     mem, frame :: frames, adv⟩
    rfl (U256.a2_isU32 b) (U256.a3_isU32 a) (U256.a2_isU32 a) (U256.a1_isU32 a) (U256.a0_isU32 a)
    hq₁ hq₀ hp₃ hp₂ fuel
  simp only [MidenState.withStack] at hmul4
  rw [hmul4]; clear hmul4; dsimp only [bind, Bind.bind, Option.bind]
  -- movdn 9, movdn 9
  miden_movdn; miden_movdn
  -- swapw 1
  rw [stepSwapw1]; dsimp only [bind, Bind.bind, Option.bind]
  -- movdn 3, movdn 3
  miden_movdn; miden_movdn
  -- padw
  rw [stepPadw]; dsimp only [bind, Bind.bind, Option.bind]
  -- locLoadwBe 16 (re-load original values)
  rw [stepLocLoadwBe (halign := wm_align_16) (hbound := wm_bound_16 hnl)]
  rw [h16_3, h16_2, h16_1, h16_0]; dsimp only [bind, Bind.bind, Option.bind]
  -- drop, drop (remove p₃, p₂)
  rw [stepDrop]; dsimp only [bind, Bind.bind, Option.bind]
  rw [stepDrop]; dsimp only [bind, Bind.bind, Option.bind]
  -- movdn 3, movdn 3
  miden_movdn; miden_movdn
  -- locStorewBe 16
  rw [stepLocStorewBe (halign := wm_align_16) (hbound := wm_bound_16 hnl)]
  dsimp only [bind, Bind.bind, Option.bind]
  -- dropw
  rw [stepDropw]; simp only [pure, Pure.pure]

-- ============================================================================
-- Round 3 Part B: 2 individual mulsteps for b₂ × a[4..5]
-- ============================================================================

set_option maxHeartbeats 32000000 in
/-- Round 3 Part B: load la(20), extract q₂/q₃, run 2 individual mulsteps, store to la(20).
    Input stack: [lo4, lo3, a₇, a₆, a₅, a₄, carry4, b₂] ++ rest
    Output stack: rest -/
private theorem wm_r3b_correct (a b : U256) (rest : List Felt)
    (mem : Nat → Felt) (frame : LocalFrame) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) (hnl : frame.numLocals ≥ 24)
    (lo4 lo3 carry4 : Felt) (hcarry4 : carry4.isU32 = true)
    (q₀ q₁ q₂ q₃ : Felt) (hq₂ : q₂.isU32 = true) (hq₃ : q₃.isU32 = true)
    (h20_3 : mem (frame.localAddr 20 + 3) = q₃)
    (h20_2 : mem (frame.localAddr 20 + 2) = q₂)
    (h20_1 : mem (frame.localAddr 20 + 1) = q₁)
    (h20_0 : mem (frame.localAddr 20) = q₀) :
    let la := frame.localAddr
    let c₅ := mulstepCarry carry4 a.a4.val b.a2.val q₂
    execWithEnv u256ProcEnv (fuel + 3)
      ⟨lo4 :: lo3 :: a.a7.val :: a.a6.val :: a.a5.val :: a.a4.val :: carry4 :: b.a2.val :: rest,
       mem, frame :: frames, adv⟩
      (Procedure.ofOps wm_r3b) =
    some ⟨rest,
          fun i =>
            if i = la 20 + 3 then mulstepLo c₅ a.a5.val b.a2.val q₃
            else if i = la 20 + 2 then mulstepLo carry4 a.a4.val b.a2.val q₂
            else if i = la 20 + 1 then lo4
            else if i = la 20 then lo3
            else mem i,
          frame :: frames, adv⟩ := by
  unfold wm_r3b execWithEnv Procedure.ofOps
  simp only [List.foldlM, u256ProcEnv]
  dsimp only [bind, Bind.bind, Option.bind]
  -- padw
  rw [stepPadw]; dsimp only [bind, Bind.bind, Option.bind]
  -- locLoadwBe 20
  rw [stepLocLoadwBe (halign := wm_align_20) (hbound := wm_bound_20 hnl)]
  rw [h20_3, h20_2, h20_1, h20_0]; dsimp only [bind, Bind.bind, Option.bind]
  -- movup 3, movup 3 (bring q₀, q₁ to top)
  miden_movup; miden_movup
  -- drop, drop (remove q₀, q₁)
  rw [stepDrop]; dsimp only [bind, Bind.bind, Option.bind]
  rw [stepDrop]; dsimp only [bind, Bind.bind, Option.bind]
  -- swapw 1
  rw [stepSwapw1]; dsimp only [bind, Bind.bind, Option.bind]
  -- movup 9, movup 9
  miden_movup; miden_movup
  -- === Mulstep 1: carry4 × a₄ with accumulator q₂ ===
  miden_dup    -- dup 1
  miden_movup  -- movup 6
  miden_movup  -- movup 8
  miden_swap   -- swap 3
  have hms1 := mulstep_execWithEnv u256ProcEnv (fuel + 1)
    carry4 a.a4.val b.a2.val q₂
    (b.a2.val :: a.a7.val :: a.a6.val :: a.a5.val :: q₃ :: lo4 :: lo3 :: rest)
    ⟨carry4 :: a.a4.val :: b.a2.val :: q₂ ::
     b.a2.val :: a.a7.val :: a.a6.val :: a.a5.val :: q₃ :: lo4 :: lo3 :: rest,
     mem, frame :: frames, adv⟩
    rfl hcarry4 (U256.a4_isU32 a) (U256.a2_isU32 b) hq₂
  simp only [MidenState.withStack] at hms1
  rw [hms1]; clear hms1; dsimp only [bind, Bind.bind, Option.bind]
  -- swap 1, movdn 6
  miden_swap
  miden_movdn
  -- === Mulstep 2: c₅ × a₅ with accumulator q₃ ===
  have hc₅u : (mulstepCarry carry4 a.a4.val b.a2.val q₂).isU32 = true :=
    mulstep_carry_isU32 carry4 a.a4.val b.a2.val q₂ hcarry4 (U256.a4_isU32 a) (U256.a2_isU32 b) hq₂
  miden_dup    -- dup 1
  miden_movup  -- movup 5
  miden_movup  -- movup 6
  miden_swap   -- swap 3
  have hms2 := mulstep_execWithEnv u256ProcEnv (fuel + 1)
    (mulstepCarry carry4 a.a4.val b.a2.val q₂) a.a5.val b.a2.val q₃
    (b.a2.val :: a.a7.val :: a.a6.val :: mulstepLo carry4 a.a4.val b.a2.val q₂ :: lo4 :: lo3 :: rest)
    ⟨mulstepCarry carry4 a.a4.val b.a2.val q₂ :: a.a5.val :: b.a2.val :: q₃ ::
     b.a2.val :: a.a7.val :: a.a6.val :: mulstepLo carry4 a.a4.val b.a2.val q₂ :: lo4 :: lo3 :: rest,
     mem, frame :: frames, adv⟩
    rfl hc₅u (U256.a5_isU32 a) (U256.a2_isU32 b) hq₃
  simp only [MidenState.withStack] at hms2
  rw [hms2]; clear hms2; dsimp only [bind, Bind.bind, Option.bind]
  -- swap 1, swap 1 (net no-op), drop (remove carry)
  miden_swap; miden_swap
  rw [stepDrop]; dsimp only [bind, Bind.bind, Option.bind]
  -- movdn 3
  miden_movdn
  -- drop, drop, drop (remove b₂, a₇, a₆)
  rw [stepDrop]; dsimp only [bind, Bind.bind, Option.bind]
  rw [stepDrop]; dsimp only [bind, Bind.bind, Option.bind]
  rw [stepDrop]; dsimp only [bind, Bind.bind, Option.bind]
  -- locStorewBe 20
  rw [stepLocStorewBe (halign := wm_align_20) (hbound := wm_bound_20 hnl)]
  dsimp only [bind, Bind.bind, Option.bind]
  -- dropw
  rw [stepDropw]; simp only [pure, Pure.pure]

-- ============================================================================
-- Round 3 correctness
-- ============================================================================

set_option maxHeartbeats 16000000 in
/-- Round 3: b₂ × a[0..5] with accumulators from Round 2.
    Input stack: rest
    Output stack: rest
    Memory: la(16) and la(20) updated with Round 3 partial products. -/
theorem wm_round3_correct (a b : U256) (rest : List Felt)
    (mem : Nat → Felt) (frame : LocalFrame) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) (hnl : frame.numLocals ≥ 24)
    (p₀ p₁ p₂ p₃ q₀ q₁ q₂ q₃ : Felt)
    (hp₂ : p₂.isU32 = true) (hp₃ : p₃.isU32 = true)
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
    let carry1 := mulstepCarry 0 a.a0.val b.a2.val p₂
    let carry2 := mulstepCarry carry1 a.a1.val b.a2.val p₃
    let carry3 := mulstepCarry carry2 a.a2.val b.a2.val q₀
    let carry4 := mulstepCarry carry3 a.a3.val b.a2.val q₁
    let c₅ := mulstepCarry carry4 a.a4.val b.a2.val q₂
    execWithEnv u256ProcEnv (fuel + 3)
      ⟨rest, mem, frame :: frames, adv⟩
      (Procedure.ofOps wm_round3) =
    some ⟨rest,
          fun i =>
            if i = la 20 + 3 then mulstepLo c₅ a.a5.val b.a2.val q₃
            else if i = la 20 + 2 then mulstepLo carry4 a.a4.val b.a2.val q₂
            else if i = la 20 + 1 then mulstepLo carry3 a.a3.val b.a2.val q₁
            else if i = la 20 then mulstepLo carry2 a.a2.val b.a2.val q₀
            else if i = la 16 + 3 then mulstepLo carry1 a.a1.val b.a2.val p₃
            else if i = la 16 + 2 then mulstepLo 0 a.a0.val b.a2.val p₂
            else if i = la 16 + 1 then p₁
            else if i = la 16 then p₀
            else mem i,
          frame :: frames, adv⟩ := by
  rw [show (wm_round3 : List Op) = wm_r3a ++ wm_r3b from wm_round3_eq_r3a_r3b]
  rw [execWithEnv_append]
  -- Apply Part A
  rw [wm_r3a_correct a b rest mem frame frames adv fuel hnl
      p₀ p₁ p₂ p₃ q₀ q₁ q₂ q₃ hp₂ hp₃ hq₀ hq₁
      h16_3 h16_2 h16_1 h16_0 h20_3 h20_2 h20_1 h20_0
      h12_3 h12_2 h12_1 h12_0 h8_3 h8_2 h8_1 h8_0
      h4_3 h4_2 h4_1 h4_0]
  simp only [bind, Bind.bind, Option.bind]
  -- Apply Part B (la(20) reads pass through la(16) updates)
  have hcarry4u : (mulstepCarry
    (mulstepCarry (mulstepCarry (mulstepCarry 0 a.a0.val b.a2.val p₂)
      a.a1.val b.a2.val p₃) a.a2.val b.a2.val q₀) a.a3.val b.a2.val q₁).isU32 = true := by
    apply mulstep_carry_isU32
    · apply mulstep_carry_isU32
      · apply mulstep_carry_isU32
        · apply mulstep_carry_isU32
          · simp [Felt.isU32]
          · exact U256.a0_isU32 a
          · exact U256.a2_isU32 b
          · exact hp₂
        · exact U256.a1_isU32 a
        · exact U256.a2_isU32 b
        · exact hp₃
      · exact U256.a2_isU32 a
      · exact U256.a2_isU32 b
      · exact hq₀
    · exact U256.a3_isU32 a
    · exact U256.a2_isU32 b
    · exact hq₁
  rw [wm_r3b_correct a b rest _ frame frames adv fuel hnl _ _ _ hcarry4u
      q₀ q₁ q₂ q₃ hq₂ hq₃
      (by mem_simp; exact h20_3) (by mem_simp; exact h20_2) (by mem_simp; exact h20_1) (by mem_simp; exact h20_0)]

end MidenLean.Proofs
