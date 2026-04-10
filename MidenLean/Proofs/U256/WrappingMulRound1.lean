import MidenLean.Proofs.U256.WrappingMulDefs

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

-- ============================================================================
-- Round 1 Part A: mulstep4 phase
-- ============================================================================

set_option maxHeartbeats 16000000 in
/-- Part A: padw, locLoadwBe 16, movdnw 2, movup 12, execProcedure emptyEnv mulstep4,
    movdn 9, movdn 9, swapw 1, locStorewBe 16, dropw.
    Computes b0 × a[0..3] and stores low results to locals 16. -/
theorem wm_r1a_correct (a b : U256) (rest : List Felt)
    (mem : Nat → Felt) (frame : LocalFrame) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) (hnl : frame.numLocals ≥ 24)
    (h16_3 : mem (frame.localAddr 16 + 3) = 0)
    (h16_2 : mem (frame.localAddr 16 + 2) = 0)
    (h16_1 : mem (frame.localAddr 16 + 1) = 0)
    (h16_0 : mem (frame.localAddr 16) = 0) :
    let la := frame.localAddr
    let c₁ := mulstepCarry 0 a.a0.val b.a0.val 0
    let c₂ := mulstepCarry c₁ a.a1.val b.a0.val 0
    let c₃ := mulstepCarry c₂ a.a2.val b.a0.val 0
    let c₄ := mulstepCarry c₃ a.a3.val b.a0.val 0
    execProcedure u256ProcEnv (fuel + 3)
      ⟨a.a7.val :: a.a6.val :: a.a5.val :: a.a4.val ::
       a.a3.val :: a.a2.val :: a.a1.val :: a.a0.val :: b.a0.val :: rest,
       mem, frame :: frames, adv⟩
      (Procedure.ofOps wm_r1a) =
    some ⟨a.a7.val :: a.a6.val :: a.a5.val :: a.a4.val :: c₄ :: b.a0.val :: rest,
          fun i =>
            if i = la 16 + 3 then mulstepLo c₃ a.a3.val b.a0.val 0
            else if i = la 16 + 2 then mulstepLo c₂ a.a2.val b.a0.val 0
            else if i = la 16 + 1 then mulstepLo c₁ a.a1.val b.a0.val 0
            else if i = la 16 then mulstepLo 0 a.a0.val b.a0.val 0
            else mem i,
          frame :: frames, adv⟩ := by
  unfold wm_r1a execProcedure Procedure.ofOps
  simp only [List.foldlM, u256ProcEnv]
  -- 1. padw
  dsimp only [bind, Bind.bind, Option.bind]
  rw [stepPadw]
  dsimp only [bind, Bind.bind, Option.bind]
  -- 2. locLoadwBe 16
  rw [stepLocLoadwBe (halign := wm_align_16) (hbound := wm_bound_16 hnl)]
  rw [h16_3, h16_2, h16_1, h16_0]
  dsimp only [bind, Bind.bind, Option.bind]
  -- 3. movdnw 2
  rw [stepMovdnw2]
  dsimp only [bind, Bind.bind, Option.bind]
  -- 4. movup 12
  miden_movup
  -- 5. execProcedure emptyEnv "mulstep4"
  have h0u : (0 : Felt).isU32 = true := by simp [Felt.isU32]
  have hmul4 := u256_mulstep4_correct
    b.a0.val a.a7.val a.a6.val a.a5.val a.a4.val
    a.a3.val a.a2.val a.a1.val a.a0.val
    (0 : Felt) (0 : Felt) (0 : Felt) (0 : Felt) rest
    ⟨b.a0.val :: a.a7.val :: a.a6.val :: a.a5.val :: a.a4.val ::
     a.a3.val :: a.a2.val :: a.a1.val :: a.a0.val ::
     (0 : Felt) :: (0 : Felt) :: (0 : Felt) :: (0 : Felt) :: rest,
     mem, frame :: frames, adv⟩
    rfl
    (U256.a0_isU32 b) (U256.a3_isU32 a) (U256.a2_isU32 a) (U256.a1_isU32 a) (U256.a0_isU32 a)
    h0u h0u h0u h0u fuel
  simp only [Concrete.State.withStack] at hmul4
  rw [hmul4]; clear hmul4
  dsimp only [bind, Bind.bind, Option.bind]
  -- 6. movdn 9
  miden_movdn
  -- 7. movdn 9
  miden_movdn
  -- 8. swapw 1
  rw [stepSwapw1]
  dsimp only [bind, Bind.bind, Option.bind]
  -- 9. locStorewBe 16
  rw [stepLocStorewBe (halign := wm_align_16) (hbound := wm_bound_16 hnl)]
  dsimp only [bind, Bind.bind, Option.bind]
  -- 10. dropw
  rw [stepDropw]
  simp only [pure, Pure.pure]

-- ============================================================================
-- Round 1 Part B: individual mulsteps (sorry for now)
-- ============================================================================

set_option maxHeartbeats 32000000 in
/-- Part B1: setup + first 2 individual mulsteps for b0 × a[4..5].
    Input stack:  [a7, a6, a5, a4, c₄, b0] ++ rest
    Output stack: [c₆, b0, a7, a6, l₅, l₄, 0, 0] ++ rest -/
private theorem wm_r1b1_correct (a b : U256) (rest : List Felt)
    (mem : Nat → Felt) (frame : LocalFrame) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) (hnl : frame.numLocals ≥ 24)
    (c₄ : Felt) (hc₄ : c₄.isU32 = true)
    (h20_3 : mem (frame.localAddr 20 + 3) = 0)
    (h20_2 : mem (frame.localAddr 20 + 2) = 0)
    (h20_1 : mem (frame.localAddr 20 + 1) = 0)
    (h20_0 : mem (frame.localAddr 20) = 0) :
    let c₅ := mulstepCarry c₄ a.a4.val b.a0.val 0
    let c₆ := mulstepCarry c₅ a.a5.val b.a0.val 0
    execProcedure u256ProcEnv (fuel + 3)
      ⟨a.a7.val :: a.a6.val :: a.a5.val :: a.a4.val :: c₄ :: b.a0.val :: rest,
       mem, frame :: frames, adv⟩
      (Procedure.ofOps wm_r1b1) =
    some ⟨c₆ :: b.a0.val :: a.a7.val :: a.a6.val ::
          mulstepLo c₅ a.a5.val b.a0.val 0 :: mulstepLo c₄ a.a4.val b.a0.val 0 ::
          (0 : Felt) :: (0 : Felt) :: rest,
          mem, frame :: frames, adv⟩ := by
  unfold wm_r1b1 execProcedure Procedure.ofOps
  simp only [List.foldlM, u256ProcEnv]
  have h0u : (0 : Felt).isU32 = true := by simp [Felt.isU32]
  -- Setup: padw
  dsimp only [bind, Bind.bind, Option.bind]
  rw [stepPadw]; dsimp only [bind, Bind.bind, Option.bind]
  -- locLoadwBe 20 (replaces top 4)
  rw [stepLocLoadwBe (halign := wm_align_20) (hbound := wm_bound_20 hnl)]
  rw [h20_3, h20_2, h20_1, h20_0]; dsimp only [bind, Bind.bind, Option.bind]
  -- swapw 1
  rw [stepSwapw1]; dsimp only [bind, Bind.bind, Option.bind]
  -- movup 9 (brings b0 to top)
  miden_movup
  -- movup 9 (brings c₄ to top)
  miden_movup
  -- Stack: [c₄, b0, a7, a6, a5, a4, 0, 0, 0, 0] ++ rest
  -- === Mulstep 1: c₄ × a4 ===
  miden_dup    -- dup 1
  miden_movup  -- movup 6
  miden_movup  -- movup 10
  miden_swap   -- swap 3
  -- Stack: [c₄, a4, b0, 0, b0, a7, a6, a5, 0, 0, 0] ++ rest
  have hms1 := mulstep_execWithEnv u256ProcEnv (fuel + 1)
    c₄ (a.a4.val) (b.a0.val) (0 : Felt)
    (b.a0.val :: a.a7.val :: a.a6.val :: a.a5.val :: (0 : Felt) :: (0 : Felt) :: (0 : Felt) :: rest)
    ⟨c₄ :: a.a4.val :: b.a0.val :: (0 : Felt) ::
     b.a0.val :: a.a7.val :: a.a6.val :: a.a5.val :: (0 : Felt) :: (0 : Felt) :: (0 : Felt) :: rest,
     mem, frame :: frames, adv⟩
    rfl hc₄ (U256.a4_isU32 a) (U256.a0_isU32 b) h0u
  simp only [Concrete.State.withStack] at hms1
  rw [hms1]; clear hms1; dsimp only [bind, Bind.bind, Option.bind]
  -- swap 1, movdn 5
  miden_swap
  miden_movdn
  -- Stack: [c₅, b0, a7, a6, a5, l₄, 0, 0, 0] ++ rest
  -- === Mulstep 2: c₅ × a5 ===
  have hc₅u : (mulstepCarry c₄ a.a4.val b.a0.val 0).isU32 = true :=
    mulstep_carry_isU32 c₄ a.a4.val b.a0.val 0 hc₄ (U256.a4_isU32 a) (U256.a0_isU32 b) h0u
  miden_dup    -- dup 1
  miden_movup  -- movup 5
  miden_movup  -- movup 9
  miden_swap   -- swap 3
  -- Stack: [c₅, a5, b0, 0, b0, a7, a6, l₄, 0, 0] ++ rest
  have hms2 := mulstep_execWithEnv u256ProcEnv (fuel + 1)
    (mulstepCarry c₄ a.a4.val b.a0.val 0) (a.a5.val) (b.a0.val) (0 : Felt)
    (b.a0.val :: a.a7.val :: a.a6.val ::
     mulstepLo c₄ a.a4.val b.a0.val 0 :: (0 : Felt) :: (0 : Felt) :: rest)
    ⟨mulstepCarry c₄ a.a4.val b.a0.val 0 :: a.a5.val :: b.a0.val :: (0 : Felt) ::
     b.a0.val :: a.a7.val :: a.a6.val ::
     mulstepLo c₄ a.a4.val b.a0.val 0 :: (0 : Felt) :: (0 : Felt) :: rest,
     mem, frame :: frames, adv⟩
    rfl hc₅u (U256.a5_isU32 a) (U256.a0_isU32 b) h0u
  simp only [Concrete.State.withStack] at hms2
  rw [hms2]; clear hms2; dsimp only [bind, Bind.bind, Option.bind]
  -- swap 1, movdn 4
  miden_swap
  miden_movdn
  simp only [pure, Pure.pure]

set_option maxHeartbeats 32000000 in
/-- Part B2: last 2 individual mulsteps for b0 × a[6..7], store to locals 20.
    Input stack:  [c₆, b0, a7, a6, l₅, l₄, 0, 0] ++ rest
    Output stack: rest -/
private theorem wm_r1b2_correct (a b : U256) (rest : List Felt)
    (mem : Nat → Felt) (frame : LocalFrame) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) (hnl : frame.numLocals ≥ 24)
    (c₆ : Felt) (hc₆ : c₆.isU32 = true) (l₅ l₄ : Felt) :
    let la := frame.localAddr
    let c₇ := mulstepCarry c₆ a.a6.val b.a0.val 0
    execProcedure u256ProcEnv (fuel + 3)
      ⟨c₆ :: b.a0.val :: a.a7.val :: a.a6.val :: l₅ :: l₄ :: (0 : Felt) :: (0 : Felt) :: rest,
       mem, frame :: frames, adv⟩
      (Procedure.ofOps wm_r1b2) =
    some ⟨rest,
          fun i =>
            if i = la 20 + 3 then mulstepLo c₇ a.a7.val b.a0.val 0
            else if i = la 20 + 2 then mulstepLo c₆ a.a6.val b.a0.val 0
            else if i = la 20 + 1 then l₅
            else if i = la 20 then l₄
            else mem i,
          frame :: frames, adv⟩ := by
  unfold wm_r1b2 execProcedure Procedure.ofOps
  simp only [List.foldlM, u256ProcEnv]
  have h0u : (0 : Felt).isU32 = true := by simp [Felt.isU32]
  -- === Mulstep 3: c₆ × a6 ===
  dsimp only [bind, Bind.bind, Option.bind]
  miden_dup    -- dup 1
  miden_movup  -- movup 4
  miden_movup  -- movup 8
  miden_swap   -- swap 3
  -- Stack: [c₆, a6, b0, 0, b0, a7, l₅, l₄, 0] ++ rest
  have hms3 := mulstep_execWithEnv u256ProcEnv (fuel + 1)
    c₆ (a.a6.val) (b.a0.val) (0 : Felt)
    (b.a0.val :: a.a7.val :: l₅ :: l₄ :: (0 : Felt) :: rest)
    ⟨c₆ :: a.a6.val :: b.a0.val :: (0 : Felt) ::
     b.a0.val :: a.a7.val :: l₅ :: l₄ :: (0 : Felt) :: rest,
     mem, frame :: frames, adv⟩
    rfl hc₆ (U256.a6_isU32 a) (U256.a0_isU32 b) h0u
  simp only [Concrete.State.withStack] at hms3
  rw [hms3]; clear hms3; dsimp only [bind, Bind.bind, Option.bind]
  -- swap 1, movdn 3
  miden_swap
  miden_movdn
  -- Stack: [c₇, b0, a7, l₆, l₅, l₄, 0] ++ rest
  -- === Mulstep 4: c₇ × a7 ===
  have hc₇u : (mulstepCarry c₆ a.a6.val b.a0.val 0).isU32 = true :=
    mulstep_carry_isU32 c₆ a.a6.val b.a0.val 0 hc₆ (U256.a6_isU32 a) (U256.a0_isU32 b) h0u
  miden_swap   -- swap 1
  miden_movup  -- movup 2
  miden_movup  -- movup 6
  miden_swap   -- swap 3
  -- Stack: [c₇, a7, b0, 0, l₆, l₅, l₄] ++ rest
  have hms4 := mulstep_execWithEnv u256ProcEnv (fuel + 1)
    (mulstepCarry c₆ a.a6.val b.a0.val 0) (a.a7.val) (b.a0.val) (0 : Felt)
    (mulstepLo c₆ a.a6.val b.a0.val 0 :: l₅ :: l₄ :: rest)
    ⟨mulstepCarry c₆ a.a6.val b.a0.val 0 :: a.a7.val :: b.a0.val :: (0 : Felt) ::
     mulstepLo c₆ a.a6.val b.a0.val 0 :: l₅ :: l₄ :: rest,
     mem, frame :: frames, adv⟩
    rfl hc₇u (U256.a7_isU32 a) (U256.a0_isU32 b) h0u
  simp only [Concrete.State.withStack] at hms4
  rw [hms4]; clear hms4; dsimp only [bind, Bind.bind, Option.bind]
  -- drop (remove carry)
  rw [stepDrop]; dsimp only [bind, Bind.bind, Option.bind]
  -- locStorewBe 20
  rw [stepLocStorewBe (halign := wm_align_20) (hbound := wm_bound_20 hnl)]
  dsimp only [bind, Bind.bind, Option.bind]
  -- dropw
  rw [stepDropw]; simp only [pure, Pure.pure]

set_option maxHeartbeats 16000000 in
/-- Part B: 4 individual mulsteps for b0 × a[4..7], stored to locals 20.
    Input stack:  [a7, a6, a5, a4, c₄, b0] ++ rest
    Output stack: rest -/
private theorem wm_r1b_correct (a b : U256) (rest : List Felt)
    (mem : Nat → Felt) (frame : LocalFrame) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) (hnl : frame.numLocals ≥ 24)
    (c₄ : Felt) (hc₄ : c₄.isU32 = true)
    (h20_3 : mem (frame.localAddr 20 + 3) = 0)
    (h20_2 : mem (frame.localAddr 20 + 2) = 0)
    (h20_1 : mem (frame.localAddr 20 + 1) = 0)
    (h20_0 : mem (frame.localAddr 20) = 0) :
    let la := frame.localAddr
    let c₅ := mulstepCarry c₄ a.a4.val b.a0.val 0
    let c₆ := mulstepCarry c₅ a.a5.val b.a0.val 0
    let c₇ := mulstepCarry c₆ a.a6.val b.a0.val 0
    execProcedure u256ProcEnv (fuel + 3)
      ⟨a.a7.val :: a.a6.val :: a.a5.val :: a.a4.val :: c₄ :: b.a0.val :: rest,
       mem, frame :: frames, adv⟩
      (Procedure.ofOps wm_r1b) =
    some ⟨rest,
          fun i =>
            if i = la 20 + 3 then mulstepLo c₇ a.a7.val b.a0.val 0
            else if i = la 20 + 2 then mulstepLo c₆ a.a6.val b.a0.val 0
            else if i = la 20 + 1 then mulstepLo c₅ a.a5.val b.a0.val 0
            else if i = la 20 then mulstepLo c₄ a.a4.val b.a0.val 0
            else mem i,
          frame :: frames, adv⟩ := by
  -- Decompose into two halves
  rw [show (wm_r1b : List Op) = wm_r1b1 ++ wm_r1b2 from wm_r1b_eq_b1_b2]
  rw [execProcedure_append]
  -- Apply Part B1
  have hc₅u : (mulstepCarry c₄ a.a4.val b.a0.val 0).isU32 = true :=
    mulstep_carry_isU32 c₄ a.a4.val b.a0.val 0 hc₄ (U256.a4_isU32 a) (U256.a0_isU32 b)
      (by simp [Felt.isU32])
  have hc₆u : (mulstepCarry (mulstepCarry c₄ a.a4.val b.a0.val 0) a.a5.val b.a0.val 0).isU32 = true :=
    mulstep_carry_isU32 _ a.a5.val b.a0.val 0 hc₅u (U256.a5_isU32 a) (U256.a0_isU32 b)
      (by simp [Felt.isU32])
  rw [wm_r1b1_correct a b rest mem frame frames adv fuel hnl c₄ hc₄ h20_3 h20_2 h20_1 h20_0]
  simp only [bind, Bind.bind, Option.bind]
  -- Apply Part B2
  rw [wm_r1b2_correct a b rest mem frame frames adv fuel hnl _ hc₆u
    (mulstepLo (mulstepCarry c₄ a.a4.val b.a0.val 0) a.a5.val b.a0.val 0)
    (mulstepLo c₄ a.a4.val b.a0.val 0)]

-- ============================================================================
-- Round 1 correctness (composed from Parts A and B)
-- ============================================================================

set_option maxHeartbeats 16000000 in
/-- Round 1: multiply b0 × a[0..7], storing partial products to locals 16 and 20.
    Input stack:  [a7, a6, a5, a4, a3, a2, a1, a0, b0] ++ rest
    Output stack: rest -/
theorem wm_round1_correct (a b : U256) (rest : List Felt)
    (mem : Nat → Felt) (frame : LocalFrame) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) (hnl : frame.numLocals ≥ 24)
    (h16_3 : mem (frame.localAddr 16 + 3) = 0)
    (h16_2 : mem (frame.localAddr 16 + 2) = 0)
    (h16_1 : mem (frame.localAddr 16 + 1) = 0)
    (h16_0 : mem (frame.localAddr 16) = 0)
    (h20_3 : mem (frame.localAddr 20 + 3) = 0)
    (h20_2 : mem (frame.localAddr 20 + 2) = 0)
    (h20_1 : mem (frame.localAddr 20 + 1) = 0)
    (h20_0 : mem (frame.localAddr 20) = 0) :
    let la := frame.localAddr
    let c₁ := mulstepCarry 0 a.a0.val b.a0.val 0
    let c₂ := mulstepCarry c₁ a.a1.val b.a0.val 0
    let c₃ := mulstepCarry c₂ a.a2.val b.a0.val 0
    let c₄ := mulstepCarry c₃ a.a3.val b.a0.val 0
    let c₅ := mulstepCarry c₄ a.a4.val b.a0.val 0
    let c₆ := mulstepCarry c₅ a.a5.val b.a0.val 0
    let c₇ := mulstepCarry c₆ a.a6.val b.a0.val 0
    execProcedure u256ProcEnv (fuel + 3)
      ⟨a.a7.val :: a.a6.val :: a.a5.val :: a.a4.val ::
       a.a3.val :: a.a2.val :: a.a1.val :: a.a0.val :: b.a0.val :: rest,
       mem, frame :: frames, adv⟩
      (Procedure.ofOps wm_round1) =
    some ⟨rest,
          fun i =>
            if i = la 20 + 3 then mulstepLo c₇ a.a7.val b.a0.val 0
            else if i = la 20 + 2 then mulstepLo c₆ a.a6.val b.a0.val 0
            else if i = la 20 + 1 then mulstepLo c₅ a.a5.val b.a0.val 0
            else if i = la 20 then mulstepLo c₄ a.a4.val b.a0.val 0
            else if i = la 16 + 3 then mulstepLo c₃ a.a3.val b.a0.val 0
            else if i = la 16 + 2 then mulstepLo c₂ a.a2.val b.a0.val 0
            else if i = la 16 + 1 then mulstepLo c₁ a.a1.val b.a0.val 0
            else if i = la 16 then mulstepLo 0 a.a0.val b.a0.val 0
            else mem i,
          frame :: frames, adv⟩ := by
  -- Split into Part A (mulstep4) and Part B (individual mulsteps)
  rw [show (wm_round1 : List Op) = wm_r1a ++ wm_r1b from wm_round1_eq_r1a_r1b]
  rw [execProcedure_append]
  -- Apply Part A
  rw [wm_r1a_correct a b rest mem frame frames adv fuel hnl h16_3 h16_2 h16_1 h16_0]
  simp only [bind, Bind.bind, Option.bind]
  -- Apply Part B (memory at la(20) passes through the la(16) updates)
  have hc₄u : (mulstepCarry
    (mulstepCarry (mulstepCarry (mulstepCarry 0 a.a0.val b.a0.val 0)
      a.a1.val b.a0.val 0) a.a2.val b.a0.val 0) a.a3.val b.a0.val 0).isU32 = true := by
    apply mulstep_carry_isU32
    · apply mulstep_carry_isU32
      · apply mulstep_carry_isU32
        · apply mulstep_carry_isU32
          · simp [Felt.isU32]
          · exact U256.a0_isU32 a
          · exact U256.a0_isU32 b
          · simp [Felt.isU32]
        · exact U256.a1_isU32 a
        · exact U256.a0_isU32 b
        · simp [Felt.isU32]
      · exact U256.a2_isU32 a
      · exact U256.a0_isU32 b
      · simp [Felt.isU32]
    · exact U256.a3_isU32 a
    · exact U256.a0_isU32 b
    · simp [Felt.isU32]
  rw [wm_r1b_correct a b rest _ frame frames adv fuel hnl _ hc₄u
      (by mem_simp; exact h20_3) (by mem_simp; exact h20_2) (by mem_simp; exact h20_1) (by mem_simp; exact h20_0)]

end MidenLean.Proofs
