import MidenLean.Proofs.Sha256.PrepareMessageScheduleAndConsume.SBs0to7
import MidenLean.Proofs.Sha256.PrepareMessageScheduleAndConsume.SBs8to15

namespace MidenLean.Proofs.Sha256

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

lemma sha256BodyOps_split :
    sha256BodyOps =
    sha256SB0Ops ++ sha256SB1Ops ++ sha256SB2Ops ++ sha256SB3Ops ++
    sha256SB4Ops ++ sha256SB5Ops ++ sha256SB6Ops ++ sha256SB7Ops ++
    sha256SB8Ops ++ sha256SB9Ops ++ sha256SB10Ops ++ sha256SB11Ops ++
    sha256SB12Ops ++ sha256SB13Ops ++ sha256SB14Ops ++ sha256SB15Ops := by
  set_option maxRecDepth 4096 in rfl

-- ============================================================================
-- Init bridge lemma
-- Proves the 6-instruction initialization block:
--   - Saves H0..H3 to locs[0..3] (working) and locs[8..11] (backup)
--   - Saves H4..H7 to locs[4..7] (working) and locs[12..15] (backup)
--   - Drops H0..H7 from the stack, leaving W0..W15
-- ============================================================================

lemma sha256_init_bridge
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
     x16 x17 x18 x19 x20 x21 x22 x23 : Felt)
    (rest : List Felt) (mem locs : Nat → Felt) (adv : List Felt) :
    execWithEnv sha256ProcEnv 2126
        ⟨x0::x1::x2::x3::x4::x5::x6::x7::
          x8::x9::x10::x11::x12::x13::x14::x15::
          x16::x17::x18::x19::x20::x21::x22::x23::rest, mem, locs, adv⟩
        sha256InitOps =
    some ⟨x8::x9::x10::x11::x12::x13::x14::x15::
           x16::x17::x18::x19::x20::x21::x22::x23::rest,
          mem,
          sha256WorkingLocs x0 x1 x2 x3 x4 x5 x6 x7 x0 x1 x2 x3 x4 x5 x6 x7 locs,
          adv⟩ := by
  unfold sha256InitOps execWithEnv
  simp only [List.foldlM]
  rw [stepLocStorewBe]; miden_bind
  rw [stepLocStorewBe]; miden_bind
  rw [stepDropw]; miden_bind
  rw [stepLocStorewBe]; miden_bind
  rw [stepLocStorewBe]; miden_bind
  rw [stepDropw]; miden_bind
  dsimp only [pure, Pure.pure]
  -- The locals field after the 6 steps is a nested if-else chain; prove it equals
  -- sha256WorkingLocs, then rewrite to close the structure equality.
  suffices hlocs : (fun i =>
      if i = 12 + 3 then x4 else if i = 12 + 2 then x5 else
      if i = 12 + 1 then x6 else if i = 12 then x7 else
      if i = 4 + 3 then x4 else if i = 4 + 2 then x5 else
      if i = 4 + 1 then x6 else if i = 4 then x7 else
      if i = 8 + 3 then x0 else if i = 8 + 2 then x1 else
      if i = 8 + 1 then x2 else if i = 8 then x3 else
      if i = 0 + 3 then x0 else if i = 0 + 2 then x1 else
      if i = 0 + 1 then x2 else if i = 0 then x3 else locs i) =
      sha256WorkingLocs x0 x1 x2 x3 x4 x5 x6 x7 x0 x1 x2 x3 x4 x5 x6 x7 locs by
    simp only [hlocs]
  funext i
  simp only [sha256WorkingLocs]
  rcases Nat.lt_or_ge i 16 with hi | hi
  · interval_cases i <;> simp
  · -- All conditions evaluate to false (all ≤ 15 < 16 ≤ i); both sides fall through to locs i.
    -- Definitional reduction: 12+3=15, 4+3=7, 8+3=11, 0+3=3, etc.
    simp only [if_neg (show i ≠ 15 from by omega), if_neg (show i ≠ 14 from by omega),
               if_neg (show i ≠ 13 from by omega), if_neg (show i ≠ 12 from by omega),
               if_neg (show i ≠ 11 from by omega), if_neg (show i ≠ 10 from by omega),
               if_neg (show i ≠ 9 from by omega), if_neg (show i ≠ 8 from by omega),
               if_neg (show i ≠ 7 from by omega), if_neg (show i ≠ 6 from by omega),
               if_neg (show i ≠ 5 from by omega), if_neg (show i ≠ 4 from by omega),
               if_neg (show i ≠ 3 from by omega), if_neg (show i ≠ 2 from by omega),
               if_neg (show i ≠ 1 from by omega), if_neg (show i ≠ 0 from by omega)]


-- ============================================================================
-- Final bridge lemma
-- Proves the final block:
--   padw; locLoadwBe 12 → loads H4..H7 from backup slots
--   padw; locLoadwBe 8  → loads H0..H3 from backup slots
--   repeat 8 [movup 8; u32WrappingAdd; movdn 7] → adds H_i to a'_i (mod 2³²)
-- Requires: compression state [a,b,c,d,e,f,g,h] at top of stack,
--           backup values H0..H7 in locs[8..15]
-- ============================================================================

lemma sha256_final_bridge
    (a b c d e f g h H0 H1 H2 H3 H4 H5 H6 H7 : Felt)
    (ha : a.isU32 = true)   (hb : b.isU32 = true)
    (hc : c.isU32 = true)   (hd : d.isU32 = true)
    (he : e.isU32 = true)   (hf : f.isU32 = true)
    (hg : g.isU32 = true)   (hh : h.isU32 = true)
    (hH0 : H0.isU32 = true) (hH1 : H1.isU32 = true)
    (hH2 : H2.isU32 = true) (hH3 : H3.isU32 = true)
    (hH4 : H4.isU32 = true) (hH5 : H5.isU32 = true)
    (hH6 : H6.isU32 = true) (hH7 : H7.isU32 = true)
    (rest : List Felt) (mem locs : Nat → Felt) (adv : List Felt)
    -- Only the backup slots (8..15) are accessed; working slots (0..7) can hold anything.
    (hLoc_11 : locs 11 = H0) (hLoc_10 : locs 10 = H1)
    (hLoc_9  : locs 9  = H2) (hLoc_8  : locs 8  = H3)
    (hLoc_15 : locs 15 = H4) (hLoc_14 : locs 14 = H5)
    (hLoc_13 : locs 13 = H6) (hLoc_12 : locs 12 = H7) :
    execWithEnv sha256ProcEnv 2126
        ⟨a :: b :: c :: d :: e :: f :: g :: h :: rest, mem, locs, adv⟩
        sha256FinalOps =
    some ⟨Felt.ofNat ((a.val + H0.val) % 2^32) ::
          Felt.ofNat ((b.val + H1.val) % 2^32) ::
          Felt.ofNat ((c.val + H2.val) % 2^32) ::
          Felt.ofNat ((d.val + H3.val) % 2^32) ::
          Felt.ofNat ((e.val + H4.val) % 2^32) ::
          Felt.ofNat ((f.val + H5.val) % 2^32) ::
          Felt.ofNat ((g.val + H6.val) % 2^32) ::
          Felt.ofNat ((h.val + H7.val) % 2^32) :: rest, mem, locs, adv⟩ := by
  unfold sha256FinalOps execWithEnv
  simp only [List.foldlM]
  -- padw; locLoadwBe 12 → loads H4..H7
  rw [stepPadw]; miden_bind
  rw [stepLocLoadwBe 12 H4 H5 H6 H7 (h0 := hLoc_15) (h1 := hLoc_14)
                                     (h2 := hLoc_13) (h3 := hLoc_12)]; miden_bind
  -- padw; locLoadwBe 8 → loads H0..H3
  rw [stepPadw]; miden_bind
  rw [stepLocLoadwBe 8 H0 H1 H2 H3 (h0 := hLoc_11) (h1 := hLoc_10)
                                    (h2 := hLoc_9) (h3 := hLoc_8)]; miden_bind
  -- After loads: stack = [H0,H1,H2,H3,H4,H5,H6,H7, a,b,c,d,e,f,g,h, rest]
  -- Inline 8 iterations of: movup 8; u32WrappingAdd; movdn 7
  -- stepU32WrappingAdd has signature (b_top :: a_second :: rest) and result (a+b)%2^32,
  -- so ha is the isU32 of the SECOND element and hb is the isU32 of the TOP element.
  -- After movup 8 each iter, the state variable is on top and H_i is second;
  -- result is H_i.val + x_i.val, which we commute to x_i.val + H_i.val.
  -- Iteration 1: movup brings a (pos 8) to top; stack = a::H0::...; add a + H0; movdn 7
  unfold execWithEnv.doRepeat
  unfold execWithEnv; simp only [List.foldlM]
  rw [stepMovup (hn := rfl) (hv := rfl)]; miden_bind
  rw [stepU32WrappingAdd (ha := hH0) (hb := ha)]
  rw [show (H0.val + a.val) % 2 ^ 32 = (a.val + H0.val) % 2 ^ 32 from by omega]
  miden_bind
  rw [stepMovdn (hn := rfl)]; miden_bind
  -- Iteration 2: movup brings b (pos 8) to top; stack = b::H1::...; add b + H1; movdn 7
  unfold execWithEnv.doRepeat
  unfold execWithEnv; simp only [List.foldlM]
  rw [stepMovup (hn := rfl) (hv := rfl)]; miden_bind
  rw [stepU32WrappingAdd (ha := hH1) (hb := hb)]
  rw [show (H1.val + b.val) % 2 ^ 32 = (b.val + H1.val) % 2 ^ 32 from by omega]
  miden_bind
  rw [stepMovdn (hn := rfl)]; miden_bind
  -- Iteration 3: movup brings c (pos 8) to top; stack = c::H2::...; add c + H2; movdn 7
  unfold execWithEnv.doRepeat
  unfold execWithEnv; simp only [List.foldlM]
  rw [stepMovup (hn := rfl) (hv := rfl)]; miden_bind
  rw [stepU32WrappingAdd (ha := hH2) (hb := hc)]
  rw [show (H2.val + c.val) % 2 ^ 32 = (c.val + H2.val) % 2 ^ 32 from by omega]
  miden_bind
  rw [stepMovdn (hn := rfl)]; miden_bind
  -- Iteration 4: movup brings d (pos 8) to top; stack = d::H3::...; add d + H3; movdn 7
  unfold execWithEnv.doRepeat
  unfold execWithEnv; simp only [List.foldlM]
  rw [stepMovup (hn := rfl) (hv := rfl)]; miden_bind
  rw [stepU32WrappingAdd (ha := hH3) (hb := hd)]
  rw [show (H3.val + d.val) % 2 ^ 32 = (d.val + H3.val) % 2 ^ 32 from by omega]
  miden_bind
  rw [stepMovdn (hn := rfl)]; miden_bind
  -- Iteration 5: movup brings e (pos 8) to top; stack = e::H4::...; add e + H4; movdn 7
  unfold execWithEnv.doRepeat
  unfold execWithEnv; simp only [List.foldlM]
  rw [stepMovup (hn := rfl) (hv := rfl)]; miden_bind
  rw [stepU32WrappingAdd (ha := hH4) (hb := he)]
  rw [show (H4.val + e.val) % 2 ^ 32 = (e.val + H4.val) % 2 ^ 32 from by omega]
  miden_bind
  rw [stepMovdn (hn := rfl)]; miden_bind
  -- Iteration 6: movup brings f (pos 8) to top; stack = f::H5::...; add f + H5; movdn 7
  unfold execWithEnv.doRepeat
  unfold execWithEnv; simp only [List.foldlM]
  rw [stepMovup (hn := rfl) (hv := rfl)]; miden_bind
  rw [stepU32WrappingAdd (ha := hH5) (hb := hf)]
  rw [show (H5.val + f.val) % 2 ^ 32 = (f.val + H5.val) % 2 ^ 32 from by omega]
  miden_bind
  rw [stepMovdn (hn := rfl)]; miden_bind
  -- Iteration 7: movup brings g (pos 8) to top; stack = g::H6::...; add g + H6; movdn 7
  unfold execWithEnv.doRepeat
  unfold execWithEnv; simp only [List.foldlM]
  rw [stepMovup (hn := rfl) (hv := rfl)]; miden_bind
  rw [stepU32WrappingAdd (ha := hH6) (hb := hg)]
  rw [show (H6.val + g.val) % 2 ^ 32 = (g.val + H6.val) % 2 ^ 32 from by omega]
  miden_bind
  rw [stepMovdn (hn := rfl)]; miden_bind
  -- Iteration 8: movup brings h (pos 8) to top; stack = h::H7::...; add h + H7; movdn 7
  unfold execWithEnv.doRepeat
  unfold execWithEnv; simp only [List.foldlM]
  rw [stepMovup (hn := rfl) (hv := rfl)]; miden_bind
  rw [stepU32WrappingAdd (ha := hH7) (hb := hh)]
  rw [show (H7.val + h.val) % 2 ^ 32 = (h.val + H7.val) % 2 ^ 32 from by omega]
  miden_bind
  rw [stepMovdn (hn := rfl)]; miden_bind
  -- Base case: doRepeat 0
  unfold execWithEnv.doRepeat
  dsimp only [pure, Pure.pure]


-- ============================================================================
-- Body bridge lemma (SBs 0–15)
-- This is the central correctness result: the 16 super-blocks together compute
-- the full SHA-256 message schedule expansion and 64 compression rounds.
--
-- Precondition:
--   Stack: [W0,..,W15] ++ rest  (16 message words, positions 0–15)
--   locs: sha256WorkingLocs H0 H1 H2 H3 H4 H5 H6 H7 H0 H1 H2 H3 H4 H5 H6 H7 base
--         (working state and backup both initialized to H0..H7)
--
-- Postcondition:
--   Stack: [a', b', c', d', e', f', g', h'] ++ rest
--          where (a'..h') = sha256Block H0..H7 (sha256Schedule W0..W15)
--   locs:  backup slots (8..15) still hold H0..H7
--          (working slots 0..7 hold the state after the last regular SB, not needed)
-- ============================================================================

private lemma sha256_body_bridge
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : Felt)
    (H0 H1 H2 H3 H4 H5 H6 H7 : Felt)
    (hw0 : w0.isU32 = true)   (hw1 : w1.isU32 = true)
    (hw2 : w2.isU32 = true)   (hw3 : w3.isU32 = true)
    (hw4 : w4.isU32 = true)   (hw5 : w5.isU32 = true)
    (hw6 : w6.isU32 = true)   (hw7 : w7.isU32 = true)
    (hw8 : w8.isU32 = true)   (hw9 : w9.isU32 = true)
    (hw10 : w10.isU32 = true) (hw11 : w11.isU32 = true)
    (hw12 : w12.isU32 = true) (hw13 : w13.isU32 = true)
    (hw14 : w14.isU32 = true) (hw15 : w15.isU32 = true)
    (hH0 : H0.isU32 = true) (hH1 : H1.isU32 = true)
    (hH2 : H2.isU32 = true) (hH3 : H3.isU32 = true)
    (hH4 : H4.isU32 = true) (hH5 : H5.isU32 = true)
    (hH6 : H6.isU32 = true) (hH7 : H7.isU32 = true)
    (rest : List Felt) (mem locs : Nat → Felt) (adv : List Felt)
    (base : Nat → Felt)
    (hlocs : locs = sha256WorkingLocs H0 H1 H2 H3 H4 H5 H6 H7
                                      H0 H1 H2 H3 H4 H5 H6 H7 base) :
    let W := sha256Schedule w0.val w1.val w2.val w3.val w4.val w5.val w6.val w7.val
                             w8.val w9.val w10.val w11.val w12.val w13.val w14.val w15.val
    let blk := sha256Block H0.val H1.val H2.val H3.val H4.val H5.val H6.val H7.val W
    execWithEnv sha256ProcEnv 2126
        ⟨w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest,
          mem, locs, adv⟩
        sha256BodyOps =
    some ⟨Felt.ofNat blk.1 :: Felt.ofNat blk.2.1 :: Felt.ofNat blk.2.2.1 ::
          Felt.ofNat blk.2.2.2.1 :: Felt.ofNat blk.2.2.2.2.1 ::
          Felt.ofNat blk.2.2.2.2.2.1 :: Felt.ofNat blk.2.2.2.2.2.2.1 ::
          Felt.ofNat blk.2.2.2.2.2.2.2 :: rest,
          mem,
          sha256WorkingLocs (Felt.ofNat blk.1) (Felt.ofNat blk.2.1) (Felt.ofNat blk.2.2.1)
                            (Felt.ofNat blk.2.2.2.1) (Felt.ofNat blk.2.2.2.2.1)
                            (Felt.ofNat blk.2.2.2.2.2.1) (Felt.ofNat blk.2.2.2.2.2.2.1)
                            (Felt.ofNat blk.2.2.2.2.2.2.2)
                            H0 H1 H2 H3 H4 H5 H6 H7 base,
          adv⟩ := by
  sorry

-- ============================================================================
-- Main correctness theorem
-- ============================================================================

set_option maxHeartbeats 8000000 in
/-- `sha256::prepare_message_schedule_and_consume` computes one SHA-256 message block:
    given an initial hash state [H0..H7] and a 512-bit message block [W0..W15],
    it expands the message schedule to W[0..63], runs all 64 SHA-256 compression rounds,
    and adds the initial hash values back to the compressed state (all arithmetic mod 2³²).
    Input stack:  [H0, H1, H2, H3, H4, H5, H6, H7, W0, .., W15] ++ rest
    Output stack: [H0''+H0, H1''+H1, ..., H7''+H7] ++ rest where H_i'' = (Felt.ofNat H_i').val
    and (H0'..H7') is the result of 64 SHA-256 compression rounds.
    Note: H_i'' = H_i' because sha256Block outputs are always < 2^32 < GOLDILOCKS_PRIME,
    but the conclusion is stated using .val to match the bridge lemma output form directly. -/
theorem sha256_prepare_message_schedule_and_consume_correct
    (x0 x1 x2 x3 x4 x5 x6 x7                              -- initial hash H0..H7
     x8 x9 x10 x11 x12 x13 x14 x15                         -- message words W0..W7
     x16 x17 x18 x19 x20 x21 x22 x23 : Felt)               -- message words W8..W15
    (rest : List Felt) (s : MidenState)
    (hs : s.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 ::
                    x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 ::
                    x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: rest)
    -- all inputs must be 32-bit values
    (h0 : x0.isU32 = true)   (h1 : x1.isU32 = true)
    (h2 : x2.isU32 = true)   (h3 : x3.isU32 = true)
    (h4 : x4.isU32 = true)   (h5 : x5.isU32 = true)
    (h6 : x6.isU32 = true)   (h7 : x7.isU32 = true)
    (h8 : x8.isU32 = true)   (h9 : x9.isU32 = true)
    (h10 : x10.isU32 = true) (h11 : x11.isU32 = true)
    (h12 : x12.isU32 = true) (h13 : x13.isU32 = true)
    (h14 : x14.isU32 = true) (h15 : x15.isU32 = true)
    (h16 : x16.isU32 = true) (h17 : x17.isU32 = true)
    (h18 : x18.isU32 = true) (h19 : x19.isU32 = true)
    (h20 : x20.isU32 = true) (h21 : x21.isU32 = true)
    (h22 : x22.isU32 = true) (h23 : x23.isU32 = true) :
    -- W[i] for i = 0..15 are the message words; W[16..63] are computed.
    -- Use projection-based let bindings to avoid tuple-destructuring pattern matches in the
    -- kernel (which would require evaluating sha256Block on symbolic arguments).
    let W := sha256Schedule x8.val x9.val x10.val x11.val x12.val x13.val x14.val x15.val
                             x16.val x17.val x18.val x19.val x20.val x21.val x22.val x23.val
    let blk := sha256Block x0.val x1.val x2.val x3.val x4.val x5.val x6.val x7.val W
    let a' := blk.1;        let b' := blk.2.1;       let c' := blk.2.2.1
    let d' := blk.2.2.2.1;  let e' := blk.2.2.2.2.1; let f' := blk.2.2.2.2.2.1
    let g' := blk.2.2.2.2.2.2.1; let h' := blk.2.2.2.2.2.2.2
    execWithEnv sha256ProcEnv 2126 s Miden.Core.Sha256.prepare_message_schedule_and_consume =
    some ⟨[ Felt.ofNat (((Felt.ofNat a').val + x0.val) % 2^32),
             Felt.ofNat (((Felt.ofNat b').val + x1.val) % 2^32),
             Felt.ofNat (((Felt.ofNat c').val + x2.val) % 2^32),
             Felt.ofNat (((Felt.ofNat d').val + x3.val) % 2^32),
             Felt.ofNat (((Felt.ofNat e').val + x4.val) % 2^32),
             Felt.ofNat (((Felt.ofNat f').val + x5.val) % 2^32),
             Felt.ofNat (((Felt.ofNat g').val + x6.val) % 2^32),
             Felt.ofNat (((Felt.ofNat h').val + x7.val) % 2^32) ] ++ rest,
           s.memory,
           sha256WorkingLocs (Felt.ofNat a') (Felt.ofNat b') (Felt.ofNat c') (Felt.ofNat d')
                             (Felt.ofNat e') (Felt.ofNat f') (Felt.ofNat g') (Felt.ofNat h')
                             x0 x1 x2 x3 x4 x5 x6 x7 s.locals,
           s.advice⟩ := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [] at hs
  subst hs
  -- Split the procedure into init + body + final
  -- init: locStorewBe 0; locStorewBe 8; dropw; locStorewBe 4; locStorewBe 12; dropw
  -- body: all 16 super-blocks (SBs 0–15)
  -- final: padw; locLoadwBe 12; padw; locLoadwBe 8; repeat 8 [movup 8; u32WrappingAdd; movdn 7]
  have hops : Miden.Core.Sha256.prepare_message_schedule_and_consume =
      sha256InitOps ++ sha256BodyOps ++ sha256FinalOps := by
    simp only [sha256BodyOps]
    set_option maxRecDepth 4096 in rfl
  rw [hops, List.append_assoc, execWithEnv_append]
  -- Apply the init bridge lemma
  rw [sha256_init_bridge]
  simp only [bind, Bind.bind, Option.bind]
  -- Split body + final
  rw [execWithEnv_append]
  -- Apply the body bridge lemma (sorry: covers all 16 SBs)
  -- The state's locs after init is sha256WorkingLocs x0..x7 x0..x7 locs (original locs = base)
  rw [sha256_body_bridge x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
      x0 x1 x2 x3 x4 x5 x6 x7
      h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23
      h0 h1 h2 h3 h4 h5 h6 h7 rest mem
      (sha256WorkingLocs x0 x1 x2 x3 x4 x5 x6 x7 x0 x1 x2 x3 x4 x5 x6 x7 locs)
      adv locs rfl]
  simp only [bind, Bind.bind, Option.bind]
  -- Apply the final bridge lemma, using backup H values from locs
  rw [sha256_final_bridge]
  · -- Both sides are definitionally equal after bridges (zeta-reducing sha256Block let)
    set_option maxRecDepth 100000 in rfl
  -- isU32 hypotheses for compressed result (proved by u32_mod_isU32)
  · exact u32_mod_isU32 _
  · exact u32_mod_isU32 _
  · exact u32_mod_isU32 _
  · exact u32_mod_isU32 _
  · exact u32_mod_isU32 _
  · exact u32_mod_isU32 _
  · exact u32_mod_isU32 _
  · exact u32_mod_isU32 _
  -- isU32 hypotheses for backup H values (= original x0..x7)
  · exact h0
  · exact h1

end MidenLean.Proofs.Sha256
