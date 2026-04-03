import MidenLean.Proofs.Sha256.PrepareMessageScheduleAndConsume.Defs

namespace MidenLean.Proofs.Sha256

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

-- ============================================================================
-- SB0 spec helpers
-- ============================================================================

private def sha256SB0W16 (w0 w1 w9 w14 : Felt) : Felt :=
  let sig1 := u32RotateRight w14.val 17 ^^^ (u32RotateRight w14.val 19 ^^^ w14.val / 2^10)
  let sig0 := u32RotateRight w1.val 7 ^^^ (u32RotateRight w1.val 18 ^^^ w1.val / 2^3)
  Felt.ofNat ((w0.val + (w9.val + sig1 + sig0) % 2^32) % 2^32)

private def sha256SB0W17 (w1 w2 w10 w15 : Felt) : Felt :=
  let sig1 := u32RotateRight w15.val 17 ^^^ (u32RotateRight w15.val 19 ^^^ w15.val / 2^10)
  let sig0 := u32RotateRight w2.val 7 ^^^ (u32RotateRight w2.val 18 ^^^ w2.val / 2^3)
  Felt.ofNat ((w1.val + (w10.val + sig1 + sig0) % 2^32) % 2^32)

private def sha256SB0W18 (w2 w3 w11 W16 : Felt) : Felt :=
  let sig1 := u32RotateRight W16.val 17 ^^^ (u32RotateRight W16.val 19 ^^^ W16.val / 2^10)
  let sig0 := u32RotateRight w3.val 7 ^^^ (u32RotateRight w3.val 18 ^^^ w3.val / 2^3)
  Felt.ofNat ((w2.val + (w11.val + sig1 + sig0) % 2^32) % 2^32)

private def sha256SB0W19 (w3 w4 w12 W17 : Felt) : Felt :=
  let sig1 := u32RotateRight W17.val 17 ^^^ (u32RotateRight W17.val 19 ^^^ W17.val / 2^10)
  let sig0 := u32RotateRight w4.val 7 ^^^ (u32RotateRight w4.val 18 ^^^ w4.val / 2^3)
  Felt.ofNat ((w3.val + (w12.val + sig1 + sig0) % 2^32) % 2^32)

/-- Result of 4 compression rounds with (K0,w0),(K1,w1),(K2,w2),(K3,w3) -/
private def sha256SB0Compress (a b c d e f g h w0 w1 w2 w3 : Felt) :
    Felt × Felt × Felt × Felt × Felt × Felt × Felt × Felt :=
  let (a1,b1,c1,d1,e1,f1,g1,h1) := consumeResult a b c d e f g h (Felt.ofNat 1116352408) w0
  let (a2,b2,c2,d2,e2,f2,g2,h2) := consumeResult a1 b1 c1 d1 e1 f1 g1 h1 (Felt.ofNat 1899447441) w1
  let (a3,b3,c3,d3,e3,f3,g3,h3) := consumeResult a2 b2 c2 d2 e2 f2 g2 h2 (Felt.ofNat 3049323471) w2
  consumeResult a3 b3 c3 d3 e3 f3 g3 h3 (Felt.ofNat 3921009573) w3

-- ============================================================================
-- SB0 sub-ops split
-- ============================================================================

/-- SB0 expand phase: 4 compute_message_schedule_word calls + swapw 1 (ops 0..32) -/
private def sha256SB0ExpandOps : List Op := [
    .inst (.dup 15), .inst (.dup 15), .inst (.dup 11), .inst (.swap 1),
    .inst (.dup 4), .inst (.dup 4), .inst (.movdn 3), .inst (.movdn 2),
    .inst (.exec "compute_message_schedule_word"),
    .inst (.swap 1), .inst (.dup 12), .inst (.swap 1),
    .inst (.dup 5), .inst (.dup 5), .inst (.movdn 3), .inst (.movdn 2),
    .inst (.exec "compute_message_schedule_word"),
    .inst (.dup 1), .inst (.dup 14), .inst (.swap 1),
    .inst (.dup 7), .inst (.dup 7), .inst (.movdn 3), .inst (.movdn 2),
    .inst (.exec "compute_message_schedule_word"),
    .inst (.dup 15), .inst (.dup 2), .inst (.dup 9), .inst (.dup 9),
    .inst (.movdn 3), .inst (.movdn 2),
    .inst (.exec "compute_message_schedule_word"),
    .inst (.swapw 1)]

/-- SB0 consume+store phase: push K0, loads, 4 consumes, stores (ops 33..51) -/
private def sha256SB0ConsumeOps : List Op := [
    .inst (.push 1116352408), .inst .padw, .inst (.locLoadwBe 4),
    .inst .padw, .inst (.locLoadwBe 0),
    .inst (.exec "consume_message_word"),
    .inst (.push 1899447441), .inst (.movdn 8),
    .inst (.exec "consume_message_word"),
    .inst (.push 3049323471), .inst (.movdn 8),
    .inst (.exec "consume_message_word"),
    .inst (.push 3921009573), .inst (.movdn 8),
    .inst (.exec "consume_message_word"),
    .inst (.locStorewBe 0), .inst .dropw,
    .inst (.locStorewBe 4), .inst .dropw]

private lemma sha256SB0Ops_split :
    sha256SB0Ops = sha256SB0ExpandOps ++ sha256SB0ConsumeOps := by
  simp only [sha256SB0ExpandOps, sha256SB0ConsumeOps, sha256SB0Ops, sha256BodyOps]
  set_option maxRecDepth 4096 in rfl

-- ============================================================================
-- SB0 expand sub-ops (per-word)
-- ============================================================================

private def sha256SB0Expand_W16Ops : List Op := [
    .inst (.dup 15), .inst (.dup 15), .inst (.dup 11), .inst (.swap 1),
    .inst (.dup 4), .inst (.dup 4), .inst (.movdn 3), .inst (.movdn 2),
    .inst (.exec "compute_message_schedule_word")]

private def sha256SB0Expand_W17Ops : List Op := [
    .inst (.swap 1), .inst (.dup 12), .inst (.swap 1),
    .inst (.dup 5), .inst (.dup 5), .inst (.movdn 3), .inst (.movdn 2),
    .inst (.exec "compute_message_schedule_word")]

private def sha256SB0Expand_W18Ops : List Op := [
    .inst (.dup 1), .inst (.dup 14), .inst (.swap 1),
    .inst (.dup 7), .inst (.dup 7), .inst (.movdn 3), .inst (.movdn 2),
    .inst (.exec "compute_message_schedule_word")]

private def sha256SB0Expand_W19_SwapOps : List Op := [
    .inst (.dup 15), .inst (.dup 2), .inst (.dup 9), .inst (.dup 9),
    .inst (.movdn 3), .inst (.movdn 2),
    .inst (.exec "compute_message_schedule_word"),
    .inst (.swapw 1)]

private lemma sha256SB0ExpandOps_split :
    sha256SB0ExpandOps = sha256SB0Expand_W16Ops ++ sha256SB0Expand_W17Ops ++
                          sha256SB0Expand_W18Ops ++ sha256SB0Expand_W19_SwapOps := by
  simp only [sha256SB0Expand_W16Ops, sha256SB0Expand_W17Ops,
             sha256SB0Expand_W18Ops, sha256SB0Expand_W19_SwapOps, sha256SB0ExpandOps]
  rfl

set_option maxHeartbeats 2000000 in
private lemma sha256_SB0_expand_W16
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : Felt)
    (hw0 : w0.isU32 = true) (hw1 : w1.isU32 = true)
    (hw9 : w9.isU32 = true) (hw14 : w14.isU32 = true)
    (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt) :
    execWithEnv sha256ProcEnv 2126
        ⟨w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest,
          mem, frames, adv⟩
        sha256SB0Expand_W16Ops =
    some ⟨sha256SB0W16 w0 w1 w9 w14 :: w15 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 ::
          w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest,
          mem, frames, adv⟩ := by
  simp only [sha256SB0Expand_W16Ops]
  unfold execWithEnv; simp only [List.foldlM]
  miden_dup; miden_dup; miden_dup; miden_swap
  miden_dup; miden_dup; miden_movdn; miden_movdn
  simp only [show sha256ProcEnv "compute_message_schedule_word" =
      some Miden.Core.Sha256.compute_message_schedule_word from rfl]
  rw [compute_message_schedule_word_at_2125 w14 w9 w1 w0
      (w15 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 ::
       w11 :: w12 :: w13 :: w14 :: w15 :: rest)
      _ rfl hw14 hw9 hw1 hw0]
  simp only [MidenState.withStack, sha256SB0W16, pure, Pure.pure]

set_option maxHeartbeats 2000000 in
private lemma sha256_SB0_expand_W17
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 W16 : Felt)
    (hw1 : w1.isU32 = true) (hw2 : w2.isU32 = true)
    (hw10 : w10.isU32 = true) (hw15 : w15.isU32 = true)
    (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt) :
    execWithEnv sha256ProcEnv 2126
        ⟨W16 :: w15 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 ::
          w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest,
          mem, frames, adv⟩
        sha256SB0Expand_W17Ops =
    some ⟨sha256SB0W17 w1 w2 w10 w15 :: W16 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 ::
          w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest,
          mem, frames, adv⟩ := by
  simp only [sha256SB0Expand_W17Ops]
  unfold execWithEnv; simp only [List.foldlM]
  miden_swap; miden_dup; miden_swap
  miden_dup; miden_dup; miden_movdn; miden_movdn
  simp only [show sha256ProcEnv "compute_message_schedule_word" =
      some Miden.Core.Sha256.compute_message_schedule_word from rfl]
  rw [compute_message_schedule_word_at_2125 w15 w10 w2 w1
      _ _ rfl hw15 hw10 hw2 hw1]
  simp only [MidenState.withStack, sha256SB0W17, pure, Pure.pure]

set_option maxHeartbeats 2000000 in
private lemma sha256_SB0_expand_W18
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 W16 W17 : Felt)
    (hw2 : w2.isU32 = true) (hw3 : w3.isU32 = true)
    (hw11 : w11.isU32 = true) (hW16 : W16.isU32 = true)
    (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt) :
    execWithEnv sha256ProcEnv 2126
        ⟨W17 :: W16 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 ::
          w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest,
          mem, frames, adv⟩
        sha256SB0Expand_W18Ops =
    some ⟨sha256SB0W18 w2 w3 w11 W16 :: W17 :: W16 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 ::
          w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest,
          mem, frames, adv⟩ := by
  simp only [sha256SB0Expand_W18Ops]
  unfold execWithEnv; simp only [List.foldlM]
  miden_dup; miden_dup; miden_swap
  miden_dup; miden_dup; miden_movdn; miden_movdn
  simp only [show sha256ProcEnv "compute_message_schedule_word" =
      some Miden.Core.Sha256.compute_message_schedule_word from rfl]
  rw [compute_message_schedule_word_at_2125 W16 w11 w3 w2
      _ _ rfl hW16 hw11 hw3 hw2]
  simp only [MidenState.withStack, sha256SB0W18, pure, Pure.pure]

set_option maxHeartbeats 2000000 in
private lemma sha256_SB0_expand_W19_swap
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 W16 W17 W18 : Felt)
    (hw3 : w3.isU32 = true) (hw4 : w4.isU32 = true)
    (hw12 : w12.isU32 = true) (hW17 : W17.isU32 = true)
    (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt) :
    execWithEnv sha256ProcEnv 2126
        ⟨W18 :: W17 :: W16 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 ::
          w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest,
          mem, frames, adv⟩
        sha256SB0Expand_W19_SwapOps =
    some ⟨w0 :: w1 :: w2 :: w3 :: sha256SB0W19 w3 w4 w12 W17 :: W18 :: W17 :: W16 ::
          w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 ::
          w12 :: w13 :: w14 :: w15 :: rest,
          mem, frames, adv⟩ := by
  simp only [sha256SB0Expand_W19_SwapOps]
  unfold execWithEnv; simp only [List.foldlM]
  miden_dup; miden_dup; miden_dup; miden_dup
  miden_movdn; miden_movdn
  simp only [show sha256ProcEnv "compute_message_schedule_word" =
      some Miden.Core.Sha256.compute_message_schedule_word from rfl]
  rw [compute_message_schedule_word_at_2125 W17 w12 w4 w3
      _ _ rfl hW17 hw12 hw4 hw3]
  simp only [MidenState.withStack, sha256SB0W19]
  rw [stepSwapw1]; miden_bind
  dsimp only [pure, Pure.pure]

-- ============================================================================
-- SB0 expand bridge (chains the 4 per-word lemmas)
-- ============================================================================

set_option maxHeartbeats 800000 in
private lemma sha256_SB0_expand_bridge
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : Felt)
    (hw0 : w0.isU32 = true) (hw1 : w1.isU32 = true) (hw2 : w2.isU32 = true)
    (hw3 : w3.isU32 = true) (hw4 : w4.isU32 = true)
    (hw9 : w9.isU32 = true) (hw10 : w10.isU32 = true) (hw11 : w11.isU32 = true)
    (hw12 : w12.isU32 = true) (hw14 : w14.isU32 = true) (hw15 : w15.isU32 = true)
    (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt) :
    let W16 := sha256SB0W16 w0 w1 w9 w14
    let W17 := sha256SB0W17 w1 w2 w10 w15
    let W18 := sha256SB0W18 w2 w3 w11 W16
    let W19 := sha256SB0W19 w3 w4 w12 W17
    execWithEnv sha256ProcEnv 2126
        ⟨w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest,
          mem, frames, adv⟩
        sha256SB0ExpandOps =
    some ⟨w0 :: w1 :: w2 :: w3 :: W19 :: W18 :: W17 :: W16 ::
          w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 ::
          w12 :: w13 :: w14 :: w15 :: rest,
          mem, frames, adv⟩ := by
  rw [sha256SB0ExpandOps_split]
  rw [List.append_assoc, List.append_assoc, execWithEnv_append]
  rw [sha256_SB0_expand_W16 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
      hw0 hw1 hw9 hw14 rest mem frames adv]
  simp only [bind, Bind.bind, Option.bind]
  rw [execWithEnv_append]
  rw [sha256_SB0_expand_W17 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
      (sha256SB0W16 w0 w1 w9 w14) hw1 hw2 hw10 hw15 rest mem frames adv]
  simp only [bind, Bind.bind, Option.bind]
  rw [execWithEnv_append]
  rw [sha256_SB0_expand_W18 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
      (sha256SB0W16 w0 w1 w9 w14) (sha256SB0W17 w1 w2 w10 w15)
      hw2 hw3 hw11 (u32_mod_isU32 _) rest mem frames adv]
  simp only [bind, Bind.bind, Option.bind]
  rw [sha256_SB0_expand_W19_swap w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
      (sha256SB0W16 w0 w1 w9 w14) (sha256SB0W17 w1 w2 w10 w15)
      (sha256SB0W18 w2 w3 w11 (sha256SB0W16 w0 w1 w9 w14))
      hw3 hw4 hw12 (u32_mod_isU32 _) rest mem frames adv]

-- ============================================================================
-- SB0 consume bridge
-- ============================================================================

set_option maxHeartbeats 4000000 in
private lemma sha256_SB0_consume_bridge
    (w0 w1 w2 w3 : Felt)
    (W16 W17 W18 W19 : Felt)
    (w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : Felt)
    (a b c d e f g h : Felt)
    (H0 H1 H2 H3 H4 H5 H6 H7 : Felt)
    (hw0 : w0.isU32 = true) (hw1 : w1.isU32 = true) (hw2 : w2.isU32 = true)
    (hw3 : w3.isU32 = true)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) (hd : d.isU32 = true)
    (he : e.isU32 = true) (hf : f.isU32 = true) (hg : g.isU32 = true) (hh : h.isU32 = true)
    (rest : List Felt) (mem : Nat → Felt) (adv : List Felt)
    (frame : LocalFrame) (frames_rest : List LocalFrame)
    (hframe_locals : frame.numLocals = 16)
    (hframe_aligned : frame.alignedNumLocals = 16)
    (h3  : mem (frame.localAddr 3)  = a) (h2  : mem (frame.localAddr 2)  = b)
    (h1  : mem (frame.localAddr 1)  = c) (h0  : mem (frame.localAddr 0)  = d)
    (h7  : mem (frame.localAddr 7)  = e) (h6  : mem (frame.localAddr 6)  = f)
    (h5  : mem (frame.localAddr 5)  = g) (h4  : mem (frame.localAddr 4)  = h)
    (h11 : mem (frame.localAddr 11) = H0) (h10 : mem (frame.localAddr 10) = H1)
    (h9  : mem (frame.localAddr 9)  = H2) (h8  : mem (frame.localAddr 8)  = H3)
    (h15 : mem (frame.localAddr 15) = H4) (h14 : mem (frame.localAddr 14) = H5)
    (h13 : mem (frame.localAddr 13) = H6) (h12 : mem (frame.localAddr 12) = H7) :
    let (na, nb, nc, nd, ne, nf, ng, nh) := sha256SB0Compress a b c d e f g h w0 w1 w2 w3
    let b0 := frame.localAddr 0
    let b4 := frame.localAddr 4
    execWithEnv sha256ProcEnv 2126
        ⟨w0 :: w1 :: w2 :: w3 :: W19 :: W18 :: W17 :: W16 ::
          w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 ::
          w12 :: w13 :: w14 :: w15 :: rest,
          mem, frame :: frames_rest, adv⟩
        sha256SB0ConsumeOps =
    some ⟨W19 :: W18 :: W17 :: W16 :: w4 :: w5 :: w6 :: w7 ::
          w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest,
          fun i =>
            if i = b4 + 3 then ne else if i = b4 + 2 then nf else
            if i = b4 + 1 then ng else if i = b4 then nh else
            if i = b0 + 3 then na else if i = b0 + 2 then nb else
            if i = b0 + 1 then nc else if i = b0 then nd else
            mem i,
          frame :: frames_rest, adv⟩ := by
  simp only [sha256SB0ConsumeOps]
  unfold execWithEnv; simp only [List.foldlM]
  -- push K0, padw, locLoadwBe 4, padw, locLoadwBe 0
  rw [stepPush]; miden_bind
  rw [stepPadw]; miden_bind
  rw [stepLocLoadwBe (idx := 4) (frame := frame) (frames_rest := frames_rest)
      (halign := by decide) (hbound := by omega)]; miden_bind
  simp only [show frame.localAddr 4 + 3 = frame.localAddr 7 from by
      simp [LocalFrame.localAddr],
    show frame.localAddr 4 + 2 = frame.localAddr 6 from by
      simp [LocalFrame.localAddr],
    show frame.localAddr 4 + 1 = frame.localAddr 5 from by
      simp [LocalFrame.localAddr]]
  rw [h7, h6, h5, h4]
  rw [stepPadw]; miden_bind
  rw [stepLocLoadwBe (idx := 0) (frame := frame) (frames_rest := frames_rest)
      (halign := by decide) (hbound := by omega)]; miden_bind
  simp only [show frame.localAddr 0 + 3 = frame.localAddr 3 from by
      simp [LocalFrame.localAddr],
    show frame.localAddr 0 + 2 = frame.localAddr 2 from by
      simp [LocalFrame.localAddr],
    show frame.localAddr 0 + 1 = frame.localAddr 1 from by
      simp [LocalFrame.localAddr]]
  rw [h3, h2, h1, h0]
  -- consume round 0 (K0=1116352408, W=w0)
  simp only [show sha256ProcEnv "consume_message_word" =
      some Miden.Core.Sha256.consume_message_word from rfl]
  rw [consume_message_word_at_2125 a b c d e f g h (Felt.ofNat 1116352408) w0
      _ _ rfl ha hb hc hd he hf hg hh (felt_ofNat_isU32_of_lt _ (by norm_num)) hw0]
  simp only [MidenState.withStack]
  -- push K1, movdn 8, consume round 1
  rw [stepPush]; miden_bind
  rw [stepMovdn (hn := rfl)]; miden_bind
  rw [consume_message_word_at_2125 _ _ _ _ _ _ _ _ (Felt.ofNat 1899447441) w1
      _ _ rfl (u32_mod_isU32 _) ha hb hc (u32_mod_isU32 _) he hf hg
      (felt_ofNat_isU32_of_lt _ (by norm_num)) hw1]
  simp only [MidenState.withStack]
  -- push K2, movdn 8, consume round 2
  rw [stepPush]; miden_bind
  rw [stepMovdn (hn := rfl)]; miden_bind
  rw [consume_message_word_at_2125 _ _ _ _ _ _ _ _ (Felt.ofNat 3049323471) w2
      _ _ rfl (u32_mod_isU32 _) (u32_mod_isU32 _) ha hb (u32_mod_isU32 _) (u32_mod_isU32 _)
      he hf (felt_ofNat_isU32_of_lt _ (by norm_num)) hw2]
  simp only [MidenState.withStack]
  -- push K3, movdn 8, consume round 3
  rw [stepPush]; miden_bind
  rw [stepMovdn (hn := rfl)]; miden_bind
  rw [consume_message_word_at_2125 _ _ _ _ _ _ _ _ (Felt.ofNat 3921009573) w3
      _ _ rfl (u32_mod_isU32 _) (u32_mod_isU32 _) (u32_mod_isU32 _) ha (u32_mod_isU32 _)
      (u32_mod_isU32 _) (u32_mod_isU32 _) he (felt_ofNat_isU32_of_lt _ (by norm_num)) hw3]
  simp only [MidenState.withStack]
  -- locStorewBe 0, dropw, locStorewBe 4, dropw
  rw [stepLocStorewBe (idx := 0) (frame := frame) (frames_rest := frames_rest)
      (halign := by decide) (hbound := by omega)]; miden_bind
  rw [stepDropw]; miden_bind
  rw [stepLocStorewBe (idx := 4) (frame := frame) (frames_rest := frames_rest)
      (halign := by decide) (hbound := by omega)]; miden_bind
  rw [stepDropw]; miden_bind
  dsimp only [pure, Pure.pure]
  simp only [sha256SB0Compress, consumeResult]
  rfl

-- ============================================================================
-- SB0 bridge: chains expand and consume
-- ============================================================================

set_option maxHeartbeats 800000 in
lemma sha256_SB0_bridge
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : Felt)
    (a b c d e f g h : Felt)
    (H0 H1 H2 H3 H4 H5 H6 H7 : Felt)
    (hw0 : w0.isU32 = true) (hw1 : w1.isU32 = true) (hw2 : w2.isU32 = true)
    (hw3 : w3.isU32 = true) (hw4 : w4.isU32 = true) (_hw5 : w5.isU32 = true)
    (_hw6 : w6.isU32 = true) (_hw7 : w7.isU32 = true) (_hw8 : w8.isU32 = true)
    (hw9 : w9.isU32 = true) (hw10 : w10.isU32 = true) (hw11 : w11.isU32 = true)
    (hw12 : w12.isU32 = true) (_hw13 : w13.isU32 = true) (hw14 : w14.isU32 = true)
    (hw15 : w15.isU32 = true)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) (hd : d.isU32 = true)
    (he : e.isU32 = true) (hf : f.isU32 = true) (hg : g.isU32 = true) (hh : h.isU32 = true)
    (_hH0 : H0.isU32 = true) (_hH1 : H1.isU32 = true) (_hH2 : H2.isU32 = true)
    (_hH3 : H3.isU32 = true) (_hH4 : H4.isU32 = true) (_hH5 : H5.isU32 = true)
    (_hH6 : H6.isU32 = true) (_hH7 : H7.isU32 = true)
    (rest : List Felt) (mem : Nat → Felt) (adv : List Felt)
    (frame : LocalFrame) (frames_rest : List LocalFrame)
    (hframe_locals : frame.numLocals = 16)
    (hframe_aligned : frame.alignedNumLocals = 16)
    (h3  : mem (frame.localAddr 3)  = a) (h2  : mem (frame.localAddr 2)  = b)
    (h1  : mem (frame.localAddr 1)  = c) (h0  : mem (frame.localAddr 0)  = d)
    (h7  : mem (frame.localAddr 7)  = e) (h6  : mem (frame.localAddr 6)  = f)
    (h5  : mem (frame.localAddr 5)  = g) (h4  : mem (frame.localAddr 4)  = h)
    (h11 : mem (frame.localAddr 11) = H0) (h10 : mem (frame.localAddr 10) = H1)
    (h9  : mem (frame.localAddr 9)  = H2) (h8  : mem (frame.localAddr 8)  = H3)
    (h15 : mem (frame.localAddr 15) = H4) (h14 : mem (frame.localAddr 14) = H5)
    (h13 : mem (frame.localAddr 13) = H6) (h12 : mem (frame.localAddr 12) = H7) :
    let W16 := sha256SB0W16 w0 w1 w9 w14
    let W17 := sha256SB0W17 w1 w2 w10 w15
    let W18 := sha256SB0W18 w2 w3 w11 W16
    let W19 := sha256SB0W19 w3 w4 w12 W17
    let (na, nb, nc, nd, ne, nf, ng, nh) := sha256SB0Compress a b c d e f g h w0 w1 w2 w3
    let b0 := frame.localAddr 0
    let b4 := frame.localAddr 4
    execWithEnv sha256ProcEnv 2126
        ⟨w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest,
          mem, frame :: frames_rest, adv⟩
        sha256SB0Ops =
    some ⟨W19 :: W18 :: W17 :: W16 :: w4 :: w5 :: w6 :: w7 ::
          w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest,
          fun i =>
            if i = b4 + 3 then ne else if i = b4 + 2 then nf else
            if i = b4 + 1 then ng else if i = b4 then nh else
            if i = b0 + 3 then na else if i = b0 + 2 then nb else
            if i = b0 + 1 then nc else if i = b0 then nd else
            mem i,
          frame :: frames_rest, adv⟩ := by
  rw [sha256SB0Ops_split, execWithEnv_append]
  rw [sha256_SB0_expand_bridge w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
      hw0 hw1 hw2 hw3 hw4 hw9 hw10 hw11 hw12 hw14 hw15 rest mem (frame :: frames_rest) adv]
  simp only [bind, Bind.bind, Option.bind]
  rw [sha256_SB0_consume_bridge w0 w1 w2 w3
      (sha256SB0W16 w0 w1 w9 w14) (sha256SB0W17 w1 w2 w10 w15)
      (sha256SB0W18 w2 w3 w11 (sha256SB0W16 w0 w1 w9 w14))
      (sha256SB0W19 w3 w4 w12 (sha256SB0W17 w1 w2 w10 w15))
      w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
      a b c d e f g h H0 H1 H2 H3 H4 H5 H6 H7
      hw0 hw1 hw2 hw3 ha hb hc hd he hf hg hh
      rest mem adv frame frames_rest hframe_locals hframe_aligned
      h3 h2 h1 h0 h7 h6 h5 h4 h11 h10 h9 h8 h15 h14 h13 h12]
  dsimp only [sha256SB0Compress, consumeResult, sha256SB0W16, sha256SB0W17, sha256SB0W18, sha256SB0W19]

-- ============================================================================
-- SB1 spec helpers
-- ============================================================================

private def sha256SB1W20 (W18 w13 w5 w4 : Felt) : Felt :=
  let sig1 := u32RotateRight W18.val 17 ^^^ (u32RotateRight W18.val 19 ^^^ W18.val / 2^10)
  let sig0 := u32RotateRight w5.val 7 ^^^ (u32RotateRight w5.val 18 ^^^ w5.val / 2^3)
  Felt.ofNat ((w4.val + (w13.val + sig1 + sig0) % 2^32) % 2^32)

private def sha256SB1W21 (W19 w14 w6 w5 : Felt) : Felt :=
  let sig1 := u32RotateRight W19.val 17 ^^^ (u32RotateRight W19.val 19 ^^^ W19.val / 2^10)
  let sig0 := u32RotateRight w6.val 7 ^^^ (u32RotateRight w6.val 18 ^^^ w6.val / 2^3)
  Felt.ofNat ((w5.val + (w14.val + sig1 + sig0) % 2^32) % 2^32)

private def sha256SB1W22 (W20 w15 w7 w6 : Felt) : Felt :=
  let sig1 := u32RotateRight W20.val 17 ^^^ (u32RotateRight W20.val 19 ^^^ W20.val / 2^10)
  let sig0 := u32RotateRight w7.val 7 ^^^ (u32RotateRight w7.val 18 ^^^ w7.val / 2^3)
  Felt.ofNat ((w6.val + (w15.val + sig1 + sig0) % 2^32) % 2^32)

private def sha256SB1W23 (W21 W16 w8 w7 : Felt) : Felt :=
  let sig1 := u32RotateRight W21.val 17 ^^^ (u32RotateRight W21.val 19 ^^^ W21.val / 2^10)
  let sig0 := u32RotateRight w8.val 7 ^^^ (u32RotateRight w8.val 18 ^^^ w8.val / 2^3)
  Felt.ofNat ((w7.val + (W16.val + sig1 + sig0) % 2^32) % 2^32)

/-- Result of 4 compression rounds with K[4..7] consuming (w4, w5, w6, w7) -/
private def sha256SB1Compress (a b c d e f g h w4 w5 w6 w7 : Felt) :
    Felt × Felt × Felt × Felt × Felt × Felt × Felt × Felt :=
  let (a1,b1,c1,d1,e1,f1,g1,h1) := consumeResult a b c d e f g h (Felt.ofNat 961987163) w4
  let (a2,b2,c2,d2,e2,f2,g2,h2) := consumeResult a1 b1 c1 d1 e1 f1 g1 h1 (Felt.ofNat 1508970993) w5
  let (a3,b3,c3,d3,e3,f3,g3,h3) := consumeResult a2 b2 c2 d2 e2 f2 g2 h2 (Felt.ofNat 2453635748) w6
  consumeResult a3 b3 c3 d3 e3 f3 g3 h3 (Felt.ofNat 2870763221) w7

-- ============================================================================
-- SB1 sub-ops split
-- ============================================================================

/-- SB1 expand phase: 4 compute_message_schedule_word calls + movupw 2 -/
private def sha256SB1ExpandOps : List Op := [
    .inst (.dup 15), .inst (.dup 15), .inst (.dup 15),
    .inst (.dup 4), .inst (.dup 9), .inst (.dup 9),
    .inst (.movdn 3), .inst (.movdn 2),
    .inst (.exec "compute_message_schedule_word"),
    .inst (.swap 1), .inst (.dup 3),
    .inst (.dup 10), .inst (.dup 10),
    .inst (.movdn 3), .inst (.movdn 2),
    .inst (.exec "compute_message_schedule_word"),
    .inst (.movup 2), .inst (.dup 2),
    .inst (.dup 11), .inst (.dup 11),
    .inst (.movdn 3), .inst (.movdn 2),
    .inst (.exec "compute_message_schedule_word"),
    .inst (.dup 6), .inst (.dup 2),
    .inst (.dup 13), .inst (.dup 13),
    .inst (.movdn 3), .inst (.movdn 2),
    .inst (.exec "compute_message_schedule_word"),
    .inst (.movupw 2)]

/-- SB1 consume+store phase -/
private def sha256SB1ConsumeOps : List Op := [
    .inst (.push 961987163), .inst .padw, .inst (.locLoadwBe 4),
    .inst .padw, .inst (.locLoadwBe 0),
    .inst (.exec "consume_message_word"),
    .inst (.push 1508970993), .inst (.movdn 8),
    .inst (.exec "consume_message_word"),
    .inst (.push 2453635748), .inst (.movdn 8),
    .inst (.exec "consume_message_word"),
    .inst (.push 2870763221), .inst (.movdn 8),
    .inst (.exec "consume_message_word"),
    .inst (.locStorewBe 0), .inst .dropw,
    .inst (.locStorewBe 4), .inst .dropw]

private lemma sha256SB1Ops_split :
    sha256SB1Ops = sha256SB1ExpandOps ++ sha256SB1ConsumeOps := by
  simp only [sha256SB1ExpandOps, sha256SB1ConsumeOps, sha256SB1Ops, sha256BodyOps]
  set_option maxRecDepth 4096 in rfl

-- ============================================================================
-- SB1 expand sub-ops (per-word)
-- ============================================================================

private def sha256SB1Expand_W20Ops : List Op := [
    .inst (.dup 15), .inst (.dup 15), .inst (.dup 15),
    .inst (.dup 4), .inst (.dup 9), .inst (.dup 9),
    .inst (.movdn 3), .inst (.movdn 2),
    .inst (.exec "compute_message_schedule_word")]

private def sha256SB1Expand_W21Ops : List Op := [
    .inst (.swap 1), .inst (.dup 3),
    .inst (.dup 10), .inst (.dup 10),
    .inst (.movdn 3), .inst (.movdn 2),
    .inst (.exec "compute_message_schedule_word")]

private def sha256SB1Expand_W22Ops : List Op := [
    .inst (.movup 2), .inst (.dup 2),
    .inst (.dup 11), .inst (.dup 11),
    .inst (.movdn 3), .inst (.movdn 2),
    .inst (.exec "compute_message_schedule_word")]

private def sha256SB1Expand_W23_MovupwOps : List Op := [
    .inst (.dup 6), .inst (.dup 2),
    .inst (.dup 13), .inst (.dup 13),
    .inst (.movdn 3), .inst (.movdn 2),
    .inst (.exec "compute_message_schedule_word"),
    .inst (.movupw 2)]

private lemma sha256SB1ExpandOps_split :
    sha256SB1ExpandOps = sha256SB1Expand_W20Ops ++ sha256SB1Expand_W21Ops ++
                          sha256SB1Expand_W22Ops ++ sha256SB1Expand_W23_MovupwOps := by
  simp only [sha256SB1Expand_W20Ops, sha256SB1Expand_W21Ops,
             sha256SB1Expand_W22Ops, sha256SB1Expand_W23_MovupwOps, sha256SB1ExpandOps]
  rfl

-- SB1 input stack: [W19, W18, W17, W16, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, rest]
-- After dup 15, dup 15, dup 15: [w13, w14, w15, W19, W18, W17, W16, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, rest]
-- After dup 4: [W18, w13, w14, w15, W19, ...]
-- After dup 9, dup 9: [w4, w5, W18, w13, ...]
-- After movdn 3, movdn 2: [W18, w13, w5, w4, ...]
-- compute: W20 = σ₁(W18) + w13 + σ₀(w5) + w4
-- Result: [W20, w14, w15, W19, W18, W17, W16, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, rest]

set_option maxHeartbeats 2000000 in
private lemma sha256_SB1_expand_W20
    (W19 W18 W17 W16 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : Felt)
    (hW18 : W18.isU32 = true) (hw13 : w13.isU32 = true)
    (hw5 : w5.isU32 = true) (hw4 : w4.isU32 = true)
    (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt) :
    execWithEnv sha256ProcEnv 2126
        ⟨W19::W18::W17::W16::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest,
          mem, frames, adv⟩
        sha256SB1Expand_W20Ops =
    some ⟨sha256SB1W20 W18 w13 w5 w4 :: w14 :: w15 :: W19 :: W18 :: W17 :: W16 ::
          w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest,
          mem, frames, adv⟩ := by
  simp only [sha256SB1Expand_W20Ops]
  unfold execWithEnv; simp only [List.foldlM]
  miden_dup; miden_dup; miden_dup
  miden_dup; miden_dup; miden_dup; miden_movdn; miden_movdn
  simp only [show sha256ProcEnv "compute_message_schedule_word" =
      some Miden.Core.Sha256.compute_message_schedule_word from rfl]
  rw [compute_message_schedule_word_at_2125 W18 w13 w5 w4
      (w14 :: w15 :: W19 :: W18 :: W17 :: W16 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 ::
       w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest)
      _ rfl hW18 hw13 hw5 hw4]
  simp only [MidenState.withStack, sha256SB1W20, pure, Pure.pure]

-- After W20: [W20, w14, w15, W19, W18, W17, W16, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, rest]
-- swap 1: [w14, W20, w15, W19, ...]
-- dup 3: [W19, w14, W20, w15, W19, ...]
-- dup 10: [w6, W19, w14, W20, w15, W19, W18, W17, W16, w4, w5, w6, ...]
-- dup 10: [w5, w6, W19, w14, ...]
-- movdn 3, movdn 2: [W19, w14, w6, w5, ...]
-- compute: W21 = σ₁(W19) + w14 + σ₀(w6) + w5

set_option maxHeartbeats 2000000 in
private lemma sha256_SB1_expand_W21
    (W19 W18 W17 W16 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 W20 : Felt)
    (hW19 : W19.isU32 = true) (hw14 : w14.isU32 = true)
    (hw6 : w6.isU32 = true) (hw5 : w5.isU32 = true)
    (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt) :
    execWithEnv sha256ProcEnv 2126
        ⟨W20 :: w14 :: w15 :: W19 :: W18 :: W17 :: W16 ::
          w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest,
          mem, frames, adv⟩
        sha256SB1Expand_W21Ops =
    some ⟨sha256SB1W21 W19 w14 w6 w5 :: W20 :: w15 :: W19 :: W18 :: W17 :: W16 ::
          w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest,
          mem, frames, adv⟩ := by
  simp only [sha256SB1Expand_W21Ops]
  unfold execWithEnv; simp only [List.foldlM]
  miden_swap; miden_dup
  miden_dup; miden_dup; miden_movdn; miden_movdn
  simp only [show sha256ProcEnv "compute_message_schedule_word" =
      some Miden.Core.Sha256.compute_message_schedule_word from rfl]
  rw [compute_message_schedule_word_at_2125 W19 w14 w6 w5
      _ _ rfl hW19 hw14 hw6 hw5]
  simp only [MidenState.withStack, sha256SB1W21, pure, Pure.pure]

-- After W21: [W21, W20, w15, W19, W18, W17, W16, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, rest]
-- movup 2: [w15, W21, W20, W19, ...]
-- dup 2: [W20, w15, W21, W20, W19, ...]
-- dup 11: [w7, W20, w15, W21, W20, W19, W18, W17, W16, w4, w5, w6, w7, ...]
-- dup 11: [w6, w7, W20, w15, ...]
-- movdn 3, movdn 2: [W20, w15, w7, w6, ...]
-- compute: W22 = σ₁(W20) + w15 + σ₀(w7) + w6

set_option maxHeartbeats 2000000 in
private lemma sha256_SB1_expand_W22
    (W19 W18 W17 W16 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 W20 W21 : Felt)
    (hW20 : W20.isU32 = true) (hw15 : w15.isU32 = true)
    (hw7 : w7.isU32 = true) (hw6 : w6.isU32 = true)
    (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt) :
    execWithEnv sha256ProcEnv 2126
        ⟨W21 :: W20 :: w15 :: W19 :: W18 :: W17 :: W16 ::
          w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest,
          mem, frames, adv⟩
        sha256SB1Expand_W22Ops =
    some ⟨sha256SB1W22 W20 w15 w7 w6 :: W21 :: W20 :: W19 :: W18 :: W17 :: W16 ::
          w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest,
          mem, frames, adv⟩ := by
  simp only [sha256SB1Expand_W22Ops]
  unfold execWithEnv; simp only [List.foldlM]
  rw [stepMovup (hn := rfl) (hv := rfl)]; miden_bind
  miden_dup
  miden_dup; miden_dup; miden_movdn; miden_movdn
  simp only [show sha256ProcEnv "compute_message_schedule_word" =
      some Miden.Core.Sha256.compute_message_schedule_word from rfl]
  rw [compute_message_schedule_word_at_2125 W20 w15 w7 w6
      _ _ rfl hW20 hw15 hw7 hw6]
  simp only [MidenState.withStack, sha256SB1W22, pure, Pure.pure]

-- After W22: [W22, W21, W20, W19, W18, W17, W16, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, rest]
-- dup 6: [W16, W22, W21, W20, W19, W18, W17, W16, w4, ...]
-- dup 2: [W21, W16, W22, W21, ...]
-- dup 13: [w8, W21, W16, W22, ...]
-- dup 13: [w7, w8, W21, W16, ...]
-- movdn 3, movdn 2: [W21, W16, w8, w7, ...]
-- compute: W23 = σ₁(W21) + W16 + σ₀(w8) + w7
-- Then movupw 2: moves w4,w5,w6,w7 to top

set_option maxHeartbeats 2000000 in
private lemma sha256_SB1_expand_W23_movupw
    (W19 W18 W17 W16 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 W20 W21 W22 : Felt)
    (hW21 : W21.isU32 = true) (hW16 : W16.isU32 = true)
    (hw8 : w8.isU32 = true) (hw7 : w7.isU32 = true)
    (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt) :
    execWithEnv sha256ProcEnv 2126
        ⟨W22 :: W21 :: W20 :: W19 :: W18 :: W17 :: W16 ::
          w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest,
          mem, frames, adv⟩
        sha256SB1Expand_W23_MovupwOps =
    some ⟨w4 :: w5 :: w6 :: w7 ::
          sha256SB1W23 W21 W16 w8 w7 :: W22 :: W21 :: W20 ::
          W19 :: W18 :: W17 :: W16 ::
          w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest,
          mem, frames, adv⟩ := by
  simp only [sha256SB1Expand_W23_MovupwOps]
  unfold execWithEnv; simp only [List.foldlM]
  miden_dup; miden_dup; miden_dup; miden_dup
  miden_movdn; miden_movdn
  simp only [show sha256ProcEnv "compute_message_schedule_word" =
      some Miden.Core.Sha256.compute_message_schedule_word from rfl]
  rw [compute_message_schedule_word_at_2125 W21 W16 w8 w7
      _ _ rfl hW21 hW16 hw8 hw7]
  simp only [MidenState.withStack, sha256SB1W23]
  rw [stepMovupw2]; miden_bind
  dsimp only [pure, Pure.pure]

-- ============================================================================
-- SB1 expand bridge (chains the 4 per-word lemmas)
-- ============================================================================

set_option maxHeartbeats 800000 in
private lemma sha256_SB1_expand_bridge
    (W19 W18 W17 W16 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : Felt)
    (hW18 : W18.isU32 = true) (hW19 : W19.isU32 = true)
    (hW16 : W16.isU32 = true)
    (hw4 : w4.isU32 = true) (hw5 : w5.isU32 = true) (hw6 : w6.isU32 = true)
    (hw7 : w7.isU32 = true) (hw8 : w8.isU32 = true)
    (hw13 : w13.isU32 = true) (hw14 : w14.isU32 = true) (hw15 : w15.isU32 = true)
    (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt) :
    let W20 := sha256SB1W20 W18 w13 w5 w4
    let W21 := sha256SB1W21 W19 w14 w6 w5
    let W22 := sha256SB1W22 W20 w15 w7 w6
    let W23 := sha256SB1W23 W21 W16 w8 w7
    execWithEnv sha256ProcEnv 2126
        ⟨W19::W18::W17::W16::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest,
          mem, frames, adv⟩
        sha256SB1ExpandOps =
    some ⟨w4 :: w5 :: w6 :: w7 :: W23 :: W22 :: W21 :: W20 ::
          W19 :: W18 :: W17 :: W16 ::
          w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest,
          mem, frames, adv⟩ := by
  rw [sha256SB1ExpandOps_split]
  rw [List.append_assoc, List.append_assoc, execWithEnv_append]
  rw [sha256_SB1_expand_W20 W19 W18 W17 W16 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
      hW18 hw13 hw5 hw4 rest mem frames adv]
  simp only [bind, Bind.bind, Option.bind]
  rw [execWithEnv_append]
  rw [sha256_SB1_expand_W21 W19 W18 W17 W16 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
      (sha256SB1W20 W18 w13 w5 w4) hW19 hw14 hw6 hw5 rest mem frames adv]
  simp only [bind, Bind.bind, Option.bind]
  rw [execWithEnv_append]
  rw [sha256_SB1_expand_W22 W19 W18 W17 W16 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
      (sha256SB1W20 W18 w13 w5 w4) (sha256SB1W21 W19 w14 w6 w5)
      (u32_mod_isU32 _) hw15 hw7 hw6 rest mem frames adv]
  simp only [bind, Bind.bind, Option.bind]
  rw [sha256_SB1_expand_W23_movupw W19 W18 W17 W16 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
      (sha256SB1W20 W18 w13 w5 w4) (sha256SB1W21 W19 w14 w6 w5)
      (sha256SB1W22 (sha256SB1W20 W18 w13 w5 w4) w15 w7 w6)
      (u32_mod_isU32 _) hW16 hw8 hw7 rest mem frames adv]

-- ============================================================================
-- SB1 consume bridge
-- ============================================================================

set_option maxHeartbeats 4000000 in
private lemma sha256_SB1_consume_bridge
    (w4 w5 w6 w7 : Felt)
    (W20 W21 W22 W23 : Felt)
    (W19 W18 W17 W16 : Felt)
    (w8 w9 w10 w11 w12 w13 w14 w15 : Felt)
    (a b c d e f g h : Felt)
    (H0 H1 H2 H3 H4 H5 H6 H7 : Felt)
    (hw4 : w4.isU32 = true) (hw5 : w5.isU32 = true) (hw6 : w6.isU32 = true)
    (hw7 : w7.isU32 = true)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) (hd : d.isU32 = true)
    (he : e.isU32 = true) (hf : f.isU32 = true) (hg : g.isU32 = true) (hh : h.isU32 = true)
    (rest : List Felt) (mem : Nat → Felt) (adv : List Felt)
    (frame : LocalFrame) (frames_rest : List LocalFrame)
    (hframe_locals : frame.numLocals = 16)
    (hframe_aligned : frame.alignedNumLocals = 16)
    (h3  : mem (frame.localAddr 3)  = a) (h2  : mem (frame.localAddr 2)  = b)
    (h1  : mem (frame.localAddr 1)  = c) (h0  : mem (frame.localAddr 0)  = d)
    (h7  : mem (frame.localAddr 7)  = e) (h6  : mem (frame.localAddr 6)  = f)
    (h5  : mem (frame.localAddr 5)  = g) (h4  : mem (frame.localAddr 4)  = h)
    (h11 : mem (frame.localAddr 11) = H0) (h10 : mem (frame.localAddr 10) = H1)
    (h9  : mem (frame.localAddr 9)  = H2) (h8  : mem (frame.localAddr 8)  = H3)
    (h15 : mem (frame.localAddr 15) = H4) (h14 : mem (frame.localAddr 14) = H5)
    (h13 : mem (frame.localAddr 13) = H6) (h12 : mem (frame.localAddr 12) = H7) :
    let (na, nb, nc, nd, ne, nf, ng, nh) := sha256SB1Compress a b c d e f g h w4 w5 w6 w7
    let b0 := frame.localAddr 0
    let b4 := frame.localAddr 4
    execWithEnv sha256ProcEnv 2126
        ⟨w4 :: w5 :: w6 :: w7 :: W23 :: W22 :: W21 :: W20 ::
          W19 :: W18 :: W17 :: W16 ::
          w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest,
          mem, frame :: frames_rest, adv⟩
        sha256SB1ConsumeOps =
    some ⟨W23 :: W22 :: W21 :: W20 :: W19 :: W18 :: W17 :: W16 ::
          w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest,
          fun i =>
            if i = b4 + 3 then ne else if i = b4 + 2 then nf else
            if i = b4 + 1 then ng else if i = b4 then nh else
            if i = b0 + 3 then na else if i = b0 + 2 then nb else
            if i = b0 + 1 then nc else if i = b0 then nd else
            mem i,
          frame :: frames_rest, adv⟩ := by
  simp only [sha256SB1ConsumeOps]
  unfold execWithEnv; simp only [List.foldlM]
  rw [stepPush]; miden_bind
  rw [stepPadw]; miden_bind
  rw [stepLocLoadwBe (idx := 4) (frame := frame) (frames_rest := frames_rest)
      (halign := by decide) (hbound := by omega)]; miden_bind
  simp only [show frame.localAddr 4 + 3 = frame.localAddr 7 from by
      simp [LocalFrame.localAddr],
    show frame.localAddr 4 + 2 = frame.localAddr 6 from by
      simp [LocalFrame.localAddr],
    show frame.localAddr 4 + 1 = frame.localAddr 5 from by
      simp [LocalFrame.localAddr]]
  rw [h7, h6, h5, h4]
  rw [stepPadw]; miden_bind
  rw [stepLocLoadwBe (idx := 0) (frame := frame) (frames_rest := frames_rest)
      (halign := by decide) (hbound := by omega)]; miden_bind
  simp only [show frame.localAddr 0 + 3 = frame.localAddr 3 from by
      simp [LocalFrame.localAddr],
    show frame.localAddr 0 + 2 = frame.localAddr 2 from by
      simp [LocalFrame.localAddr],
    show frame.localAddr 0 + 1 = frame.localAddr 1 from by
      simp [LocalFrame.localAddr]]
  rw [h3, h2, h1, h0]
  simp only [show sha256ProcEnv "consume_message_word" =
      some Miden.Core.Sha256.consume_message_word from rfl]
  rw [consume_message_word_at_2125 a b c d e f g h (Felt.ofNat 961987163) w4
      _ _ rfl ha hb hc hd he hf hg hh (felt_ofNat_isU32_of_lt _ (by norm_num)) hw4]
  simp only [MidenState.withStack]
  rw [stepPush]; miden_bind
  rw [stepMovdn (hn := rfl)]; miden_bind
  rw [consume_message_word_at_2125 _ _ _ _ _ _ _ _ (Felt.ofNat 1508970993) w5
      _ _ rfl (u32_mod_isU32 _) ha hb hc (u32_mod_isU32 _) he hf hg
      (felt_ofNat_isU32_of_lt _ (by norm_num)) hw5]
  simp only [MidenState.withStack]
  rw [stepPush]; miden_bind
  rw [stepMovdn (hn := rfl)]; miden_bind
  rw [consume_message_word_at_2125 _ _ _ _ _ _ _ _ (Felt.ofNat 2453635748) w6
      _ _ rfl (u32_mod_isU32 _) (u32_mod_isU32 _) ha hb (u32_mod_isU32 _) (u32_mod_isU32 _)
      he hf (felt_ofNat_isU32_of_lt _ (by norm_num)) hw6]
  simp only [MidenState.withStack]
  rw [stepPush]; miden_bind
  rw [stepMovdn (hn := rfl)]; miden_bind
  rw [consume_message_word_at_2125 _ _ _ _ _ _ _ _ (Felt.ofNat 2870763221) w7
      _ _ rfl (u32_mod_isU32 _) (u32_mod_isU32 _) (u32_mod_isU32 _) ha (u32_mod_isU32 _)
      (u32_mod_isU32 _) (u32_mod_isU32 _) he (felt_ofNat_isU32_of_lt _ (by norm_num)) hw7]
  simp only [MidenState.withStack]
  rw [stepLocStorewBe (idx := 0) (frame := frame) (frames_rest := frames_rest)
      (halign := by decide) (hbound := by omega)]; miden_bind
  rw [stepDropw]; miden_bind
  rw [stepLocStorewBe (idx := 4) (frame := frame) (frames_rest := frames_rest)
      (halign := by decide) (hbound := by omega)]; miden_bind
  rw [stepDropw]; miden_bind
  dsimp only [pure, Pure.pure]
  simp only [sha256SB1Compress, consumeResult]
  rfl

-- ============================================================================
-- SB1 bridge: chains expand and consume
-- ============================================================================

set_option maxHeartbeats 800000 in
lemma sha256_SB1_bridge
    (W19 W18 W17 W16 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : Felt)
    (a b c d e f g h : Felt)
    (H0 H1 H2 H3 H4 H5 H6 H7 : Felt)
    (hW19 : W19.isU32 = true) (hW18 : W18.isU32 = true)
    (_hW17 : W17.isU32 = true) (hW16 : W16.isU32 = true)
    (hw4 : w4.isU32 = true) (hw5 : w5.isU32 = true)
    (hw6 : w6.isU32 = true) (hw7 : w7.isU32 = true)
    (hw8 : w8.isU32 = true) (_hw9 : w9.isU32 = true)
    (_hw10 : w10.isU32 = true) (_hw11 : w11.isU32 = true)
    (_hw12 : w12.isU32 = true)
    (hw13 : w13.isU32 = true) (hw14 : w14.isU32 = true) (hw15 : w15.isU32 = true)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) (hd : d.isU32 = true)
    (he : e.isU32 = true) (hf : f.isU32 = true) (hg : g.isU32 = true) (hh : h.isU32 = true)
    (_hH0 : H0.isU32 = true) (_hH1 : H1.isU32 = true) (_hH2 : H2.isU32 = true)
    (_hH3 : H3.isU32 = true) (_hH4 : H4.isU32 = true) (_hH5 : H5.isU32 = true)
    (_hH6 : H6.isU32 = true) (_hH7 : H7.isU32 = true)
    (rest : List Felt) (mem : Nat → Felt) (adv : List Felt)
    (frame : LocalFrame) (frames_rest : List LocalFrame)
    (hframe_locals : frame.numLocals = 16)
    (hframe_aligned : frame.alignedNumLocals = 16)
    (h3  : mem (frame.localAddr 3)  = a) (h2  : mem (frame.localAddr 2)  = b)
    (h1  : mem (frame.localAddr 1)  = c) (h0  : mem (frame.localAddr 0)  = d)
    (h7  : mem (frame.localAddr 7)  = e) (h6  : mem (frame.localAddr 6)  = f)
    (h5  : mem (frame.localAddr 5)  = g) (h4  : mem (frame.localAddr 4)  = h)
    (h11 : mem (frame.localAddr 11) = H0) (h10 : mem (frame.localAddr 10) = H1)
    (h9  : mem (frame.localAddr 9)  = H2) (h8  : mem (frame.localAddr 8)  = H3)
    (h15 : mem (frame.localAddr 15) = H4) (h14 : mem (frame.localAddr 14) = H5)
    (h13 : mem (frame.localAddr 13) = H6) (h12 : mem (frame.localAddr 12) = H7) :
    let W20 := sha256SB1W20 W18 w13 w5 w4
    let W21 := sha256SB1W21 W19 w14 w6 w5
    let W22 := sha256SB1W22 W20 w15 w7 w6
    let W23 := sha256SB1W23 W21 W16 w8 w7
    let (na, nb, nc, nd, ne, nf, ng, nh) := sha256SB1Compress a b c d e f g h w4 w5 w6 w7
    let b0 := frame.localAddr 0
    let b4 := frame.localAddr 4
    execWithEnv sha256ProcEnv 2126
        ⟨W19::W18::W17::W16::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest,
          mem, frame :: frames_rest, adv⟩
        sha256SB1Ops =
    some ⟨W23 :: W22 :: W21 :: W20 :: W19 :: W18 :: W17 :: W16 ::
          w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest,
          fun i =>
            if i = b4 + 3 then ne else if i = b4 + 2 then nf else
            if i = b4 + 1 then ng else if i = b4 then nh else
            if i = b0 + 3 then na else if i = b0 + 2 then nb else
            if i = b0 + 1 then nc else if i = b0 then nd else
            mem i,
          frame :: frames_rest, adv⟩ := by
  rw [sha256SB1Ops_split, execWithEnv_append]
  rw [sha256_SB1_expand_bridge W19 W18 W17 W16 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
      hW18 hW19 hW16 hw4 hw5 hw6 hw7 hw8 hw13 hw14 hw15 rest mem (frame :: frames_rest) adv]
  simp only [bind, Bind.bind, Option.bind]
  rw [sha256_SB1_consume_bridge w4 w5 w6 w7
      (sha256SB1W20 W18 w13 w5 w4) (sha256SB1W21 W19 w14 w6 w5)
      (sha256SB1W22 (sha256SB1W20 W18 w13 w5 w4) w15 w7 w6)
      (sha256SB1W23 (sha256SB1W21 W19 w14 w6 w5) W16 w8 w7)
      W19 W18 W17 W16
      w8 w9 w10 w11 w12 w13 w14 w15
      a b c d e f g h H0 H1 H2 H3 H4 H5 H6 H7
      hw4 hw5 hw6 hw7 ha hb hc hd he hf hg hh
      rest mem adv frame frames_rest hframe_locals hframe_aligned
      h3 h2 h1 h0 h7 h6 h5 h4 h11 h10 h9 h8 h15 h14 h13 h12]
  dsimp only [sha256SB1Compress, consumeResult, sha256SB1W20, sha256SB1W21, sha256SB1W22, sha256SB1W23]

-- ============================================================================
-- SB2 spec helpers
-- ============================================================================

private def sha256SB2W24 (W22 W17 w9 w8 : Felt) : Felt :=
  let sig1 := u32RotateRight W22.val 17 ^^^ (u32RotateRight W22.val 19 ^^^ W22.val / 2^10)
  let sig0 := u32RotateRight w9.val 7 ^^^ (u32RotateRight w9.val 18 ^^^ w9.val / 2^3)
  Felt.ofNat ((w8.val + (W17.val + sig1 + sig0) % 2^32) % 2^32)

private def sha256SB2W25 (W23 W18 w10 w9 : Felt) : Felt :=
  let sig1 := u32RotateRight W23.val 17 ^^^ (u32RotateRight W23.val 19 ^^^ W23.val / 2^10)
  let sig0 := u32RotateRight w10.val 7 ^^^ (u32RotateRight w10.val 18 ^^^ w10.val / 2^3)
  Felt.ofNat ((w9.val + (W18.val + sig1 + sig0) % 2^32) % 2^32)

private def sha256SB2W26 (W24 W19 w11 w10 : Felt) : Felt :=
  let sig1 := u32RotateRight W24.val 17 ^^^ (u32RotateRight W24.val 19 ^^^ W24.val / 2^10)
  let sig0 := u32RotateRight w11.val 7 ^^^ (u32RotateRight w11.val 18 ^^^ w11.val / 2^3)
  Felt.ofNat ((w10.val + (W19.val + sig1 + sig0) % 2^32) % 2^32)

private def sha256SB2W27 (W25 W20 w12 w11 : Felt) : Felt :=
  let sig1 := u32RotateRight W25.val 17 ^^^ (u32RotateRight W25.val 19 ^^^ W25.val / 2^10)
  let sig0 := u32RotateRight w12.val 7 ^^^ (u32RotateRight w12.val 18 ^^^ w12.val / 2^3)
  Felt.ofNat ((w11.val + (W20.val + sig1 + sig0) % 2^32) % 2^32)

/-- Result of 4 compression rounds with K[8..11] consuming (w8, w9, w10, w11) -/
private def sha256SB2Compress (a b c d e f g h w8 w9 w10 w11 : Felt) :
    Felt × Felt × Felt × Felt × Felt × Felt × Felt × Felt :=
  let (a1,b1,c1,d1,e1,f1,g1,h1) := consumeResult a b c d e f g h (Felt.ofNat 3624381080) w8
  let (a2,b2,c2,d2,e2,f2,g2,h2) := consumeResult a1 b1 c1 d1 e1 f1 g1 h1 (Felt.ofNat 310598401) w9
  let (a3,b3,c3,d3,e3,f3,g3,h3) := consumeResult a2 b2 c2 d2 e2 f2 g2 h2 (Felt.ofNat 607225278) w10
  consumeResult a3 b3 c3 d3 e3 f3 g3 h3 (Felt.ofNat 1426881987) w11

-- ============================================================================
-- SB2 sub-ops split
-- ============================================================================

/-- SB2 expand phase: 4 compute_message_schedule_word calls + movupw 3 -/
private def sha256SB2ExpandOps : List Op := [
    .inst (.dup 6), .inst (.dup 2),
    .inst (.dup 11), .inst (.dup 11),
    .inst (.movdn 3), .inst (.movdn 2),
    .inst (.exec "compute_message_schedule_word"),
    .inst (.dup 6), .inst (.dup 2),
    .inst (.dup 13), .inst (.dup 13),
    .inst (.movdn 3), .inst (.movdn 2),
    .inst (.exec "compute_message_schedule_word"),
    .inst (.dup 6), .inst (.dup 2),
    .inst (.dup 15), .inst (.dup 15),
    .inst (.movdn 3), .inst (.movdn 2),
    .inst (.exec "compute_message_schedule_word"),
    .inst (.dup 15), .inst (.dup 15),
    .inst (.swap 1), .inst (.dup 8),
    .inst (.dup 4),
    .inst (.exec "compute_message_schedule_word"),
    .inst (.movupw 3)]

/-- SB2 consume+store phase -/
private def sha256SB2ConsumeOps : List Op := [
    .inst (.push 3624381080), .inst .padw, .inst (.locLoadwBe 4),
    .inst .padw, .inst (.locLoadwBe 0),
    .inst (.exec "consume_message_word"),
    .inst (.push 310598401), .inst (.movdn 8),
    .inst (.exec "consume_message_word"),
    .inst (.push 607225278), .inst (.movdn 8),
    .inst (.exec "consume_message_word"),
    .inst (.push 1426881987), .inst (.movdn 8),
    .inst (.exec "consume_message_word"),
    .inst (.locStorewBe 0), .inst .dropw,
    .inst (.locStorewBe 4), .inst .dropw]

private lemma sha256SB2Ops_split :
    sha256SB2Ops = sha256SB2ExpandOps ++ sha256SB2ConsumeOps := by
  simp only [sha256SB2ExpandOps, sha256SB2ConsumeOps, sha256SB2Ops, sha256BodyOps]
  set_option maxRecDepth 4096 in rfl

-- ============================================================================
-- SB2 expand sub-ops (per-word)
-- ============================================================================

private def sha256SB2Expand_W24Ops : List Op := [
    .inst (.dup 6), .inst (.dup 2),
    .inst (.dup 11), .inst (.dup 11),
    .inst (.movdn 3), .inst (.movdn 2),
    .inst (.exec "compute_message_schedule_word")]

private def sha256SB2Expand_W25Ops : List Op := [
    .inst (.dup 6), .inst (.dup 2),
    .inst (.dup 13), .inst (.dup 13),
    .inst (.movdn 3), .inst (.movdn 2),
    .inst (.exec "compute_message_schedule_word")]

private def sha256SB2Expand_W26Ops : List Op := [
    .inst (.dup 6), .inst (.dup 2),
    .inst (.dup 15), .inst (.dup 15),
    .inst (.movdn 3), .inst (.movdn 2),
    .inst (.exec "compute_message_schedule_word")]

private def sha256SB2Expand_W27_MovupwOps : List Op := [
    .inst (.dup 15), .inst (.dup 15),
    .inst (.swap 1), .inst (.dup 8),
    .inst (.dup 4),
    .inst (.exec "compute_message_schedule_word"),
    .inst (.movupw 3)]

private lemma sha256SB2ExpandOps_split :
    sha256SB2ExpandOps = sha256SB2Expand_W24Ops ++ sha256SB2Expand_W25Ops ++
                          sha256SB2Expand_W26Ops ++ sha256SB2Expand_W27_MovupwOps := by
  simp only [sha256SB2Expand_W24Ops, sha256SB2Expand_W25Ops,
             sha256SB2Expand_W26Ops, sha256SB2Expand_W27_MovupwOps, sha256SB2ExpandOps]
  rfl

-- SB2 input: [W23, W22, W21, W20, W19, W18, W17, W16, w8, w9, w10, w11, w12, w13, w14, w15, rest]
-- dup 6: [W17, W23, ...] ; dup 2: [W22, W17, W23, W22, ...]
-- dup 11, dup 11: [w8, w9, W22, W17, ...] ; movdn3, movdn2: [W22, W17, w9, w8, ...]
-- compute W24 = σ₁(W22) + W17 + σ₀(w9) + w8

set_option maxHeartbeats 2000000 in
private lemma sha256_SB2_expand_W24
    (W23 W22 W21 W20 W19 W18 W17 W16 w8 w9 w10 w11 w12 w13 w14 w15 : Felt)
    (hW22 : W22.isU32 = true) (hW17 : W17.isU32 = true)
    (hw9 : w9.isU32 = true) (hw8 : w8.isU32 = true)
    (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt) :
    execWithEnv sha256ProcEnv 2126
        ⟨W23::W22::W21::W20::W19::W18::W17::W16::w8::w9::w10::w11::w12::w13::w14::w15::rest,
          mem, frames, adv⟩
        sha256SB2Expand_W24Ops =
    some ⟨sha256SB2W24 W22 W17 w9 w8 :: W23 :: W22 :: W21 :: W20 :: W19 :: W18 :: W17 :: W16 ::
          w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest,
          mem, frames, adv⟩ := by
  simp only [sha256SB2Expand_W24Ops]
  unfold execWithEnv; simp only [List.foldlM]
  miden_dup; miden_dup
  miden_dup; miden_dup; miden_movdn; miden_movdn
  simp only [show sha256ProcEnv "compute_message_schedule_word" =
      some Miden.Core.Sha256.compute_message_schedule_word from rfl]
  rw [compute_message_schedule_word_at_2125 W22 W17 w9 w8
      (W23 :: W22 :: W21 :: W20 :: W19 :: W18 :: W17 :: W16 ::
       w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest)
      _ rfl hW22 hW17 hw9 hw8]
  simp only [MidenState.withStack, sha256SB2W24, pure, Pure.pure]

-- After W24: [W24, W23, W22, W21, W20, W19, W18, W17, W16, w8, w9, w10, w11, w12, w13, w14, w15, rest]
-- dup 6: [W18, W24, ...] ; dup 2: [W23, W18, W24, W23, ...]
-- dup 13, dup 13: [w9, w10, W23, W18, ...] ; movdn3, movdn2: [W23, W18, w10, w9, ...]
-- compute W25 = σ₁(W23) + W18 + σ₀(w10) + w9

set_option maxHeartbeats 2000000 in
private lemma sha256_SB2_expand_W25
    (W23 W22 W21 W20 W19 W18 W17 W16 w8 w9 w10 w11 w12 w13 w14 w15 W24 : Felt)
    (hW23 : W23.isU32 = true) (hW18 : W18.isU32 = true)
    (hw10 : w10.isU32 = true) (hw9 : w9.isU32 = true)
    (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt) :
    execWithEnv sha256ProcEnv 2126
        ⟨W24 :: W23 :: W22 :: W21 :: W20 :: W19 :: W18 :: W17 :: W16 ::
          w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest,
          mem, frames, adv⟩
        sha256SB2Expand_W25Ops =
    some ⟨sha256SB2W25 W23 W18 w10 w9 :: W24 :: W23 :: W22 :: W21 :: W20 :: W19 :: W18 :: W17 :: W16 ::
          w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest,
          mem, frames, adv⟩ := by
  simp only [sha256SB2Expand_W25Ops]
  unfold execWithEnv; simp only [List.foldlM]
  miden_dup; miden_dup
  miden_dup; miden_dup; miden_movdn; miden_movdn
  simp only [show sha256ProcEnv "compute_message_schedule_word" =
      some Miden.Core.Sha256.compute_message_schedule_word from rfl]
  rw [compute_message_schedule_word_at_2125 W23 W18 w10 w9
      _ _ rfl hW23 hW18 hw10 hw9]
  simp only [MidenState.withStack, sha256SB2W25, pure, Pure.pure]

-- After W25: [W25, W24, W23, W22, W21, W20, W19, W18, W17, W16, w8, w9, w10, w11, w12, w13, w14, w15, rest]
-- dup 6: [W19, W25, ...] ; dup 2: [W24, W19, W25, W24, ...]
-- dup 15, dup 15: [w10, w11, W24, W19, ...] ; movdn3, movdn2: [W24, W19, w11, w10, ...]
-- compute W26 = σ₁(W24) + W19 + σ₀(w11) + w10

set_option maxHeartbeats 2000000 in
private lemma sha256_SB2_expand_W26
    (W23 W22 W21 W20 W19 W18 W17 W16 w8 w9 w10 w11 w12 w13 w14 w15 W24 W25 : Felt)
    (hW24 : W24.isU32 = true) (hW19 : W19.isU32 = true)
    (hw11 : w11.isU32 = true) (hw10 : w10.isU32 = true)
    (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt) :
    execWithEnv sha256ProcEnv 2126
        ⟨W25 :: W24 :: W23 :: W22 :: W21 :: W20 :: W19 :: W18 :: W17 :: W16 ::
          w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest,
          mem, frames, adv⟩
        sha256SB2Expand_W26Ops =
    some ⟨sha256SB2W26 W24 W19 w11 w10 :: W25 :: W24 :: W23 :: W22 :: W21 :: W20 :: W19 :: W18 :: W17 :: W16 ::
          w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest,
          mem, frames, adv⟩ := by
  simp only [sha256SB2Expand_W26Ops]
  unfold execWithEnv; simp only [List.foldlM]
  miden_dup; miden_dup
  miden_dup; miden_dup; miden_movdn; miden_movdn
  simp only [show sha256ProcEnv "compute_message_schedule_word" =
      some Miden.Core.Sha256.compute_message_schedule_word from rfl]
  rw [compute_message_schedule_word_at_2125 W24 W19 w11 w10
      _ _ rfl hW24 hW19 hw11 hw10]
  simp only [MidenState.withStack, sha256SB2W26, pure, Pure.pure]

-- After W26: [W26, W25, W24, W23, W22, W21, W20, W19, W18, W17, W16, w8, w9, w10, w11, w12, w13, w14, w15, rest]
-- dup 15: [w12, W26, ...] ; dup 15: [w11, w12, W26, ...]
-- swap 1: [w12, w11, W26, ...]
-- dup 8: [W20, w12, w11, W26, W25, W24, W23, W22, W21, W20, ...]
-- dup 4: [W25, W20, w12, w11, W26, ...]
-- compute W27 = σ₁(W25) + W20 + σ₀(w12) + w11
-- Then movupw 3

set_option maxHeartbeats 2000000 in
private lemma sha256_SB2_expand_W27_movupw
    (W23 W22 W21 W20 W19 W18 W17 W16 w8 w9 w10 w11 w12 w13 w14 w15 W24 W25 W26 : Felt)
    (hW25 : W25.isU32 = true) (hW20 : W20.isU32 = true)
    (hw12 : w12.isU32 = true) (hw11 : w11.isU32 = true)
    (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt) :
    execWithEnv sha256ProcEnv 2126
        ⟨W26 :: W25 :: W24 :: W23 :: W22 :: W21 :: W20 :: W19 :: W18 :: W17 :: W16 ::
          w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest,
          mem, frames, adv⟩
        sha256SB2Expand_W27_MovupwOps =
    some ⟨w8 :: w9 :: w10 :: w11 ::
          sha256SB2W27 W25 W20 w12 w11 :: W26 :: W25 :: W24 ::
          W23 :: W22 :: W21 :: W20 :: W19 :: W18 :: W17 :: W16 ::
          w12 :: w13 :: w14 :: w15 :: rest,
          mem, frames, adv⟩ := by
  simp only [sha256SB2Expand_W27_MovupwOps]
  unfold execWithEnv; simp only [List.foldlM]
  miden_dup; miden_dup; miden_swap; miden_dup; miden_dup
  simp only [show sha256ProcEnv "compute_message_schedule_word" =
      some Miden.Core.Sha256.compute_message_schedule_word from rfl]
  rw [compute_message_schedule_word_at_2125 W25 W20 w12 w11
      _ _ rfl hW25 hW20 hw12 hw11]
  simp only [MidenState.withStack, sha256SB2W27]
  rw [stepMovupw3]; miden_bind
  dsimp only [pure, Pure.pure]

-- ============================================================================
-- SB2 expand bridge
-- ============================================================================

set_option maxHeartbeats 800000 in
private lemma sha256_SB2_expand_bridge
    (W23 W22 W21 W20 W19 W18 W17 W16 w8 w9 w10 w11 w12 w13 w14 w15 : Felt)
    (hW22 : W22.isU32 = true) (hW23 : W23.isU32 = true)
    (hW19 : W19.isU32 = true) (hW18 : W18.isU32 = true)
    (hW17 : W17.isU32 = true) (hW20 : W20.isU32 = true)
    (hw8 : w8.isU32 = true) (hw9 : w9.isU32 = true)
    (hw10 : w10.isU32 = true) (hw11 : w11.isU32 = true) (hw12 : w12.isU32 = true)
    (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt) :
    let W24 := sha256SB2W24 W22 W17 w9 w8
    let W25 := sha256SB2W25 W23 W18 w10 w9
    let W26 := sha256SB2W26 W24 W19 w11 w10
    let W27 := sha256SB2W27 W25 W20 w12 w11
    execWithEnv sha256ProcEnv 2126
        ⟨W23::W22::W21::W20::W19::W18::W17::W16::w8::w9::w10::w11::w12::w13::w14::w15::rest,
          mem, frames, adv⟩
        sha256SB2ExpandOps =
    some ⟨w8 :: w9 :: w10 :: w11 :: W27 :: W26 :: W25 :: W24 ::
          W23 :: W22 :: W21 :: W20 :: W19 :: W18 :: W17 :: W16 ::
          w12 :: w13 :: w14 :: w15 :: rest,
          mem, frames, adv⟩ := by
  rw [sha256SB2ExpandOps_split]
  rw [List.append_assoc, List.append_assoc, execWithEnv_append]
  rw [sha256_SB2_expand_W24 W23 W22 W21 W20 W19 W18 W17 W16 w8 w9 w10 w11 w12 w13 w14 w15
      hW22 hW17 hw9 hw8 rest mem frames adv]
  simp only [bind, Bind.bind, Option.bind]
  rw [execWithEnv_append]
  rw [sha256_SB2_expand_W25 W23 W22 W21 W20 W19 W18 W17 W16 w8 w9 w10 w11 w12 w13 w14 w15
      (sha256SB2W24 W22 W17 w9 w8) hW23 hW18 hw10 hw9 rest mem frames adv]
  simp only [bind, Bind.bind, Option.bind]
  rw [execWithEnv_append]
  rw [sha256_SB2_expand_W26 W23 W22 W21 W20 W19 W18 W17 W16 w8 w9 w10 w11 w12 w13 w14 w15
      (sha256SB2W24 W22 W17 w9 w8) (sha256SB2W25 W23 W18 w10 w9)
      (u32_mod_isU32 _) hW19 hw11 hw10 rest mem frames adv]
  simp only [bind, Bind.bind, Option.bind]
  rw [sha256_SB2_expand_W27_movupw W23 W22 W21 W20 W19 W18 W17 W16 w8 w9 w10 w11 w12 w13 w14 w15
      (sha256SB2W24 W22 W17 w9 w8) (sha256SB2W25 W23 W18 w10 w9)
      (sha256SB2W26 (sha256SB2W24 W22 W17 w9 w8) W19 w11 w10)
      (u32_mod_isU32 _) hW20 hw12 hw11 rest mem frames adv]

-- ============================================================================
-- SB2 consume bridge
-- ============================================================================

set_option maxHeartbeats 4000000 in
private lemma sha256_SB2_consume_bridge
    (w8 w9 w10 w11 : Felt)
    (W24 W25 W26 W27 : Felt)
    (W23 W22 W21 W20 W19 W18 W17 W16 : Felt)
    (w12 w13 w14 w15 : Felt)
    (a b c d e f g h : Felt)
    (H0 H1 H2 H3 H4 H5 H6 H7 : Felt)
    (hw8 : w8.isU32 = true) (hw9 : w9.isU32 = true) (hw10 : w10.isU32 = true)
    (hw11 : w11.isU32 = true)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) (hd : d.isU32 = true)
    (he : e.isU32 = true) (hf : f.isU32 = true) (hg : g.isU32 = true) (hh : h.isU32 = true)
    (rest : List Felt) (mem : Nat → Felt) (adv : List Felt)
    (frame : LocalFrame) (frames_rest : List LocalFrame)
    (hframe_locals : frame.numLocals = 16)
    (hframe_aligned : frame.alignedNumLocals = 16)
    (h3  : mem (frame.localAddr 3)  = a) (h2  : mem (frame.localAddr 2)  = b)
    (h1  : mem (frame.localAddr 1)  = c) (h0  : mem (frame.localAddr 0)  = d)
    (h7  : mem (frame.localAddr 7)  = e) (h6  : mem (frame.localAddr 6)  = f)
    (h5  : mem (frame.localAddr 5)  = g) (h4  : mem (frame.localAddr 4)  = h)
    (h11 : mem (frame.localAddr 11) = H0) (h10 : mem (frame.localAddr 10) = H1)
    (h9  : mem (frame.localAddr 9)  = H2) (h8  : mem (frame.localAddr 8)  = H3)
    (h15 : mem (frame.localAddr 15) = H4) (h14 : mem (frame.localAddr 14) = H5)
    (h13 : mem (frame.localAddr 13) = H6) (h12 : mem (frame.localAddr 12) = H7) :
    let (na, nb, nc, nd, ne, nf, ng, nh) := sha256SB2Compress a b c d e f g h w8 w9 w10 w11
    execWithEnv sha256ProcEnv 2126
        ⟨w8 :: w9 :: w10 :: w11 :: W27 :: W26 :: W25 :: W24 ::
          W23 :: W22 :: W21 :: W20 :: W19 :: W18 :: W17 :: W16 ::
          w12 :: w13 :: w14 :: w15 :: rest,
          mem, frame :: frames_rest, adv⟩
        sha256SB2ConsumeOps =
    some ⟨W27 :: W26 :: W25 :: W24 :: W23 :: W22 :: W21 :: W20 ::
          W19 :: W18 :: W17 :: W16 :: w12 :: w13 :: w14 :: w15 :: rest,
          fun i =>
            if i = frame.localAddr 4 + 3 then ne else if i = frame.localAddr 4 + 2 then nf else
            if i = frame.localAddr 4 + 1 then ng else if i = frame.localAddr 4 then nh else
            if i = frame.localAddr 0 + 3 then na else if i = frame.localAddr 0 + 2 then nb else
            if i = frame.localAddr 0 + 1 then nc else if i = frame.localAddr 0 then nd else
            mem i,
          frame :: frames_rest, adv⟩ := by
  simp only [sha256SB2ConsumeOps]
  unfold execWithEnv; simp only [List.foldlM]
  rw [stepPush]; miden_bind
  rw [stepPadw]; miden_bind
  rw [stepLocLoadwBe (idx := 4) (frame := frame) (frames_rest := frames_rest)
      (halign := by decide) (hbound := by omega)]; miden_bind
  simp only [show frame.localAddr 4 + 3 = frame.localAddr 7 from by
      simp [LocalFrame.localAddr],
    show frame.localAddr 4 + 2 = frame.localAddr 6 from by
      simp [LocalFrame.localAddr],
    show frame.localAddr 4 + 1 = frame.localAddr 5 from by
      simp [LocalFrame.localAddr]]
  rw [h7, h6, h5, h4]
  rw [stepPadw]; miden_bind
  rw [stepLocLoadwBe (idx := 0) (frame := frame) (frames_rest := frames_rest)
      (halign := by decide) (hbound := by omega)]; miden_bind
  simp only [show frame.localAddr 0 + 3 = frame.localAddr 3 from by
      simp [LocalFrame.localAddr],
    show frame.localAddr 0 + 2 = frame.localAddr 2 from by
      simp [LocalFrame.localAddr],
    show frame.localAddr 0 + 1 = frame.localAddr 1 from by
      simp [LocalFrame.localAddr]]
  rw [h3, h2, h1, h0]
  simp only [show sha256ProcEnv "consume_message_word" =
      some Miden.Core.Sha256.consume_message_word from rfl]
  rw [consume_message_word_at_2125 a b c d e f g h (Felt.ofNat 3624381080) w8
      _ _ rfl ha hb hc hd he hf hg hh (felt_ofNat_isU32_of_lt _ (by norm_num)) hw8]
  simp only [MidenState.withStack]
  rw [stepPush]; miden_bind
  rw [stepMovdn (hn := rfl)]; miden_bind
  rw [consume_message_word_at_2125 _ _ _ _ _ _ _ _ (Felt.ofNat 310598401) w9
      _ _ rfl (u32_mod_isU32 _) ha hb hc (u32_mod_isU32 _) he hf hg
      (felt_ofNat_isU32_of_lt _ (by norm_num)) hw9]
  simp only [MidenState.withStack]
  rw [stepPush]; miden_bind
  rw [stepMovdn (hn := rfl)]; miden_bind
  rw [consume_message_word_at_2125 _ _ _ _ _ _ _ _ (Felt.ofNat 607225278) w10
      _ _ rfl (u32_mod_isU32 _) (u32_mod_isU32 _) ha hb (u32_mod_isU32 _) (u32_mod_isU32 _)
      he hf (felt_ofNat_isU32_of_lt _ (by norm_num)) hw10]
  simp only [MidenState.withStack]
  rw [stepPush]; miden_bind
  rw [stepMovdn (hn := rfl)]; miden_bind
  rw [consume_message_word_at_2125 _ _ _ _ _ _ _ _ (Felt.ofNat 1426881987) w11
      _ _ rfl (u32_mod_isU32 _) (u32_mod_isU32 _) (u32_mod_isU32 _) ha (u32_mod_isU32 _)
      (u32_mod_isU32 _) (u32_mod_isU32 _) he (felt_ofNat_isU32_of_lt _ (by norm_num)) hw11]
  simp only [MidenState.withStack]
  rw [stepLocStorewBe (idx := 0) (frame := frame) (frames_rest := frames_rest)
      (halign := by decide) (hbound := by omega)]; miden_bind
  rw [stepDropw]; miden_bind
  rw [stepLocStorewBe (idx := 4) (frame := frame) (frames_rest := frames_rest)
      (halign := by decide) (hbound := by omega)]; miden_bind
  rw [stepDropw]; miden_bind
  dsimp only [pure, Pure.pure]
  simp only [sha256SB2Compress, consumeResult]
  rfl


-- ============================================================================
-- SB2 bridge: chains expand and consume
-- ============================================================================

set_option maxHeartbeats 800000 in
lemma sha256_SB2_bridge
    (W23 W22 W21 W20 W19 W18 W17 W16 w8 w9 w10 w11 w12 w13 w14 w15 : Felt)
    (a b c d e f g h : Felt)
    (H0 H1 H2 H3 H4 H5 H6 H7 : Felt)
    (hW23 : W23.isU32 = true) (hW22 : W22.isU32 = true)
    (_hW21 : W21.isU32 = true) (hW20 : W20.isU32 = true)
    (hW19 : W19.isU32 = true) (hW18 : W18.isU32 = true)
    (hW17 : W17.isU32 = true) (_hW16 : W16.isU32 = true)
    (hw8 : w8.isU32 = true) (hw9 : w9.isU32 = true)
    (hw10 : w10.isU32 = true) (hw11 : w11.isU32 = true)
    (hw12 : w12.isU32 = true) (_hw13 : w13.isU32 = true)
    (_hw14 : w14.isU32 = true) (_hw15 : w15.isU32 = true)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) (hd : d.isU32 = true)
    (he : e.isU32 = true) (hf : f.isU32 = true) (hg : g.isU32 = true) (hh : h.isU32 = true)
    (_hH0 : H0.isU32 = true) (_hH1 : H1.isU32 = true) (_hH2 : H2.isU32 = true)
    (_hH3 : H3.isU32 = true) (_hH4 : H4.isU32 = true) (_hH5 : H5.isU32 = true)
    (_hH6 : H6.isU32 = true) (_hH7 : H7.isU32 = true)
    (rest : List Felt) (mem : Nat → Felt) (adv : List Felt)
    (frame : LocalFrame) (frames_rest : List LocalFrame)
    (hframe_locals : frame.numLocals = 16)
    (hframe_aligned : frame.alignedNumLocals = 16)
    (h3  : mem (frame.localAddr 3)  = a) (h2  : mem (frame.localAddr 2)  = b)
    (h1  : mem (frame.localAddr 1)  = c) (h0  : mem (frame.localAddr 0)  = d)
    (h7  : mem (frame.localAddr 7)  = e) (h6  : mem (frame.localAddr 6)  = f)
    (h5  : mem (frame.localAddr 5)  = g) (h4  : mem (frame.localAddr 4)  = h)
    (h11 : mem (frame.localAddr 11) = H0) (h10 : mem (frame.localAddr 10) = H1)
    (h9  : mem (frame.localAddr 9)  = H2) (h8  : mem (frame.localAddr 8)  = H3)
    (h15 : mem (frame.localAddr 15) = H4) (h14 : mem (frame.localAddr 14) = H5)
    (h13 : mem (frame.localAddr 13) = H6) (h12 : mem (frame.localAddr 12) = H7) :
    let W24 := sha256SB2W24 W22 W17 w9 w8
    let W25 := sha256SB2W25 W23 W18 w10 w9
    let W26 := sha256SB2W26 W24 W19 w11 w10
    let W27 := sha256SB2W27 W25 W20 w12 w11
    let (na, nb, nc, nd, ne, nf, ng, nh) := sha256SB2Compress a b c d e f g h w8 w9 w10 w11
    execWithEnv sha256ProcEnv 2126
        ⟨W23::W22::W21::W20::W19::W18::W17::W16::w8::w9::w10::w11::w12::w13::w14::w15::rest,
          mem, frame :: frames_rest, adv⟩
        sha256SB2Ops =
    some ⟨W27 :: W26 :: W25 :: W24 :: W23 :: W22 :: W21 :: W20 ::
          W19 :: W18 :: W17 :: W16 :: w12 :: w13 :: w14 :: w15 :: rest,
          fun i =>
            if i = frame.localAddr 4 + 3 then ne else if i = frame.localAddr 4 + 2 then nf else
            if i = frame.localAddr 4 + 1 then ng else if i = frame.localAddr 4 then nh else
            if i = frame.localAddr 0 + 3 then na else if i = frame.localAddr 0 + 2 then nb else
            if i = frame.localAddr 0 + 1 then nc else if i = frame.localAddr 0 then nd else
            mem i,
          frame :: frames_rest, adv⟩ := by
  rw [sha256SB2Ops_split, execWithEnv_append]
  rw [sha256_SB2_expand_bridge W23 W22 W21 W20 W19 W18 W17 W16 w8 w9 w10 w11 w12 w13 w14 w15
      hW22 hW23 hW19 hW18 hW17 hW20 hw8 hw9 hw10 hw11 hw12 rest mem (frame :: frames_rest) adv]
  simp only [bind, Bind.bind, Option.bind]
  rw [sha256_SB2_consume_bridge w8 w9 w10 w11
      (sha256SB2W24 W22 W17 w9 w8) (sha256SB2W25 W23 W18 w10 w9)
      (sha256SB2W26 (sha256SB2W24 W22 W17 w9 w8) W19 w11 w10)
      (sha256SB2W27 (sha256SB2W25 W23 W18 w10 w9) W20 w12 w11)
      W23 W22 W21 W20 W19 W18 W17 W16
      w12 w13 w14 w15
      a b c d e f g h H0 H1 H2 H3 H4 H5 H6 H7
      hw8 hw9 hw10 hw11 ha hb hc hd he hf hg hh
      rest mem adv frame frames_rest hframe_locals hframe_aligned
      h3 h2 h1 h0 h7 h6 h5 h4 h11 h10 h9 h8 h15 h14 h13 h12]
  dsimp only [sha256SB2Compress, consumeResult, sha256SB2W24, sha256SB2W25, sha256SB2W26, sha256SB2W27]

-- ============================================================================
-- SB3 spec helpers
-- ============================================================================

private def sha256SB3W28 (W26 W21 w13 w12 : Felt) : Felt :=
  let sig1 := u32RotateRight W26.val 17 ^^^ (u32RotateRight W26.val 19 ^^^ W26.val / 2^10)
  let sig0 := u32RotateRight w13.val 7 ^^^ (u32RotateRight w13.val 18 ^^^ w13.val / 2^3)
  Felt.ofNat ((w12.val + (W21.val + sig1 + sig0) % 2^32) % 2^32)

private def sha256SB3W29 (W27 W22 w14 w13 : Felt) : Felt :=
  let sig1 := u32RotateRight W27.val 17 ^^^ (u32RotateRight W27.val 19 ^^^ W27.val / 2^10)
  let sig0 := u32RotateRight w14.val 7 ^^^ (u32RotateRight w14.val 18 ^^^ w14.val / 2^3)
  Felt.ofNat ((w13.val + (W22.val + sig1 + sig0) % 2^32) % 2^32)

private def sha256SB3W30 (W28 W23 w15 w14 : Felt) : Felt :=
  let sig1 := u32RotateRight W28.val 17 ^^^ (u32RotateRight W28.val 19 ^^^ W28.val / 2^10)
  let sig0 := u32RotateRight w15.val 7 ^^^ (u32RotateRight w15.val 18 ^^^ w15.val / 2^3)
  Felt.ofNat ((w14.val + (W23.val + sig1 + sig0) % 2^32) % 2^32)

private def sha256SB3W31 (W29 W24 W16 w15 : Felt) : Felt :=
  let sig1 := u32RotateRight W29.val 17 ^^^ (u32RotateRight W29.val 19 ^^^ W29.val / 2^10)
  let sig0 := u32RotateRight W16.val 7 ^^^ (u32RotateRight W16.val 18 ^^^ W16.val / 2^3)
  Felt.ofNat ((w15.val + (W24.val + sig1 + sig0) % 2^32) % 2^32)

/-- Result of 4 compression rounds with K[12..15] consuming (w12, w13, w14, w15) -/
private def sha256SB3Compress (a b c d e f g h w12 w13 w14 w15 : Felt) :
    Felt × Felt × Felt × Felt × Felt × Felt × Felt × Felt :=
  let (a1,b1,c1,d1,e1,f1,g1,h1) := consumeResult a b c d e f g h (Felt.ofNat 1925078388) w12
  let (a2,b2,c2,d2,e2,f2,g2,h2) := consumeResult a1 b1 c1 d1 e1 f1 g1 h1 (Felt.ofNat 2162078206) w13
  let (a3,b3,c3,d3,e3,f3,g3,h3) := consumeResult a2 b2 c2 d2 e2 f2 g2 h2 (Felt.ofNat 2614888103) w14
  consumeResult a3 b3 c3 d3 e3 f3 g3 h3 (Felt.ofNat 3248222580) w15

-- ============================================================================
-- SB3 sub-ops split
-- SB3 starts with movupw 3; movupw 3 to rearrange the stack, then 4 expand
-- computations, then movupw 2, then consume+store.
-- ============================================================================

/-- SB3 pre-expand phase: two movupw 3 ops to rearrange stack -/
private def sha256SB3PreOps : List Op := [
    .inst (.movupw 3), .inst (.movupw 3)]

/-- SB3 expand phase: 4 compute_message_schedule_word calls + movupw 2 -/
private def sha256SB3ExpandOps : List Op := [
    .inst (.dup 14), .inst (.dup 10),
    .inst (.dup 7), .inst (.dup 7),
    .inst (.movdn 3), .inst (.movdn 2),
    .inst (.exec "compute_message_schedule_word"),
    .inst (.dup 14), .inst (.dup 10),
    .inst (.dup 9), .inst (.dup 9),
    .inst (.movdn 3), .inst (.movdn 2),
    .inst (.exec "compute_message_schedule_word"),
    .inst (.dup 14), .inst (.dup 2),
    .inst (.dup 11), .inst (.dup 11),
    .inst (.movdn 3), .inst (.movdn 2),
    .inst (.exec "compute_message_schedule_word"),
    .inst (.dup 14), .inst (.dup 2),
    .inst (.dup 8), .inst (.dup 13),
    .inst (.movdn 3), .inst (.movdn 2),
    .inst (.exec "compute_message_schedule_word"),
    .inst (.movupw 2)]

/-- SB3 consume+store phase -/
private def sha256SB3ConsumeOps : List Op := [
    .inst (.push 1925078388), .inst .padw, .inst (.locLoadwBe 4),
    .inst .padw, .inst (.locLoadwBe 0),
    .inst (.exec "consume_message_word"),
    .inst (.push 2162078206), .inst (.movdn 8),
    .inst (.exec "consume_message_word"),
    .inst (.push 2614888103), .inst (.movdn 8),
    .inst (.exec "consume_message_word"),
    .inst (.push 3248222580), .inst (.movdn 8),
    .inst (.exec "consume_message_word"),
    .inst (.locStorewBe 0), .inst .dropw,
    .inst (.locStorewBe 4), .inst .dropw]

private lemma sha256SB3Ops_split :
    sha256SB3Ops = sha256SB3PreOps ++ sha256SB3ExpandOps ++ sha256SB3ConsumeOps := by
  simp only [sha256SB3PreOps, sha256SB3ExpandOps, sha256SB3ConsumeOps, sha256SB3Ops, sha256BodyOps]
  set_option maxRecDepth 4096 in rfl

-- ============================================================================
-- SB3 expand sub-ops (per-word)
-- ============================================================================

private def sha256SB3Expand_W28Ops : List Op := [
    .inst (.dup 14), .inst (.dup 10),
    .inst (.dup 7), .inst (.dup 7),
    .inst (.movdn 3), .inst (.movdn 2),
    .inst (.exec "compute_message_schedule_word")]

private def sha256SB3Expand_W29Ops : List Op := [
    .inst (.dup 14), .inst (.dup 10),
    .inst (.dup 9), .inst (.dup 9),
    .inst (.movdn 3), .inst (.movdn 2),
    .inst (.exec "compute_message_schedule_word")]

private def sha256SB3Expand_W30Ops : List Op := [
    .inst (.dup 14), .inst (.dup 2),
    .inst (.dup 11), .inst (.dup 11),
    .inst (.movdn 3), .inst (.movdn 2),
    .inst (.exec "compute_message_schedule_word")]

private def sha256SB3Expand_W31_MovupwOps : List Op := [
    .inst (.dup 14), .inst (.dup 2),
    .inst (.dup 8), .inst (.dup 13),
    .inst (.movdn 3), .inst (.movdn 2),
    .inst (.exec "compute_message_schedule_word"),
    .inst (.movupw 2)]

private lemma sha256SB3ExpandOps_split :
    sha256SB3ExpandOps = sha256SB3Expand_W28Ops ++ sha256SB3Expand_W29Ops ++
                          sha256SB3Expand_W30Ops ++ sha256SB3Expand_W31_MovupwOps := by
  simp only [sha256SB3Expand_W28Ops, sha256SB3Expand_W29Ops,
             sha256SB3Expand_W30Ops, sha256SB3Expand_W31_MovupwOps, sha256SB3ExpandOps]
  rfl

-- SB3 input: [W27, W26, W25, W24, W23, W22, W21, W20, W19, W18, W17, W16, w12, w13, w14, w15, rest]
-- After movupw 3, movupw 3:
-- [W19, W18, W17, W16, w12, w13, w14, w15, W27, W26, W25, W24, W23, W22, W21, W20, rest]

set_option maxHeartbeats 800000 in
private lemma sha256_SB3_pre_bridge
    (W27 W26 W25 W24 W23 W22 W21 W20 W19 W18 W17 W16 w12 w13 w14 w15 : Felt)
    (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt) :
    execWithEnv sha256ProcEnv 2126
        ⟨W27::W26::W25::W24::W23::W22::W21::W20::W19::W18::W17::W16::w12::w13::w14::w15::rest,
          mem, frames, adv⟩
        sha256SB3PreOps =
    some ⟨W19::W18::W17::W16::w12::w13::w14::w15::W27::W26::W25::W24::W23::W22::W21::W20::rest,
          mem, frames, adv⟩ := by
  simp only [sha256SB3PreOps]
  unfold execWithEnv; simp only [List.foldlM]
  rw [stepMovupw3]; miden_bind
  rw [stepMovupw3]; miden_bind
  dsimp only [pure, Pure.pure]

-- After pre: [W19, W18, W17, W16, w12, w13, w14, w15, W27, W26, W25, W24, W23, W22, W21, W20, rest]
-- positions: 0:W19, 1:W18, 2:W17, 3:W16, 4:w12, 5:w13, 6:w14, 7:w15, 8:W27, 9:W26, 10:W25, 11:W24, 12:W23, 13:W22, 14:W21, 15:W20
-- dup 14 → W21 ; dup 10 → W26 (after push of W21)
-- After dup 14: [W21, W19, W18, W17, W16, w12, w13, w14, w15, W27, W26, W25, W24, W23, W22, W21, W20, ...]
-- positions after: 0:W21, 1:W19, ..., 10:W26, ...
-- After dup 10: [W26, W21, W19, ...]
-- positions after: 0:W26, 1:W21, 2:W19, ..., 7:w13, ...
-- dup 7 → w13: [w13, W26, W21, W19, ...]
-- dup 7 → w12: [w12, w13, W26, W21, ...]
-- movdn 3, movdn 2: [W26, W21, w13, w12, ...]
-- compute W28 = σ₁(W26) + W21 + σ₀(w13) + w12

set_option maxHeartbeats 2000000 in
private lemma sha256_SB3_expand_W28
    (W19 W18 W17 W16 w12 w13 w14 w15 W27 W26 W25 W24 W23 W22 W21 W20 : Felt)
    (hW26 : W26.isU32 = true) (hW21 : W21.isU32 = true)
    (hw13 : w13.isU32 = true) (hw12 : w12.isU32 = true)
    (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt) :
    execWithEnv sha256ProcEnv 2126
        ⟨W19::W18::W17::W16::w12::w13::w14::w15::W27::W26::W25::W24::W23::W22::W21::W20::rest,
          mem, frames, adv⟩
        sha256SB3Expand_W28Ops =
    some ⟨sha256SB3W28 W26 W21 w13 w12 :: W19 :: W18 :: W17 :: W16 ::
          w12 :: w13 :: w14 :: w15 :: W27 :: W26 :: W25 :: W24 :: W23 :: W22 :: W21 :: W20 :: rest,
          mem, frames, adv⟩ := by
  simp only [sha256SB3Expand_W28Ops]
  unfold execWithEnv; simp only [List.foldlM]
  miden_dup; miden_dup
  miden_dup; miden_dup; miden_movdn; miden_movdn
  simp only [show sha256ProcEnv "compute_message_schedule_word" =
      some Miden.Core.Sha256.compute_message_schedule_word from rfl]
  rw [compute_message_schedule_word_at_2125 W26 W21 w13 w12
      (W19 :: W18 :: W17 :: W16 :: w12 :: w13 :: w14 :: w15 ::
       W27 :: W26 :: W25 :: W24 :: W23 :: W22 :: W21 :: W20 :: rest)
      _ rfl hW26 hW21 hw13 hw12]
  simp only [MidenState.withStack, sha256SB3W28, pure, Pure.pure]

-- After W28: [W28, W19, W18, W17, W16, w12, w13, w14, w15, W27, W26, W25, W24, W23, W22, W21, W20, rest]
-- positions: 0:W28, 1:W19, 2:W18, 3:W17, 4:W16, 5:w12, 6:w13, 7:w14, 8:w15, 9:W27, 10:W26, 11:W25, 12:W24, 13:W23, 14:W22, 15:W21, 16:W20
-- dup 14 → W22: [W22, W28, W19, W18, W17, W16, w12, w13, w14, w15, W27, W26, W25, W24, W23, W22, W21, W20, ...]
-- After: 0:W22, 1:W28, 2:W19, ..., 10:W27
-- dup 10 → W27: [W27, W22, W28, ...]
-- After: 0:W27, 1:W22, 2:W28, ..., 9:w14
-- dup 9 → w14: [w14, W27, W22, W28, ...]
-- After: 0:w14, ..., 9:w13
-- dup 9 → w13: [w13, w14, W27, W22, ...]
-- movdn 3, movdn 2: [W27, W22, w14, w13, ...]
-- compute W29 = σ₁(W27) + W22 + σ₀(w14) + w13

set_option maxHeartbeats 2000000 in
private lemma sha256_SB3_expand_W29
    (W19 W18 W17 W16 w12 w13 w14 w15 W27 W26 W25 W24 W23 W22 W21 W20 W28 : Felt)
    (hW27 : W27.isU32 = true) (hW22 : W22.isU32 = true)
    (hw14 : w14.isU32 = true) (hw13 : w13.isU32 = true)
    (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt) :
    execWithEnv sha256ProcEnv 2126
        ⟨W28 :: W19 :: W18 :: W17 :: W16 ::
          w12 :: w13 :: w14 :: w15 :: W27 :: W26 :: W25 :: W24 :: W23 :: W22 :: W21 :: W20 :: rest,
          mem, frames, adv⟩
        sha256SB3Expand_W29Ops =
    some ⟨sha256SB3W29 W27 W22 w14 w13 :: W28 :: W19 :: W18 :: W17 :: W16 ::
          w12 :: w13 :: w14 :: w15 :: W27 :: W26 :: W25 :: W24 :: W23 :: W22 :: W21 :: W20 :: rest,
          mem, frames, adv⟩ := by
  simp only [sha256SB3Expand_W29Ops]
  unfold execWithEnv; simp only [List.foldlM]
  miden_dup; miden_dup
  miden_dup; miden_dup; miden_movdn; miden_movdn
  simp only [show sha256ProcEnv "compute_message_schedule_word" =
      some Miden.Core.Sha256.compute_message_schedule_word from rfl]
  rw [compute_message_schedule_word_at_2125 W27 W22 w14 w13
      _ _ rfl hW27 hW22 hw14 hw13]
  simp only [MidenState.withStack, sha256SB3W29, pure, Pure.pure]

-- After W29: [W29, W28, W19, W18, W17, W16, w12, w13, w14, w15, W27, W26, W25, W24, W23, W22, W21, W20, rest]
-- positions: 0:W29, 1:W28, 2:W19, 3:W18, 4:W17, 5:W16, 6:w12, 7:w13, 8:w14, 9:w15, 10:W27, 11:W26, 12:W25, 13:W24, 14:W23, 15:W22, 16:W21, 17:W20
-- dup 14 → W23: [W23, W29, W28, ...]
-- After: 0:W23, 1:W29, 2:W28, ..., 2 is W28
-- dup 2 → W28: [W28, W23, W29, W28, ...]
-- After: 0:W28, 1:W23, 2:W29, ..., 11:w15
-- dup 11 → w15: [w15, W28, W23, W29, ...]
-- After: 0:w15, ..., 11:w14
-- dup 11 → w14: [w14, w15, W28, W23, ...]
-- movdn 3, movdn 2: [W28, W23, w15, w14, ...]
-- compute W30 = σ₁(W28) + W23 + σ₀(w15) + w14

set_option maxHeartbeats 2000000 in
private lemma sha256_SB3_expand_W30
    (W19 W18 W17 W16 w12 w13 w14 w15 W27 W26 W25 W24 W23 W22 W21 W20 W28 W29 : Felt)
    (hW28 : W28.isU32 = true) (hW23 : W23.isU32 = true)
    (hw15 : w15.isU32 = true) (hw14 : w14.isU32 = true)
    (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt) :
    execWithEnv sha256ProcEnv 2126
        ⟨W29 :: W28 :: W19 :: W18 :: W17 :: W16 ::
          w12 :: w13 :: w14 :: w15 :: W27 :: W26 :: W25 :: W24 :: W23 :: W22 :: W21 :: W20 :: rest,
          mem, frames, adv⟩
        sha256SB3Expand_W30Ops =
    some ⟨sha256SB3W30 W28 W23 w15 w14 :: W29 :: W28 :: W19 :: W18 :: W17 :: W16 ::
          w12 :: w13 :: w14 :: w15 :: W27 :: W26 :: W25 :: W24 :: W23 :: W22 :: W21 :: W20 :: rest,
          mem, frames, adv⟩ := by
  simp only [sha256SB3Expand_W30Ops]
  unfold execWithEnv; simp only [List.foldlM]
  miden_dup; miden_dup
  miden_dup; miden_dup; miden_movdn; miden_movdn
  simp only [show sha256ProcEnv "compute_message_schedule_word" =
      some Miden.Core.Sha256.compute_message_schedule_word from rfl]
  rw [compute_message_schedule_word_at_2125 W28 W23 w15 w14
      _ _ rfl hW28 hW23 hw15 hw14]
  simp only [MidenState.withStack, sha256SB3W30, pure, Pure.pure]

-- After W30: [W30, W29, W28, W19, W18, W17, W16, w12, w13, w14, w15, W27, W26, W25, W24, W23, W22, W21, W20, rest]
-- positions: 0:W30, 1:W29, 2:W28, 3:W19, 4:W18, 5:W17, 6:W16, 7:w12, 8:w13, 9:w14, 10:w15, 11:W27, 12:W26, 13:W25, 14:W24, 15:W23, 16:W22, 17:W21, 18:W20
-- dup 14 → W24: [W24, W30, W29, W28, ...]
-- After: 0:W24, 1:W30, 2:W29, ...
-- dup 2 → W29: [W29, W24, W30, W29, W28, ...]
-- After: 0:W29, 1:W24, 2:W30, ..., 8:W16
-- dup 8 → W16: [W16, W29, W24, W30, ...]
-- After: 0:W16, ..., 13:w15
-- dup 13 → w15: [w15, W16, W29, W24, ...]
-- movdn 3, movdn 2: [W29, W24, W16, w15, ...]
-- compute W31 = σ₁(W29) + W24 + σ₀(W16) + w15
-- Then movupw 2

set_option maxHeartbeats 2000000 in
private lemma sha256_SB3_expand_W31_movupw
    (W19 W18 W17 W16 w12 w13 w14 w15 W27 W26 W25 W24 W23 W22 W21 W20 W28 W29 W30 : Felt)
    (hW29 : W29.isU32 = true) (hW24 : W24.isU32 = true)
    (hW16 : W16.isU32 = true) (hw15 : w15.isU32 = true)
    (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt) :
    execWithEnv sha256ProcEnv 2126
        ⟨W30 :: W29 :: W28 :: W19 :: W18 :: W17 :: W16 ::
          w12 :: w13 :: w14 :: w15 :: W27 :: W26 :: W25 :: W24 :: W23 :: W22 :: W21 :: W20 :: rest,
          mem, frames, adv⟩
        sha256SB3Expand_W31_MovupwOps =
    some ⟨w12 :: w13 :: w14 :: w15 ::
          sha256SB3W31 W29 W24 W16 w15 :: W30 :: W29 :: W28 ::
          W19 :: W18 :: W17 :: W16 ::
          W27 :: W26 :: W25 :: W24 :: W23 :: W22 :: W21 :: W20 :: rest,
          mem, frames, adv⟩ := by
  simp only [sha256SB3Expand_W31_MovupwOps]
  unfold execWithEnv; simp only [List.foldlM]
  miden_dup; miden_dup; miden_dup; miden_dup
  miden_movdn; miden_movdn
  simp only [show sha256ProcEnv "compute_message_schedule_word" =
      some Miden.Core.Sha256.compute_message_schedule_word from rfl]
  rw [compute_message_schedule_word_at_2125 W29 W24 W16 w15
      _ _ rfl hW29 hW24 hW16 hw15]
  simp only [MidenState.withStack, sha256SB3W31]
  rw [stepMovupw2]; miden_bind
  dsimp only [pure, Pure.pure]

-- ============================================================================
-- SB3 expand bridge
-- ============================================================================

set_option maxHeartbeats 800000 in
private lemma sha256_SB3_expand_bridge
    (W19 W18 W17 W16 w12 w13 w14 w15 W27 W26 W25 W24 W23 W22 W21 W20 : Felt)
    (hW26 : W26.isU32 = true) (hW27 : W27.isU32 = true)
    (hW23 : W23.isU32 = true) (hW22 : W22.isU32 = true)
    (hW21 : W21.isU32 = true) (hW24 : W24.isU32 = true)
    (hW16 : W16.isU32 = true)
    (hw12 : w12.isU32 = true) (hw13 : w13.isU32 = true)
    (hw14 : w14.isU32 = true) (hw15 : w15.isU32 = true)
    (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt) :
    let W28 := sha256SB3W28 W26 W21 w13 w12
    let W29 := sha256SB3W29 W27 W22 w14 w13
    let W30 := sha256SB3W30 W28 W23 w15 w14
    let W31 := sha256SB3W31 W29 W24 W16 w15
    execWithEnv sha256ProcEnv 2126
        ⟨W19::W18::W17::W16::w12::w13::w14::w15::W27::W26::W25::W24::W23::W22::W21::W20::rest,
          mem, frames, adv⟩
        sha256SB3ExpandOps =
    some ⟨w12 :: w13 :: w14 :: w15 :: W31 :: W30 :: W29 :: W28 ::
          W19 :: W18 :: W17 :: W16 ::
          W27 :: W26 :: W25 :: W24 :: W23 :: W22 :: W21 :: W20 :: rest,
          mem, frames, adv⟩ := by
  rw [sha256SB3ExpandOps_split]
  rw [List.append_assoc, List.append_assoc, execWithEnv_append]
  rw [sha256_SB3_expand_W28 W19 W18 W17 W16 w12 w13 w14 w15 W27 W26 W25 W24 W23 W22 W21 W20
      hW26 hW21 hw13 hw12 rest mem frames adv]
  simp only [bind, Bind.bind, Option.bind]
  rw [execWithEnv_append]
  rw [sha256_SB3_expand_W29 W19 W18 W17 W16 w12 w13 w14 w15 W27 W26 W25 W24 W23 W22 W21 W20
      (sha256SB3W28 W26 W21 w13 w12) hW27 hW22 hw14 hw13 rest mem frames adv]
  simp only [bind, Bind.bind, Option.bind]
  rw [execWithEnv_append]
  rw [sha256_SB3_expand_W30 W19 W18 W17 W16 w12 w13 w14 w15 W27 W26 W25 W24 W23 W22 W21 W20
      (sha256SB3W28 W26 W21 w13 w12) (sha256SB3W29 W27 W22 w14 w13)
      (u32_mod_isU32 _) hW23 hw15 hw14 rest mem frames adv]
  simp only [bind, Bind.bind, Option.bind]
  rw [sha256_SB3_expand_W31_movupw W19 W18 W17 W16 w12 w13 w14 w15 W27 W26 W25 W24 W23 W22 W21 W20
      (sha256SB3W28 W26 W21 w13 w12) (sha256SB3W29 W27 W22 w14 w13)
      (sha256SB3W30 (sha256SB3W28 W26 W21 w13 w12) W23 w15 w14)
      (u32_mod_isU32 _) hW24 hW16 hw15 rest mem frames adv]

-- ============================================================================
-- SB3 consume bridge
-- ============================================================================

set_option maxHeartbeats 4000000 in
private lemma sha256_SB3_consume_bridge
    (w12 w13 w14 w15 : Felt)
    (W28 W29 W30 W31 : Felt)
    (W19 W18 W17 W16 : Felt)
    (W27 W26 W25 W24 W23 W22 W21 W20 : Felt)
    (a b c d e f g h : Felt)
    (H0 H1 H2 H3 H4 H5 H6 H7 : Felt)
    (hw12 : w12.isU32 = true) (hw13 : w13.isU32 = true) (hw14 : w14.isU32 = true)
    (hw15 : w15.isU32 = true)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) (hd : d.isU32 = true)
    (he : e.isU32 = true) (hf : f.isU32 = true) (hg : g.isU32 = true) (hh : h.isU32 = true)
    (rest : List Felt) (mem : Nat → Felt) (adv : List Felt)
    (frame : LocalFrame) (frames_rest : List LocalFrame)
    (hframe_locals : frame.numLocals = 16)
    (hframe_aligned : frame.alignedNumLocals = 16)
    (h3  : mem (frame.localAddr 3)  = a) (h2  : mem (frame.localAddr 2)  = b)
    (h1  : mem (frame.localAddr 1)  = c) (h0  : mem (frame.localAddr 0)  = d)
    (h7  : mem (frame.localAddr 7)  = e) (h6  : mem (frame.localAddr 6)  = f)
    (h5  : mem (frame.localAddr 5)  = g) (h4  : mem (frame.localAddr 4)  = h)
    (h11 : mem (frame.localAddr 11) = H0) (h10 : mem (frame.localAddr 10) = H1)
    (h9  : mem (frame.localAddr 9)  = H2) (h8  : mem (frame.localAddr 8)  = H3)
    (h15 : mem (frame.localAddr 15) = H4) (h14 : mem (frame.localAddr 14) = H5)
    (h13 : mem (frame.localAddr 13) = H6) (h12 : mem (frame.localAddr 12) = H7) :
    let (na, nb, nc, nd, ne, nf, ng, nh) := sha256SB3Compress a b c d e f g h w12 w13 w14 w15
    execWithEnv sha256ProcEnv 2126
        ⟨w12 :: w13 :: w14 :: w15 :: W31 :: W30 :: W29 :: W28 ::
          W19 :: W18 :: W17 :: W16 ::
          W27 :: W26 :: W25 :: W24 :: W23 :: W22 :: W21 :: W20 :: rest,
          mem, frame :: frames_rest, adv⟩
        sha256SB3ConsumeOps =
    some ⟨W31 :: W30 :: W29 :: W28 :: W19 :: W18 :: W17 :: W16 ::
          W27 :: W26 :: W25 :: W24 :: W23 :: W22 :: W21 :: W20 :: rest,
          fun i =>
            if i = frame.localAddr 4 + 3 then ne else if i = frame.localAddr 4 + 2 then nf else
            if i = frame.localAddr 4 + 1 then ng else if i = frame.localAddr 4 then nh else
            if i = frame.localAddr 0 + 3 then na else if i = frame.localAddr 0 + 2 then nb else
            if i = frame.localAddr 0 + 1 then nc else if i = frame.localAddr 0 then nd else
            mem i,
          frame :: frames_rest, adv⟩ := by
  simp only [sha256SB3ConsumeOps]
  unfold execWithEnv; simp only [List.foldlM]
  rw [stepPush]; miden_bind
  rw [stepPadw]; miden_bind
  rw [stepLocLoadwBe (idx := 4) (frame := frame) (frames_rest := frames_rest)
      (halign := by decide) (hbound := by omega)]; miden_bind
  simp only [show frame.localAddr 4 + 3 = frame.localAddr 7 from by
      simp [LocalFrame.localAddr],
    show frame.localAddr 4 + 2 = frame.localAddr 6 from by
      simp [LocalFrame.localAddr],
    show frame.localAddr 4 + 1 = frame.localAddr 5 from by
      simp [LocalFrame.localAddr]]
  rw [h7, h6, h5, h4]
  rw [stepPadw]; miden_bind
  rw [stepLocLoadwBe (idx := 0) (frame := frame) (frames_rest := frames_rest)
      (halign := by decide) (hbound := by omega)]; miden_bind
  simp only [show frame.localAddr 0 + 3 = frame.localAddr 3 from by
      simp [LocalFrame.localAddr],
    show frame.localAddr 0 + 2 = frame.localAddr 2 from by
      simp [LocalFrame.localAddr],
    show frame.localAddr 0 + 1 = frame.localAddr 1 from by
      simp [LocalFrame.localAddr]]
  rw [h3, h2, h1, h0]
  simp only [show sha256ProcEnv "consume_message_word" =
      some Miden.Core.Sha256.consume_message_word from rfl]
  rw [consume_message_word_at_2125 a b c d e f g h (Felt.ofNat 1925078388) w12
      _ _ rfl ha hb hc hd he hf hg hh (felt_ofNat_isU32_of_lt _ (by norm_num)) hw12]
  simp only [MidenState.withStack]
  rw [stepPush]; miden_bind
  rw [stepMovdn (hn := rfl)]; miden_bind
  rw [consume_message_word_at_2125 _ _ _ _ _ _ _ _ (Felt.ofNat 2162078206) w13
      _ _ rfl (u32_mod_isU32 _) ha hb hc (u32_mod_isU32 _) he hf hg
      (felt_ofNat_isU32_of_lt _ (by norm_num)) hw13]
  simp only [MidenState.withStack]
  rw [stepPush]; miden_bind
  rw [stepMovdn (hn := rfl)]; miden_bind
  rw [consume_message_word_at_2125 _ _ _ _ _ _ _ _ (Felt.ofNat 2614888103) w14
      _ _ rfl (u32_mod_isU32 _) (u32_mod_isU32 _) ha hb (u32_mod_isU32 _) (u32_mod_isU32 _)
      he hf (felt_ofNat_isU32_of_lt _ (by norm_num)) hw14]
  simp only [MidenState.withStack]
  rw [stepPush]; miden_bind
  rw [stepMovdn (hn := rfl)]; miden_bind
  rw [consume_message_word_at_2125 _ _ _ _ _ _ _ _ (Felt.ofNat 3248222580) w15
      _ _ rfl (u32_mod_isU32 _) (u32_mod_isU32 _) (u32_mod_isU32 _) ha (u32_mod_isU32 _)
      (u32_mod_isU32 _) (u32_mod_isU32 _) he (felt_ofNat_isU32_of_lt _ (by norm_num)) hw15]
  simp only [MidenState.withStack]
  rw [stepLocStorewBe (idx := 0) (frame := frame) (frames_rest := frames_rest)
      (halign := by decide) (hbound := by omega)]; miden_bind
  rw [stepDropw]; miden_bind
  rw [stepLocStorewBe (idx := 4) (frame := frame) (frames_rest := frames_rest)
      (halign := by decide) (hbound := by omega)]; miden_bind
  rw [stepDropw]; miden_bind
  dsimp only [pure, Pure.pure]
  simp only [sha256SB3Compress, consumeResult]
  rfl


-- ============================================================================
-- SB3 bridge: chains pre + expand + consume
-- ============================================================================

set_option maxHeartbeats 800000 in
lemma sha256_SB3_bridge
    (W27 W26 W25 W24 W23 W22 W21 W20 W19 W18 W17 W16 w12 w13 w14 w15 : Felt)
    (a b c d e f g h : Felt)
    (H0 H1 H2 H3 H4 H5 H6 H7 : Felt)
    (hW27 : W27.isU32 = true) (hW26 : W26.isU32 = true)
    (_hW25 : W25.isU32 = true) (hW24 : W24.isU32 = true)
    (hW23 : W23.isU32 = true) (hW22 : W22.isU32 = true)
    (hW21 : W21.isU32 = true) (_hW20 : W20.isU32 = true)
    (_hW19 : W19.isU32 = true) (_hW18 : W18.isU32 = true)
    (_hW17 : W17.isU32 = true) (hW16 : W16.isU32 = true)
    (hw12 : w12.isU32 = true) (hw13 : w13.isU32 = true)
    (hw14 : w14.isU32 = true) (hw15 : w15.isU32 = true)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) (hd : d.isU32 = true)
    (he : e.isU32 = true) (hf : f.isU32 = true) (hg : g.isU32 = true) (hh : h.isU32 = true)
    (_hH0 : H0.isU32 = true) (_hH1 : H1.isU32 = true) (_hH2 : H2.isU32 = true)
    (_hH3 : H3.isU32 = true) (_hH4 : H4.isU32 = true) (_hH5 : H5.isU32 = true)
    (_hH6 : H6.isU32 = true) (_hH7 : H7.isU32 = true)
    (rest : List Felt) (mem : Nat → Felt) (adv : List Felt)
    (frame : LocalFrame) (frames_rest : List LocalFrame)
    (hframe_locals : frame.numLocals = 16)
    (hframe_aligned : frame.alignedNumLocals = 16)
    (h3  : mem (frame.localAddr 3)  = a) (h2  : mem (frame.localAddr 2)  = b)
    (h1  : mem (frame.localAddr 1)  = c) (h0  : mem (frame.localAddr 0)  = d)
    (h7  : mem (frame.localAddr 7)  = e) (h6  : mem (frame.localAddr 6)  = f)
    (h5  : mem (frame.localAddr 5)  = g) (h4  : mem (frame.localAddr 4)  = h)
    (h11 : mem (frame.localAddr 11) = H0) (h10 : mem (frame.localAddr 10) = H1)
    (h9  : mem (frame.localAddr 9)  = H2) (h8  : mem (frame.localAddr 8)  = H3)
    (h15 : mem (frame.localAddr 15) = H4) (h14 : mem (frame.localAddr 14) = H5)
    (h13 : mem (frame.localAddr 13) = H6) (h12 : mem (frame.localAddr 12) = H7) :
    let W28 := sha256SB3W28 W26 W21 w13 w12
    let W29 := sha256SB3W29 W27 W22 w14 w13
    let W30 := sha256SB3W30 W28 W23 w15 w14
    let W31 := sha256SB3W31 W29 W24 W16 w15
    let (na, nb, nc, nd, ne, nf, ng, nh) := sha256SB3Compress a b c d e f g h w12 w13 w14 w15
    execWithEnv sha256ProcEnv 2126
        ⟨W27::W26::W25::W24::W23::W22::W21::W20::W19::W18::W17::W16::w12::w13::w14::w15::rest,
          mem, frame :: frames_rest, adv⟩
        sha256SB3Ops =
    some ⟨W31 :: W30 :: W29 :: W28 :: W19 :: W18 :: W17 :: W16 ::
          W27 :: W26 :: W25 :: W24 :: W23 :: W22 :: W21 :: W20 :: rest,
          fun i =>
            if i = frame.localAddr 4 + 3 then ne else if i = frame.localAddr 4 + 2 then nf else
            if i = frame.localAddr 4 + 1 then ng else if i = frame.localAddr 4 then nh else
            if i = frame.localAddr 0 + 3 then na else if i = frame.localAddr 0 + 2 then nb else
            if i = frame.localAddr 0 + 1 then nc else if i = frame.localAddr 0 then nd else
            mem i,
          frame :: frames_rest, adv⟩ := by
  rw [sha256SB3Ops_split, List.append_assoc, execWithEnv_append]
  rw [sha256_SB3_pre_bridge W27 W26 W25 W24 W23 W22 W21 W20 W19 W18 W17 W16 w12 w13 w14 w15
      rest mem (frame :: frames_rest) adv]
  simp only [bind, Bind.bind, Option.bind]
  rw [execWithEnv_append]
  rw [sha256_SB3_expand_bridge W19 W18 W17 W16 w12 w13 w14 w15 W27 W26 W25 W24 W23 W22 W21 W20
      hW26 hW27 hW23 hW22 hW21 hW24 hW16 hw12 hw13 hw14 hw15 rest mem (frame :: frames_rest) adv]
  simp only [bind, Bind.bind, Option.bind]
  rw [sha256_SB3_consume_bridge w12 w13 w14 w15
      (sha256SB3W28 W26 W21 w13 w12) (sha256SB3W29 W27 W22 w14 w13)
      (sha256SB3W30 (sha256SB3W28 W26 W21 w13 w12) W23 w15 w14)
      (sha256SB3W31 (sha256SB3W29 W27 W22 w14 w13) W24 W16 w15)
      W19 W18 W17 W16
      W27 W26 W25 W24 W23 W22 W21 W20
      a b c d e f g h H0 H1 H2 H3 H4 H5 H6 H7
      hw12 hw13 hw14 hw15 ha hb hc hd he hf hg hh
      rest mem adv frame frames_rest hframe_locals hframe_aligned
      h3 h2 h1 h0 h7 h6 h5 h4 h11 h10 h9 h8 h15 h14 h13 h12]
  dsimp only [sha256SB3Compress, consumeResult, sha256SB3W28, sha256SB3W29, sha256SB3W30, sha256SB3W31]


-- Ops split lemmas for SBs 4–11
-- Each SBi = expand ops ++ consume ops with the appropriate K constants

private lemma sha256SB4Ops_split :
    sha256SB4Ops = sha256RegularExpandOps ++ sha256RegularConsumeOps 3835390401 4022224774 264347078 604807628 := by
  simp only [sha256RegularExpandOps, sha256RegularConsumeOps, sha256SB4Ops, sha256BodyOps]
  set_option maxRecDepth 4096 in rfl

private lemma sha256SB5Ops_split :
    sha256SB5Ops = sha256RegularExpandOps ++ sha256RegularConsumeOps 770255983 1249150122 1555081692 1996064986 := by
  simp only [sha256RegularExpandOps, sha256RegularConsumeOps, sha256SB5Ops, sha256BodyOps]
  set_option maxRecDepth 4096 in rfl

private lemma sha256SB6Ops_split :
    sha256SB6Ops = sha256SB6ExpandOps ++ sha256RegularConsumeOps 2554220882 2821834349 2952996808 3210313671 := by
  simp only [sha256SB6ExpandOps, sha256RegularConsumeOps, sha256SB6Ops, sha256BodyOps]
  set_option maxRecDepth 4096 in rfl

private lemma sha256SB7Ops_split :
    sha256SB7Ops = sha256RegularExpandOps ++ sha256RegularConsumeOps 3336571891 3584528711 113926993 338241895 := by
  simp only [sha256RegularExpandOps, sha256RegularConsumeOps, sha256SB7Ops, sha256BodyOps]
  set_option maxRecDepth 4096 in rfl

private lemma sha256SB8Ops_split :
    sha256SB8Ops = sha256RegularExpandOps ++ sha256RegularConsumeOps 666307205 773529912 1294757372 1396182291 := by
  simp only [sha256RegularExpandOps, sha256RegularConsumeOps, sha256SB8Ops, sha256BodyOps]
  set_option maxRecDepth 4096 in rfl

private lemma sha256SB9Ops_split :
    sha256SB9Ops = sha256RegularExpandOps ++ sha256RegularConsumeOps 1695183700 1986661051 2177026350 2456956037 := by
  simp only [sha256RegularExpandOps, sha256RegularConsumeOps, sha256SB9Ops, sha256BodyOps]
  set_option maxRecDepth 4096 in rfl

private lemma sha256SB10Ops_split :
    sha256SB10Ops = sha256RegularExpandOps ++ sha256RegularConsumeOps 2730485921 2820302411 3259730800 3345764771 := by
  simp only [sha256RegularExpandOps, sha256RegularConsumeOps, sha256SB10Ops, sha256BodyOps]
  set_option maxRecDepth 4096 in rfl

private lemma sha256SB11Ops_split :
    sha256SB11Ops = sha256RegularExpandOps ++ sha256RegularConsumeOps 3516065817 3600352804 4094571909 275423344 := by
  simp only [sha256RegularExpandOps, sha256RegularConsumeOps, sha256SB11Ops, sha256BodyOps]
  set_option maxRecDepth 4096 in rfl

-- ============================================================================
-- Regular expand per-word sub-ops
-- ============================================================================

-- After movupw 3, the input [a0,a1,a2,a3, b0,b1,b2,b3, c0,c1,c2,c3, d0,d1,d2,d3]
-- becomes [d0,d1,d2,d3, a0,a1,a2,a3, b0,b1,b2,b3, c0,c1,c2,c3].
-- Compute 1: σ₁(a1) + c2 + σ₀(b2) + b3
-- Compute 2: σ₁(a0) + c1 + σ₀(b1) + b2
-- Compute 3: σ₁(new1) + c0 + σ₀(b0) + b1
-- Compute 4: σ₁(new2) + a3 + σ₀(d3) + b0
-- Then movupw 3 + rev_element_order:
--   → [b3,b2,b1,b0, new4,new3,new2,new1, d0,d1,d2,d3, a0,a1,a2,a3, c0,c1,c2,c3]

private def sha256RegularExpand_W1Ops : List Op := [
    .inst (.dup 14), .inst (.dup 6), .inst (.dup 13), .inst (.dup 13),
    .inst (.movdn 3), .inst (.movdn 3), .inst (.exec "compute_message_schedule_word")]

private def sha256RegularExpand_W2Ops : List Op := [
    .inst (.dup 14), .inst (.dup 6), .inst (.dup 13), .inst (.dup 13),
    .inst (.movdn 3), .inst (.movdn 3), .inst (.exec "compute_message_schedule_word")]

private def sha256RegularExpand_W3Ops : List Op := [
    .inst (.dup 14), .inst (.dup 2), .inst (.dup 13), .inst (.dup 13),
    .inst (.movdn 3), .inst (.movdn 3), .inst (.exec "compute_message_schedule_word")]

private def sha256RegularExpand_W4A_RevOps : List Op := [
    .inst (.dup 10), .inst (.dup 2), .inst (.dup 8), .inst (.dup 14),
    .inst (.movdn 3), .inst (.movdn 2), .inst (.exec "compute_message_schedule_word"),
    .inst (.movupw 3), .inst (.exec "rev_element_order")]

private def sha256SB6Expand_W4B_RevOps : List Op := [
    .inst (.dup 10), .inst (.dup 2), .inst (.dup 13), .inst (.dup 9),
    .inst (.movdn 3), .inst (.movdn 3), .inst (.exec "compute_message_schedule_word"),
    .inst (.movupw 3), .inst (.exec "rev_element_order")]

private lemma sha256RegularExpandOps_split :
    sha256RegularExpandOps = [.inst (.movupw 3)] ++ sha256RegularExpand_W1Ops ++
      sha256RegularExpand_W2Ops ++ sha256RegularExpand_W3Ops ++ sha256RegularExpand_W4A_RevOps := by
  simp only [sha256RegularExpand_W1Ops, sha256RegularExpand_W2Ops,
             sha256RegularExpand_W3Ops, sha256RegularExpand_W4A_RevOps, sha256RegularExpandOps]
  rfl

private lemma sha256SB6ExpandOps_split :
    sha256SB6ExpandOps = [.inst (.movupw 3)] ++ sha256RegularExpand_W1Ops ++
      sha256RegularExpand_W2Ops ++ sha256RegularExpand_W3Ops ++ sha256SB6Expand_W4B_RevOps := by
  simp only [sha256RegularExpand_W1Ops, sha256RegularExpand_W2Ops,
             sha256RegularExpand_W3Ops, sha256SB6Expand_W4B_RevOps, sha256SB6ExpandOps]
  rfl

-- ============================================================================
-- Per-word expand lemmas (generic, usable by all SBs 4–11)
-- ============================================================================

-- After movupw 3, stack is:
-- [d0,d1,d2,d3, a0,a1,a2,a3, b0,b1,b2,b3, c0,c1,c2,c3, rest]

-- Compute 1: dup 14=c2, dup 6=a1 (shifted), dup 13=b3 (shifted), dup 13=b2 (shifted)
-- After movdn 3, movdn 3: [a1, c2, b2, b3, ...]
-- Result: sha256W a1 c2 b2 b3

set_option maxHeartbeats 2000000 in
private lemma sha256_regular_expand_W1
    (d0 d1 d2 d3 a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 : Felt)
    (ha1 : a1.isU32 = true) (hc2 : c2.isU32 = true)
    (hb2 : b2.isU32 = true) (hb3 : b3.isU32 = true)
    (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt) :
    execWithEnv sha256ProcEnv 2126
        ⟨d0::d1::d2::d3::a0::a1::a2::a3::b0::b1::b2::b3::c0::c1::c2::c3::rest,
          mem, frames, adv⟩
        sha256RegularExpand_W1Ops =
    some ⟨sha256W a1 c2 b2 b3 :: d0 :: d1 :: d2 :: d3 :: a0 :: a1 :: a2 :: a3 ::
          b0 :: b1 :: b2 :: b3 :: c0 :: c1 :: c2 :: c3 :: rest,
          mem, frames, adv⟩ := by
  simp only [sha256RegularExpand_W1Ops]
  unfold execWithEnv; simp only [List.foldlM]
  miden_dup; miden_dup; miden_dup; miden_dup; miden_movdn; miden_movdn
  simp only [show sha256ProcEnv "compute_message_schedule_word" =
      some Miden.Core.Sha256.compute_message_schedule_word from rfl]
  rw [compute_message_schedule_word_at_2125 a1 c2 b2 b3 _ _ rfl ha1 hc2 hb2 hb3]
  simp only [MidenState.withStack, sha256W, pure, Pure.pure]

-- After W1: [new1, d0,d1,d2,d3, a0,a1,a2,a3, b0,b1,b2,b3, c0,c1,c2,c3, rest] (17 elems)
-- Compute 2: dup 14=c1, dup 6=a0 (shifted), dup 13=b2 (shifted), dup 13=b1 (shifted)
-- After movdn 3, movdn 3: [a0, c1, b1, b2, ...]
-- Result: sha256W a0 c1 b1 b2

set_option maxHeartbeats 2000000 in
private lemma sha256_regular_expand_W2
    (d0 d1 d2 d3 a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 new1 : Felt)
    (ha0 : a0.isU32 = true) (hc1 : c1.isU32 = true)
    (hb1 : b1.isU32 = true) (hb2 : b2.isU32 = true)
    (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt) :
    execWithEnv sha256ProcEnv 2126
        ⟨new1 :: d0 :: d1 :: d2 :: d3 :: a0 :: a1 :: a2 :: a3 ::
          b0 :: b1 :: b2 :: b3 :: c0 :: c1 :: c2 :: c3 :: rest,
          mem, frames, adv⟩
        sha256RegularExpand_W2Ops =
    some ⟨sha256W a0 c1 b1 b2 :: new1 :: d0 :: d1 :: d2 :: d3 :: a0 :: a1 :: a2 :: a3 ::
          b0 :: b1 :: b2 :: b3 :: c0 :: c1 :: c2 :: c3 :: rest,
          mem, frames, adv⟩ := by
  simp only [sha256RegularExpand_W2Ops]
  unfold execWithEnv; simp only [List.foldlM]
  miden_dup; miden_dup; miden_dup; miden_dup; miden_movdn; miden_movdn
  simp only [show sha256ProcEnv "compute_message_schedule_word" =
      some Miden.Core.Sha256.compute_message_schedule_word from rfl]
  rw [compute_message_schedule_word_at_2125 a0 c1 b1 b2 _ _ rfl ha0 hc1 hb1 hb2]
  simp only [MidenState.withStack, sha256W, pure, Pure.pure]

-- After W2: [new2, new1, d0,..., c3, rest] (18 elems)
-- Compute 3: dup 14=c0, dup 2=new1, dup 13=b0 (shifted), dup 13=b1 (shifted... wait)
-- Actually traced: dup 13 after pushing c0 and new1 gives b1, then dup 13 gives b0
-- After movdn 3, movdn 3: [new1, c0, b0, b1, ...]
-- Result: sha256W new1 c0 b0 b1

set_option maxHeartbeats 2000000 in
private lemma sha256_regular_expand_W3
    (d0 d1 d2 d3 a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 new1 new2 : Felt)
    (hnew1 : new1.isU32 = true) (hc0 : c0.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true)
    (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt) :
    execWithEnv sha256ProcEnv 2126
        ⟨new2 :: new1 :: d0 :: d1 :: d2 :: d3 :: a0 :: a1 :: a2 :: a3 ::
          b0 :: b1 :: b2 :: b3 :: c0 :: c1 :: c2 :: c3 :: rest,
          mem, frames, adv⟩
        sha256RegularExpand_W3Ops =
    some ⟨sha256W new1 c0 b0 b1 :: new2 :: new1 :: d0 :: d1 :: d2 :: d3 ::
          a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 :: c0 :: c1 :: c2 :: c3 :: rest,
          mem, frames, adv⟩ := by
  simp only [sha256RegularExpand_W3Ops]
  unfold execWithEnv; simp only [List.foldlM]
  miden_dup; miden_dup; miden_dup; miden_dup; miden_movdn; miden_movdn
  simp only [show sha256ProcEnv "compute_message_schedule_word" =
      some Miden.Core.Sha256.compute_message_schedule_word from rfl]
  rw [compute_message_schedule_word_at_2125 new1 c0 b0 b1 _ _ rfl hnew1 hc0 hb0 hb1]
  simp only [MidenState.withStack, sha256W, pure, Pure.pure]

-- After W3: [new3, new2, new1, d0,..., c3, rest] (19 elems)
-- Compute 4 (Type A): dup 10=a3, dup 2=new2, dup 8=d3, dup 14=b0
-- After movdn 3, movdn 2: [new2, a3, d3, b0, ...]
-- Result: sha256W new2 a3 d3 b0
-- Then movupw 3: brings [b0,b1,b2,b3] to top
-- Then rev_element_order: [b3,b2,b1,b0, ...]

set_option maxHeartbeats 2000000 in
private lemma sha256_regular_expand_W4A_rev
    (d0 d1 d2 d3 a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 new1 new2 new3 : Felt)
    (hnew2 : new2.isU32 = true) (ha3 : a3.isU32 = true)
    (hd3 : d3.isU32 = true) (hb0 : b0.isU32 = true)
    (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt) :
    execWithEnv sha256ProcEnv 2126
        ⟨new3 :: new2 :: new1 :: d0 :: d1 :: d2 :: d3 :: a0 :: a1 :: a2 :: a3 ::
          b0 :: b1 :: b2 :: b3 :: c0 :: c1 :: c2 :: c3 :: rest,
          mem, frames, adv⟩
        sha256RegularExpand_W4A_RevOps =
    some ⟨b3 :: b2 :: b1 :: b0 ::
          sha256W new2 a3 d3 b0 :: new3 :: new2 :: new1 ::
          d0 :: d1 :: d2 :: d3 :: a0 :: a1 :: a2 :: a3 :: c0 :: c1 :: c2 :: c3 :: rest,
          mem, frames, adv⟩ := by
  simp only [sha256RegularExpand_W4A_RevOps]
  unfold execWithEnv; simp only [List.foldlM]
  miden_dup; miden_dup; miden_dup; miden_dup; miden_movdn
  rw [stepMovdn (hn := rfl)]; miden_bind
  simp only [show sha256ProcEnv "compute_message_schedule_word" =
      some Miden.Core.Sha256.compute_message_schedule_word from rfl]
  rw [compute_message_schedule_word_at_2125 new2 a3 d3 b0 _ _ rfl hnew2 ha3 hd3 hb0]
  simp only [MidenState.withStack, sha256W]
  rw [stepMovupw3]; miden_bind
  simp only [show sha256ProcEnv "rev_element_order" =
      some Miden.Core.Sha256.rev_element_order from rfl]
  rw [rev_element_order_at_2125]
  dsimp only [pure, Pure.pure]

-- Compute 4 (Type B, SB6 only): dup 10=a3, dup 2=new2, dup 13=b0, dup 9=d3
-- After movdn 3, movdn 3: [new2, a3, d3, b0, ...] (same result as Type A)

set_option maxHeartbeats 2000000 in
private lemma sha256_SB6_expand_W4B_rev
    (d0 d1 d2 d3 a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 new1 new2 new3 : Felt)
    (hnew2 : new2.isU32 = true) (ha3 : a3.isU32 = true)
    (hd3 : d3.isU32 = true) (hb0 : b0.isU32 = true)
    (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt) :
    execWithEnv sha256ProcEnv 2126
        ⟨new3 :: new2 :: new1 :: d0 :: d1 :: d2 :: d3 :: a0 :: a1 :: a2 :: a3 ::
          b0 :: b1 :: b2 :: b3 :: c0 :: c1 :: c2 :: c3 :: rest,
          mem, frames, adv⟩
        sha256SB6Expand_W4B_RevOps =
    some ⟨b3 :: b2 :: b1 :: b0 ::
          sha256W new2 a3 d3 b0 :: new3 :: new2 :: new1 ::
          d0 :: d1 :: d2 :: d3 :: a0 :: a1 :: a2 :: a3 :: c0 :: c1 :: c2 :: c3 :: rest,
          mem, frames, adv⟩ := by
  simp only [sha256SB6Expand_W4B_RevOps]
  unfold execWithEnv; simp only [List.foldlM]
  miden_dup; miden_dup; miden_dup; miden_dup; miden_movdn; miden_movdn
  simp only [show sha256ProcEnv "compute_message_schedule_word" =
      some Miden.Core.Sha256.compute_message_schedule_word from rfl]
  rw [compute_message_schedule_word_at_2125 new2 a3 d3 b0 _ _ rfl hnew2 ha3 hd3 hb0]
  simp only [MidenState.withStack, sha256W]
  rw [stepMovupw3]; miden_bind
  simp only [show sha256ProcEnv "rev_element_order" =
      some Miden.Core.Sha256.rev_element_order from rfl]
  rw [rev_element_order_at_2125]
  dsimp only [pure, Pure.pure]

-- ============================================================================
-- Regular expand bridge (Type A: SBs 4,5,7,8,9,10,11)
-- ============================================================================

-- Input: [a0,a1,a2,a3, b0,b1,b2,b3, c0,c1,c2,c3, d0,d1,d2,d3, rest]
-- Output: [b3,b2,b1,b0, new4,new3,new2,new1, d0,d1,d2,d3, a0,a1,a2,a3, c0,c1,c2,c3, rest]
-- where new1 = sha256W a1 c2 b2 b3
--       new2 = sha256W a0 c1 b1 b2
--       new3 = sha256W new1 c0 b0 b1
--       new4 = sha256W new2 a3 d3 b0

set_option maxHeartbeats 800000 in
lemma sha256_regular_expand_bridge
    (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 : Felt)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true) (ha3 : a3.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true) (hb2 : b2.isU32 = true) (hb3 : b3.isU32 = true)
    (hc0 : c0.isU32 = true) (hc1 : c1.isU32 = true) (hc2 : c2.isU32 = true)
    (hd3 : d3.isU32 = true)
    (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt) :
    let new1 := sha256W a1 c2 b2 b3
    let new2 := sha256W a0 c1 b1 b2
    let new3 := sha256W new1 c0 b0 b1
    let new4 := sha256W new2 a3 d3 b0
    execWithEnv sha256ProcEnv 2126
        ⟨a0::a1::a2::a3::b0::b1::b2::b3::c0::c1::c2::c3::d0::d1::d2::d3::rest,
          mem, frames, adv⟩
        sha256RegularExpandOps =
    some ⟨b3 :: b2 :: b1 :: b0 :: new4 :: new3 :: new2 :: new1 ::
          d0 :: d1 :: d2 :: d3 :: a0 :: a1 :: a2 :: a3 :: c0 :: c1 :: c2 :: c3 :: rest,
          mem, frames, adv⟩ := by
  rw [sha256RegularExpandOps_split]
  rw [List.append_assoc, List.append_assoc, List.append_assoc, execWithEnv_append]
  -- movupw 3
  unfold execWithEnv; simp only [List.foldlM]
  rw [stepMovupw3]; miden_bind; simp only [bind, Bind.bind, Option.bind]
  -- W1
  rw [execWithEnv_append]
  rw [sha256_regular_expand_W1 d0 d1 d2 d3 a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3
      ha1 hc2 hb2 hb3 rest mem frames adv]
  simp only [bind, Bind.bind, Option.bind]
  -- W2
  rw [execWithEnv_append]
  rw [sha256_regular_expand_W2 d0 d1 d2 d3 a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3
      (sha256W a1 c2 b2 b3) ha0 hc1 hb1 hb2 rest mem frames adv]
  simp only [bind, Bind.bind, Option.bind]
  -- W3
  rw [execWithEnv_append]
  rw [sha256_regular_expand_W3 d0 d1 d2 d3 a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3
      (sha256W a1 c2 b2 b3) (sha256W a0 c1 b1 b2)
      (u32_mod_isU32 _) hc0 hb0 hb1 rest mem frames adv]
  simp only [bind, Bind.bind, Option.bind]
  -- W4A + rev
  rw [sha256_regular_expand_W4A_rev d0 d1 d2 d3 a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3
      (sha256W a1 c2 b2 b3) (sha256W a0 c1 b1 b2)
      (sha256W (sha256W a1 c2 b2 b3) c0 b0 b1)
      (u32_mod_isU32 _) ha3 hd3 hb0 rest mem frames adv]

-- ============================================================================
-- SB6 expand bridge (Type B)
-- ============================================================================

set_option maxHeartbeats 800000 in
lemma sha256_SB6_expand_bridge
    (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 : Felt)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true) (ha3 : a3.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true) (hb2 : b2.isU32 = true) (hb3 : b3.isU32 = true)
    (hc0 : c0.isU32 = true) (hc1 : c1.isU32 = true) (hc2 : c2.isU32 = true)
    (hd3 : d3.isU32 = true)
    (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt) :
    let new1 := sha256W a1 c2 b2 b3
    let new2 := sha256W a0 c1 b1 b2
    let new3 := sha256W new1 c0 b0 b1
    let new4 := sha256W new2 a3 d3 b0
    execWithEnv sha256ProcEnv 2126
        ⟨a0::a1::a2::a3::b0::b1::b2::b3::c0::c1::c2::c3::d0::d1::d2::d3::rest,
          mem, frames, adv⟩
        sha256SB6ExpandOps =
    some ⟨b3 :: b2 :: b1 :: b0 :: new4 :: new3 :: new2 :: new1 ::
          d0 :: d1 :: d2 :: d3 :: a0 :: a1 :: a2 :: a3 :: c0 :: c1 :: c2 :: c3 :: rest,
          mem, frames, adv⟩ := by
  rw [sha256SB6ExpandOps_split]
  rw [List.append_assoc, List.append_assoc, List.append_assoc, execWithEnv_append]
  -- movupw 3
  unfold execWithEnv; simp only [List.foldlM]
  rw [stepMovupw3]; miden_bind; simp only [bind, Bind.bind, Option.bind]
  -- W1
  rw [execWithEnv_append]
  rw [sha256_regular_expand_W1 d0 d1 d2 d3 a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3
      ha1 hc2 hb2 hb3 rest mem frames adv]
  simp only [bind, Bind.bind, Option.bind]
  -- W2
  rw [execWithEnv_append]
  rw [sha256_regular_expand_W2 d0 d1 d2 d3 a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3
      (sha256W a1 c2 b2 b3) ha0 hc1 hb1 hb2 rest mem frames adv]
  simp only [bind, Bind.bind, Option.bind]
  -- W3
  rw [execWithEnv_append]
  rw [sha256_regular_expand_W3 d0 d1 d2 d3 a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3
      (sha256W a1 c2 b2 b3) (sha256W a0 c1 b1 b2)
      (u32_mod_isU32 _) hc0 hb0 hb1 rest mem frames adv]
  simp only [bind, Bind.bind, Option.bind]
  -- W4B + rev (SB6 variant)
  rw [sha256_SB6_expand_W4B_rev d0 d1 d2 d3 a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3
      (sha256W a1 c2 b2 b3) (sha256W a0 c1 b1 b2)
      (sha256W (sha256W a1 c2 b2 b3) c0 b0 b1)
      (u32_mod_isU32 _) ha3 hd3 hb0 rest mem frames adv]

-- ============================================================================
-- Regular consume bridge (parameterized by K constants)
-- ============================================================================

-- Input after expand: [b3,b2,b1,b0, new4,...,new1, d0,...,d3, a0,...,a3, c0,...,c3, rest]
-- The top 4 (b3,b2,b1,b0) are the message words consumed with K values.
-- After consume+store+drop: [new4,...,new1, d0,...,d3, a0,...,a3, c0,...,c3, rest]

set_option maxHeartbeats 4000000 in
lemma sha256_regular_consume_bridge
    (w0 w1 w2 w3 : Felt)
    (r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Felt)
    (a b c d e f g h : Felt)
    (H0 H1 H2 H3 H4 H5 H6 H7 : Felt)
    (k0 k1 k2 k3 : Nat)
    (hk0 : k0 < 2^32) (hk1 : k1 < 2^32) (hk2 : k2 < 2^32) (hk3 : k3 < 2^32)
    (hw0 : w0.isU32 = true) (hw1 : w1.isU32 = true) (hw2 : w2.isU32 = true)
    (hw3 : w3.isU32 = true)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) (hd : d.isU32 = true)
    (he : e.isU32 = true) (hf : f.isU32 = true) (hg : g.isU32 = true) (hh : h.isU32 = true)
    (rest : List Felt) (mem : Nat → Felt) (adv : List Felt)
    (frame : LocalFrame) (frames_rest : List LocalFrame)
    (hframe_locals : frame.numLocals = 16)
    (hframe_aligned : frame.alignedNumLocals = 16)
    (h3  : mem (frame.localAddr 3)  = a) (h2  : mem (frame.localAddr 2)  = b)
    (h1  : mem (frame.localAddr 1)  = c) (h0  : mem (frame.localAddr 0)  = d)
    (h7  : mem (frame.localAddr 7)  = e) (h6  : mem (frame.localAddr 6)  = f)
    (h5  : mem (frame.localAddr 5)  = g) (h4  : mem (frame.localAddr 4)  = h)
    (h11 : mem (frame.localAddr 11) = H0) (h10 : mem (frame.localAddr 10) = H1)
    (h9  : mem (frame.localAddr 9)  = H2) (h8  : mem (frame.localAddr 8)  = H3)
    (h15 : mem (frame.localAddr 15) = H4) (h14 : mem (frame.localAddr 14) = H5)
    (h13 : mem (frame.localAddr 13) = H6) (h12 : mem (frame.localAddr 12) = H7) :
    let (na, nb, nc, nd, ne, nf, ng, nh) := sha256Compress4 a b c d e f g h w0 w1 w2 w3 k0 k1 k2 k3
    execWithEnv sha256ProcEnv 2126
        ⟨w0 :: w1 :: w2 :: w3 :: r4 :: r5 :: r6 :: r7 ::
          r8 :: r9 :: r10 :: r11 :: r12 :: r13 :: r14 :: r15 :: rest,
          mem, frames, adv⟩
        (sha256RegularConsumeOps k0 k1 k2 k3) =
    some ⟨r4 :: r5 :: r6 :: r7 :: r8 :: r9 :: r10 :: r11 ::
          r12 :: r13 :: r14 :: r15 :: rest,
          fun i =>
            if i = frame.localAddr 4 + 3 then ne else if i = frame.localAddr 4 + 2 then nf else
            if i = frame.localAddr 4 + 1 then ng else if i = frame.localAddr 4 then nh else
            if i = frame.localAddr 0 + 3 then na else if i = frame.localAddr 0 + 2 then nb else
            if i = frame.localAddr 0 + 1 then nc else if i = frame.localAddr 0 then nd else
            mem i,
          frame :: frames_rest, adv⟩ := by
  simp only [sha256RegularConsumeOps]
  unfold execWithEnv; simp only [List.foldlM]
  rw [stepPush]; miden_bind
  rw [stepPadw]; miden_bind
  rw [stepLocLoadwBe (idx := 4) (frame := frame) (frames_rest := frames_rest)
      (halign := by decide) (hbound := by omega)]; miden_bind
  simp only [show frame.localAddr 4 + 3 = frame.localAddr 7 from by
      simp [LocalFrame.localAddr],
    show frame.localAddr 4 + 2 = frame.localAddr 6 from by
      simp [LocalFrame.localAddr],
    show frame.localAddr 4 + 1 = frame.localAddr 5 from by
      simp [LocalFrame.localAddr]]
  rw [h7, h6, h5, h4]
  rw [stepPadw]; miden_bind
  rw [stepLocLoadwBe (idx := 0) (frame := frame) (frames_rest := frames_rest)
      (halign := by decide) (hbound := by omega)]; miden_bind
  simp only [show frame.localAddr 0 + 3 = frame.localAddr 3 from by
      simp [LocalFrame.localAddr],
    show frame.localAddr 0 + 2 = frame.localAddr 2 from by
      simp [LocalFrame.localAddr],
    show frame.localAddr 0 + 1 = frame.localAddr 1 from by
      simp [LocalFrame.localAddr]]
  rw [h3, h2, h1, h0]
  simp only [show sha256ProcEnv "consume_message_word" =
      some Miden.Core.Sha256.consume_message_word from rfl]
  rw [consume_message_word_at_2125 a b c d e f g h (Felt.ofNat k0) w0
      _ _ rfl ha hb hc hd he hf hg hh (felt_ofNat_isU32_of_lt _ hk0) hw0]
  simp only [MidenState.withStack]
  rw [stepPush]; miden_bind
  rw [stepMovdn (hn := rfl)]; miden_bind
  rw [consume_message_word_at_2125 _ _ _ _ _ _ _ _ (Felt.ofNat k1) w1
      _ _ rfl (u32_mod_isU32 _) ha hb hc (u32_mod_isU32 _) he hf hg
      (felt_ofNat_isU32_of_lt _ hk1) hw1]
  simp only [MidenState.withStack]
  rw [stepPush]; miden_bind
  rw [stepMovdn (hn := rfl)]; miden_bind
  rw [consume_message_word_at_2125 _ _ _ _ _ _ _ _ (Felt.ofNat k2) w2
      _ _ rfl (u32_mod_isU32 _) (u32_mod_isU32 _) ha hb (u32_mod_isU32 _) (u32_mod_isU32 _)
      he hf (felt_ofNat_isU32_of_lt _ hk2) hw2]
  simp only [MidenState.withStack]
  rw [stepPush]; miden_bind
  rw [stepMovdn (hn := rfl)]; miden_bind
  rw [consume_message_word_at_2125 _ _ _ _ _ _ _ _ (Felt.ofNat k3) w3
      _ _ rfl (u32_mod_isU32 _) (u32_mod_isU32 _) (u32_mod_isU32 _) ha (u32_mod_isU32 _)
      (u32_mod_isU32 _) (u32_mod_isU32 _) he (felt_ofNat_isU32_of_lt _ hk3) hw3]
  simp only [MidenState.withStack]
  rw [stepLocStorewBe (idx := 0) (frame := frame) (frames_rest := frames_rest)
      (halign := by decide) (hbound := by omega)]; miden_bind
  rw [stepDropw]; miden_bind
  rw [stepLocStorewBe (idx := 4) (frame := frame) (frames_rest := frames_rest)
      (halign := by decide) (hbound := by omega)]; miden_bind
  rw [stepDropw]; miden_bind
  dsimp only [pure, Pure.pure]
  simp only [sha256Compress4, consumeResult]
  rfl

-- ============================================================================
-- SB4–SB11 bridge lemmas
-- Each uses the generic expand + consume bridge.
-- Input: [a0,...,a3, b0,...,b3, c0,...,c3, d0,...,d3, rest]
-- Output: [new4,...,new1, d0,...,d3, a0,...,a3, c0,...,c3, rest]
--   with locs updated to sha256WorkingLocs (compress result) ...
-- ============================================================================

-- SB4: Input from SB3 = [W31,W30,W29,W28, W19,W18,W17,W16, W27,W26,W25,W24, W23,W22,W21,W20]
-- a=[W31..W28], b=[W19..W16], c=[W27..W24], d=[W23..W20]
-- new1 = sha256W W30 W25 W17 W16 (= W32)
-- new2 = sha256W W31 W26 W18 W17 (= W33)
-- new3 = sha256W W32 W27 W19 W18 (= W34)
-- new4 = sha256W W33 W28 W20 W19 (= W35)
-- Consumed: [b3,b2,b1,b0] = [W16,W17,W18,W19] with K[16..19]
-- Output: [W35,W34,W33,W32, W23,W22,W21,W20, W31,W30,W29,W28, W27,W26,W25,W24]

set_option maxHeartbeats 800000 in
lemma sha256_SB4_bridge
    (W31 W30 W29 W28 W19 W18 W17 W16 W27 W26 W25 W24 W23 W22 W21 W20 : Felt)
    (a b c d e f g h : Felt)
    (H0 H1 H2 H3 H4 H5 H6 H7 : Felt)
    (hW31 : W31.isU32 = true) (hW30 : W30.isU32 = true)
    (_hW29 : W29.isU32 = true) (hW28 : W28.isU32 = true)
    (hW19 : W19.isU32 = true) (hW18 : W18.isU32 = true)
    (hW17 : W17.isU32 = true) (hW16 : W16.isU32 = true)
    (hW27 : W27.isU32 = true) (hW26 : W26.isU32 = true)
    (hW25 : W25.isU32 = true) (_hW24 : W24.isU32 = true)
    (hW20 : W20.isU32 = true) (_hW21 : W21.isU32 = true)
    (_hW22 : W22.isU32 = true) (_hW23 : W23.isU32 = true)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) (hd : d.isU32 = true)
    (he : e.isU32 = true) (hf : f.isU32 = true) (hg : g.isU32 = true) (hh : h.isU32 = true)
    (_hH0 : H0.isU32 = true) (_hH1 : H1.isU32 = true) (_hH2 : H2.isU32 = true)
    (_hH3 : H3.isU32 = true) (_hH4 : H4.isU32 = true) (_hH5 : H5.isU32 = true)
    (_hH6 : H6.isU32 = true) (_hH7 : H7.isU32 = true)
    (rest : List Felt) (mem : Nat → Felt) (adv : List Felt)
    (frame : LocalFrame) (frames_rest : List LocalFrame)
    (hframe_locals : frame.numLocals = 16)
    (hframe_aligned : frame.alignedNumLocals = 16)
    (h3  : mem (frame.localAddr 3)  = a) (h2  : mem (frame.localAddr 2)  = b)
    (h1  : mem (frame.localAddr 1)  = c) (h0  : mem (frame.localAddr 0)  = d)
    (h7  : mem (frame.localAddr 7)  = e) (h6  : mem (frame.localAddr 6)  = f)
    (h5  : mem (frame.localAddr 5)  = g) (h4  : mem (frame.localAddr 4)  = h)
    (h11 : mem (frame.localAddr 11) = H0) (h10 : mem (frame.localAddr 10) = H1)
    (h9  : mem (frame.localAddr 9)  = H2) (h8  : mem (frame.localAddr 8)  = H3)
    (h15 : mem (frame.localAddr 15) = H4) (h14 : mem (frame.localAddr 14) = H5)
    (h13 : mem (frame.localAddr 13) = H6) (h12 : mem (frame.localAddr 12) = H7) :
    let W32 := sha256W W30 W25 W17 W16
    let W33 := sha256W W31 W26 W18 W17
    let W34 := sha256W W32 W27 W19 W18
    let W35 := sha256W W33 W28 W20 W19
    let (na, nb, nc, nd, ne, nf, ng, nh) := sha256Compress4 a b c d e f g h W16 W17 W18 W19 3835390401 4022224774 264347078 604807628
    execWithEnv sha256ProcEnv 2126
        ⟨W31::W30::W29::W28::W19::W18::W17::W16::W27::W26::W25::W24::W23::W22::W21::W20::rest,
          mem, frame :: frames_rest, adv⟩
        sha256SB4Ops =
    some ⟨W35 :: W34 :: W33 :: W32 :: W23 :: W22 :: W21 :: W20 ::
          W31 :: W30 :: W29 :: W28 :: W27 :: W26 :: W25 :: W24 :: rest,
          fun i =>
            if i = frame.localAddr 4 + 3 then ne else if i = frame.localAddr 4 + 2 then nf else
            if i = frame.localAddr 4 + 1 then ng else if i = frame.localAddr 4 then nh else
            if i = frame.localAddr 0 + 3 then na else if i = frame.localAddr 0 + 2 then nb else
            if i = frame.localAddr 0 + 1 then nc else if i = frame.localAddr 0 then nd else
            mem i,
          frame :: frames_rest, adv⟩ := by
  rw [sha256SB4Ops_split, execWithEnv_append]
  rw [sha256_regular_expand_bridge W31 W30 W29 W28 W19 W18 W17 W16 W27 W26 W25 W24 W23 W22 W21 W20
      hW31 hW30 hW28 hW19 hW18 hW17 hW16 hW27 hW26 hW25 hW20 rest mem (frame :: frames_rest) adv]
  simp only [bind, Bind.bind, Option.bind]
  rw [sha256_regular_consume_bridge W16 W17 W18 W19
      (sha256W (sha256W W31 W26 W18 W17) W28 W20 W19)
      (sha256W (sha256W W30 W25 W17 W16) W27 W19 W18)
      (sha256W W31 W26 W18 W17) (sha256W W30 W25 W17 W16)
      W23 W22 W21 W20 W31 W30 W29 W28 W27 W26 W25 W24
      a b c d e f g h H0 H1 H2 H3 H4 H5 H6 H7
      3835390401 4022224774 264347078 604807628
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hW16 hW17 hW18 hW19 ha hb hc hd he hf hg hh
      rest mem adv frame frames_rest hframe_locals hframe_aligned
      h3 h2 h1 h0 h7 h6 h5 h4 h11 h10 h9 h8 h15 h14 h13 h12]
  dsimp only [sha256Compress4, consumeResult, sha256W]

-- SB5: Input = SB4 output = [W35,W34,W33,W32, W23,W22,W21,W20, W31,W30,W29,W28, W27,W26,W25,W24]
-- a=[W35..W32], b=[W23..W20], c=[W31..W28], d=[W27..W24]
-- new1 = sha256W W34 W29 W21 W20 (= W36)
-- new2 = sha256W W35 W30 W22 W21 (= W37)
-- new3 = sha256W W36 W31 W23 W22 (= W38)
-- new4 = sha256W W37 W32 W24 W23 (= W39)
-- Consumed: [W20,W21,W22,W23] with K[20..23]
-- Output: [W39,W38,W37,W36, W27,W26,W25,W24, W35,W34,W33,W32, W31,W30,W29,W28]

set_option maxHeartbeats 800000 in
lemma sha256_SB5_bridge
    (W35 W34 W33 W32 W23 W22 W21 W20 W31 W30 W29 W28 W27 W26 W25 W24 : Felt)
    (a b c d e f g h : Felt)
    (H0 H1 H2 H3 H4 H5 H6 H7 : Felt)
    (hW35 : W35.isU32 = true) (hW34 : W34.isU32 = true)
    (_hW33 : W33.isU32 = true) (hW32 : W32.isU32 = true)
    (hW23 : W23.isU32 = true) (hW22 : W22.isU32 = true)
    (hW21 : W21.isU32 = true) (hW20 : W20.isU32 = true)
    (hW31 : W31.isU32 = true) (hW30 : W30.isU32 = true)
    (hW29 : W29.isU32 = true) (_hW28 : W28.isU32 = true)
    (hW24 : W24.isU32 = true) (_hW25 : W25.isU32 = true)
    (_hW26 : W26.isU32 = true) (_hW27 : W27.isU32 = true)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) (hd : d.isU32 = true)
    (he : e.isU32 = true) (hf : f.isU32 = true) (hg : g.isU32 = true) (hh : h.isU32 = true)
    (_hH0 : H0.isU32 = true) (_hH1 : H1.isU32 = true) (_hH2 : H2.isU32 = true)
    (_hH3 : H3.isU32 = true) (_hH4 : H4.isU32 = true) (_hH5 : H5.isU32 = true)
    (_hH6 : H6.isU32 = true) (_hH7 : H7.isU32 = true)
    (rest : List Felt) (mem : Nat → Felt) (adv : List Felt)
    (frame : LocalFrame) (frames_rest : List LocalFrame)
    (hframe_locals : frame.numLocals = 16)
    (hframe_aligned : frame.alignedNumLocals = 16)
    (h3  : mem (frame.localAddr 3)  = a) (h2  : mem (frame.localAddr 2)  = b)
    (h1  : mem (frame.localAddr 1)  = c) (h0  : mem (frame.localAddr 0)  = d)
    (h7  : mem (frame.localAddr 7)  = e) (h6  : mem (frame.localAddr 6)  = f)
    (h5  : mem (frame.localAddr 5)  = g) (h4  : mem (frame.localAddr 4)  = h)
    (h11 : mem (frame.localAddr 11) = H0) (h10 : mem (frame.localAddr 10) = H1)
    (h9  : mem (frame.localAddr 9)  = H2) (h8  : mem (frame.localAddr 8)  = H3)
    (h15 : mem (frame.localAddr 15) = H4) (h14 : mem (frame.localAddr 14) = H5)
    (h13 : mem (frame.localAddr 13) = H6) (h12 : mem (frame.localAddr 12) = H7) :
    let W36 := sha256W W34 W29 W21 W20
    let W37 := sha256W W35 W30 W22 W21
    let W38 := sha256W W36 W31 W23 W22
    let W39 := sha256W W37 W32 W24 W23
    let (na, nb, nc, nd, ne, nf, ng, nh) := sha256Compress4 a b c d e f g h W20 W21 W22 W23 770255983 1249150122 1555081692 1996064986
    execWithEnv sha256ProcEnv 2126
        ⟨W35::W34::W33::W32::W23::W22::W21::W20::W31::W30::W29::W28::W27::W26::W25::W24::rest,
          mem, frame :: frames_rest, adv⟩
        sha256SB5Ops =
    some ⟨W39 :: W38 :: W37 :: W36 :: W27 :: W26 :: W25 :: W24 ::
          W35 :: W34 :: W33 :: W32 :: W31 :: W30 :: W29 :: W28 :: rest,
          fun i =>
            if i = frame.localAddr 4 + 3 then ne else if i = frame.localAddr 4 + 2 then nf else
            if i = frame.localAddr 4 + 1 then ng else if i = frame.localAddr 4 then nh else
            if i = frame.localAddr 0 + 3 then na else if i = frame.localAddr 0 + 2 then nb else
            if i = frame.localAddr 0 + 1 then nc else if i = frame.localAddr 0 then nd else
            mem i,
          frame :: frames_rest, adv⟩ := by
  rw [sha256SB5Ops_split, execWithEnv_append]
  rw [sha256_regular_expand_bridge W35 W34 W33 W32 W23 W22 W21 W20 W31 W30 W29 W28 W27 W26 W25 W24
      hW35 hW34 hW32 hW23 hW22 hW21 hW20 hW31 hW30 hW29 hW24 rest mem (frame :: frames_rest) adv]
  simp only [bind, Bind.bind, Option.bind]
  rw [sha256_regular_consume_bridge W20 W21 W22 W23
      (sha256W (sha256W W35 W30 W22 W21) W32 W24 W23)
      (sha256W (sha256W W34 W29 W21 W20) W31 W23 W22)
      (sha256W W35 W30 W22 W21) (sha256W W34 W29 W21 W20)
      W27 W26 W25 W24 W35 W34 W33 W32 W31 W30 W29 W28
      a b c d e f g h H0 H1 H2 H3 H4 H5 H6 H7
      770255983 1249150122 1555081692 1996064986
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hW20 hW21 hW22 hW23 ha hb hc hd he hf hg hh
      rest mem adv frame frames_rest hframe_locals hframe_aligned
      h3 h2 h1 h0 h7 h6 h5 h4 h11 h10 h9 h8 h15 h14 h13 h12]
  dsimp only [sha256Compress4, consumeResult, sha256W]

-- SB6: Input = SB5 output = [W39,W38,W37,W36, W27,W26,W25,W24, W35,W34,W33,W32, W31,W30,W29,W28]
-- a=[W39..W36], b=[W27..W24], c=[W35..W32], d=[W31..W28]
-- new1 = sha256W W38 W33 W25 W24 (= W40)
-- new2 = sha256W W39 W34 W26 W25 (= W41)
-- new3 = sha256W W40 W35 W27 W26 (= W42)
-- new4 = sha256W W41 W36 W28 W27 (= W43)
-- Consumed: [W24,W25,W26,W27] with K[24..27]
-- Output: [W43,W42,W41,W40, W31,W30,W29,W28, W39,W38,W37,W36, W35,W34,W33,W32]

set_option maxHeartbeats 800000 in
lemma sha256_SB6_bridge
    (W39 W38 W37 W36 W27 W26 W25 W24 W35 W34 W33 W32 W31 W30 W29 W28 : Felt)
    (a b c d e f g h : Felt)
    (H0 H1 H2 H3 H4 H5 H6 H7 : Felt)
    (hW39 : W39.isU32 = true) (hW38 : W38.isU32 = true)
    (_hW37 : W37.isU32 = true) (hW36 : W36.isU32 = true)
    (hW27 : W27.isU32 = true) (hW26 : W26.isU32 = true)
    (hW25 : W25.isU32 = true) (hW24 : W24.isU32 = true)
    (hW35 : W35.isU32 = true) (hW34 : W34.isU32 = true)
    (hW33 : W33.isU32 = true) (_hW32 : W32.isU32 = true)
    (hW28 : W28.isU32 = true) (_hW29 : W29.isU32 = true)
    (_hW30 : W30.isU32 = true) (_hW31 : W31.isU32 = true)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) (hd : d.isU32 = true)
    (he : e.isU32 = true) (hf : f.isU32 = true) (hg : g.isU32 = true) (hh : h.isU32 = true)
    (_hH0 : H0.isU32 = true) (_hH1 : H1.isU32 = true) (_hH2 : H2.isU32 = true)
    (_hH3 : H3.isU32 = true) (_hH4 : H4.isU32 = true) (_hH5 : H5.isU32 = true)
    (_hH6 : H6.isU32 = true) (_hH7 : H7.isU32 = true)
    (rest : List Felt) (mem : Nat → Felt) (adv : List Felt)
    (frame : LocalFrame) (frames_rest : List LocalFrame)
    (hframe_locals : frame.numLocals = 16)
    (hframe_aligned : frame.alignedNumLocals = 16)
    (h3  : mem (frame.localAddr 3)  = a) (h2  : mem (frame.localAddr 2)  = b)
    (h1  : mem (frame.localAddr 1)  = c) (h0  : mem (frame.localAddr 0)  = d)
    (h7  : mem (frame.localAddr 7)  = e) (h6  : mem (frame.localAddr 6)  = f)
    (h5  : mem (frame.localAddr 5)  = g) (h4  : mem (frame.localAddr 4)  = h)
    (h11 : mem (frame.localAddr 11) = H0) (h10 : mem (frame.localAddr 10) = H1)
    (h9  : mem (frame.localAddr 9)  = H2) (h8  : mem (frame.localAddr 8)  = H3)
    (h15 : mem (frame.localAddr 15) = H4) (h14 : mem (frame.localAddr 14) = H5)
    (h13 : mem (frame.localAddr 13) = H6) (h12 : mem (frame.localAddr 12) = H7) :
    let W40 := sha256W W38 W33 W25 W24
    let W41 := sha256W W39 W34 W26 W25
    let W42 := sha256W W40 W35 W27 W26
    let W43 := sha256W W41 W36 W28 W27
    let (na, nb, nc, nd, ne, nf, ng, nh) := sha256Compress4 a b c d e f g h W24 W25 W26 W27 2554220882 2821834349 2952996808 3210313671
    execWithEnv sha256ProcEnv 2126
        ⟨W39::W38::W37::W36::W27::W26::W25::W24::W35::W34::W33::W32::W31::W30::W29::W28::rest,
          mem, frame :: frames_rest, adv⟩
        sha256SB6Ops =
    some ⟨W43 :: W42 :: W41 :: W40 :: W31 :: W30 :: W29 :: W28 ::
          W39 :: W38 :: W37 :: W36 :: W35 :: W34 :: W33 :: W32 :: rest,
          fun i =>
            if i = frame.localAddr 4 + 3 then ne else if i = frame.localAddr 4 + 2 then nf else
            if i = frame.localAddr 4 + 1 then ng else if i = frame.localAddr 4 then nh else
            if i = frame.localAddr 0 + 3 then na else if i = frame.localAddr 0 + 2 then nb else
            if i = frame.localAddr 0 + 1 then nc else if i = frame.localAddr 0 then nd else
            mem i,
          frame :: frames_rest, adv⟩ := by
  rw [sha256SB6Ops_split, execWithEnv_append]
  rw [sha256_SB6_expand_bridge W39 W38 W37 W36 W27 W26 W25 W24 W35 W34 W33 W32 W31 W30 W29 W28
      hW39 hW38 hW36 hW27 hW26 hW25 hW24 hW35 hW34 hW33 hW28 rest mem (frame :: frames_rest) adv]
  simp only [bind, Bind.bind, Option.bind]
  rw [sha256_regular_consume_bridge W24 W25 W26 W27
      (sha256W (sha256W W39 W34 W26 W25) W36 W28 W27)
      (sha256W (sha256W W38 W33 W25 W24) W35 W27 W26)
      (sha256W W39 W34 W26 W25) (sha256W W38 W33 W25 W24)
      W31 W30 W29 W28 W39 W38 W37 W36 W35 W34 W33 W32
      a b c d e f g h H0 H1 H2 H3 H4 H5 H6 H7
      2554220882 2821834349 2952996808 3210313671
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hW24 hW25 hW26 hW27 ha hb hc hd he hf hg hh
      rest mem adv frame frames_rest hframe_locals hframe_aligned
      h3 h2 h1 h0 h7 h6 h5 h4 h11 h10 h9 h8 h15 h14 h13 h12]
  dsimp only [sha256Compress4, consumeResult, sha256W]

-- SB7: Input = SB6 output = [W43,W42,W41,W40, W31,W30,W29,W28, W39,W38,W37,W36, W35,W34,W33,W32]
-- a=[W43..W40], b=[W31..W28], c=[W39..W36], d=[W35..W32]
-- new1 = sha256W W42 W37 W29 W28 (= W44)
-- new2 = sha256W W43 W38 W30 W29 (= W45)
-- new3 = sha256W W44 W39 W31 W30 (= W46)
-- new4 = sha256W W45 W40 W32 W31 (= W47)
-- Consumed: [W28,W29,W30,W31] with K[28..31]
-- Output: [W47,W46,W45,W44, W35,W34,W33,W32, W43,W42,W41,W40, W39,W38,W37,W36]

set_option maxHeartbeats 800000 in
lemma sha256_SB7_bridge
    (W43 W42 W41 W40 W31 W30 W29 W28 W39 W38 W37 W36 W35 W34 W33 W32 : Felt)
    (a b c d e f g h : Felt)
    (H0 H1 H2 H3 H4 H5 H6 H7 : Felt)
    (hW43 : W43.isU32 = true) (hW42 : W42.isU32 = true)
    (_hW41 : W41.isU32 = true) (hW40 : W40.isU32 = true)
    (hW31 : W31.isU32 = true) (hW30 : W30.isU32 = true)
    (hW29 : W29.isU32 = true) (hW28 : W28.isU32 = true)
    (hW39 : W39.isU32 = true) (hW38 : W38.isU32 = true)
    (hW37 : W37.isU32 = true) (_hW36 : W36.isU32 = true)
    (hW32 : W32.isU32 = true) (_hW33 : W33.isU32 = true)
    (_hW34 : W34.isU32 = true) (_hW35 : W35.isU32 = true)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) (hd : d.isU32 = true)
    (he : e.isU32 = true) (hf : f.isU32 = true) (hg : g.isU32 = true) (hh : h.isU32 = true)
    (_hH0 : H0.isU32 = true) (_hH1 : H1.isU32 = true) (_hH2 : H2.isU32 = true)
    (_hH3 : H3.isU32 = true) (_hH4 : H4.isU32 = true) (_hH5 : H5.isU32 = true)
    (_hH6 : H6.isU32 = true) (_hH7 : H7.isU32 = true)
    (rest : List Felt) (mem : Nat → Felt) (adv : List Felt)
    (frame : LocalFrame) (frames_rest : List LocalFrame)
    (hframe_locals : frame.numLocals = 16)
    (hframe_aligned : frame.alignedNumLocals = 16)
    (h3  : mem (frame.localAddr 3)  = a) (h2  : mem (frame.localAddr 2)  = b)
    (h1  : mem (frame.localAddr 1)  = c) (h0  : mem (frame.localAddr 0)  = d)
    (h7  : mem (frame.localAddr 7)  = e) (h6  : mem (frame.localAddr 6)  = f)
    (h5  : mem (frame.localAddr 5)  = g) (h4  : mem (frame.localAddr 4)  = h)
    (h11 : mem (frame.localAddr 11) = H0) (h10 : mem (frame.localAddr 10) = H1)
    (h9  : mem (frame.localAddr 9)  = H2) (h8  : mem (frame.localAddr 8)  = H3)
    (h15 : mem (frame.localAddr 15) = H4) (h14 : mem (frame.localAddr 14) = H5)
    (h13 : mem (frame.localAddr 13) = H6) (h12 : mem (frame.localAddr 12) = H7) :
    let W44 := sha256W W42 W37 W29 W28
    let W45 := sha256W W43 W38 W30 W29
    let W46 := sha256W W44 W39 W31 W30
    let W47 := sha256W W45 W40 W32 W31
    let (na, nb, nc, nd, ne, nf, ng, nh) := sha256Compress4 a b c d e f g h W28 W29 W30 W31 3336571891 3584528711 113926993 338241895
    execWithEnv sha256ProcEnv 2126
        ⟨W43::W42::W41::W40::W31::W30::W29::W28::W39::W38::W37::W36::W35::W34::W33::W32::rest,
          mem, frame :: frames_rest, adv⟩
        sha256SB7Ops =
    some ⟨W47 :: W46 :: W45 :: W44 :: W35 :: W34 :: W33 :: W32 ::
          W43 :: W42 :: W41 :: W40 :: W39 :: W38 :: W37 :: W36 :: rest,
          fun i =>
            if i = frame.localAddr 4 + 3 then ne else if i = frame.localAddr 4 + 2 then nf else
            if i = frame.localAddr 4 + 1 then ng else if i = frame.localAddr 4 then nh else
            if i = frame.localAddr 0 + 3 then na else if i = frame.localAddr 0 + 2 then nb else
            if i = frame.localAddr 0 + 1 then nc else if i = frame.localAddr 0 then nd else
            mem i,
          frame :: frames_rest, adv⟩ := by
  rw [sha256SB7Ops_split, execWithEnv_append]
  rw [sha256_regular_expand_bridge W43 W42 W41 W40 W31 W30 W29 W28 W39 W38 W37 W36 W35 W34 W33 W32
      hW43 hW42 hW40 hW31 hW30 hW29 hW28 hW39 hW38 hW37 hW32 rest mem (frame :: frames_rest) adv]
  simp only [bind, Bind.bind, Option.bind]
  rw [sha256_regular_consume_bridge W28 W29 W30 W31
      (sha256W (sha256W W43 W38 W30 W29) W40 W32 W31)
      (sha256W (sha256W W42 W37 W29 W28) W39 W31 W30)
      (sha256W W43 W38 W30 W29) (sha256W W42 W37 W29 W28)
      W35 W34 W33 W32 W43 W42 W41 W40 W39 W38 W37 W36
      a b c d e f g h H0 H1 H2 H3 H4 H5 H6 H7
      3336571891 3584528711 113926993 338241895
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hW28 hW29 hW30 hW31 ha hb hc hd he hf hg hh
      rest mem adv frame frames_rest hframe_locals hframe_aligned
      h3 h2 h1 h0 h7 h6 h5 h4 h11 h10 h9 h8 h15 h14 h13 h12]
  dsimp only [sha256Compress4, consumeResult, sha256W]

end MidenLean.Proofs.Sha256
