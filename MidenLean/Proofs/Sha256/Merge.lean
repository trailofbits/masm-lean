import MidenLean.Proofs.Sha256.PrepareMessageScheduleAndConsume
import MidenLean.Proofs.Sha256.ConsumePaddingMessageSchedule

namespace MidenLean.Proofs.Sha256

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

-- ============================================================================
-- Bridge: consume_padding_message_schedule at fuel 2126
-- (merge runs at 2127; exec calls use fuel 2126)
-- ============================================================================

private lemma sha256_consume_padding_at_2126
    (x0 x1 x2 x3 x4 x5 x6 x7 : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: rest)
    (h0 : x0.isU32 = true) (h1 : x1.isU32 = true)
    (h2 : x2.isU32 = true) (h3 : x3.isU32 = true)
    (h4 : x4.isU32 = true) (h5 : x5.isU32 = true)
    (h6 : x6.isU32 = true) (h7 : x7.isU32 = true) :
    execWithEnv sha256ProcEnv 2126 s Miden.Core.Sha256.consume_padding_message_schedule =
    some (s.withStack (sha256PaddingState x0 x1 x2 x3 x4 x5 x6 x7 ++ rest)) :=
  execWithEnv_fuel_mono sha256ProcEnv (by norm_num)
    (sha256_consume_padding_message_schedule_correct x0 x1 x2 x3 x4 x5 x6 x7 rest s hs
      h0 h1 h2 h3 h4 h5 h6 h7)

-- ============================================================================
-- Output specification
-- ============================================================================

-- The SHA-256 initial hash values (FIPS 180-4, Section 5.3.3)
private def mergeH0 : Felt := Felt.ofNat 1779033703
private def mergeH1 : Felt := Felt.ofNat 3144134277
private def mergeH2 : Felt := Felt.ofNat 1013904242
private def mergeH3 : Felt := Felt.ofNat 2773480762
private def mergeH4 : Felt := Felt.ofNat 1359893119
private def mergeH5 : Felt := Felt.ofNat 2600822924
private def mergeH6 : Felt := Felt.ofNat  528734635
private def mergeH7 : Felt := Felt.ofNat 1541459225

/-- The output of `sha256::merge`: SHA-256 of a single 512-bit block followed by
    the padding block, starting from the standard initial hash values. -/
def sha256MergeOutput
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : Felt) : List Felt :=
  let W := sha256Schedule w0.val w1.val w2.val w3.val w4.val w5.val w6.val w7.val
                           w8.val w9.val w10.val w11.val w12.val w13.val w14.val w15.val
  let blk := sha256Block mergeH0.val mergeH1.val mergeH2.val mergeH3.val
                          mergeH4.val mergeH5.val mergeH6.val mergeH7.val W
  let r0 := Felt.ofNat (((Felt.ofNat blk.1).val + mergeH0.val) % 2^32)
  let r1 := Felt.ofNat (((Felt.ofNat blk.2.1).val + mergeH1.val) % 2^32)
  let r2 := Felt.ofNat (((Felt.ofNat blk.2.2.1).val + mergeH2.val) % 2^32)
  let r3 := Felt.ofNat (((Felt.ofNat blk.2.2.2.1).val + mergeH3.val) % 2^32)
  let r4 := Felt.ofNat (((Felt.ofNat blk.2.2.2.2.1).val + mergeH4.val) % 2^32)
  let r5 := Felt.ofNat (((Felt.ofNat blk.2.2.2.2.2.1).val + mergeH5.val) % 2^32)
  let r6 := Felt.ofNat (((Felt.ofNat blk.2.2.2.2.2.2.1).val + mergeH6.val) % 2^32)
  let r7 := Felt.ofNat (((Felt.ofNat blk.2.2.2.2.2.2.2).val + mergeH7.val) % 2^32)
  sha256PaddingState r0 r1 r2 r3 r4 r5 r6 r7

-- ============================================================================
-- Main correctness theorem
-- ============================================================================

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
/-- `sha256::merge` computes the SHA-256 hash of a 512-bit input block followed by
    the padding block, using the standard SHA-256 initial hash values.
    Input stack:  [W0..W15] ++ rest  (16 message words, all u32)
    Output stack: [sha256MergeOutput W0..W15] ++ rest  (8 hash words) -/
theorem sha256_merge_correct
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Felt)
    (rest : List Felt) (s : MidenState)
    (hs : s.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 ::
                    x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest)
    (h0  : x0.isU32  = true) (h1  : x1.isU32  = true)
    (h2  : x2.isU32  = true) (h3  : x3.isU32  = true)
    (h4  : x4.isU32  = true) (h5  : x5.isU32  = true)
    (h6  : x6.isU32  = true) (h7  : x7.isU32  = true)
    (h8  : x8.isU32  = true) (h9  : x9.isU32  = true)
    (h10 : x10.isU32 = true) (h11 : x11.isU32 = true)
    (h12 : x12.isU32 = true) (h13 : x13.isU32 = true)
    (h14 : x14.isU32 = true) (h15 : x15.isU32 = true) :
    ∃ locs', execWithEnv sha256ProcEnv 2127 s Miden.Core.Sha256.merge =
      some ⟨sha256MergeOutput x0 x1 x2 x3 x4 x5 x6 x7
                               x8 x9 x10 x11 x12 x13 x14 x15 ++ rest,
            s.memory, locs', s.advice⟩ := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [] at hs
  subst hs
  -- Unfold merge and step through the 8 push instructions
  unfold Miden.Core.Sha256.merge execWithEnv
  simp only [List.foldlM]
  -- Push H7, H6, H5, H4, H3, H2, H1, H0 (bottom to top)
  rw [stepPush]; miden_bind
  rw [stepPush]; miden_bind
  rw [stepPush]; miden_bind
  rw [stepPush]; miden_bind
  rw [stepPush]; miden_bind
  rw [stepPush]; miden_bind
  rw [stepPush]; miden_bind
  rw [stepPush]; miden_bind
  -- Stack now: [H0, H1, H2, H3, H4, H5, H6, H7, x0..x15, rest]
  -- Fold the pushed literal IV values back to their named definitions
  simp only [show (1779033703 : Felt) = mergeH0 from rfl,
             show (3144134277 : Felt) = mergeH1 from rfl,
             show (1013904242 : Felt) = mergeH2 from rfl,
             show (2773480762 : Felt) = mergeH3 from rfl,
             show (1359893119 : Felt) = mergeH4 from rfl,
             show (2600822924 : Felt) = mergeH5 from rfl,
             show (528734635 : Felt)  = mergeH6 from rfl,
             show (1541459225 : Felt) = mergeH7 from rfl]
  -- exec "prepare_message_schedule_and_consume" at fuel 2126
  simp only [show sha256ProcEnv "prepare_message_schedule_and_consume" =
    some Miden.Core.Sha256.prepare_message_schedule_and_consume from rfl]
  rw [sha256_prepare_message_schedule_and_consume_correct
      mergeH0 mergeH1 mergeH2 mergeH3 mergeH4 mergeH5 mergeH6 mergeH7
      x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
      rest ⟨_, mem, locs, adv⟩ rfl
      (felt_ofNat_isU32_of_lt _ (by norm_num))
      (felt_ofNat_isU32_of_lt _ (by norm_num))
      (felt_ofNat_isU32_of_lt _ (by norm_num))
      (felt_ofNat_isU32_of_lt _ (by norm_num))
      (felt_ofNat_isU32_of_lt _ (by norm_num))
      (felt_ofNat_isU32_of_lt _ (by norm_num))
      (felt_ofNat_isU32_of_lt _ (by norm_num))
      (felt_ofNat_isU32_of_lt _ (by norm_num))
      h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15]
  simp only [bind, Bind.bind, Option.bind]
  -- exec "consume_padding_message_schedule" at fuel 2126
  simp only [show sha256ProcEnv "consume_padding_message_schedule" =
    some Miden.Core.Sha256.consume_padding_message_schedule from rfl]
  rw [sha256_consume_padding_at_2126 _ _ _ _ _ _ _ _ _ _
      rfl
      (u32_mod_isU32 _) (u32_mod_isU32 _) (u32_mod_isU32 _) (u32_mod_isU32 _)
      (u32_mod_isU32 _) (u32_mod_isU32 _) (u32_mod_isU32 _) (u32_mod_isU32 _)]
  simp only [MidenState.withStack, sha256MergeOutput]
  exact ⟨_, rfl⟩

end MidenLean.Proofs.Sha256
