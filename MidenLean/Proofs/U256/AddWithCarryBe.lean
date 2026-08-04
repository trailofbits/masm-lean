import MidenLean.Proofs.U256.Common
import MidenLean.Symbolic.Tactic

namespace MidenLean.Proofs

open MidenLean

-- ============================================================================
-- Chunk definitions
-- ============================================================================

/-- Chunk 1: swapw3, setup, add limbs 0 and 1. -/
private def awc_chunk1 : List Op := [
  .inst (.swapw 3), .inst (.movup 3), .inst (.movup 7), .inst .u32OverflowAdd,
  .inst (.movup 4), .inst (.movup 7), .inst .u32OverflowAdd3
]

/-- Chunk 2: add limbs 2 and 3. -/
private def awc_chunk2 : List Op := [
  .inst (.movup 4), .inst (.movup 6), .inst .u32OverflowAdd3,
  .inst (.movup 4), .inst (.movup 5), .inst .u32OverflowAdd3
]

/-- Chunk 3: transition (movdn12, swapw2, movup12) + add limbs 4 and 5. -/
private def awc_chunk3 : List Op := [
  .inst (.movdn 12), .inst (.swapw 2), .inst (.movup 12),
  .inst (.movup 4), .inst (.movup 8), .inst .u32OverflowAdd3,
  .inst (.movup 4), .inst (.movup 7), .inst .u32OverflowAdd3
]

/-- Chunk 4: add limbs 6 and 7 (final). -/
private def awc_chunk4 : List Op := [
  .inst (.movup 4), .inst (.movup 6), .inst .u32OverflowAdd3,
  .inst (.movup 4), .inst (.movup 5), .inst .u32OverflowAdd3
]

/-- The procedure body decomposes into the four chunks. -/
private theorem awc_decomp :
    Miden.Core.U256.add_with_carry_be.body =
    awc_chunk1 ++ (awc_chunk2 ++ (awc_chunk3 ++ awc_chunk4)) := by
  simp [Miden.Core.U256.add_with_carry_be, awc_chunk1, awc_chunk2, awc_chunk3, awc_chunk4]

-- ============================================================================
-- Chunk correctness lemmas
-- ============================================================================

set_option maxHeartbeats 400000 in
/-- Chunk 1: swapw3 + add limbs 0,1.
    Input:  [b7..b0, a7..a0 | rest]
    Output: [c1, r1, r0, a3, a2, b3, b2, a7..a4, b7..b4 | rest] -/
private theorem awc_chunk1_correct
    (env : ProcEnv) (fuel : Nat)
    (b7 b6 b5 b4 b3 b2 b1 b0 a7 a6 a5 a4 a3 a2 a1 a0 : Felt)
    (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true) :
    let s0 := a0.val + b0.val
    let s1 := s0 / 2^32 + a1.val + b1.val
    execProcedure env (fuel + 1)
      ⟨b7 :: b6 :: b5 :: b4 :: b3 :: b2 :: b1 :: b0 ::
       a7 :: a6 :: a5 :: a4 :: a3 :: a2 :: a1 :: a0 :: rest, mem, frames, adv⟩
      awc_chunk1 =
    some ⟨Felt.ofNat (s1 / 2^32) :: Felt.ofNat (s1 % 2^32) ::
          Felt.ofNat (s0 % 2^32) :: a3 :: a2 :: b3 :: b2 ::
          a7 :: a6 :: a5 :: a4 :: b7 :: b6 :: b5 :: b4 :: rest,
          mem, frames, adv⟩ := by
  miden_vcg

set_option maxHeartbeats 400000 in
/-- Chunk 2: add limbs 2,3.
    Input:  [cin, prev1, prev0, x3, x2, y3, y2, z0..z3, w0..w3 | rest]
    Output: [c3, r2, r1, prev1, prev0, z0..z3, w0..w3 | rest] -/
private theorem awc_chunk2_correct
    (env : ProcEnv) (fuel : Nat)
    (cin prev1 prev0 x3 x2 y3 y2 z0 z1 z2 z3 w0 w1 w2 w3 : Felt)
    (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (hcin : cin.isU32 = true)
    (hx2 : x2.isU32 = true) (hy2 : y2.isU32 = true)
    (hx3 : x3.isU32 = true) (hy3 : y3.isU32 = true) :
    let s2 := cin.val + x2.val + y2.val
    let s3 := s2 / 2^32 + x3.val + y3.val
    execProcedure env (fuel + 1)
      ⟨cin :: prev1 :: prev0 :: x3 :: x2 :: y3 :: y2 :: z0 :: z1 :: z2 :: z3 ::
       w0 :: w1 :: w2 :: w3 :: rest, mem, frames, adv⟩
      awc_chunk2 =
    some ⟨Felt.ofNat (s3 / 2^32) :: Felt.ofNat (s3 % 2^32) ::
          Felt.ofNat (s2 % 2^32) :: prev1 :: prev0 ::
          z0 :: z1 :: z2 :: z3 :: w0 :: w1 :: w2 :: w3 :: rest,
          mem, frames, adv⟩ := by
  miden_vcg

set_option maxHeartbeats 400000 in
/-- Chunk 3: transition (movdn12, swapw2, movup12) + add limbs 4,5.
    Input:  [cin, prev3..prev0, z0..z3, w0..w3 | rest]
    Output: [c5, r5, r4, w0, w1, z0, z1, prev3..prev0 | rest] -/
private theorem awc_chunk3_correct
    (env : ProcEnv) (fuel : Nat)
    (cin prev3 prev2 prev1 prev0 z0 z1 z2 z3 w0 w1 w2 w3 : Felt)
    (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (hcin : cin.isU32 = true)
    (hw3 : w3.isU32 = true) (hz3 : z3.isU32 = true)
    (hw2 : w2.isU32 = true) (hz2 : z2.isU32 = true) :
    let s4 := cin.val + w3.val + z3.val
    let s5 := s4 / 2^32 + w2.val + z2.val
    execProcedure env (fuel + 1)
      ⟨cin :: prev3 :: prev2 :: prev1 :: prev0 ::
       z0 :: z1 :: z2 :: z3 :: w0 :: w1 :: w2 :: w3 :: rest, mem, frames, adv⟩
      awc_chunk3 =
    some ⟨Felt.ofNat (s5 / 2^32) :: Felt.ofNat (s5 % 2^32) :: Felt.ofNat (s4 % 2^32) ::
          w0 :: w1 :: z0 :: z1 :: prev3 :: prev2 :: prev1 :: prev0 :: rest,
          mem, frames, adv⟩ := by
  miden_vcg

set_option maxHeartbeats 400000 in
/-- Chunk 4: add limbs 6,7 (final).
    Input:  [cin, prev5, prev4, w0, w1, z0, z1, prev3..prev0 | rest]
    Output: [carry, r7, r6, prev5, prev4, prev3..prev0 | rest] -/
private theorem awc_chunk4_correct
    (env : ProcEnv) (fuel : Nat)
    (cin prev5 prev4 w0 w1 z0 z1 prev3 prev2 prev1 prev0 : Felt)
    (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (hcin : cin.isU32 = true)
    (hw1 : w1.isU32 = true) (hz1 : z1.isU32 = true)
    (hw0 : w0.isU32 = true) (hz0 : z0.isU32 = true) :
    let s6 := cin.val + w1.val + z1.val
    let s7 := s6 / 2^32 + w0.val + z0.val
    execProcedure env (fuel + 1)
      ⟨cin :: prev5 :: prev4 :: w0 :: w1 :: z0 :: z1 ::
       prev3 :: prev2 :: prev1 :: prev0 :: rest, mem, frames, adv⟩
      awc_chunk4 =
    some ⟨Felt.ofNat (s7 / 2^32) :: Felt.ofNat (s7 % 2^32) :: Felt.ofNat (s6 % 2^32) ::
          prev5 :: prev4 :: prev3 :: prev2 :: prev1 :: prev0 :: rest,
          mem, frames, adv⟩ := by
  miden_vcg

-- ============================================================================
-- Carry chain bridging lemma
-- ============================================================================

/-- The carry chain computes a.toNat + b.toNat: carry * 2^256 + result_limbs = sum. -/
private theorem carry_chain_eq_sum
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Nat)
    (_ha0 : a0 < 2^32) (_ha1 : a1 < 2^32) (_ha2 : a2 < 2^32) (_ha3 : a3 < 2^32)
    (_ha4 : a4 < 2^32) (_ha5 : a5 < 2^32) (_ha6 : a6 < 2^32) (_ha7 : a7 < 2^32)
    (_hb0 : b0 < 2^32) (_hb1 : b1 < 2^32) (_hb2 : b2 < 2^32) (_hb3 : b3 < 2^32)
    (_hb4 : b4 < 2^32) (_hb5 : b5 < 2^32) (_hb6 : b6 < 2^32) (_hb7 : b7 < 2^32) :
    let s0 := a0 + b0
    let s1 := s0 / 2^32 + a1 + b1
    let s2 := s1 / 2^32 + a2 + b2
    let s3 := s2 / 2^32 + a3 + b3
    let s4 := s3 / 2^32 + b4 + a4
    let s5 := s4 / 2^32 + b5 + a5
    let s6 := s5 / 2^32 + b6 + a6
    let s7 := s6 / 2^32 + b7 + a7
    s7 / 2^32 * 2^256 +
    (s7 % 2^32 * 2^224 + s6 % 2^32 * 2^192 + s5 % 2^32 * 2^160 + s4 % 2^32 * 2^128 +
     s3 % 2^32 * 2^96 + s2 % 2^32 * 2^64 + s1 % 2^32 * 2^32 + s0 % 2^32) =
    (a7 * 2^224 + a6 * 2^192 + a5 * 2^160 + a4 * 2^128 +
     a3 * 2^96 + a2 * 2^64 + a1 * 2^32 + a0) +
    (b7 * 2^224 + b6 * 2^192 + b5 * 2^160 + b4 * 2^128 +
     b3 * 2^96 + b2 * 2^64 + b1 * 2^32 + b0) := by
  simp only []
  set q0 := (a0 + b0) / 2^32
  set r0 := (a0 + b0) % 2^32
  have h0 : q0 * 2^32 + r0 = a0 + b0 := by omega
  have h0r : r0 < 2^32 := Nat.mod_lt _ (by positivity)
  set q1 := (q0 + a1 + b1) / 2^32
  set r1 := (q0 + a1 + b1) % 2^32
  have h1 : q1 * 2^32 + r1 = q0 + a1 + b1 := by omega
  have h1r : r1 < 2^32 := Nat.mod_lt _ (by positivity)
  set q2 := (q1 + a2 + b2) / 2^32
  set r2 := (q1 + a2 + b2) % 2^32
  have h2 : q2 * 2^32 + r2 = q1 + a2 + b2 := by omega
  have h2r : r2 < 2^32 := Nat.mod_lt _ (by positivity)
  set q3 := (q2 + a3 + b3) / 2^32
  set r3 := (q2 + a3 + b3) % 2^32
  have h3 : q3 * 2^32 + r3 = q2 + a3 + b3 := by omega
  have h3r : r3 < 2^32 := Nat.mod_lt _ (by positivity)
  set q4 := (q3 + b4 + a4) / 2^32
  set r4 := (q3 + b4 + a4) % 2^32
  have h4 : q4 * 2^32 + r4 = q3 + b4 + a4 := by omega
  have h4r : r4 < 2^32 := Nat.mod_lt _ (by positivity)
  set q5 := (q4 + b5 + a5) / 2^32
  set r5 := (q4 + b5 + a5) % 2^32
  have h5 : q5 * 2^32 + r5 = q4 + b5 + a5 := by omega
  have h5r : r5 < 2^32 := Nat.mod_lt _ (by positivity)
  set q6 := (q5 + b6 + a6) / 2^32
  set r6 := (q5 + b6 + a6) % 2^32
  have h6 : q6 * 2^32 + r6 = q5 + b6 + a6 := by omega
  have h6r : r6 < 2^32 := Nat.mod_lt _ (by positivity)
  set q7 := (q6 + b7 + a7) / 2^32
  set r7 := (q6 + b7 + a7) % 2^32
  have h7 : q7 * 2^32 + r7 = q6 + b7 + a7 := by omega
  have h7r : r7 < 2^32 := Nat.mod_lt _ (by positivity)
  omega

/-- Given carry * 2^256 + (d7*2^224 + ... + d0) = total with each dk < 2^32,
    each dk equals the corresponding digit extraction from total. -/
private theorem digit_extraction
    (carry d7 d6 d5 d4 d3 d2 d1 d0 total : Nat)
    (h0 : d0 < 2^32) (h1 : d1 < 2^32) (h2 : d2 < 2^32) (h3 : d3 < 2^32)
    (h4 : d4 < 2^32) (h5 : d5 < 2^32) (h6 : d6 < 2^32) (h7 : d7 < 2^32)
    (hchain : carry * 2^256 +
              (d7 * 2^224 + d6 * 2^192 + d5 * 2^160 + d4 * 2^128 +
               d3 * 2^96 + d2 * 2^64 + d1 * 2^32 + d0) = total) :
    carry = total / 2^256 ∧
    d7 = (total / 2^224) % 2^32 ∧
    d6 = (total / 2^192) % 2^32 ∧
    d5 = (total / 2^160) % 2^32 ∧
    d4 = (total / 2^128) % 2^32 ∧
    d3 = (total / 2^96) % 2^32 ∧
    d2 = (total / 2^64) % 2^32 ∧
    d1 = (total / 2^32) % 2^32 ∧
    d0 = total % 2^32 := by
  constructor; · omega
  constructor; · omega
  constructor; · omega
  constructor; · omega
  constructor; · omega
  constructor; · omega
  constructor; · omega
  constructor; · omega
  omega

-- ============================================================================
-- Main theorem: chunked composition (carry-chain form)
-- ============================================================================

set_option maxHeartbeats 8000000 in
/-- `u256::add_with_carry_be` raw carry-chain form.
    Input stack:  [b7, ..., b0, a7, ..., a0] ++ rest  (big-endian limbs)
    Output stack: [carry, r7, ..., r0] ++ rest
    where carry * 2^256 + U256.mk(r0..r7).toNat = a.toNat + b.toNat.
    Parametric in `fuel` so this lemma serves both as a callee summary for
    reflective callers and as the basis for `u256_add_with_carry_be_correct`. -/
@[miden_exec_summary]
theorem u256_add_with_carry_be_exec
    (a b : U256) (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) :
    let s := a.toNat + b.toNat
    execProcedure u256ProcEnv (fuel + 1)
      ⟨b.a7.val :: b.a6.val :: b.a5.val :: b.a4.val ::
       b.a3.val :: b.a2.val :: b.a1.val :: b.a0.val ::
       a.a7.val :: a.a6.val :: a.a5.val :: a.a4.val ::
       a.a3.val :: a.a2.val :: a.a1.val :: a.a0.val :: rest, mem, frames, adv⟩
      Miden.Core.U256.add_with_carry_be =
    some ⟨Felt.ofNat (s / 2^256) ::
          Felt.ofNat ((s / 2^224) % 2^32) :: Felt.ofNat ((s / 2^192) % 2^32) ::
          Felt.ofNat ((s / 2^160) % 2^32) :: Felt.ofNat ((s / 2^128) % 2^32) ::
          Felt.ofNat ((s / 2^96) % 2^32)  :: Felt.ofNat ((s / 2^64) % 2^32) ::
          Felt.ofNat ((s / 2^32) % 2^32)  :: Felt.ofNat (s % 2^32) :: rest,
          mem, frames, adv⟩ := by
  -- Decompose procedure into chunks
  rw [execProcedure_body_eq _ _ _ _ _ awc_decomp rfl, execProcedure_append]
  -- Chunk 1
  rw [awc_chunk1_correct (ha0 := a.a0_isU32) (ha1 := a.a1_isU32)
      (hb0 := b.a0_isU32) (hb1 := b.a1_isU32)]
  simp only [bind, Bind.bind, Option.bind]
  -- Abbreviate carry chain values after chunk 1
  set s0 := a.a0.val.val + b.a0.val.val
  set s1 := s0 / 2 ^ 32 + a.a1.val.val + b.a1.val.val
  -- Chunk 2
  rw [execProcedure_append]
  have hc1_isU32 : (Felt.ofNat (s1 / 2 ^ 32)).isU32 = true := by
    apply felt_ofNat_isU32_of_lt
    have := a.a0.val_lt; have := b.a0.val_lt
    have := a.a1.val_lt; have := b.a1.val_lt
    omega
  have hc1_val : (Felt.ofNat (s1 / 2 ^ 32)).val = s1 / 2 ^ 32 := by
    apply felt_ofNat_val_lt; unfold GOLDILOCKS_PRIME
    have := a.a0.val_lt; have := b.a0.val_lt
    have := a.a1.val_lt; have := b.a1.val_lt
    omega
  rw [awc_chunk2_correct (hcin := hc1_isU32) (hx2 := a.a2_isU32) (hy2 := b.a2_isU32)
      (hx3 := a.a3_isU32) (hy3 := b.a3_isU32)]
  simp only [bind, Bind.bind, Option.bind]
  conv_lhs => rw [hc1_val]
  -- Abbreviate carry chain values after chunk 2
  set s2 := s1 / 2 ^ 32 + a.a2.val.val + b.a2.val.val
  set s3 := s2 / 2 ^ 32 + a.a3.val.val + b.a3.val.val
  -- Chunk 3
  rw [execProcedure_append]
  have hc3_isU32 : (Felt.ofNat (s3 / 2 ^ 32)).isU32 = true := by
    apply felt_ofNat_isU32_of_lt
    have := a.a0.val_lt; have := b.a0.val_lt; have := a.a1.val_lt; have := b.a1.val_lt
    have := a.a2.val_lt; have := b.a2.val_lt; have := a.a3.val_lt; have := b.a3.val_lt
    omega
  have hc3_val : (Felt.ofNat (s3 / 2 ^ 32)).val = s3 / 2 ^ 32 := by
    apply felt_ofNat_val_lt; unfold GOLDILOCKS_PRIME
    have := a.a0.val_lt; have := b.a0.val_lt; have := a.a1.val_lt; have := b.a1.val_lt
    have := a.a2.val_lt; have := b.a2.val_lt; have := a.a3.val_lt; have := b.a3.val_lt
    omega
  rw [awc_chunk3_correct (hcin := hc3_isU32) (hw3 := b.a4_isU32) (hz3 := a.a4_isU32)
      (hw2 := b.a5_isU32) (hz2 := a.a5_isU32)]
  simp only [bind, Bind.bind, Option.bind]
  conv_lhs => rw [hc3_val]
  -- Abbreviate carry chain values after chunk 3
  set s4 := s3 / 2 ^ 32 + b.a4.val.val + a.a4.val.val
  set s5 := s4 / 2 ^ 32 + b.a5.val.val + a.a5.val.val
  -- Chunk 4
  have hc5_isU32 : (Felt.ofNat (s5 / 2 ^ 32)).isU32 = true := by
    apply felt_ofNat_isU32_of_lt
    have := a.a0.val_lt; have := b.a0.val_lt; have := a.a1.val_lt; have := b.a1.val_lt
    have := a.a2.val_lt; have := b.a2.val_lt; have := a.a3.val_lt; have := b.a3.val_lt
    have := a.a4.val_lt; have := b.a4.val_lt; have := a.a5.val_lt; have := b.a5.val_lt
    omega
  have hc5_val : (Felt.ofNat (s5 / 2 ^ 32)).val = s5 / 2 ^ 32 := by
    apply felt_ofNat_val_lt; unfold GOLDILOCKS_PRIME
    have := a.a0.val_lt; have := b.a0.val_lt; have := a.a1.val_lt; have := b.a1.val_lt
    have := a.a2.val_lt; have := b.a2.val_lt; have := a.a3.val_lt; have := b.a3.val_lt
    have := a.a4.val_lt; have := b.a4.val_lt; have := a.a5.val_lt; have := b.a5.val_lt
    omega
  rw [awc_chunk4_correct (hcin := hc5_isU32) (hw1 := b.a6_isU32) (hz1 := a.a6_isU32)
      (hw0 := b.a7_isU32) (hz0 := a.a7_isU32)]
  conv_lhs => rw [hc5_val]
  -- Abbreviate remaining carry chain values
  set s6 := s5 / 2 ^ 32 + b.a6.val.val + a.a6.val.val
  set s7 := s6 / 2 ^ 32 + b.a7.val.val + a.a7.val.val
  -- The carry chain identity
  have hchain := carry_chain_eq_sum
    a.a0.val.val a.a1.val.val a.a2.val.val a.a3.val.val
    a.a4.val.val a.a5.val.val a.a6.val.val a.a7.val.val
    b.a0.val.val b.a1.val.val b.a2.val.val b.a3.val.val
    b.a4.val.val b.a5.val.val b.a6.val.val b.a7.val.val
    a.a0.val_lt a.a1.val_lt a.a2.val_lt a.a3.val_lt
    a.a4.val_lt a.a5.val_lt a.a6.val_lt a.a7.val_lt
    b.a0.val_lt b.a1.val_lt b.a2.val_lt b.a3.val_lt
    b.a4.val_lt b.a5.val_lt b.a6.val_lt b.a7.val_lt
  simp only [] at hchain
  -- Digit extraction
  have hdigits := digit_extraction (s7 / 2 ^ 32)
    (s7 % 2 ^ 32) (s6 % 2 ^ 32) (s5 % 2 ^ 32) (s4 % 2 ^ 32)
    (s3 % 2 ^ 32) (s2 % 2 ^ 32) (s1 % 2 ^ 32) (s0 % 2 ^ 32)
    (a.toNat + b.toNat)
    (Nat.mod_lt _ (by positivity)) (Nat.mod_lt _ (by positivity))
    (Nat.mod_lt _ (by positivity)) (Nat.mod_lt _ (by positivity))
    (Nat.mod_lt _ (by positivity)) (Nat.mod_lt _ (by positivity))
    (Nat.mod_lt _ (by positivity)) (Nat.mod_lt _ (by positivity))
  simp only [U256.toNat] at hdigits
  obtain ⟨hdc, hd7, hd6, hd5, hd4, hd3, hd2, hd1, hd0⟩ := hdigits hchain
  simp only [hdc, hd7, hd6, hd5, hd4, hd3, hd2, hd1, hd0, U256.toNat]

/-- `u256::add_with_carry_be` adds two big-endian 256-bit values with carry propagation.
    Input stack:  [b.a7, ..., b.a0, a.a7, ..., a.a0] ++ rest
    Output stack: [(a.toNat+b.toNat)/2^256, (a+b).a7, ..., (a+b).a0] ++ rest
    where the carry is 0 or 1. -/
theorem u256_add_with_carry_be_correct
    (a b : U256) (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) :
    execProcedure u256ProcEnv (fuel + 1)
      ⟨b.a7.val :: b.a6.val :: b.a5.val :: b.a4.val ::
       b.a3.val :: b.a2.val :: b.a1.val :: b.a0.val ::
       a.a7.val :: a.a6.val :: a.a5.val :: a.a4.val ::
       a.a3.val :: a.a2.val :: a.a1.val :: a.a0.val :: rest, mem, frames, adv⟩
      Miden.Core.U256.add_with_carry_be =
    some ⟨Felt.ofNat ((a.toNat + b.toNat) / 2^256) ::
          (a + b).a7.val :: (a + b).a6.val :: (a + b).a5.val :: (a + b).a4.val ::
          (a + b).a3.val :: (a + b).a2.val :: (a + b).a1.val :: (a + b).a0.val :: rest,
          mem, frames, adv⟩ := by
  rw [u256_add_with_carry_be_exec a b rest mem frames adv fuel]
  simp only [HAdd.hAdd, Add.add, U256.ofNat_a0, U256.ofNat_a1, U256.ofNat_a2, U256.ofNat_a3,
             U256.ofNat_a4, U256.ofNat_a5, U256.ofNat_a6, U256.ofNat_a7]

end MidenLean.Proofs
