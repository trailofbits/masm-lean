import MidenLean.Proofs.U256.Common
import MidenLean.Proofs.Tactics

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

-- ============================================================================
-- Chunk definitions
-- ============================================================================

private def xor_half1 : List Op := [
  .inst (.swapw 3),
  .inst (.movup 3),
  .inst (.movup 7),
  .inst (.u32Xor),
  .inst (.movup 3),
  .inst (.movup 6),
  .inst (.u32Xor),
  .inst (.movup 3),
  .inst (.movup 5),
  .inst (.u32Xor),
  .inst (.movup 3),
  .inst (.movup 4),
  .inst (.u32Xor)
]

private def xor_half2 : List Op := [
  .inst (.swapw 2),
  .inst (.movup 3),
  .inst (.movup 7),
  .inst (.u32Xor),
  .inst (.movup 3),
  .inst (.movup 6),
  .inst (.u32Xor),
  .inst (.movup 3),
  .inst (.movup 5),
  .inst (.u32Xor),
  .inst (.movup 3),
  .inst (.movup 4),
  .inst (.u32Xor)
]

private theorem xor_decomp :
    Miden.Core.U256.xor = xor_half1 ++ xor_half2 := by
  simp [Miden.Core.U256.xor, xor_half1, xor_half2]

-- ============================================================================
-- Swapw helper lemmas
-- ============================================================================

private theorem stepSwapw3 (mem locs : Nat → Felt) (adv : List Felt)
    (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 : Felt) (rest : List Felt) :
    execInstruction ⟨a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
        c0 :: c1 :: c2 :: c3 :: d0 :: d1 :: d2 :: d3 :: rest, mem, locs, adv⟩ (.swapw 3) =
      some ⟨d0 :: d1 :: d2 :: d3 :: b0 :: b1 :: b2 :: b3 ::
        c0 :: c1 :: c2 :: c3 :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execSwapw; simp [MidenState.withStack]

private theorem stepSwapw2 (mem locs : Nat → Felt) (adv : List Felt)
    (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 : Felt) (rest : List Felt) :
    execInstruction ⟨a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
        c0 :: c1 :: c2 :: c3 :: rest, mem, locs, adv⟩ (.swapw 2) =
      some ⟨c0 :: c1 :: c2 :: c3 :: b0 :: b1 :: b2 :: b3 ::
        a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execSwapw; simp [MidenState.withStack]

-- ============================================================================
-- Chunk correctness lemmas
-- ============================================================================

set_option maxHeartbeats 16000000 in
private theorem xor_half1_correct
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Felt)
    (rest : List Felt) (mem locs : Nat → Felt) (adv : List Felt)
    (ha4 : a4.isU32 = true) (ha5 : a5.isU32 = true)
    (ha6 : a6.isU32 = true) (ha7 : a7.isU32 = true)
    (hb4 : b4.isU32 = true) (hb5 : b5.isU32 = true)
    (hb6 : b6.isU32 = true) (hb7 : b7.isU32 = true) :
    exec 31 ⟨b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 ::
        a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: rest, mem, locs, adv⟩ xor_half1 =
    some ⟨Felt.ofNat (a4.val ^^^ b4.val) ::
        Felt.ofNat (a5.val ^^^ b5.val) ::
        Felt.ofNat (a6.val ^^^ b6.val) ::
        Felt.ofNat (a7.val ^^^ b7.val) ::
        a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 :: rest, mem, locs, adv⟩ := by
  unfold exec xor_half1 execWithEnv
  simp only [List.foldlM]
  rw [stepSwapw3]; miden_bind
  miden_movup; miden_movup
  rw [stepU32Xor (ha := ha7) (hb := hb7)]; miden_bind
  miden_movup; miden_movup
  rw [stepU32Xor (ha := ha6) (hb := hb6)]; miden_bind
  miden_movup; miden_movup
  rw [stepU32Xor (ha := ha5) (hb := hb5)]; miden_bind
  miden_movup; miden_movup
  rw [stepU32Xor (ha := ha4) (hb := hb4)]
  simp only [pure, Pure.pure]

set_option maxHeartbeats 16000000 in
private theorem xor_half2_correct
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt)
    (r4 r5 r6 r7 : Felt)
    (rest : List Felt) (mem locs : Nat → Felt) (adv : List Felt)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (ha2 : a2.isU32 = true) (ha3 : a3.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true)
    (hb2 : b2.isU32 = true) (hb3 : b3.isU32 = true) :
    exec 31 ⟨r4 :: r5 :: r6 :: r7 ::
        a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 :: rest, mem, locs, adv⟩ xor_half2 =
    some ⟨Felt.ofNat (b0.val ^^^ a0.val) ::
        Felt.ofNat (b1.val ^^^ a1.val) ::
        Felt.ofNat (b2.val ^^^ a2.val) ::
        Felt.ofNat (b3.val ^^^ a3.val) ::
        r4 :: r5 :: r6 :: r7 :: rest, mem, locs, adv⟩ := by
  unfold exec xor_half2 execWithEnv
  simp only [List.foldlM]
  rw [stepSwapw2]; miden_bind
  miden_movup; miden_movup
  rw [stepU32Xor (ha := hb3) (hb := ha3)]; miden_bind
  miden_movup; miden_movup
  rw [stepU32Xor (ha := hb2) (hb := ha2)]; miden_bind
  miden_movup; miden_movup
  rw [stepU32Xor (ha := hb1) (hb := ha1)]; miden_bind
  miden_movup; miden_movup
  rw [stepU32Xor (ha := hb0) (hb := ha0)]
  simp only [pure, Pure.pure]

-- ============================================================================
-- Main theorems
-- ============================================================================

set_option maxHeartbeats 8000000 in
theorem u256_xor_raw
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Felt)
    (rest : List Felt) (s : MidenState)
    (hs : s.stack = b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 ::
                    a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: rest)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (ha2 : a2.isU32 = true) (ha3 : a3.isU32 = true)
    (ha4 : a4.isU32 = true) (ha5 : a5.isU32 = true)
    (ha6 : a6.isU32 = true) (ha7 : a7.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true)
    (hb2 : b2.isU32 = true) (hb3 : b3.isU32 = true)
    (hb4 : b4.isU32 = true) (hb5 : b5.isU32 = true)
    (hb6 : b6.isU32 = true) (hb7 : b7.isU32 = true) :
    exec 31 s Miden.Core.U256.xor =
    some (s.withStack (
      Felt.ofNat (b0.val ^^^ a0.val) ::
      Felt.ofNat (b1.val ^^^ a1.val) ::
      Felt.ofNat (b2.val ^^^ a2.val) ::
      Felt.ofNat (b3.val ^^^ a3.val) ::
      Felt.ofNat (a4.val ^^^ b4.val) ::
      Felt.ofNat (a5.val ^^^ b5.val) ::
      Felt.ofNat (a6.val ^^^ b6.val) ::
      Felt.ofNat (a7.val ^^^ b7.val) :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  rw [xor_decomp, MidenLean.exec_append]
  rw [xor_half1_correct (ha4 := ha4) (ha5 := ha5) (ha6 := ha6) (ha7 := ha7)
    (hb4 := hb4) (hb5 := hb5) (hb6 := hb6) (hb7 := hb7)]
  simp only [bind, Bind.bind, Option.bind]
  rw [xor_half2_correct (ha0 := ha0) (ha1 := ha1) (ha2 := ha2) (ha3 := ha3)
    (hb0 := hb0) (hb1 := hb1) (hb2 := hb2) (hb3 := hb3)]

/-- `u256::xor` computes bitwise XOR of two 256-bit values.
    Input stack:  [b.a0, b.a1, ..., b.a7, a.a0, a.a1, ..., a.a7] ++ rest
    Output stack: [(a ^^^ b).a0, (a ^^^ b).a1, ..., (a ^^^ b).a7] ++ rest -/
theorem u256_xor_correct (a b : U256) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val ::
                    b.a4.val :: b.a5.val :: b.a6.val :: b.a7.val ::
                    a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val ::
                    a.a4.val :: a.a5.val :: a.a6.val :: a.a7.val :: rest) :
    exec 31 s Miden.Core.U256.xor =
    some (s.withStack (
      (a ^^^ b).a0.val :: (a ^^^ b).a1.val ::
      (a ^^^ b).a2.val :: (a ^^^ b).a3.val ::
      (a ^^^ b).a4.val :: (a ^^^ b).a5.val ::
      (a ^^^ b).a6.val :: (a ^^^ b).a7.val :: rest)) := by
  simp only [U256.xor_a0, U256.xor_a1, U256.xor_a2, U256.xor_a3,
    U256.xor_a4, U256.xor_a5, U256.xor_a6, U256.xor_a7,
    Nat.xor_comm a.a0.val.val, Nat.xor_comm a.a1.val.val,
    Nat.xor_comm a.a2.val.val, Nat.xor_comm a.a3.val.val]
  exact u256_xor_raw a.a0.val a.a1.val a.a2.val a.a3.val
    a.a4.val a.a5.val a.a6.val a.a7.val
    b.a0.val b.a1.val b.a2.val b.a3.val
    b.a4.val b.a5.val b.a6.val b.a7.val rest s hs
    a.a0.isU32 a.a1.isU32 a.a2.isU32 a.a3.isU32
    a.a4.isU32 a.a5.isU32 a.a6.isU32 a.a7.isU32
    b.a0.isU32 b.a1.isU32 b.a2.isU32 b.a3.isU32
    b.a4.isU32 b.a5.isU32 b.a6.isU32 b.a7.isU32

end MidenLean.Proofs
