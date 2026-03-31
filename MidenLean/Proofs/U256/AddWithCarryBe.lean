import MidenLean.Proofs.U256.Common
import MidenLean.Proofs.Tactics

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

-- ============================================================================
-- Helper step lemmas
-- ============================================================================

set_option maxHeartbeats 4000000 in
private theorem stepU32OverflowAdd (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, frames, adv⟩ .u32OverflowAdd =
    some ⟨Felt.ofNat ((a.val + b.val) / 2^32) ::
          Felt.ofNat ((a.val + b.val) % 2^32) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execU32OverflowAdd u32WideAdd u32Max
  simp [ha, hb, MidenState.withStack]

set_option maxHeartbeats 4000000 in
private theorem stepU32OverflowAdd3 (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b c : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) :
    execInstruction ⟨c :: b :: a :: rest, mem, frames, adv⟩ .u32OverflowAdd3 =
    some ⟨Felt.ofNat ((a.val + b.val + c.val) / 2^32) ::
          Felt.ofNat ((a.val + b.val + c.val) % 2^32) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execU32OverflowAdd3 u32WideAdd3 u32Max
  simp [ha, hb, hc, MidenState.withStack]

private theorem stepSwapw3 (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 : Felt) (rest : List Felt) :
    execInstruction ⟨a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
        c0 :: c1 :: c2 :: c3 :: d0 :: d1 :: d2 :: d3 :: rest, mem, frames, adv⟩ (.swapw 3) =
      some ⟨d0 :: d1 :: d2 :: d3 :: b0 :: b1 :: b2 :: b3 ::
        c0 :: c1 :: c2 :: c3 :: a0 :: a1 :: a2 :: a3 :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execSwapw; simp [MidenState.withStack]

private theorem stepSwapw2 (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 : Felt) (rest : List Felt) :
    execInstruction ⟨a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
        c0 :: c1 :: c2 :: c3 :: rest, mem, frames, adv⟩ (.swapw 2) =
      some ⟨c0 :: c1 :: c2 :: c3 :: b0 :: b1 :: b2 :: b3 ::
        a0 :: a1 :: a2 :: a3 :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execSwapw; simp [MidenState.withStack]

-- ============================================================================
-- Main theorem
-- ============================================================================

set_option maxHeartbeats 16000000 in
theorem u256_add_with_carry_be_run
    (env : ProcEnv) (fuel : Nat)
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Felt) (rest : List Felt)
    (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (ha2 : a2.isU32 = true) (ha3 : a3.isU32 = true)
    (ha4 : a4.isU32 = true) (ha5 : a5.isU32 = true)
    (ha6 : a6.isU32 = true) (ha7 : a7.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true)
    (hb2 : b2.isU32 = true) (hb3 : b3.isU32 = true)
    (hb4 : b4.isU32 = true) (hb5 : b5.isU32 = true)
    (hb6 : b6.isU32 = true) (hb7 : b7.isU32 = true) :
    execWithEnv env (fuel + 1)
      ⟨b7 :: b6 :: b5 :: b4 :: b3 :: b2 :: b1 :: b0 ::
       a7 :: a6 :: a5 :: a4 :: a3 :: a2 :: a1 :: a0 :: rest, mem, frames, adv⟩
      Miden.Core.U256.add_with_carry_be =
    some ⟨
      let s0 := a0.val + b0.val
      let c0 := s0 / 2 ^ 32
      let s1 := c0 + a1.val + b1.val
      let c1 := s1 / 2 ^ 32
      let s2 := c1 + a2.val + b2.val
      let c2 := s2 / 2 ^ 32
      let s3 := c2 + a3.val + b3.val
      let c3 := s3 / 2 ^ 32
      let s4 := c3 + b4.val + a4.val
      let c4 := s4 / 2 ^ 32
      let s5 := c4 + b5.val + a5.val
      let c5 := s5 / 2 ^ 32
      let s6 := c5 + b6.val + a6.val
      let c6 := s6 / 2 ^ 32
      let s7 := c6 + b7.val + a7.val
      Felt.ofNat (s7 / 2 ^ 32) ::
      Felt.ofNat (s7 % 2 ^ 32) :: Felt.ofNat (s6 % 2 ^ 32) ::
      Felt.ofNat (s5 % 2 ^ 32) :: Felt.ofNat (s4 % 2 ^ 32) ::
      Felt.ofNat (s3 % 2 ^ 32) :: Felt.ofNat (s2 % 2 ^ 32) ::
      Felt.ofNat (s1 % 2 ^ 32) :: Felt.ofNat (s0 % 2 ^ 32) :: rest, mem, frames, adv⟩ := by
  unfold Miden.Core.U256.add_with_carry_be execWithEnv
  simp only [List.foldlM]
  -- Establish input bounds
  have ha0_lt : a0.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using ha0
  have ha1_lt : a1.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using ha1
  have ha2_lt : a2.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using ha2
  have ha3_lt : a3.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using ha3
  have ha4_lt : a4.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using ha4
  have ha5_lt : a5.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using ha5
  have ha6_lt : a6.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using ha6
  have ha7_lt : a7.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using ha7
  have hb0_lt : b0.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using hb0
  have hb1_lt : b1.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using hb1
  have hb2_lt : b2.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using hb2
  have hb3_lt : b3.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using hb3
  have hb4_lt : b4.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using hb4
  have hb5_lt : b5.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using hb5
  have hb6_lt : b6.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using hb6
  have hb7_lt : b7.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using hb7
  -- Carry isU32 and val lemmas for carries 0-6 (carry 7 is the final overflow)
  have hc0_isU32 : (Felt.ofNat ((a0.val + b0.val) / 2 ^ 32)).isU32 = true := by
    simp only [Felt.isU32, decide_eq_true_eq]
    rw [felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)]; omega
  have hc0_val : (Felt.ofNat ((a0.val + b0.val) / 2 ^ 32)).val =
      (a0.val + b0.val) / 2 ^ 32 :=
    felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)
  have hc1_isU32 : (Felt.ofNat (((a0.val + b0.val) / 2 ^ 32 + a1.val + b1.val) /
      2 ^ 32)).isU32 = true := by
    simp only [Felt.isU32, decide_eq_true_eq]
    rw [felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)]; omega
  have hc1_val : (Felt.ofNat (((a0.val + b0.val) / 2 ^ 32 + a1.val + b1.val) /
      2 ^ 32)).val = ((a0.val + b0.val) / 2 ^ 32 + a1.val + b1.val) / 2 ^ 32 :=
    felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)
  have hc2_isU32 : (Felt.ofNat ((((a0.val + b0.val) / 2 ^ 32 + a1.val + b1.val) /
      2 ^ 32 + a2.val + b2.val) / 2 ^ 32)).isU32 = true := by
    simp only [Felt.isU32, decide_eq_true_eq]
    rw [felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)]; omega
  have hc2_val : (Felt.ofNat ((((a0.val + b0.val) / 2 ^ 32 + a1.val + b1.val) /
      2 ^ 32 + a2.val + b2.val) / 2 ^ 32)).val =
      (((a0.val + b0.val) / 2 ^ 32 + a1.val + b1.val) / 2 ^ 32 + a2.val + b2.val) /
        2 ^ 32 :=
    felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)
  have hc3_isU32 : (Felt.ofNat (((((a0.val + b0.val) / 2 ^ 32 + a1.val + b1.val) /
      2 ^ 32 + a2.val + b2.val) / 2 ^ 32 + a3.val + b3.val) / 2 ^ 32)).isU32 = true := by
    simp only [Felt.isU32, decide_eq_true_eq]
    rw [felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)]; omega
  have hc3_val : (Felt.ofNat (((((a0.val + b0.val) / 2 ^ 32 + a1.val + b1.val) /
      2 ^ 32 + a2.val + b2.val) / 2 ^ 32 + a3.val + b3.val) / 2 ^ 32)).val =
      ((((a0.val + b0.val) / 2 ^ 32 + a1.val + b1.val) / 2 ^ 32 + a2.val + b2.val) /
        2 ^ 32 + a3.val + b3.val) / 2 ^ 32 :=
    felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)
  have hc4_isU32 : (Felt.ofNat ((((((a0.val + b0.val) / 2 ^ 32 + a1.val + b1.val) /
      2 ^ 32 + a2.val + b2.val) / 2 ^ 32 + a3.val + b3.val) / 2 ^ 32 +
      b4.val + a4.val) / 2 ^ 32)).isU32 = true := by
    simp only [Felt.isU32, decide_eq_true_eq]
    rw [felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)]; omega
  have hc4_val : (Felt.ofNat ((((((a0.val + b0.val) / 2 ^ 32 + a1.val + b1.val) /
      2 ^ 32 + a2.val + b2.val) / 2 ^ 32 + a3.val + b3.val) / 2 ^ 32 +
      b4.val + a4.val) / 2 ^ 32)).val =
      (((((a0.val + b0.val) / 2 ^ 32 + a1.val + b1.val) / 2 ^ 32 + a2.val + b2.val) /
        2 ^ 32 + a3.val + b3.val) / 2 ^ 32 + b4.val + a4.val) / 2 ^ 32 :=
    felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)
  have hc5_isU32 : (Felt.ofNat (((((((a0.val + b0.val) / 2 ^ 32 + a1.val + b1.val) /
      2 ^ 32 + a2.val + b2.val) / 2 ^ 32 + a3.val + b3.val) / 2 ^ 32 +
      b4.val + a4.val) / 2 ^ 32 + b5.val + a5.val) / 2 ^ 32)).isU32 = true := by
    simp only [Felt.isU32, decide_eq_true_eq]
    rw [felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)]; omega
  have hc5_val : (Felt.ofNat (((((((a0.val + b0.val) / 2 ^ 32 + a1.val + b1.val) /
      2 ^ 32 + a2.val + b2.val) / 2 ^ 32 + a3.val + b3.val) / 2 ^ 32 +
      b4.val + a4.val) / 2 ^ 32 + b5.val + a5.val) / 2 ^ 32)).val =
      ((((((a0.val + b0.val) / 2 ^ 32 + a1.val + b1.val) / 2 ^ 32 + a2.val + b2.val) /
        2 ^ 32 + a3.val + b3.val) / 2 ^ 32 + b4.val + a4.val) / 2 ^ 32 +
        b5.val + a5.val) / 2 ^ 32 :=
    felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)
  have hc6_isU32 : (Felt.ofNat ((((((((a0.val + b0.val) / 2 ^ 32 + a1.val + b1.val) /
      2 ^ 32 + a2.val + b2.val) / 2 ^ 32 + a3.val + b3.val) / 2 ^ 32 +
      b4.val + a4.val) / 2 ^ 32 + b5.val + a5.val) / 2 ^ 32 +
      b6.val + a6.val) / 2 ^ 32)).isU32 = true := by
    simp only [Felt.isU32, decide_eq_true_eq]
    rw [felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)]; omega
  have hc6_val : (Felt.ofNat ((((((((a0.val + b0.val) / 2 ^ 32 + a1.val + b1.val) /
      2 ^ 32 + a2.val + b2.val) / 2 ^ 32 + a3.val + b3.val) / 2 ^ 32 +
      b4.val + a4.val) / 2 ^ 32 + b5.val + a5.val) / 2 ^ 32 +
      b6.val + a6.val) / 2 ^ 32)).val =
      (((((((a0.val + b0.val) / 2 ^ 32 + a1.val + b1.val) / 2 ^ 32 + a2.val + b2.val) /
        2 ^ 32 + a3.val + b3.val) / 2 ^ 32 + b4.val + a4.val) / 2 ^ 32 +
        b5.val + a5.val) / 2 ^ 32 + b6.val + a6.val) / 2 ^ 32 :=
    felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)
  -- Step through instructions
  -- 1: swapw 3
  rw [stepSwapw3]; miden_bind
  -- 2: movup 3
  miden_movup
  -- 3: movup 7
  miden_movup
  -- 4: u32OverflowAdd (a0 + b0)
  rw [stepU32OverflowAdd (ha := ha0) (hb := hb0)]; miden_bind
  -- 5: movup 4
  miden_movup
  -- 6: movup 7
  miden_movup
  -- 7: u32OverflowAdd3 (c0 + a1 + b1)
  rw [stepU32OverflowAdd3 (ha := hc0_isU32) (hb := ha1) (hc := hb1)]; miden_bind
  rw [hc0_val]
  -- 8: movup 4
  miden_movup
  -- 9: movup 6
  miden_movup
  -- 10: u32OverflowAdd3 (c1 + a2 + b2)
  rw [stepU32OverflowAdd3 (ha := hc1_isU32) (hb := ha2) (hc := hb2)]; miden_bind
  rw [hc1_val]
  -- 11: movup 4
  miden_movup
  -- 12: movup 5
  miden_movup
  -- 13: u32OverflowAdd3 (c2 + a3 + b3)
  rw [stepU32OverflowAdd3 (ha := hc2_isU32) (hb := ha3) (hc := hb3)]; miden_bind
  rw [hc2_val]
  -- 14: movdn 12
  miden_movdn
  -- 15: swapw 2
  rw [stepSwapw2]; miden_bind
  -- 16: movup 12
  miden_movup
  -- 17: movup 4
  miden_movup
  -- 18: movup 8
  miden_movup
  -- 19: u32OverflowAdd3 (c3 + b4 + a4)
  rw [stepU32OverflowAdd3 (ha := hc3_isU32) (hb := hb4) (hc := ha4)]; miden_bind
  rw [hc3_val]
  -- 20: movup 4
  miden_movup
  -- 21: movup 7
  miden_movup
  -- 22: u32OverflowAdd3 (c4 + b5 + a5)
  rw [stepU32OverflowAdd3 (ha := hc4_isU32) (hb := hb5) (hc := ha5)]; miden_bind
  rw [hc4_val]
  -- 23: movup 4
  miden_movup
  -- 24: movup 6
  miden_movup
  -- 25: u32OverflowAdd3 (c5 + b6 + a6)
  rw [stepU32OverflowAdd3 (ha := hc5_isU32) (hb := hb6) (hc := ha6)]; miden_bind
  rw [hc5_val]
  -- 26: movup 4
  miden_movup
  -- 27: movup 5
  miden_movup
  -- 28: u32OverflowAdd3 (c6 + b7 + a7)
  rw [stepU32OverflowAdd3 (ha := hc6_isU32) (hb := hb7) (hc := ha7)]; miden_bind
  rw [hc6_val]
  simp only [pure, Pure.pure]

/-- `u256::add_with_carry_be` adds two big-endian 256-bit values with carry propagation.
    Input stack:  [b7, ..., b0, a7, ..., a0] ++ rest  (big-endian)
    Output stack: [carry, r7, r6, ..., r0] ++ rest  (big-endian)
    where r_i are the result limbs and carry is the final overflow (0 or 1). -/
theorem u256_add_with_carry_be_correct
    (a b : U256) (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) :
    execWithEnv u256ProcEnv (fuel + 1)
      ⟨b.a7.val :: b.a6.val :: b.a5.val :: b.a4.val ::
       b.a3.val :: b.a2.val :: b.a1.val :: b.a0.val ::
       a.a7.val :: a.a6.val :: a.a5.val :: a.a4.val ::
       a.a3.val :: a.a2.val :: a.a1.val :: a.a0.val :: rest, mem, frames, adv⟩
      Miden.Core.U256.add_with_carry_be =
    some ⟨
      let s0 := a.a0.val.val + b.a0.val.val
      let c0 := s0 / 2 ^ 32
      let s1 := c0 + a.a1.val.val + b.a1.val.val
      let c1 := s1 / 2 ^ 32
      let s2 := c1 + a.a2.val.val + b.a2.val.val
      let c2 := s2 / 2 ^ 32
      let s3 := c2 + a.a3.val.val + b.a3.val.val
      let c3 := s3 / 2 ^ 32
      let s4 := c3 + b.a4.val.val + a.a4.val.val
      let c4 := s4 / 2 ^ 32
      let s5 := c4 + b.a5.val.val + a.a5.val.val
      let c5 := s5 / 2 ^ 32
      let s6 := c5 + b.a6.val.val + a.a6.val.val
      let c6 := s6 / 2 ^ 32
      let s7 := c6 + b.a7.val.val + a.a7.val.val
      Felt.ofNat (s7 / 2 ^ 32) ::
      Felt.ofNat (s7 % 2 ^ 32) :: Felt.ofNat (s6 % 2 ^ 32) ::
      Felt.ofNat (s5 % 2 ^ 32) :: Felt.ofNat (s4 % 2 ^ 32) ::
      Felt.ofNat (s3 % 2 ^ 32) :: Felt.ofNat (s2 % 2 ^ 32) ::
      Felt.ofNat (s1 % 2 ^ 32) :: Felt.ofNat (s0 % 2 ^ 32) :: rest, mem, frames, adv⟩ :=
  u256_add_with_carry_be_run u256ProcEnv fuel
    a.a0.val a.a1.val a.a2.val a.a3.val a.a4.val a.a5.val a.a6.val a.a7.val
    b.a0.val b.a1.val b.a2.val b.a3.val b.a4.val b.a5.val b.a6.val b.a7.val
    rest mem frames adv
    a.a0.isU32 a.a1.isU32 a.a2.isU32 a.a3.isU32
    a.a4.isU32 a.a5.isU32 a.a6.isU32 a.a7.isU32
    b.a0.isU32 b.a1.isU32 b.a2.isU32 b.a3.isU32
    b.a4.isU32 b.a5.isU32 b.a6.isU32 b.a7.isU32

end MidenLean.Proofs
