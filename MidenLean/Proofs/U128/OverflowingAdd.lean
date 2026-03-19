import MidenLean.Proofs.Tactics
import MidenLean.Generated.U128

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

theorem u128_overflowing_add_run
    (env : ProcEnv) (fuel : Nat)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (ha2 : a2.isU32 = true) (ha3 : a3.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true)
    (hb2 : b2.isU32 = true) (hb3 : b3.isU32 = true) :
    execWithEnv env (fuel + 1)
      ⟨b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv, evts⟩
      Miden.Core.U128.overflowing_add =
    some ⟨
      let sum0 := b0.val + a0.val
      let carry0 := sum0 / 2 ^ 32
      let sum1 := carry0 + a1.val + b1.val
      let carry1 := sum1 / 2 ^ 32
      let sum2 := carry1 + a2.val + b2.val
      let carry2 := sum2 / 2 ^ 32
      let sum3 := carry2 + a3.val + b3.val
      Felt.ofNat (sum3 / 2 ^ 32) ::
      Felt.ofNat (sum0 % 2 ^ 32) ::
      Felt.ofNat (sum1 % 2 ^ 32) ::
      Felt.ofNat (sum2 % 2 ^ 32) ::
      Felt.ofNat (sum3 % 2 ^ 32) :: rest,
      mem, locs, adv⟩ := by
  unfold Miden.Core.U128.overflowing_add execWithEnv
  simp only [List.foldlM]
  have ha0_lt : a0.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using ha0
  have ha1_lt : a1.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using ha1
  have ha2_lt : a2.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using ha2
  have ha3_lt : a3.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using ha3
  have hb0_lt : b0.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using hb0
  have hb1_lt : b1.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using hb1
  have hb2_lt : b2.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using hb2
  have hb3_lt : b3.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using hb3
  have hcarry0_lt : (b0.val + a0.val) / 2 ^ 32 < 2 ^ 32 := by omega
  have hcarry1_lt : ((b0.val + a0.val) / 2 ^ 32 + a1.val + b1.val) / 2 ^ 32 < 2 ^ 32 := by
    omega
  have hcarry2_lt :
      ((((b0.val + a0.val) / 2 ^ 32 + a1.val + b1.val) / 2 ^ 32) + a2.val + b2.val) / 2 ^ 32 <
        2 ^ 32 := by
    omega
  have hcarry0_isU32 : (Felt.ofNat ((b0.val + a0.val) / 2 ^ 32)).isU32 = true := by
    simp only [Felt.isU32, decide_eq_true_eq]
    rw [felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)]
    omega
  have hcarry1_isU32 :
      (Felt.ofNat (((b0.val + a0.val) / 2 ^ 32 + a1.val + b1.val) / 2 ^ 32)).isU32 = true := by
    simp only [Felt.isU32, decide_eq_true_eq]
    rw [felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)]
    omega
  have hcarry2_isU32 :
      (Felt.ofNat
          (((((b0.val + a0.val) / 2 ^ 32 + a1.val + b1.val) / 2 ^ 32) + a2.val + b2.val) /
            2 ^ 32)).isU32 = true := by
    simp only [Felt.isU32, decide_eq_true_eq]
    rw [felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)]
    omega
  have hcarry0_val : (Felt.ofNat ((b0.val + a0.val) / 2 ^ 32)).val = (b0.val + a0.val) / 2 ^ 32 := by
    apply felt_ofNat_val_lt
    unfold GOLDILOCKS_PRIME
    omega
  have hcarry1_val :
      (Felt.ofNat (((b0.val + a0.val) / 2 ^ 32 + a1.val + b1.val) / 2 ^ 32)).val =
        ((b0.val + a0.val) / 2 ^ 32 + a1.val + b1.val) / 2 ^ 32 := by
    apply felt_ofNat_val_lt
    unfold GOLDILOCKS_PRIME
    omega
  have hcarry2_val :
      (Felt.ofNat
          (((((b0.val + a0.val) / 2 ^ 32 + a1.val + b1.val) / 2 ^ 32) + a2.val + b2.val) /
            2 ^ 32)).val =
        ((((b0.val + a0.val) / 2 ^ 32 + a1.val + b1.val) / 2 ^ 32) + a2.val + b2.val) / 2 ^ 32 := by
    apply felt_ofNat_val_lt
    unfold GOLDILOCKS_PRIME
    omega
  have hsum0_isU32 : (Felt.ofNat ((b0.val + a0.val) % 2 ^ 32)).isU32 = true := u32_mod_isU32 _
  have hsum1_isU32 :
      (Felt.ofNat (((b0.val + a0.val) / 2 ^ 32 + a1.val + b1.val) % 2 ^ 32)).isU32 = true :=
    u32_mod_isU32 _
  have hsum2_isU32 :
      (Felt.ofNat
          (((((b0.val + a0.val) / 2 ^ 32 + a1.val + b1.val) / 2 ^ 32) + a2.val + b2.val) %
            2 ^ 32)).isU32 = true :=
    u32_mod_isU32 _
  miden_movup
  rw [stepU32WidenAdd (ha := hb0) (hb := ha0)]
  miden_bind
  miden_movdn
  miden_movup
  miden_movup
  rw [stepU32WidenAdd3 (ha := hcarry0_isU32) (hb := ha1) (hc := hb1)]
  miden_bind
  rw [hcarry0_val]
  miden_movdn
  miden_movup
  miden_movup
  rw [stepU32WidenAdd3 (ha := hcarry1_isU32) (hb := ha2) (hc := hb2)]
  miden_bind
  rw [hcarry1_val]
  miden_movdn
  miden_movup
  miden_movup
  rw [stepU32WidenAdd3 (ha := hcarry2_isU32) (hb := ha3) (hc := hb3)]
  miden_bind
  rw [hcarry2_val]
  miden_movdn
  simp only [pure, Pure.pure]

/-- `u128::overflowing_add` correctly computes addition of two 128-bit values with carry.
    Input stack:  [b0, b1, b2, b3, a0, a1, a2, a3] ++ rest
    Output stack: [overflow, c0, c1, c2, c3] ++ rest
    where `c0..c3` are the low-to-high limbs of `a + b` and `overflow` is the final carry. -/
theorem u128_overflowing_add_correct
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (ha2 : a2.isU32 = true) (ha3 : a3.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true)
    (hb2 : b2.isU32 = true) (hb3 : b3.isU32 = true) :
    exec 20 s Miden.Core.U128.overflowing_add =
    some (s.withStack (
      let sum0 := b0.val + a0.val
      let carry0 := sum0 / 2 ^ 32
      let sum1 := carry0 + a1.val + b1.val
      let carry1 := sum1 / 2 ^ 32
      let sum2 := carry1 + a2.val + b2.val
      let carry2 := sum2 / 2 ^ 32
      let sum3 := carry2 + a3.val + b3.val
      Felt.ofNat (sum3 / 2 ^ 32) ::
      Felt.ofNat (sum0 % 2 ^ 32) ::
      Felt.ofNat (sum1 % 2 ^ 32) ::
      Felt.ofNat (sum2 % 2 ^ 32) ::
      Felt.ofNat (sum3 % 2 ^ 32) :: rest)) := by
  obtain ⟨stk, mem, locs, adv, evts⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  simpa [exec] using
    u128_overflowing_add_run (fun _ => none) 19 a0 a1 a2 a3 b0 b1 b2 b3 rest mem locs adv
      ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3

end MidenLean.Proofs
