import MidenLean.Proofs.Tactics
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 40000000 in
/-- u64.widening_mul correctly computes the full 128-bit product of two u64 values.
    Input stack:  [b_lo, b_hi, a_lo, a_hi] ++ rest
    Output stack: [c0, c1, c2, c3] ++ rest
    where (c3, c2, c1, c0) represents the 128-bit product as four 32-bit limbs.
    This is a full multiply, not reduced mod 2^64. -/
theorem u64_widening_mul_correct
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest)
    (ha_lo : a_lo.isU32 = true) (ha_hi : a_hi.isU32 = true)
    (hb_lo : b_lo.isU32 = true) (hb_hi : b_hi.isU32 = true) :
    exec 23 s Miden.Core.Math.U64.widening_mul =
    some (s.withStack (
      let prod := a_lo.val * b_lo.val + (a_hi.val * b_lo.val) * 2^32 +
                  (a_lo.val * b_hi.val) * 2^32 + (a_hi.val * b_hi.val) * 2^64
      let c0 := Felt.ofNat (prod % 2^32)
      let c1 := Felt.ofNat ((prod / 2^32) % 2^32)
      let c2 := Felt.ofNat ((prod / 2^64) % 2^32)
      let c3 := Felt.ofNat ((prod / 2^96) % 2^32)
      c0 :: c1 :: c2 :: c3 :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.Math.U64.widening_mul execWithEnv
  simp only [List.foldlM]
  change (do
    let s' ← execInstruction ⟨b_lo :: b_hi :: a_lo :: a_hi :: rest, mem, locs, adv⟩ .reversew
    let s' ← execInstruction s' (.dup 3)
    let s' ← execInstruction s' (.dup 2)
    let s' ← execInstruction s' .u32WidenMul
    let s' ← execInstruction s' (.swap 1)
    let s' ← execInstruction s' (.dup 4)
    let s' ← execInstruction s' (.movup 4)
    let s' ← execInstruction s' .u32WidenMadd
    let s' ← execInstruction s' (.movup 5)
    let s' ← execInstruction s' (.dup 4)
    let s' ← execInstruction s' .u32WidenMadd
    let s' ← execInstruction s' (.swap 1)
    let s' ← execInstruction s' (.movup 5)
    let s' ← execInstruction s' (.movup 5)
    let s' ← execInstruction s' .u32WidenMadd
    let s' ← execInstruction s' (.swap 1)
    let s' ← execInstruction s' (.movup 3)
    let s' ← execInstruction s' (.movup 2)
    let s' ← execInstruction s' .u32WidenAdd
    let s' ← execInstruction s' (.swap 1)
    let s' ← execInstruction s' (.movup 2)
    let s' ← execInstruction s' .add
    let s' ← execInstruction s' .reversew
    pure s') = _
  -- reversew: [a_hi, a_lo, b_hi, b_lo, rest]
  rw [stepReverseW]; miden_bind
  -- dup 3: [b_lo, a_hi, a_lo, b_hi, b_lo, rest]
  miden_dup
  -- dup 2: [b_hi, b_lo, a_hi, a_lo, b_hi, b_lo, rest]
  miden_dup
  -- u32WidenMul: b_lo * b_hi
  rw [stepU32WidenMul (ha := by assumption) (hb := by assumption)]; miden_bind
  -- swap 1: rearrange for next madd
  miden_swap
  -- dup 4: [b_lo, a_lo * b_lo % 2^32, a_lo * b_lo / 2^32, a_hi, a_lo, b_hi, b_lo, rest]
  miden_dup
  -- movup 4: rearrange for madd(a_hi * b_lo)
  miden_movup
  -- u32WidenMadd: a_hi * b_lo + carry
  have h_prod_lo_isU32 : (Felt.ofNat (b_lo.val * b_hi.val % 2^32)).isU32 = true :=
    u32_mod_isU32 _
  have h_carry_1_isU32 : (Felt.ofNat (b_lo.val * b_hi.val / 2^32)).isU32 = true :=
    u32_prod_div_isU32 b_lo b_hi hb_lo hb_hi
  rw [stepU32WidenMadd (ha := by assumption) (hb := by assumption) (hc := by assumption)]; miden_bind
  -- Continue stepping through remaining instructions
  miden_movup
  miden_dup
  have h_carry_2_isU32 : (Felt.ofNat ((a_hi.val * b_lo.val + b_lo.val * b_hi.val / 2^32) / 2^32)).isU32 = true := by
    apply felt_ofNat_isU32_of_lt
    simp only [Felt.isU32, decide_eq_true_eq] at ha_lo ha_hi hb_lo hb_hi
    have h1 : a_hi.val * b_lo.val ≤ (2^32 - 1) * (2^32 - 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h2 : b_lo.val * b_hi.val / 2^32 ≤ (2^32 - 1) * (2^32 - 1) / 2^32 :=
      Nat.div_le_div_right (Nat.mul_le_mul (by omega) (by omega))
    have h3 : (2^32 - 1) * (2^32 - 1) / (2^32 : Nat) = 2^32 - 2 := by native_decide
    have h4 : a_hi.val * b_lo.val + b_lo.val * b_hi.val / 2^32
        ≤ (2^32 - 1) * (2^32 - 1) + (2^32 - 2) := by omega
    have h5 : ((2^32 - 1) * (2^32 - 1) + (2^32 - 2)) / (2^32 : Nat) = 2^32 - 2 := by native_decide
    omega
  rw [stepU32WidenMadd (ha := by assumption) (hb := by assumption) (hc := by assumption)]; miden_bind
  miden_swap
  miden_movup
  miden_movup
  have h_carry_3_isU32 : (Felt.ofNat ((a_lo.val * b_hi.val + (a_hi.val * b_lo.val + b_lo.val * b_hi.val / 2^32) / 2^32) / 2^32)).isU32 = true := by
    apply felt_ofNat_isU32_of_lt
    simp only [Felt.isU32, decide_eq_true_eq] at ha_lo ha_hi hb_lo hb_hi
    have h1 : a_lo.val * b_hi.val ≤ (2^32 - 1) * (2^32 - 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h2 : (a_hi.val * b_lo.val + b_lo.val * b_hi.val / 2^32) / 2^32 ≤ 2^32 - 2 := by
      have ha : a_hi.val * b_lo.val ≤ (2^32 - 1) * (2^32 - 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      have hb : b_lo.val * b_hi.val / 2^32 ≤ 2^32 - 2 := by
        have hh : b_lo.val * b_hi.val / 2^32 ≤ (2^32 - 1) * (2^32 - 1) / 2^32 :=
          Nat.div_le_div_right (Nat.mul_le_mul (by omega) (by omega))
        have hh2 : (2^32 - 1) * (2^32 - 1) / (2^32 : Nat) = 2^32 - 2 := by native_decide
        omega
      have hc : a_hi.val * b_lo.val + b_lo.val * b_hi.val / 2^32 ≤ (2^32 - 1)^2 + 2^32 - 2 := by omega
      have hd : ((2^32 - 1)^2 + 2^32 - 2) / (2^32 : Nat) = 2^32 - 2 := by native_decide
      omega
    have h3 : a_lo.val * b_hi.val + (a_hi.val * b_lo.val + b_lo.val * b_hi.val / 2^32) / 2^32
        ≤ (2^32 - 1)^2 + (2^32 - 2) := by omega
    have h4 : ((2^32 - 1)^2 + (2^32 - 2)) / (2^32 : Nat) = 2^32 - 2 := by native_decide
    omega
  rw [stepU32WidenMadd (ha := by assumption) (hb := by assumption) (hc := by assumption)]; miden_bind
  miden_swap
  miden_movup
  miden_movup
  rw [stepU32WidenAdd (ha := by assumption) (hb := by assumption)]; miden_bind
  miden_swap
  miden_movup
  rw [stepAdd]; miden_bind
  rw [stepReverseW]; dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]

end MidenLean.Proofs
