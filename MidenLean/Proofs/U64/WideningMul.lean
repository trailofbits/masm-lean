import MidenLean.Proofs.Tactics
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 16000000 in
/-- u64.widening_mul correctly computes the full 128-bit product of two u64 values.
    Input stack:  [b_lo, b_hi, a_lo, a_hi] ++ rest
    Output stack: [c0, c1, c2, c3] ++ rest
    where (c3, c2, c1, c0) is the 128-bit product a * b.
    Requires a_lo, a_hi, b_lo, b_hi to be u32 for the u32 checked arithmetic. -/
theorem u64_widening_mul_correct
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest)
    (ha_lo : a_lo.isU32 = true) (ha_hi : a_hi.isU32 = true)
    (hb_lo : b_lo.isU32 = true) (hb_hi : b_hi.isU32 = true) :
    exec 30 s Miden.Core.U64.widening_mul =
    some (s.withStack (
      let prod0 := b_lo.val * a_lo.val
      let cross1 := b_hi.val * a_lo.val + prod0 / 2^32
      let cross2 := b_lo.val * a_hi.val + cross1 % 2^32
      let high := b_hi.val * a_hi.val + cross2 / 2^32
      let widenAdd := cross1 / 2^32 + high % 2^32
      Felt.ofNat (prod0 % 2^32) ::
      Felt.ofNat (cross2 % 2^32) ::
      Felt.ofNat (widenAdd % 2^32) ::
      (Felt.ofNat (widenAdd / 2^32) + Felt.ofNat (high / 2^32)) :: rest)) := by
  miden_setup Miden.Core.U64.widening_mul
  -- 1. reversew: [b_lo, b_hi, a_lo, a_hi] -> [a_hi, a_lo, b_hi, b_lo]
  rw [stepReversew]; miden_bind
  -- 2. dup 3
  miden_dup
  -- 3. dup 2
  miden_dup
  -- 4. u32WidenMul: b_lo * a_lo
  rw [stepU32WidenMul (ha := by assumption) (hb := by assumption)]; miden_bind
  -- 5. swap 1
  miden_swap
  -- 6. dup 4
  miden_dup
  -- 7. movup 4
  miden_movup
  -- 8. u32WidenMadd: b_hi * a_lo + carry0
  have h_carry0_isU32 : (Felt.ofNat (b_lo.val * a_lo.val / 2 ^ 32)).isU32 = true :=
    u32_prod_div_isU32 b_lo a_lo hb_lo ha_lo
  have h_prod0_mod_isU32 : (Felt.ofNat (b_lo.val * a_lo.val % 2 ^ 32)).isU32 = true :=
    u32_mod_isU32 _
  rw [stepU32WidenMadd (ha := by assumption) (hb := by assumption) (hc := by assumption)]; miden_bind
  have h_carry0 : (Felt.ofNat (b_lo.val * a_lo.val / 2 ^ 32)).val =
      b_lo.val * a_lo.val / 2 ^ 32 :=
    felt_ofNat_val_lt _ (u32_prod_div_lt_prime b_lo a_lo hb_lo ha_lo)
  rw [h_carry0]
  -- 9. movup 5
  miden_movup
  -- 10. dup 4
  miden_dup
  -- 11. u32WidenMadd: b_lo * a_hi + cross1_lo
  have h_cross1_lo_isU32 : (Felt.ofNat ((b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2 ^ 32) % 2 ^ 32)).isU32 = true :=
    u32_mod_isU32 _
  have h_cross1_hi_isU32 : (Felt.ofNat ((b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2 ^ 32) / 2 ^ 32)).isU32 = true := by
    apply felt_ofNat_isU32_of_lt
    simp only [Felt.isU32, decide_eq_true_eq] at ha_lo hb_lo hb_hi
    have hcarry : b_lo.val * a_lo.val / 2^32 < 2^32 := by
      have : b_lo.val * a_lo.val ≤ (2^32 - 1) * (2^32 - 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      calc b_lo.val * a_lo.val / 2^32
          ≤ (2^32 - 1) * (2^32 - 1) / 2^32 := Nat.div_le_div_right this
        _ < 2^32 := by native_decide
    have htotal : b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2^32 ≤
        (2^32 - 1) * (2^32 - 1) + (2^32 - 1) :=
      Nat.add_le_add (Nat.mul_le_mul (by omega) (by omega)) (by omega)
    calc (b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2^32) / 2^32
        ≤ ((2^32 - 1) * (2^32 - 1) + (2^32 - 1)) / 2^32 := Nat.div_le_div_right htotal
      _ < 2^32 := by native_decide
  rw [stepU32WidenMadd (ha := by assumption) (hb := by assumption) (hc := by assumption)]; miden_bind
  have h_cross1_lo : (Felt.ofNat ((b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2 ^ 32) % 2 ^ 32)).val =
      (b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2 ^ 32) % 2 ^ 32 :=
    felt_ofNat_val_lt _ (u32_mod_lt_prime _)
  rw [h_cross1_lo]
  -- 12. swap 1
  miden_swap
  -- 13. movup 5
  miden_movup
  -- 14. movup 5
  miden_movup
  -- 15. u32WidenMadd: b_hi * a_hi + cross2_hi
  have h_cross2_lo_isU32 : (Felt.ofNat ((b_lo.val * a_hi.val + (b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2 ^ 32) % 2 ^ 32) % 2 ^ 32)).isU32 = true :=
    u32_mod_isU32 _
  have h_cross2_hi_isU32 : (Felt.ofNat ((b_lo.val * a_hi.val + (b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2 ^ 32) % 2 ^ 32) / 2 ^ 32)).isU32 = true := by
    apply felt_ofNat_isU32_of_lt
    simp only [Felt.isU32, decide_eq_true_eq] at ha_lo ha_hi hb_lo hb_hi
    have hmod : (b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2 ^ 32) % 2 ^ 32 < 2^32 :=
      Nat.mod_lt _ (by decide)
    have htotal : b_lo.val * a_hi.val + (b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2 ^ 32) % 2 ^ 32 ≤
        (2^32 - 1) * (2^32 - 1) + (2^32 - 1) :=
      Nat.add_le_add (Nat.mul_le_mul (by omega) (by omega)) (by omega)
    calc (b_lo.val * a_hi.val + (b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2 ^ 32) % 2 ^ 32) / 2^32
        ≤ ((2^32 - 1) * (2^32 - 1) + (2^32 - 1)) / 2^32 := Nat.div_le_div_right htotal
      _ < 2^32 := by native_decide
  rw [stepU32WidenMadd (ha := by assumption) (hb := by assumption) (hc := by assumption)]; miden_bind
  have h_cross2_hi : (Felt.ofNat ((b_lo.val * a_hi.val + (b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2 ^ 32) % 2 ^ 32) / 2 ^ 32)).val =
      (b_lo.val * a_hi.val + (b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2 ^ 32) % 2 ^ 32) / 2 ^ 32 := by
    apply felt_ofNat_val_lt
    simp only [Felt.isU32, decide_eq_true_eq] at ha_lo ha_hi hb_lo hb_hi
    have htotal : b_lo.val * a_hi.val + (b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2 ^ 32) % 2 ^ 32 ≤
        (2^32 - 1) * (2^32 - 1) + (2^32 - 1) :=
      Nat.add_le_add (Nat.mul_le_mul (by omega) (by omega)) (by omega)
    calc (b_lo.val * a_hi.val + (b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2 ^ 32) % 2 ^ 32) / 2^32
        ≤ ((2^32 - 1) * (2^32 - 1) + (2^32 - 1)) / 2^32 := Nat.div_le_div_right htotal
      _ < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; native_decide
  rw [h_cross2_hi]
  -- 16. swap 1
  miden_swap
  -- 17. movup 3
  miden_movup
  -- 18. movup 2
  miden_movup
  -- 19. u32WidenAdd: cross1_hi + high_lo
  have h_cross1_hi : (Felt.ofNat ((b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2 ^ 32) / 2 ^ 32)).val =
      (b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2 ^ 32) / 2 ^ 32 := by
    apply felt_ofNat_val_lt
    simp only [Felt.isU32, decide_eq_true_eq] at ha_lo hb_lo hb_hi
    have htotal : b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2^32 ≤
        (2^32 - 1) * (2^32 - 1) + (2^32 - 1) :=
      Nat.add_le_add (Nat.mul_le_mul (by omega) (by omega)) (by
        have : b_lo.val * a_lo.val ≤ (2^32 - 1) * (2^32 - 1) :=
          Nat.mul_le_mul (by omega) (by omega)
        calc b_lo.val * a_lo.val / 2^32
            ≤ (2^32 - 1) * (2^32 - 1) / 2^32 := Nat.div_le_div_right this
          _ ≤ 2^32 - 1 := by native_decide)
    calc (b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2^32) / 2^32
        ≤ ((2^32 - 1) * (2^32 - 1) + (2^32 - 1)) / 2^32 := Nat.div_le_div_right htotal
      _ < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; native_decide
  have h_high_lo : (Felt.ofNat ((b_hi.val * a_hi.val + (b_lo.val * a_hi.val + (b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2 ^ 32) % 2 ^ 32) / 2 ^ 32) % 2 ^ 32)).val =
      (b_hi.val * a_hi.val + (b_lo.val * a_hi.val + (b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2 ^ 32) % 2 ^ 32) / 2 ^ 32) % 2 ^ 32 :=
    felt_ofNat_val_lt _ (u32_mod_lt_prime _)
  have h_high_lo_isU32 : (Felt.ofNat ((b_hi.val * a_hi.val + (b_lo.val * a_hi.val + (b_hi.val * a_lo.val + b_lo.val * a_lo.val / 2 ^ 32) % 2 ^ 32) / 2 ^ 32) % 2 ^ 32)).isU32 = true :=
    u32_mod_isU32 _
  rw [stepU32WidenAdd (ha := h_cross1_hi_isU32) (hb := h_high_lo_isU32)]; miden_bind
  rw [h_cross1_hi, h_high_lo]
  -- 20. swap 1
  miden_swap
  -- 21. movup 2
  miden_movup
  -- 22. add
  rw [stepAdd]; miden_bind
  -- 23. reversew
  rw [stepReversew]; dsimp only [pure, Pure.pure]

end MidenLean.Proofs
